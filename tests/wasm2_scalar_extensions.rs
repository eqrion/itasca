//! Literal scalar extension encodings keep feature gates and LEB behavior visible.
use itasca::{validate_module, ValidationProfile};

fn module(input: u8, output: u8, operation: &[u8]) -> Vec<u8> {
    let mut bytes = vec![
        0,
        97,
        115,
        109,
        1,
        0,
        0,
        0, // Header.
        1,
        6,
        1,
        96,
        1,
        input,
        1,
        output, // One function type.
        3,
        2,
        1,
        0, // One function.
        10,
        (operation.len() + 6) as u8,
        1,
        (operation.len() + 4) as u8,
        0,
        32,
        0, // No locals; local.get 0.
    ];
    bytes.extend_from_slice(operation);
    bytes.push(11);
    bytes
}

fn check(input: u8, output: u8, operation: &[u8]) {
    let bytes = module(input, output, operation);
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::WASM2)
        .validate_all(&bytes)
        .unwrap();
    assert!(validate_module(&bytes, ValidationProfile::Wasm2).is_ok());
    assert!(validate_module(&bytes, ValidationProfile::Wasm1).is_err());
    let wrong = if input == 127 { 126 } else { 127 };
    assert!(validate_module(&module(wrong, output, operation), ValidationProfile::Wasm2).is_err());
}

#[test]
fn sign_extensions_preserve_integer_width_and_profile_gate() {
    for opcode in 0xc0..=0xc4 {
        let ty = if opcode < 0xc2 { 127 } else { 126 };
        check(ty, ty, &[opcode]);
    }
}

#[test]
fn saturating_conversions_accept_all_valid_subopcode_widths() {
    for subopcode in 0..8 {
        let input = if subopcode % 4 < 2 { 125 } else { 124 };
        let output = if subopcode < 4 { 127 } else { 126 };
        check(input, output, &[0xfc, subopcode]);
        check(input, output, &[0xfc, subopcode + 128, 0]);
        check(input, output, &[0xfc, subopcode + 128, 128, 128, 128, 0]);
    }
}

#[test]
fn prefixed_opcode_rejects_malformed_and_reserved_subopcodes() {
    for operation in [
        &[0xfc][..],
        &[0xfc, 128, 128, 128, 128, 128, 0],
        &[0xfc, 128, 128, 128, 128, 16],
        &[0xfc, 18],
        &[0xfc, 255, 255, 255, 255, 15],
    ] {
        let bytes = module(125, 127, operation);
        assert!(
            wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::WASM2)
                .validate_all(&bytes)
                .is_err()
        );
        assert!(validate_module(&bytes, ValidationProfile::Wasm2).is_err());
    }
}
