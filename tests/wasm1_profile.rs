//! Wasm 1.0 runs the Wasm 2.0 body rules plus the filters for its grammar and
//! `br_table` typing; each case here separates the two profiles.
use itasca::{validate_module, ValidationProfile};

fn section(id: u8, payload: &[u8]) -> Vec<u8> {
    let mut bytes = vec![id];
    leb(&mut bytes, payload.len() as u32);
    bytes.extend_from_slice(payload);
    bytes
}

fn leb(bytes: &mut Vec<u8>, mut value: u32) {
    loop {
        let byte = (value & 0x7f) as u8;
        value >>= 7;
        if value == 0 {
            bytes.push(byte);
            return;
        }
        bytes.push(byte | 0x80);
    }
}

/// One `() -> ()` function with an optional funcref table and the given body
/// instructions, which must leave the stack empty.
fn module(table: bool, body: &[u8]) -> Vec<u8> {
    let mut bytes = vec![0, 97, 115, 109, 1, 0, 0, 0];
    bytes.extend(section(1, &[1, 0x60, 0, 0]));
    bytes.extend(section(3, &[1, 0]));
    if table {
        bytes.extend(section(4, &[1, 0x70, 0, 0]));
    }
    let mut code = vec![0];
    code.extend_from_slice(body);
    code.push(0x0b);
    let mut entries = vec![1];
    leb(&mut entries, code.len() as u32);
    entries.extend(code);
    bytes.extend(section(10, &entries));
    bytes
}

fn wasm2_only(bytes: &[u8]) {
    assert!(validate_module(bytes, ValidationProfile::Wasm2).is_ok());
    assert!(validate_module(bytes, ValidationProfile::Wasm1).is_err());
}

#[test]
fn branch_table_targets_must_have_identical_types() {
    // block (result i64) block (result i32) unreachable br_table 0 1 end drop
    // i64.const 0 end drop
    let body = [
        0x02, 0x7e, 0x02, 0x7f, 0x00, 0x0e, 0x01, 0x00, 0x01, 0x0b, 0x1a, 0x42, 0x00, 0x0b, 0x1a,
    ];
    wasm2_only(&module(false, &body));
    // The same targets with one result type are valid in both profiles.
    let same = [
        0x02, 0x7f, 0x02, 0x7f, 0x00, 0x0e, 0x01, 0x00, 0x01, 0x0b, 0x1a, 0x41, 0x00, 0x0b, 0x1a,
    ];
    assert!(validate_module(&module(false, &same), ValidationProfile::Wasm1).is_ok());
}

#[test]
fn call_indirect_table_is_a_reserved_zero_byte() {
    // i32.const 0 call_indirect 0 with the table index spelled 0x80 0x00.
    wasm2_only(&module(true, &[0x41, 0x00, 0x11, 0x00, 0x80, 0x00]));
    let reserved = module(true, &[0x41, 0x00, 0x11, 0x00, 0x00]);
    assert!(validate_module(&reserved, ValidationProfile::Wasm1).is_ok());
}

#[test]
fn block_types_are_empty_or_one_number_type() {
    // block (result v128) unreachable end drop
    wasm2_only(&module(false, &[0x02, 0x7b, 0x00, 0x0b, 0x1a]));
    // block (type 0) end
    wasm2_only(&module(false, &[0x02, 0x00, 0x0b]));
}

#[test]
fn signatures_have_at_most_1000_parameters_in_both_profiles() {
    let mut ty = vec![1, 0x60];
    leb(&mut ty, 1001);
    ty.extend(std::iter::repeat(0x7f).take(1001));
    ty.push(0);
    let mut bytes = vec![0, 97, 115, 109, 1, 0, 0, 0];
    bytes.extend(section(1, &ty));
    assert!(validate_module(&bytes, ValidationProfile::Wasm1).is_err());
    assert!(validate_module(&bytes, ValidationProfile::Wasm2).is_err());
}
