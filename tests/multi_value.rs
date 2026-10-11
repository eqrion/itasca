use itasca::{validate_module_with_profile, ValidationProfile};

fn encode(wat: &str) -> Vec<u8> {
    let buf = wast::parser::ParseBuffer::new(wat).unwrap();
    let mut module = wast::parser::parse::<wast::Wat>(&buf).unwrap();
    module.encode().unwrap()
}

fn check(wat: &str, expected: bool) {
    let bytes = encode(wat);
    let mut features = wasmparser::WasmFeatures::WASM1;
    features.set(wasmparser::WasmFeatures::MULTI_VALUE, true);
    assert_eq!(
        wasmparser::Validator::new_with_features(features)
            .validate_all(&bytes)
            .is_ok(),
        expected,
        "reference: {wat}"
    );
    assert_eq!(
        validate_module_with_profile(&bytes, ValidationProfile::MultiValue).is_ok(),
        expected,
        "itasca: {wat}"
    );
}

#[test]
fn function_results_and_profile_selection() {
    let wat = "(module (func (result i32 i64) i32.const 1 i64.const 2))";
    check(wat, true);
    assert!(validate_module_with_profile(&encode(wat), ValidationProfile::Wasm1).is_err());
    assert!(itasca::validate_module(&encode(wat), itasca::ValidationProfile::Wasm1).is_err());
    check("(module (func (param i32) (result i32) local.get 0))", true);
    check("(module (func (param i32) (result i32)))", false);
    check(
        "(module (func (result i32 i64) i64.const 1 i32.const 2))",
        false,
    );
    check("(module (func (result i32 i64) unreachable))", true);
    check(
        "(module (func (result i32 i64) i32.const 1 i64.const 2 return))",
        true,
    );
}

#[test]
fn block_inputs_outputs_and_exact_heights() {
    check("(module (func (result i32 i64) i32.const 3 block (param i32) (result i32 i64) i64.const 4 end))", true);
    check("(module (func block (param i32) drop end))", false);
    check(
        "(module (func unreachable block (param i32 i64) drop drop end))",
        true,
    );
    check(
        "(module (func block (result i32 i64) i32.const 1 i64.const 2 i32.const 3 end drop drop))",
        false,
    );
    check(
        "(module (func (result i32 i64) block (result i32 i64) i32.const 1 i64.const 2 br 0 end))",
        true,
    );
    check("(module (func (result i32 i64) block (result i32 i64) i32.const 1 i64.const 2 i32.const 0 br_if 0 end))", true);
}

#[test]
fn loop_labels_take_inputs() {
    check(
        "(module (func i32.const 0 loop (param i32) i32.const 0 br_if 0 drop end))",
        true,
    );
    check("(module (func i32.const 0 loop (param i32) (result i64) i32.const 0 br_if 0 drop i64.const 0 end drop))", true);
    check(
        "(module (func i32.const 0 loop (param i32) (result i64) drop i64.const 0 br 0 end drop))",
        false,
    );
}

#[test]
fn explicit_and_implicit_else() {
    check("(module (func (result i32 i64) i32.const 1 i64.const 2 i32.const 0 if (param i32 i64) (result i32 i64) end))", true);
    check(
        "(module (func i32.const 1 i64.const 2 i32.const 0 if (param i32 i64) drop drop end))",
        false,
    );
    check("(module (func (result i64) i32.const 1 i32.const 0 if (param i32) (result i64) drop i64.const 2 else drop i64.const 3 end))", true);
    check("(module (func (result i64) i32.const 1 i32.const 0 if (param i32) (result i64) drop i64.const 2 else i64.const 3 end))", false);
    check(
        "(module (func unreachable if (result i32 i64) end drop drop))",
        false,
    );
}

#[test]
fn direct_and_indirect_calls() {
    check("(module (type $t (func (param i32) (result i32 i64))) (func $f (type $t) local.get 0 i64.const 0) (func (result i32 i64) i32.const 1 call $f))", true);
    check("(module (type $t (func (result i32 i64))) (table 1 funcref) (func (result i32 i64) i32.const 0 call_indirect (type $t)))", true);
    check("(module (type $t (func (result i32 i64))) (func (result i32 i64) i32.const 0 call_indirect (type $t)))", false);
}

#[test]
fn branch_table_preserves_bottom_and_requires_equal_arity() {
    check("(module (func block (result i32) block (result i64) unreachable br_table 0 1 end drop i32.const 0 end drop))", true);
    check("(module (func block (result i32 i64) block (result i64 i32) unreachable select select i32.const 0 br_table 0 1 end drop drop i32.const 0 i64.const 0 end drop drop))", true);
    check("(module (func block (result i32 i64) block (result i64) unreachable br_table 0 1 end drop i32.const 0 i64.const 0 end drop drop))", false);
    check("(module (func block (result i32) block (result i64) i64.const 1 i32.const 0 br_table 0 1 end drop i32.const 0 end drop))", false);
}

#[test]
fn signature_limits_at_decode_time() {
    for n in [999, 1000, 1001] {
        let results = "i32 ".repeat(n);
        let wat = format!("(module (func (result {results}) unreachable))");
        let bytes = encode(&wat);
        assert_eq!(
            itasca::validate_module(&bytes, itasca::ValidationProfile::MultiValue).is_ok(),
            n <= 1000
        );
        let wat = format!("(module (type (func (param {results}))))");
        assert!(itasca::validate_module(&encode(&wat), ValidationProfile::Wasm1).is_ok());
        assert_eq!(
            itasca::validate_module(&encode(&wat), itasca::ValidationProfile::MultiValue).is_ok(),
            n <= 1000
        );
    }
    // Truncated type payload with an excessive result count: reject the count.
    let bytes = b"\0asm\x01\0\0\0\x01\x05\x01\x60\x00\xe9\x07";
    assert_eq!(
        itasca::validate_module(bytes, itasca::ValidationProfile::MultiValue).unwrap_err(),
        itasca::Error::Read(itasca::OpError::TooManyResults)
    );
    assert_eq!(
        itasca::validate_module(bytes, ValidationProfile::Wasm1).unwrap_err(),
        itasca::Error::Read(itasca::OpError::UnexpectedEof)
    );
    let bytes = b"\0asm\x01\0\0\0\x01\x04\x01\x60\xe9\x07";
    assert_eq!(
        itasca::validate_module(bytes, ValidationProfile::MultiValue).unwrap_err(),
        itasca::Error::Read(itasca::OpError::TooManyParams)
    );
    assert_eq!(
        itasca::validate_module(bytes, ValidationProfile::Wasm1).unwrap_err(),
        itasca::Error::Read(itasca::OpError::UnexpectedEof)
    );
}

#[test]
fn active_segment_encodings_follow_the_selected_profile() {
    // Empty active segments using the Core 2 explicit index-zero spelling.
    let element = b"\0asm\x01\0\0\0\x04\x04\x01\x70\x00\x01\x09\x08\x01\x02\x00\x41\x00\x0b\x00\x00";
    let data = b"\0asm\x01\0\0\0\x05\x03\x01\x00\x01\x0b\x07\x01\x02\x00\x41\x00\x0b\x00";
    for bytes in [&element[..], &data[..]] {
        assert!(itasca::validate_module(bytes, ValidationProfile::MultiValue).is_ok());
        assert!(itasca::validate_module(bytes, ValidationProfile::Wasm1).is_err());
    }
    // Passive/declarative segments still require disabled proposals.
    let passive_element = b"\0asm\x01\0\0\0\x09\x04\x01\x01\x00\x00";
    let declarative_element = b"\0asm\x01\0\0\0\x09\x04\x01\x03\x00\x00";
    let passive_data = b"\0asm\x01\0\0\0\x0b\x03\x01\x01\x00";
    for bytes in [&passive_element[..], &declarative_element[..], &passive_data[..]] {
        assert!(itasca::validate_module(bytes, ValidationProfile::MultiValue).is_err());
    }
}

fn multivalue_config() -> wasm_smith::Config {
    wasm_smith::Config {
        bulk_memory_enabled: false,
        reference_types_enabled: false,
        simd_enabled: false,
        relaxed_simd_enabled: false,
        multi_value_enabled: true,
        saturating_float_to_int_enabled: false,
        sign_extension_ops_enabled: false,
        exceptions_enabled: false,
        memory64_enabled: false,
        tail_call_enabled: false,
        threads_enabled: false,
        shared_everything_threads_enabled: false,
        gc_enabled: false,
        custom_descriptors_enabled: false,
        custom_page_sizes_enabled: false,
        wide_arithmetic_enabled: false,
        extended_const_enabled: false,
        max_tables: 1,
        max_funcs: 8,
        max_instructions: 100,
        max_memories: 1,
        ..wasm_smith::Config::default()
    }
}

#[test]
fn generated_modules_and_mutations() {
    let mut rng = 0x9188_daaa_33ff_7171u64;
    let mut generated = 0;
    let mut mutations = 0;
    for _ in 0..128 {
        let mut entropy = vec![0; 4096];
        for byte in &mut entropy {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            *byte = rng as u8;
        }
        let mut input = arbitrary::Unstructured::new(&entropy);
        let Ok(module) = wasm_smith::Module::new(multivalue_config(), &mut input) else {
            continue;
        };
        generated += 1;
        let bytes = module.to_bytes();
        let mut features = wasmparser::WasmFeatures::WASM1;
        features.set(wasmparser::WasmFeatures::MULTI_VALUE, true);
        wasmparser::Validator::new_with_features(features)
            .validate_all(&bytes)
            .unwrap();
        assert!(
            itasca::validate_module(&bytes, itasca::ValidationProfile::MultiValue).is_ok(),
            "generated module {generated}"
        );
        for i in (0..bytes.len()).step_by((bytes.len() / 24).max(1)) {
            let mut changed = bytes.clone();
            changed[i] ^= 0x81;
            let expected = wasmparser::Validator::new_with_features(features)
                .validate_all(&changed)
                .is_ok();
            let actual = itasca::validate_module(&changed, itasca::ValidationProfile::MultiValue);
            assert_eq!(
                actual.is_ok(),
                expected,
                "module {generated}, byte {i}: {actual:?}"
            );
            mutations += 1;
        }
    }
    assert!(generated >= 100, "generated {generated}");
    assert!(mutations >= 2400, "mutated {mutations}");
}
