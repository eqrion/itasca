#![no_main]

use arbitrary::Unstructured;
use libfuzzer_sys::fuzz_target;
use wasm_smith::{Config, Module};
use wasmparser::{Parser, Payload, Validator, WasmFeatures};

/// Enable every Core 2.0 feature and disable all later proposals. Small
/// signatures, functions, and index spaces keep generated programs practical
/// and below itasca's documented resource limits, including multiple tables.
fn wasm2_config(min_uleb_size: u8) -> Config {
    Config {
        bulk_memory_enabled: true,
        reference_types_enabled: true,
        simd_enabled: true,
        multi_value_enabled: true,
        saturating_float_to_int_enabled: true,
        sign_extension_ops_enabled: true,
        relaxed_simd_enabled: false,
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
        max_tables: 4,
        max_memories: 1,
        max_types: 32,
        max_type_size: 64,
        max_funcs: 32,
        max_globals: 32,
        max_imports: 32,
        max_exports: 32,
        max_data_segments: 32,
        max_element_segments: 32,
        max_elements: 32,
        max_instructions: 256,
        min_uleb_size,
        ..Config::default()
    }
}

// Guard the resource bounds independently of wasm-smith's implementation.
// Oversized generated programs are outside the completeness contract; they
// are still exercised by the raw-byte soundness target.
fn within_limits(bytes: &[u8]) -> bool {
    if bytes.len() > 1_073_741_824 {
        return false;
    }
    for payload in Parser::new(0).parse_all(bytes) {
        match payload.expect("wasm-smith bytes already validated by wasmparser") {
            Payload::TypeSection(types) => {
                for ty in types.into_iter_err_on_gc_types() {
                    let ty = ty.unwrap();
                    if ty.params().len() > 1000 || ty.results().len() > 1000 {
                        return false;
                    }
                }
            }
            Payload::CodeSectionEntry(body) => {
                let mut locals = 0_u64;
                for local in body.get_locals_reader().unwrap() {
                    locals += u64::from(local.unwrap().0);
                }
                if locals > 50_000 {
                    return false;
                }
                // This includes local declarations, so it is a conservative
                // bound on the instruction body (including its final end).
                if body.range().len() > 7_654_321 {
                    return false;
                }
            }
            _ => {}
        }
    }
    true
}

fuzz_target!(|data: &[u8]| {
    let Some((&encoding, data)) = data.split_first() else {
        return;
    };
    let mut u = Unstructured::new(data);
    let Ok(module) = Module::new(wasm2_config(1 + encoding % 5), &mut u) else {
        return;
    };
    let bytes = module.to_bytes();
    Validator::new_with_features(WasmFeatures::WASM2)
        .validate_all(&bytes)
        .expect("wasm-smith produced bytes outside Core 2.0");
    if !within_limits(&bytes) {
        return;
    }
    let result = itasca::validate_module(&bytes, itasca::ValidationProfile::Wasm2);
    assert!(result.is_ok(), "itasca rejected valid Core 2.0: {result:?}");
});
