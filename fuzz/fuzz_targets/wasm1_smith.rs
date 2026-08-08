#![no_main]

use arbitrary::Unstructured;
use libfuzzer_sys::fuzz_target;
use wasm_smith::{Config, Module};
use wasmparser::{Validator, WasmFeatures};

#[path = "../../tests/support/mvp_binary.rs"]
mod mvp_binary;

/// `wasm_smith::Config` restricted to exactly the Wasm 1.0 feature set, so
/// every module generated is one veriwasm claims to support.
fn wasm1_config() -> Config {
    Config {
        bulk_memory_enabled: false,
        reference_types_enabled: false,
        simd_enabled: false,
        relaxed_simd_enabled: false,
        multi_value_enabled: false,
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
        max_memories: 1,
        ..Config::default()
    }
}

// Completeness check: every module wasm-smith generates under a Wasm-1.0-only
// config is well-typed Wasm 1.0, so veriwasm must accept it. `wasm-smith`
// serializes through `wasm-encoder`, which only emits the post-bulk-memory
// element/data section encoding (see `mvp_binary`), so bytes are rewritten to
// genuine Wasm 1.0 encoding before either validator sees them.
fuzz_target!(|data: &[u8]| {
    let mut u = Unstructured::new(data);
    let module = match Module::new(wasm1_config(), &mut u) {
        Ok(m) => m,
        Err(_) => return,
    };
    let bytes = match mvp_binary::normalize_to_wasm1(&module.to_bytes()) {
        Ok(b) => b,
        Err(_) => return,
    };

    assert!(
        Validator::new_with_features(WasmFeatures::WASM1)
            .validate_all(&bytes)
            .is_ok(),
        "wasm-smith (or the Wasm 1.0 re-encoding) produced a module wasmparser rejects"
    );
    assert!(
        veriwasm::validate_module(&bytes).is_ok(),
        "veriwasm rejected a module wasm-smith generated and wasmparser accepts"
    );
});
