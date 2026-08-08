#![no_main]

use libfuzzer_sys::fuzz_target;
use wasmparser::{Validator, WasmFeatures};

// Soundness check: unstructured bytes occasionally decode as a header plus
// garbage, which is exactly what exercises decoder edge cases. veriwasm must
// never accept what wasmparser, configured for the Wasm 1.0 feature set,
// rejects.
//
// The converse isn't checked here: veriwasm enforces a few implementation
// caps (`src/limits.rs`) that Wasm 1.0 itself does not, so it can reject
// things wasmparser accepts. A compact
// LEB128 count claiming, say, 50,001 locals is exactly what random mutation
// finds easily, and rejecting it is by design, not a bug. Completeness is
// checked instead by `wasm1_smith`, which only ever generates modules well
// under those caps.
fuzz_target!(|data: &[u8]| {
    let wasmparser_valid = Validator::new_with_features(WasmFeatures::WASM1)
        .validate_all(data)
        .is_ok();
    let veriwasm_valid = veriwasm::validate_module(data).is_ok();

    assert!(
        !veriwasm_valid || wasmparser_valid,
        "veriwasm accepted a module wasmparser rejects"
    );
});
