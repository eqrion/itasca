#![no_main]

use libfuzzer_sys::fuzz_target;
use wasmparser::{Validator, WasmFeatures};

// Arbitrary bytes exercise binary decoding and rejection. Acceptance must
// imply Core 2.0 validity. The converse is checked by wasm2_smith, where
// generated modules remain within the validator's implementation limits.
fuzz_target!(|data: &[u8]| {
    let reference = Validator::new_with_features(WasmFeatures::WASM2)
        .validate_all(data)
        .is_ok();
    let actual = itasca::validate_module(data, itasca::ValidationProfile::Wasm2).is_ok();
    assert!(
        !actual || reference,
        "itasca accepted invalid Core 2.0 bytes"
    );
});
