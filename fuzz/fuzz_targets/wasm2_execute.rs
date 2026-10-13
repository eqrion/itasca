#![no_main]
#[path = "../../tests/support/runtime_differential.rs"]
mod differential;
#[path = "../../tests/support/mvp_binary.rs"]
mod mvp_binary;
mod runtime_smith_support;
libfuzzer_sys::fuzz_target!(|data: &[u8]| {
    runtime_smith_support::run(data, itasca::ValidationProfile::Wasm2);
});
