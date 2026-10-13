#![no_main]
use libfuzzer_sys::fuzz_target;
#[path = "../../tests/support/runtime_differential.rs"]
mod differential;
#[path = "../../tests/support/mvp_binary.rs"]
mod mvp_binary;
#[path = "../../tests/support/runtime_numeric.rs"]
mod numeric;

fuzz_target!(|data: &[u8]| {
    let (bytes, profile) = numeric::module(data);
    let status = differential::compare(&bytes, profile, data);
    assert_eq!(status, differential::Coverage::Compared);
    differential::record(status);
});
