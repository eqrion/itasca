#![no_main]
use libfuzzer_sys::fuzz_target;
#[path = "../../tests/support/runtime_differential.rs"]
mod differential;
#[path = "../../tests/support/runtime_numeric.rs"]
mod numeric;

fuzz_target!(|data: &[u8]| {
    let bytes = numeric::module(data);
    let status = differential::compare(&bytes, data);
    assert_eq!(status, differential::Coverage::Compared);
    differential::record(status);
});
