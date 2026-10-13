#![no_main]
#[path = "../../tests/support/runtime_differential.rs"]
mod differential;
#[path = "../../tests/support/mvp_binary.rs"]
mod mvp_binary;
#[path = "../../tests/support/runtime_scenarios.rs"]
mod scenarios;
libfuzzer_sys::fuzz_target!(|data: &[u8]| {
    differential::record(scenarios::stateful(data));
});
