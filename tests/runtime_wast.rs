//! Execute the pinned specification scripts against itasca's runtime.
//!
//! Validation fixtures remain independently checked by the existing corpus
//! tests. This harness executes every action in script order, including effects
//! that survive a trapping call or failed instantiation.

#[path = "support/runtime_wast.rs"]
mod harness;
#[path = "support/mvp_binary.rs"]
mod mvp_binary;

#[test]
fn wasm1_execution_corpus() {
    harness::run_corpus(
        "tests/third_party/wasm-spec/test/core",
        itasca::ValidationProfile::Wasm1,
    );
}

#[test]
fn wasm2_execution_corpus() {
    harness::run_corpus("tests/spec2", itasca::ValidationProfile::Wasm2);
}
