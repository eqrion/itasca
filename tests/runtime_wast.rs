//! Execute the pinned specification scripts against itasca's runtime.
//!
//! Validation fixtures remain independently checked by the existing corpus
//! tests. This harness executes every action in script order, including effects
//! that survive a trapping call or failed instantiation.

#[path = "support/runtime_wast.rs"]
mod harness;
#[test]
fn wasm2_execution_corpus() {
    harness::run_corpus("tests/spec2");
}
