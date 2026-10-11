# Wasm 2.0 control-flow corpus

These 15 files are unmodified copies from
[WebAssembly/spec wg-2.0](https://github.com/WebAssembly/spec/tree/fffc6e12fa454e475455a7b58d3b5dc343980c10/test/core),
commit `fffc6e12fa454e475455a7b58d3b5dc343980c10`. The accompanying `LICENSE`
is copied from that commit's `test/LICENSE` (Apache 2.0).
The separate Wasm 1.0 submodule and binary fixtures retain their existing pin.

`cargo test --test spec2_tests` parses these WAST files and runs their module
validation assertions against the experimental multi-value profile. It does
not rewrite their element/data segments into Wasm 1.0 encoding. Literal binary
modules, including malformed binaries, retain their bytes. Unexpected encoding
errors fail the test. Modules expected to fail linking or trap during
instantiation must still pass validation.

The frozen totals are 17 accepted modules, 489 rejected binaries, 90 quoted
malformed-text cases without a binary, and 1186 runtime/link registration
assertions left for an interpreter. The positive modules contain many functions;
these counts are modules, not individual operators or runtime invocations.

Four positive modules require proposals beyond multi-value and are excluded:
`br_table.wast:3`, `call_indirect.wast:623`, `select.wast:1`, and
`select.wast:518`. Each must pass wasmparser's Wasm 2.0 validation and fail its
Wasm 1.0 + multi-value feature selection. Exclusions are classified independently
of itasca and included in the frozen totals. The focused Rust tests separately
exercise multi-value branch tables, including bottom-compatible mixed targets.

This is the control-flow subset of the 2.0 suite, not full Wasm 2.0 coverage.
