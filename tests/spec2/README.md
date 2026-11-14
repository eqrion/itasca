# Wasm 2.0 conformance corpus

These 148 WAST files are unmodified copies of all recursive `test/core/**/*.wast`
files from
[WebAssembly/spec wg-2.0](https://github.com/WebAssembly/spec/tree/fffc6e12fa454e475455a7b58d3b5dc343980c10/test/core),
commit `fffc6e12fa454e475455a7b58d3b5dc343980c10`, including 58 SIMD files.
The accompanying `LICENSE` is copied from that commit's `test/LICENSE`
(Apache 2.0). The Wasm 1.0 test gate and binary fixtures were removed; the active
corpus is Wasm 2.0.

`cargo test --test spec2_tests wasm2_corpus_matches_reference` checks every
module-validation assertion with pinned wasmparser's `WasmFeatures::WASM2`.
There are no positive feature exclusions. Literal binary modules, including
malformed binaries, retain their bytes. No element/data segment normalization
is applied. Unexpected encoding errors fail the test. Quoted malformed text
that cannot produce a binary is counted separately; it is not a validator
input. Modules expected to fail linking or trap during instantiation must
still pass validation. Confusing Unicode is enabled in the WAST lexer because
the corpus intentionally exercises valid UTF-8 names.

The frozen full-suite totals are 1716 accepted modules, 2875 rejected binaries,
1081 quoted malformed-text cases without a binary, and 48334 runtime and
registration directives counted by the validation-only gate. These counts describe
modules and WAST assertions, not individual operators.

`cargo test --test runtime_wast` executes the pinned Wasm 2.0 corpus, with zero
unsupported directives. The Core 2.0 execution gate freezes 1599 successful
module declarations, 22 registrations, 155 standalone invocations, 45734 return
assertions, 2442 trap assertions, 83 unlinkable assertions, and 15 stack-exhaustion
assertions. It also checks 2146 invalid modules, 729 malformed binaries, and the
same 1081 malformed-text cases. The difference from the validation-only counts
is explicit: its 1716 accepted modules include the 1599 declarations, 83
unlinkable modules, and 34 modules whose instantiation traps. All 48334 formerly
counted runtime directives and those 117 instantiation failures are executed.

The full itasca gate, `wasm2_complete_corpus`, runs by default and checks the
same assertions against itasca's Wasm 2.0 validator:

```sh
cargo test --test spec2_tests wasm2_complete_corpus
```

`wasm2_multivalue_corpus` retains a 15-file control-flow comparison against
wasmparser configured for MVP plus multi-value. This reference configuration
is only a reference configuration: every tested module is checked with
itasca's Wasm 2.0 validator. Its frozen totals remain 17 accepted modules,
489 rejected binaries, 90 quoted malformed-text cases, and 1186 runtime/link
assertions. The comparison excludes four positive modules outside the reference
feature set:
`br_table.wast:3`, `call_indirect.wast:623`, `select.wast:1`, and
`select.wast:518`. Each excluded module is confirmed valid by wasmparser's
Wasm 2.0 configuration; the full-suite gates exercise all four with itasca.
