# itasca

***veritas caput***

A formally verified streaming WebAssembly 1.0 validator.

## Background

This project was built using Claude extensively. It's meant to be an experiment of AI-assisted formal verification.

Written by Ryan Hunt, who is learning formal verification but is a newbie.

With formal verification it is very easy to mistaken about what you have proved. I've tried to be as rigorous as I can, but be warned.

I believe the top-level theorems for whole module validation are solid, but the decomposed module validation entry points may have some gaps.

## Overview

This is a Rust library that implements the Wasm 1.0 decoding and validation algorithm. You can view the [docs here](https://docs.rs/itasca/latest/itasca/).

It implements both a 'whole module' validator, and also a 'decomposed' streaming validator. The interface is compatible with SpiderMonkey's WebAssembly engine and a branch with it integrated is [here](https://github.com/eqrion/firefox/tree/itasca).

The library has been verified to correspond with the [WasmCert](https://github.com/WasmCert/WasmCert-Coq) mechanisation of the specification. See [formal verification](#formal-verification) for more details.

To test this out yourself, run:
```bash
# build the rust code
make build
# run the rust tests
make test
# run charon to get llbc
make llbc
# generate the rocq (coq) code from llbc
make coq
# compile all the rocq code
make prove
```

## Decomposed module validation

In order to be useful in a real production Wasm engine, we can't just expose a single 'validate module' entry point.

For example SpiderMonkey does the following:
  - It fuses decoding and validation to minimize the size of AST it builds.
  - It validates functions in parallel on other threads.
  - It validates function bodies while building internal compiler IRs.
  - It can validate while bytes are streaming off the network, and are discontiguous.

This library was designed to expose an API compatible with all of the above.

This complicates the proofs and leaves preconditions that the user must follow (these are hypotheses that must be met for the proofs to apply).

The goal is that the preconditions are straightforward to follow and don't require reasoning over the contents of the Wasm module.

The overall sequence of calls must roughly be:
```
// Validate everything all at once.
validate_module() {
  // Validate all sections until the code section.
  validate_env()

  // Validate the code section and call a hook for each entry entry.
  // Must be called after validate_env, and the hook must call
  // validate_code_entry.
  validate_code() {
    // Validate a single code section entry (i.e. function body).
    validate_code_entry()
  }

  // Validate everything after the code section.
  validate_tail()
}
```

The `validate_code` hook allows for each function to be dispatched to worker threads for parallel validation and compilation. The caller is obligated to just ensure `validate_code_entry` is eventually called and the result reported.

`validate_code_entry` has a hook per-opcode to allow it to be used by a compiler to build an IR. Importantly `validate_code_entry` drives all the validation and the compiler just listens to the results.

Custom sections are reported via hooks on `validate_env/tail`

## Testing

In addition to formal verification, the validator has been conventionally tested.

`/tests/` contains both an ad-hoc unit test suite, along with an import of the Wasm 1.0 spec-test suite.
`/fuzz/` contains a differential fuzzer against the `wasmparser` Rust crate.

It has also been integrated into SpiderMonkey in a [branch](https://github.com/eqrion/firefox/tree/itasca) and passes all of SpiderMonkey's tests.

## Formal Verification

The Rust code is extracted using [Charon](https://github.com/AeneasVerif/charon) to LLBC (a JSON extraction of the rustc internals). That is converted using [Aeneas](https://github.com/AeneasVerif/aeneas) to [Rocq](https://rocq-prover.org/).

The Rocq code models the original Rust code. We then combine that with the [WasmCert](https://github.com/WasmCert/WasmCert-Coq) Rocq mechanisation of the Wasm specification. We then have proofs that the model of the Rust code corresponds to WasmCert version.

`theories` contains the Rocq source code.

### Reading the theorems

- "Accepts" means the Rust function returned `Ok`.
- "Returns" means it did not panic, overflow, index out of bounds, or loop forever.
- "Decodes to" means the bytes match the hand-written binary format in `Spec_Module.v` / `Spec_Expr.v`.
- "Well typed" means WasmCert's declarative typing judgement (`module_typing` for modules, `be_typing` for instruction sequences) holds.

Completeness results have two side conditions:

- **Implementation limits.** Modules, function bodies, and locals have limits on their size. A valid module over one of these limits is rejected. These limits match what SpiderMonkey already imposes.
- **Wasm 1.0 restrictions.** WasmCert formalises Wasm 2.0, so its checker accepts modules 1.0 does not. These are captured by `module_1_0`.

### The whole-module entry point

| Theorem | Statement |
|---|---|
| [`validate_module_no_panic`](theories/Module_NoPanic.v#L3125) | `validate_module` returns on every input. No hypotheses. |
| [`validate_module_typed`](theories/Module_Typing.v#L1037) | If `validate_module` accepts, the bytes decode to a module that is well typed. `import_types` and `export_types` succeed and report that module's import and export types. |
| [`validate_module_typechecked`](theories/Module_Wasm10.v#L1088) | If the bytes decode to a Wasm 1.0 module that WasmCert's type checker accepts, and it is within the implementation limits, `validate_module` accepts it and reports the same import and export types as the checker. |
| [`validate_module_with_no_panic`](theories/Module_Driven.v#L810) | `validate_module_with` returns on every input, provided the visitor's hooks return. |
| [`validate_module_driven`](theories/Module_Sound.v#L6818) | If `validate_module_with` accepts, `validate_module` accepts the same bytes with the same result. Assumes that any overridden `on_code_entry` only accepts entries `validate_code_entry` accepts. |
| [`validate_module_with_complete`](theories/Module_Driven.v#L840) | `validate_module_with` accepts every valid module `validate_module` does, provided the visitor's hooks return `Ok`. |

### One function body

These are stated against a WasmCert context `C0`, with seven `_agree` equations saying `C0` is the context described by the environment and `Context` passed in.

| Theorem | Statement |
|---|---|
| [`validate_body_no_panic`](theories/OpIter_NoPanic.v#L177) | `validate_body` returns for every body, environment and context. No hypotheses. |
| [`validate_body_with_no_panic`](theories/OpIter_NoPanic.v#L154) | Same for `validate_body_with`, provided the visitor's hooks return. |
| [`validate_body_with_typed`](theories/OpIter_Validate.v#L1386) | If `validate_body_with` accepts a body with at most one result, the bytes decode to an instruction sequence that is well typed in `C0`. Holds for every visitor, so hooks can't turn a rejection into an acceptance. |
| [`validate_body_complete`](theories/OpIter_Complete.v#L3333) | If the bytes decode to an instruction sequence that WasmCert's checker accepts in `C0`, and the Wasm 1.0 restrictions and body size limit hold, `validate_body` accepts. WasmCert's checker is equivalent to `be_typing` for bodies, so this is full completeness. |
| [`validate_body_with_trace`](theories/OpIter_Validate.v#L1287) | If `validate_body_with` accepts, the visitor was shown exactly the operators the bytes encode, in order, none skipped or invented. Applies to visitors that satisfy `records`, meaning each hook logs the operator it is named for. |
| [`validate_body_trace`](theories/OpIter_Validate.v#L1511), [`trace_records`](theories/OpIter_Table.v#L1046) | A visitor that logs every hook satisfies `records`, so the trace theorem applies to a real visitor. This also shows no opcode is sent to the wrong hook. |

### The decomposed entry points

Every decomposed entry point requires `data.len() <= MAX_MODULE_BYTES`, and that the `Env` and positions passed in came from the earlier steps on the same bytes.

| Theorem | Statement |
|---|---|
| [`validate_module_of_parts`](theories/Module_Driven.v#L747) | If `validate_env`, `validate_code` and `validate_tail` each accept, each starting where the last stopped on the same bytes, `validate_module` accepts with the same `Env` and `Tail`. Everything above applies. |
| [`validate_code_entry_ok`](theories/Module_NoPanic.v#L2562) | `validate_code_entry` returns when given an `Env` from `validate_env` and an in-bounds position, and on success moves forward within the data. |
| [`validate_code_entry_with_sound`](theories/Module_Sound.v#L5660) | If `validate_code_entry_with` accepts, the bytes from `pos` decode to a code entry that is well typed at its declared function type, and the visitor was shown exactly its operators. Unlike the body theorems, the context is built from `Env`, so there are no `_agree` hypotheses. |
| [`validate_code_entry_complete`](theories/Module_Complete.v#L3997) | `validate_code_entry` accepts every well-typed code entry within the implementation limits. |
| [`validate_code_entry_driven`](theories/Module_Driven.v#L153) | If `validate_code_entry_with` accepts, `validate_code_entry` accepts. No hypotheses on the visitor. This is how an `on_code_entry` override meets the `validate_module_driven` assumption. |
| [`validate_code_with_deferred`](theories/Module_Driven.v#L662) | An `on_code_entry` can return before validating its entry. If every entry it was handed later validates, `validate_code` accepts. This is the theorem for validating on other threads. |
| [`validate_module_regions_typed`](theories/Module_Typing.v#L1086) | The env, code section and tail can be in three separate buffers. If each part accepts, the buffers fit together exactly, and the code buffer starts with the code section header, the concatenated bytes are a well-typed module. |
| [`validate_module_regions_deferred_typed`](theories/Module_Driven.v#L922) | The two above combined: three buffers and deferred entries. This is the streaming, parallel case SpiderMonkey uses. |

### The trust base

**WasmCert-Coq is a faithful formalisation of WebAssembly.** "Well typed" means WasmCert says so.

**The binary format is transcribed correctly.** `Spec_Binary.v`,
`Spec_Expr.v` and `Spec_Module.v` are a hand transcription of the spec's
binary format, since WasmCert has no verified parser to prove against.
[`repr_module_det`](theories/Spec_Module.v#L933), [`repr_expr_det`](theories/Spec_Expr.v#L542) and [`repr_ops_det`](theories/Spec_Binary.v#L814) check that no byte string can be read two ways.

**`Translate.v` maps itasca's types to WasmCert's correctly.** One line per case. At the module level, the proofs already check it against `Spec_Module.v` and WasmCert. It matters most for the body theorems, whose `_agree` hypotheses use it directly.

**Charon and Aeneas translate Rust to Rocq faithfully.** Otherwise the proofs are about a different program.

**The hand-written axioms about Rust.** `Aeneas_Specs.v` and `Itasca_FunsExternal.v` describe the standard library functions Aeneas doesn't translate (`Vec`, slices, `PartialEq`) and the `loop` combinator. Termination relies on `loop_unfold` modelling a Rust loop correctly. Running out of memory isn't modelled, so "returns" assumes allocation succeeds.

**Rocq's kernel.** There are no `Admitted` proofs and no guard or positivity checking bypasses.

### Not proven

- Module completeness is stated against WasmCert's type checker, not `module_typing`. WasmCert proves its module checker sound but not complete. Function bodies don't have this gap.
- The custom section ranges reported to `ModuleVisitor` are unverified.
- Which error a rejection returns.
- Anything about execution.
