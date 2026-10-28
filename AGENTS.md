# Coding-agent instructions

itasca is a Rust WebAssembly validator verified in Lean against SpecTec-generated
Wasm 2.0 typing rules and explicit Wasm 1.0 and Wasm 2.0 profiles.

Before changing Rust, proofs, or extraction inputs, read
[DEVELOPMENT.md](DEVELOPMENT.md), the
[public guarantees and trust boundary](README.md#formal-verification), and the
[Lean guide](lean/README.md). Keep their claims consistent with the actual
consumer API and checked theorem premises.

## Coupled sources

- `src/` and `lean/Itasca/Generated/` are coupled. Regenerate committed
  `Types.lean` and `Funs.lean` with `just extract`; never edit them by hand.
  Rust comment and line-number changes also require regeneration.
- `FunsExternal.lean` is handwritten. The generated external template is ignored
  and must never be imported by a proof.
- `lean/SpecTec/{Wasm2Prefix,wasm2.0,Wasm2Builtins}.lean` are generated from
  pinned sources, versioned patches, and `lean/scripts/spec_split.py`. Change
  source or generator, run `just spec-update`, then `just spec-check`; never
  patch generated specification files.
- `lean/SpecExt/` holds handwritten specification extensions. Builtins keep
  exact generated signatures, checked by `Wasm2Builtins`. Temporary opaque
  placeholders are permitted only by the staged audit policy; they are not
  execution correctness proofs.
- `lean/Itasca/Runtime/` holds the runtime proofs. Validator proofs must never
  import `Itasca.Runtime` or `SpecExt`. Runtime changes must preserve the
  validator's extracted definitions and theorem statements.
- Keep `lean/scripts/`: its audit-import and external-model checks are part of
  verification. Upstream trackers and archived Rocq records are not build inputs.

## Rust and API discipline

Stay within the extraction constraints in [DEVELOPMENT.md](DEVELOPMENT.md#rust-extraction-constraints).
Use explicit loop counters and copy helpers. Do not introduce iterators,
closures, `.clone()`, bitwise operations, `String`, or new borrow/indexing patterns
without checking their extraction and proof impact. Enums are supported; retain
raw-byte constants where they directly describe binary dispatch.

Keep public validation at complete-module and issued-batch boundaries. Expose
validated metadata through shared accessors. Preserve the source-coherence,
worker-provenance, callback, and lifetime obligations of the streaming API.
Use the documented rustdoc style and keep byte-coordinate systems explicit.

## Proof discipline

Do not add axioms, `sorry`, `admit`, `native_decide`, unsafe proof shortcuts, or
kernel bypasses. `Itasca.Audit` and `SpecExt.Audit` permit only `propext`, `Classical.choice`, and
`Quot.sound`. Every new proof module must be reachable through its library's audit imports;
run `just audit-imports` after adding or moving files. Keep `Support/`, `Spec/`,
`Binary/`, and `Handler/` free of imports from higher layers.
Audit proof-bearing adapter definitions as well as exported theorems.

Use `just check Itasca.ModuleName` for iteration and `just prove` for integration.
Preserve dependency and build caches. Scratch files belong in `$TMPDIR`, outside
the proof source tree. Report any trust-boundary change explicitly.

## Required checks

- Handwritten Lean proofs or adapters: `just prove`.
- Rust or extraction inputs: `cargo test`, `cargo test --no-default-features`,
  `just extract`, `just extract-check`, and `just prove`.
- Aeneas source patches or pins: the Rust/extraction checks plus `just regressions`.
- SpecTec sources, patches, or pins: `just spec-update`, `just spec-check`, and
  `just prove`.
- Documentation outside extraction inputs: check links and `git diff --check`.

`just verify` runs both Rust test configurations, Rust/specification regeneration
checks, toolchain regressions, and the integrated Lean build. `just trust` reruns
the transitive axiom report. The Rocq implementation is archived under
`rocq-baseline`; the active branch has no Rocq build requirement.
