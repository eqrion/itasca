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
  Rust changes still require regeneration. Generated comments retain Rust
  filenames but omit line ranges, so moving lines no longer changes those
  comments.
- `FunsExternal.lean` is handwritten. The generated external template is ignored
  and must never be imported by a proof.
- `lean/SpecTec/wasm2.0.lean` is generated from pinned sources and versioned
  patches, including the handwritten builtin patch applied to generated output.
  Change source or generator, run `just spec-update`, then `just spec-check`; never
  edit generated specification files by hand.
- `patches/spectec-wasm2-builtins.patch` supplies the trusted builtin definitions
  in the generated specification, including checks against generated signatures.
  `lean/SpecExt/` holds supporting proofs and handwritten specification extensions.
  Do not introduce opaque builtin placeholders.
- `lean/Itasca/Runtime/` holds the runtime proofs. Validator proofs must never
  import `Itasca.Runtime` or `SpecExt`. Runtime changes must preserve the
  validator's extracted definitions and theorem statements.
- Keep specification regeneration reproducible through the pinned sources and patches.
  Upstream trackers and archived Rocq records are not build inputs.

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

Follow the [proof engineering guide](lean/PROOF_ENGINEERING.md).

Do not add axioms, `sorry`, `admit`, `native_decide`, unsafe proof shortcuts, or
kernel bypasses. Use only the standard logical axioms `propext`, `Classical.choice`,
and `Quot.sound`. Keep `Support/`, `Spec/`, `Binary/`, and `Handler/` free of
imports from higher layers. `just lint` checks layering and forbidden
constructs; `just audit` checks the headline theorem axiom allowlist and
statement cone. Review proof-bearing adapters as well as exported theorems.

Iterate with the Lean language server tools, confirm with
`just check Itasca.ModuleName`, and use `just prove` for integration.
Preserve dependency and build caches. Scratch files belong in `$TMPDIR`, outside
the proof source tree. Report any trust-boundary change explicitly.

## Required checks

- Handwritten Lean proofs or adapters: `just prove`, `just lint`, and `just audit`.
- Rust or extraction inputs: `cargo test`, `cargo test --no-default-features`,
  `just extract`, `just extract-check`, and `just prove`.
- Extraction tool installation or pins: the Rust/extraction checks.
- SpecTec sources, patches, or pins: `just spec-update`, `just spec-check`, and
  `just prove`.
- Documentation outside extraction inputs: check links and `git diff --check`.

`just verify` runs both Rust test configurations, Rust/specification regeneration
checks and the integrated Lean build. The Rocq implementation is archived under
`rocq-baseline`; the active branch has no Rocq build requirement.
