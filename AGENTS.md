# Coding-agent instructions

itasca is a Rust WebAssembly validator verified in Lean against SpecTec-generated
Wasm 2.0 typing rules and an independent binary grammar.

Before changing Rust, proofs, or extraction inputs, read
[DEVELOPMENT.md](DEVELOPMENT.md), the
[public guarantees and trust boundary](README.md#formal-verification), and the
[Lean guide](lean/README.md). Keep their claims consistent with the actual
consumer API and checked theorem premises.

## Coupled sources

- `src/` and `lean/Itasca/Generated/` are coupled. Regenerate committed
  `Types.lean`, the six `Funs{Validator,RuntimeCommon,Compiler,Store,Interp,Instantiate}.lean`
  partitions, and the `Funs.lean` umbrella with `just extract`; never edit them
  by hand. Rust changes still require regeneration. Generated comments retain
  Rust filenames but omit line ranges, so moving lines no longer changes those
  comments. After comment normalization, `lean/scripts/split_funs.py` partitions
  the generated functions without rewriting declaration text.
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
- `lean/Itasca/Results/Definitions/` owns public semantic vocabulary; the other
  `Results/*.lean` modules own public theorem statements. Follow the semantic
  namespace policy in
  [lean/NAMESPACES.md](lean/NAMESPACES.md): namespace subjects align with owners
  beneath organizational directories; Results, Definitions and Runtime do not add
  namespace prefixes. Preserve extracted and upstream operation identities.
  Public definitions import only other public definitions and the named extracted,
  specification and upstream foundations, never handwritten implementation modules. Public vocabulary
  placement overrides the general rule that proof files mirror Rust.
- `lean/Itasca/Runtime/` holds runtime implementation proofs. Validator proofs
  must never import Runtime implementation modules, extracted execution
  partitions or `SpecExt`, including transitively through public definitions. Validation,
  Streaming and Callbacks subject entries obey the same isolation. Compiler
  proofs and their definition owners must not import `FunsInterp` transitively;
  preserve Local → Body → Module stages. Runtime changes must preserve the
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
imports from higher implementation layers. They may import narrow public
definitions without gaining forbidden execution dependencies. `just lint` checks
layering, forbidden constructs and transitive definition imports; `just audit`
checks every registered Results theorem, the axiom allowlist and semantic closure
location, and checks the generated audit report and interface manifest. Use
`just audit --update` to refresh artifacts explicitly and review the changes. Review proof-bearing
adapters and generated match-helper emitters as well as exported theorems.

Iterate with the Lean language server tools, confirm with
`just check Itasca.ModuleName`, and use `just prove` for integration.
Preserve dependency and build caches. Scratch files belong in `$TMPDIR`, outside
the proof source tree. Report any trust-boundary change explicitly.

## Required checks

These are integration checkpoints, not commands to repeat after each edit.
During a coherent unfinished migration, use LSP and targeted `just check` calls;
run source architecture checks after import changes. At a completed checkpoint,
run the required checks once. After a successful current `just prove`, use
`just audit --no-build` to reuse that build. Never reuse a build after subsequent
source edits affecting the audited environment. Refresh artifacts intentionally
with `just audit --no-build --update` and review the diffs.

- Handwritten Lean proofs or adapters: `just prove`, `just lint`, and `just audit`.
- Rust or extraction inputs: `cargo test`, `cargo test --no-default-features`,
  `just extract`, `just extract-check`, and `just prove`.
- Extraction tool installation or pins: the Rust/extraction checks.
- SpecTec sources, patches, or pins: `just spec-update`, `just spec-check`, and
  `just prove`.
- Documentation outside extraction inputs: check links and `git diff --check`.

`just verify` runs both Rust test configurations, Rust/specification regeneration
checks, tooling regression tests, lint, the integrated Lean build and strict
audit/artifact checks. The audit reuses the integrated build. The Rocq implementation is archived under
`rocq-baseline`; the active branch has no Rocq build requirement.
