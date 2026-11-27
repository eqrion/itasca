# Shared Wasm metadata proof migration

This is a work-in-progress snapshot. Rust validation returns `ModuleMetadata` with shared immutable `Arc<CodeMetadata>`. A streaming visitor can post a batch that owns a strong reference to the metadata. The batch still borrows the source bytes. The tail parser fills the module’s data segments, and the visitor API has no tail-ready hook.

## Verified at the checkpoint

- Rust tests, formatting, the no-default-features build, extraction and the generated-model consistency check passed after the Rust change. The work since those checks is in handwritten Lean.
- The function-body, code-entry, batch validation and callback-trace proofs build. The section parsers, import and export accessor contracts, custom-section trace proofs and tail parser proofs build.
- `Itasca.Module.Env.Requirements` builds. Its `metadata.validate_env.semantic_spec` proves that a successful prefix parse yields the independently encoded declarations, their retained representation, semantic validity and the bounds needed by later phases.
- `Itasca.Module.Elab.ValidatedSections` builds. Given represented declarations, valid metadata, typed code entries and valid data segments, its `typed` theorem assembles the SpecTec `Module_ok` judgment. Its `restrictions` and `elaborates` proofs also build.

## First failing target and remaining work

The full `just prove` run reaches `Itasca.Module.Elab.ToTyping` and fails in `accessor_types` and `matches_from_env`. Downstream targets depending on these theorems have yet to be verified. A successful targeted build does not establish the public whole-module or streaming guarantees.

1. In `Itasca/Itasca/Module/Elab/ToTyping.lean`, connect the raw typed import declarations to the ordered per-kind descriptor lookups used by `ModuleMetadata.import_types`. The reader contract is in `Module/Readers/ImportTypes.lean`. The new cache carries both imported and defined descriptors.
2. Prove `Matches` for the final shared module and data vector. The outstanding correspondence includes eager functions (start or exported), exported table, memory and global flags, and the final stored data. The per-section updates are recorded in `Module/Sections/Exports.lean` and `Module/Env/Encoding.lean`. The declared-function-reference correspondence is proved in `Module/Elab/ValidatedSections.lean`.
3. Migrate the dependent completeness, whole-module, slice and streaming-driver proofs and examples. Validate the public entry points with `just prove` and then `just audit`. Keep the README qualification on public guarantees until both pass.

## Public premise and trusted model

`CodeEntry.Bounds` now requires the imported-function count to fit in the function descriptor vector. The worker subtracts that count to locate defined functions. `Module.Environment.Cache.imported_func_bound` derives the premise for decoded modules.

The handwritten Aeneas model represents strong references to immutable code metadata by their underlying value. Construction, cloning and dereferencing preserve that value. The model assumes successful allocation and a representable strong count. Atomic ordering, destruction timing and allocation or reference-count exhaustion are outside the proof. See the repository README’s trust boundary and `ItascaRust/ItascaRust/{TypesExternal,FunsExternal}.lean`.

## Resume from the repository root

```sh
cd lean/Itasca
lake build Itasca.Module.Env.Requirements Itasca.Module.Elab.ValidatedSections Itasca.Results.Batch Itasca.Results.Trace
lake build Itasca.Module.Elab.ToTyping
cd ..
just prove
just audit
```

The snapshot includes the extracted Lean model. Run `just extract` from `lean/` after editing extracted Rust, and review the generated diff.
