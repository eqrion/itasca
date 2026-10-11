# Upstream follow-up tracker

The Lean migration required five concrete upstream changes. All are local:
no issue or pull request has been submitted for them. This document records the
patches, reproductions, and follow-up work so they can be discussed with the
Aeneas and SpecTec maintainers. Issue/PR fields below are deliberately unfilled.

The patches change tool or specification sources. Generated Lean is regenerated
through the normal pipeline and must not be edited by hand. Passing local
regressions does not establish that a general upstream bug is fixed: two SpecTec
changes only avoid affected source patterns in the judgments used here.

## Pinned sources

| Component | Checkout and revision |
| --- | --- |
| Aeneas | [AeneasVerif/aeneas](https://github.com/AeneasVerif/aeneas), `vendor/aeneas-lean`, `557eff83ecef5083b98a52a94ca7fae63d6c1dab` |
| Charon | [AeneasVerif/charon](https://github.com/AeneasVerif/charon), revision from Aeneas's `charon-pin`: `c8f15d7d658c86a95658f71ad99cddd4be002e04` |
| SpecTec | [zilinc/spectec, lean-backend](https://github.com/zilinc/spectec/tree/lean-backend), `vendor/spectec`, `edc84f7ec81f927f3fdb952a82ecd38fed8e4f29` |
| Lean / Mathlib | `v4.31.0`; transitive revisions in [lean/lake-manifest.json](lean/lake-manifest.json) |
| Extraction / generator tools | Rust `nightly-2026-09-17`, OCaml `5.2.0`, Dune `3.23.1` |

[Baseline revisions](lean/baseline/revisions.json) retain the old Rocq pins too.
The archived Rocq tree is the `rocq-baseline` tag at
`e7a6ce602de0716de89f955300f711b23bc1403e`.
See [lean/README.md](lean/README.md) for installation and
[lean/upstream/README.md](lean/upstream/README.md) for the original investigation.

## Five implemented changes

### 1. Aeneas: generated names can capture namespaces

**Status:** general Lean-backend fix implemented locally, with upstream-style
regressions. **Issue:** not filed. **PR:** not submitted.

A structure field named `types` hides the namespace in later
`types.FuncType` field types. A field named `module` similarly hides
`module.ImportDesc`. Local binders can also hide namespaces in constructor
references such as `types.ValueType.I32`.

[Aeneas patch](patches/aeneas-lean-extraction.patch) qualifies generated type
references with their root namespace and reserves namespace prefixes when naming
local binders. Builtin names, declaration names, and recursive-group references
retain their required treatment. The change is specific to the Lean backend.

Reproduce with [namespace-shadow.rs](lean/upstream/namespace-shadow.rs) and
`make -C lean aeneas-repro`. The patch adds
`vendor/aeneas-lean/tests/src/namespace-shadow.rs` and its generated
`tests/lean/NamespaceShadow.lean`; `just regressions` checks fields, generics,
recursive references, constructor evaluation, and an explicit namespace override.

- [x] Fix extractor sources and check both the minimal and full-validator cases.
- [x] Add regression sources and regenerated expected Lean output to the patch.
- [ ] Submit the naming fix and tests; fill in the issue/PR links above.
- [ ] Check upstream's preferred naming policy and remove this patch component after updating the pin.

### 2. Aeneas: deeply nested `else if` output loses valid indentation

**Status:** general Lean-backend printer fix implemented locally, with regressions.
**Issue:** not filed. **PR:** not submitted.

The numeric visitor dispatcher exhausts OCaml Format's indentation budget as
successive `else if` clauses keep opening deeper boxes. Lean then interprets a
continued function application as separate statements in a `do` block.

The same [Aeneas patch](patches/aeneas-lean-extraction.patch), in
`src/extract/Extract.ml`, prints Lean `else if` chains at constant indentation.
It preserves the translated expression and does not require a wider line limit.

The patch adds `tests/src/deep-else-if.rs` and regenerated
`tests/lean/DeepElseIf.lean` in the Aeneas checkout. `just regressions` extracts
and checks its 48-branch dispatcher, including early, late, and fallback paths.
The actual validator's dispatchers are covered by `just extract-check` and
`just prove`.

- [x] Fix the printer and check the minimal dispatcher and full extraction.
- [ ] Submit the printing change and regression, separately from naming if maintainers prefer.
- [ ] Remove this patch component after the upstream fix is pinned and both regressions still pass.

### 3. SpecTec: optional mutability drops the immutable case

**Status:** equivalent source-rule workaround implemented; the general
transformation defect is **not fixed**. **Issue:** not filed. **PR:** not submitted.

At the pinned revision, `|- MUT? t : OK` yields a Lean `Globaltype_ok`
constructor only for `some MUT`, omitting immutable globals. The
`remove-indexed-types` pass in `spectec/src/middlend/undep.ml` rewrites an
`IterE` with `(Opt, [])` to `OptE (Some e1)`.

[The local patch](patches/spectec-wasm2-global-mutability.patch) changes the
Wasm source rule in `specification/wasm-2.0/6-typing.spectec` to `|- mut t : OK`.
Because `syntax mut = MUT?`, the variable includes both valid cases. This avoids
the affected pattern without changing the allowed globals.

[optional-mutability.spectec](lean/upstream/optional-mutability.spectec) retains
the original failing form. `make -C lean spec-repro` regenerates its output in
`lean/.build/optional-mutability.lean`; this reproducer intentionally continues
to exhibit the unfixed general defect. [SpecChecks](lean/Itasca/SpecChecks.lean)
checks both mutabilities in the patched full specification, and
[TypeTranslation](lean/Itasca/Support/TypeTranslation.lean) covers every extracted global type.

- [x] Minimize and locate the transformation defect; regenerate an equivalent local workaround.
- [ ] File the reproducer and proposed source workaround with the SpecTec maintainers.
- [ ] Fix the general optional-pattern transformation and test constructors with and without iteration variables.
- [ ] Remove the workaround only after the original rule generates both cases and the full proofs pass.

### 4. SpecTec: four-byte UTF-8 has the wrong scalar upper bound

**Status:** specification-source typo corrected locally. This is not a backend
repair. **Issue:** not filed. **PR:** not submitted.

`specification/wasm-2.0/A-binary.spectec` bounded four-byte UTF-8 characters by
`U+10000 <= ch < U+11000`. The upper bound must be `U+110000`, consistent with
the character syntax in `1-syntax.spectec`. The old bound excluded valid names
containing characters such as U+1F600.

[The module source patch](patches/spectec-wasm2-module.patch) corrects the bound.
[SpecChecks](lean/Itasca/SpecChecks.lean) proves actual byte encodings for
U+10000, U+1F600, and U+10FFFF. [ModuleUnicodeExamples](lean/Itasca/Examples/ModuleUnicodeExamples.lean)
checks public acceptance at the upper scalar boundary and rejection above it;
[ModuleImportedGlobalExamples](lean/Itasca/Examples/ModuleImportedGlobalExamples.lean)
covers an emoji-named import. Run `just spec-check` and `just prove`.

- [x] Correct the source and regenerate the committed specification.
- [x] Add boundary and real-name regression proofs.
- [ ] Submit the source correction and boundary cases; fill in issue/PR links.
- [ ] Remove this patch hunk when the corrected source is pinned.

### 5. SpecTec: `otherwise` guards disappear from import projections

**Status:** four source functions rewritten locally; general `otherwise`
translation is **not fixed**. **Issue:** not filed. **PR:** not submitted.

The generated fallback rules for `funcsxt`, `globalsxt`, `tablesxt`, and `memsxt`
lose their `otherwise` guards. For example, the unpatched relation can derive
`fun_funcsxt [FUNC ft] []`, dropping a matching function import and changing the
module's index spaces.

[The module source patch](patches/spectec-wasm2-module.patch) replaces each
fallback in `specification/wasm-2.0/2-syntax-aux.spectec` with explicit cases for
the three nonmatching external-type constructors. No matching case can then be
silently discarded. [ModuleTranslation](lean/Itasca/Module/ModuleTranslation.lean)
proves exact canonical projections and their uniqueness.

[otherwise-projection.spectec](lean/upstream/otherwise-projection.spectec)
reduces the defect to KEEP/DROP tags. `make -C lean spec-repro` produces
`lean/.build/otherwise-projection.lean`, whose uncorrected fallback still permits
dropping KEEP. [SpecChecks](lean/Itasca/SpecChecks.lean) proves that the four
patched full-spec projections cannot drop a singleton matching import.

- [x] Minimize the lost guard and replace all four relied-on fallbacks with disjoint cases.
- [ ] File the reproducer and source workaround with the backend maintainers.
- [ ] Implement general guard preservation, including overlapping and ordered source clauses.
- [ ] Restore the original fallbacks only after the no-drop and uniqueness proofs pass on regenerated output.

## Additional module specification gaps

These are **not repaired in the upstream source patches**. The local
[ModuleConditions/Profile](lean/Itasca/Module/ModuleProfile.lean) supplies them explicitly;
module soundness establishes them and completeness requires them. They are not
hidden assumptions that an unchecked parser happened to enforce.

### Export names are not required to be distinct

**Status:** confirmed missing source condition; covered by the local profile.
**Issue/PR:** not filed / not submitted.

`Module_ok` in `specification/wasm-2.0/6-typing.spectec` contains a
`TODO: disjoint export names`. Its generated constructor therefore admits
otherwise well-typed modules with duplicate export names. The local condition
is `unique_exports`, a `Nodup` statement about **decoded Unicode names**, with
strict UTF-8 injectivity proved in [ModuleUnicodeUnique](lean/Itasca/Binary/ModuleUnicodeUnique.lean).
[ModuleNegativeExamples](lean/Itasca/Examples/ModuleNegativeExamples.lean) checks public
rejection of duplicate U+10FFFF export names.

- [ ] Add a minimized source-level duplicate-name case to an upstream report.
- [ ] Agree on and implement the missing uniqueness premise, then regenerate and update the assembly proofs.
- [ ] Reassess whether the supplemental profile field can be derived directly from generated `Module_ok`.

### The memory count omits imported memories

**Status:** confirmed mismatch in the source module rule; covered by the local
profile. **Issue/PR:** not filed / not submitted.

The same `Module_ok` rule checks `|mt*| <= 1`, where `mt*` contains only defined
memories. Its context is built with `MEMS imt* mt*`, including imported memories.
The Wasm 2.0 single-memory restriction must count both. The local `memory_count`
condition checks the combined count; accepted runtime environments also establish
that bound.

- [ ] Add a minimal imported-plus-defined-memory case, and a two-import case, to an upstream report.
- [ ] Correct the source condition to bound the full memory index space and add generated-judgment regressions.
- [ ] Reassess the supplemental profile premise after regenerating and checking all module proofs.

The table count, single-result function/block restriction, and homogeneous
`br_table` targets are separate **Wasm 1.0 profile differences**, not requests to
restrict a Wasm 2.0 specification. The
[branch-table boundary example](lean/Itasca/Examples/WasmCompletenessBoundary.lean)
demonstrates a valid 2.0 typing derivation rejected by the unchanged 1.0 validator.

## Investigations to preserve

### Adjacent list-repetition rewrite

The same `undep.ml` branch implicated in optional mutability rewrites list
repetition without iteration variables to a singleton list. This deserves a
semantic review; no general fix or standalone list reproducer is committed.
Do not infer that fixing the optional case settles the list case.

- [ ] Minimize a source rule with unconstrained repetition and compare source, intermediate, and Lean meanings.
- [ ] Determine whether the rewrite is intended in every reachable context; file and fix any failing case.

### UTF-8 arithmetic rules and byte-range constraints

The multi-byte rules in `A-binary.spectec` state scalar ranges and arithmetic
reconstruction but omit explicit leading/continuation-byte ranges. This is a
separate concern from the fixed scalar upper bound. Review whether surrounding
elaboration supplies the missing constraints and whether the generated relation
admits unintended byte decompositions. No general source repair or isolated
regression for this concern is included in the current patches.

The proofs here do not assume that generated `fun_utf8` is a unique or strict
decoder. [ModuleBinary](lean/Itasca/Binary/ModuleBinary.lean) uses an independent strict
UTF-8 grammar; [ModuleUnicode](lean/Itasca/Binary/ModuleUnicode.lean) constructs generated
witnesses from it, and [ModuleUnicodeUnique](lean/Itasca/Binary/ModuleUnicodeUnique.lean)
proves canonical re-encoding and decoded-name injectivity from that strict grammar.

- [ ] Create a minimized invalid-byte decomposition and check the source and generated judgments.
- [ ] Agree on the intended constraints with SpecTec maintainers and add regressions before expanding reliance on the generated UTF-8 relation.

## Updating or retiring patches

[lean/Makefile](lean/Makefile) applies patches idempotently and fails when a
checkout has incompatible edits. The two Aeneas fixes share one patch; the
UTF-8 correction and four import-projection workarounds share another. Remove
only the component that has an upstream replacement.

After changing a pin or patch:

```sh
just regressions              # Patched Aeneas reproductions and generated tests
just extract-check            # Nonmutating comparison with regenerated Rust extraction
make -C lean spec-repro        # Inspect the still-unfixed general SpecTec cases
just spec-check               # Regenerate, compare, and compile the specification
just prove                    # Integrated proofs and axiom audit
just trust                    # Explicit Lean dependency audit
```

If reviewed output is expected to change, use `just extract` for the Rust model
or `make -C lean spec-update` for the generated specification, inspect the diff,
and rerun the checks. The SpecTec checkpoint in the upstream checkout remains
untouched; our generated source is [lean/SpecTec/wasm2.0.lean](lean/SpecTec/wasm2.0.lean).
Keep the pin, patch, regression, and this tracker synchronized. The final test
and theorem-parity evidence belongs in [lean/PARITY.md](lean/PARITY.md).
