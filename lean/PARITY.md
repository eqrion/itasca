# Rocq-to-Lean guarantee comparison

This review compares the public guarantees in the
[archived README](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/README.md#formal-verification)
with the actual Lean theorem statements and their definitions. The Rocq
baseline is `e7a6ce602de0716de89f955300f711b23bc1403e`, preserved by the
`rocq-baseline` tag. All Rocq links below are pinned to that revision. This is
a statement and trust-boundary review, not an inference from theorem names or
successful builds.

The Lean results cover the documented whole-module, body, visiting, decomposed,
and deferred-worker workflows for supported modules. Some results cover more
than the baseline; some helper statements have different premises. **Literal
theorem parity and equivalence of the two complete specifications have not been
proved.** In particular:

- The old independent expression and module binary-determinism theorems have
  no full Lean counterparts yet. Lean proves flat instruction/immediate decoding
  uniqueness, not uniqueness of the entire structured body or raw module AST.
- Accepted-entry soundness for an arbitrary supplied `Env` has an additional
  parameter-vector bound in Lean. Successful environment parsing derives it
  for the documented consumer workflow.
- Separate-buffer module soundness in Lean requires the concatenated module
  to fit `MAX_MODULE_BYTES`; the old region theorems themselves did not.
  Lean also permits an empty code region when there are no defined functions.
- Completeness now targets generated declarative typing plus an explicit Wasm
  1.0 profile. This is a different specification, not a proved replacement of
  every WasmCert judgment by an equivalent SpecTec judgment.

These differences do not exclude accepted supported modules or the documented
SpiderMonkey-style decomposition within the combined module-size cap, using an
environment obtained from `validate_env`. They matter when quoting the stronger
old helper statements for fabricated environments, oversized concatenations,
or independent AST uniqueness.

## Meaning of the new certificate

“Returns” means an ordinary success or validation error in the extracted model,
excluding modeled panic, overflow, out-of-bounds access, and divergence.
Allocation failure is outside the model. “Accepts” means ordinary `Ok`.

[ModuleSound.Validated](Itasca/ModuleSoundness.lean) uses **one raw module
witness** for independent full-byte encoding, elaboration into generated
SpecTec syntax, generated `Module_ok`, the Wasm 1.0 profile, correspondence with
the returned environment/tail, and successful public import/export accessors.
The Rust `Module` does not retain function bodies. The theorem connects its
metadata to this full witness; it does not claim that Rust returns a full AST.
[Matches and AccessorTypes](Itasca/ModuleMetadata.lean) preserve the relevant
declarations, resolved index spaces, import/export order, and external types.

The [body context](Itasca/EnvTranslation.lean) is constructed from the actual
stored types, cached function signatures, globals, tables, memories, locals,
and results. This replaces the seven Rocq `_agree` hypotheses. A standalone
body theorem describes the supplied environment; it does not establish that
the environment came from a valid module. Whole-module proofs establish the
[cache correspondence](Itasca/ModuleEnv.lean) themselves.

## Whole-module public guarantees

In this table and those below, “same contract” describes the API guarantee
after changing the specification and representation. It does not assert a
formal cross-specification equivalence theorem.

| Archived Rocq theorem | Lean theorem and comparison |
| --- | --- |
| [`validate_module_no_panic`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_NoPanic.v#L3125) | [`module.validate_module.wasm_total`](Itasca/ModuleValidation.lean): same unconditional ordinary-return contract for arbitrary input bytes. No valid-input or environment premise. |
| [`validate_module_typed`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Typing.v#L1037) | [`module.validate_module.wasm_sound`](Itasca/ModuleValidation.lean): acceptance implies the full `Validated` certificate, including exact bytes and actual accessor results. Lean additionally exposes the explicit 1.0 profile and cache correspondence in that certificate. |
| [`validate_module_typechecked`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Wasm10.v#L1088) | [`wasm_complete` / `wasm_complete_with_metadata`](Itasca/ModuleCompleteness.lean): independent bounded encoding, `Elaborates`, generated `Module_ok`, and `Profile` imply actual acceptance and matching metadata for the specified raw module. Rocq assumed success of WasmCert's executable module checker, whose completeness against declarative module typing was not available. Lean reaches a declarative target directly, without a parser-success or cache-coherence hypothesis. This strengthening of the target is within the new formalization. |
| [`validate_module_with_no_panic`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Driven.v#L810) | [`module.validate_module_with.total_with_hooks`](Itasca/ModuleVisitorValidation.lean): custom hooks and code hooks must return. The code-hook contract is needed for environments satisfying bounds and validity derived by the parser. Entry overrides may defer validation; termination does not imply entry correctness. The precise hook-bound predicates differ from Rocq's `env_small` formulation. |
| [`validate_module_driven`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Sound.v#L6818) | [`module.validate_module_with.accepted_erase`](Itasca/ModuleVisitorTransfer.lean): visiting acceptance transfers to default acceptance with the same returned module. `Validates` requires accepted entry overrides to imply default entry acceptance. It is needed only for the decoded environment, rather than Rocq's universally quantified environments. No hook-totality premise is needed. |
| [`validate_module_with_complete`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Driven.v#L840) | [`accepted_lift` and `wasm_complete`](Itasca/ModuleVisitorTransfer.lean): accepting custom hooks and code hooks lift every actual default acceptance; a declarative completeness corollary is also provided. The old named theorem took encoded/typed input premises; Lean provides the direct acceptance-transfer statement as well. An entry hook need only accept when default entry validation accepts. |

## Function bodies and opcode visitors

Body soundness needs the context's result vector to have the zero-or-one-result
shape represented by a Wasm 1.0 block type. Body termination does not need that
restriction. Standalone body completeness also requires zero-or-one results
in stored type and function signatures, an independently encoded typed body,
the recursive 1.0 profile, and the body-byte limit.

| Archived Rocq theorem | Lean theorem and comparison |
| --- | --- |
| [`validate_body_no_panic`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/OpIter_NoPanic.v#L177) | [`code.validate_body.wasm_total`](Itasca/WasmSoundness.lean): same unconditional contract for arbitrary bytes, environment, and context. |
| [`validate_body_with_no_panic`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/OpIter_NoPanic.v#L154) | [`code.validate_body_with.wasm_total`](Itasca/WasmSoundness.lean): ordinary return under [`FullVisitor.Total`](Itasca/FullVisitor.lean), covering all actual opcode hooks. |
| [`validate_body_with_typed`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/OpIter_Validate.v#L1386) | [`code.validate_body_with.wasm_sound`](Itasca/VisitorBodyErasure.lean) and [`wasm1_sound`](Itasca/Wasm1Soundness.lean): arbitrary accepted visitors yield independent exact body bytes and declarative typing in the actual context; the latter also yields the recursive 1.0 profile. No visitor termination or acceptance assumption is used to erase an accepted run. |
| [`validate_body_complete`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/OpIter_Complete.v#L3333) | [`code.validate_body.wasm_complete`](Itasca/WasmComplete.lean): declarative typing plus encoding, profile, signature arities, and size imply acceptance. Rocq used the executable body checker, with equivalence to its declarative body typing available. Lean proves the declarative direction directly; [`VisitorBodyComplete`](Itasca/VisitorBodyComplete.lean) lifts it to accepting visitors. |
| [`validate_body_with_trace`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/OpIter_Validate.v#L1287) | [`code.validate_body_with.trace_sound`](Itasca/VisitorBodyTrace.lean): an accepted recording visitor sees the exact encoded token sequence belonging to the same typed body witness. Hook identities, original arguments, validator states, and outcomes are retained. The more general `.trace` covers every ordinary result, including rejection and partial branch tables. |
| [`validate_body_trace`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/OpIter_Validate.v#L1511) and [`trace_records`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/OpIter_Table.v#L1046) | [`VisitorRecording`](Itasca/VisitorRecording.lean) proves concrete recorder/instrumentation recording contracts; [`VisitorBodyTrace`](Itasca/VisitorBodyTrace.lean) proves recorder and instrumentation theorems through the actual API. [`VisitorTraceCorollaries`](Itasca/VisitorTraceCorollaries.lean) projects successful observations to flat tokens with no pending branch-table labels. |

The old generic trace theorem concluded
[`traced`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/OpIter_Visit.v#L1750),
which quantified over observers satisfying `records` and an initially empty
pending-label accumulator. Lean's observation theorem instead takes an explicit
`Records` premise. Its instrumentation theorems apply to arbitrary original
ordinary runs and preserve the original result and visitor state while adding
observations. Thus the recording premise is supported by an actual wrapper,
not an assumption that the implementation dispatched the right hook.

Body rejection traces specify the observed prefix, not successful validation
of unread bytes. In `br_table`, a resolved label is reported before common-type
merging: the mismatching label is observable, an unknown label is not, and the
default target has no label callback. An observed rejecting callback is last
and matches the returned visitor error. These ordinary-result guarantees go
beyond the old accepted-body trace statements.

## Decomposed and deferred guarantees

The archived README's documented consumer contract required bounded buffers and
environments/positions obtained from earlier phases. Several underlying Rocq
theorems were more general than that prose; the distinctions below are material
when comparing the literal statements.

| Archived Rocq theorem | Lean theorem and comparison |
| --- | --- |
| [`validate_module_of_parts`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Driven.v#L747) | [`ModulePipeline.accepted_of_parts`](Itasca/ModulePipeline.lean) and [`wasm_sound_of_parts`](Itasca/ModuleRegions.lean): same accepted adjacent-phase composition with the module-size bound and exact returned environment/tail. |
| [`validate_code_entry_ok`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_NoPanic.v#L2562) | [`module.validate_code_entry.spec_of_env`](Itasca/ModuleDecomposed.lean) derives entry return, byte provenance, and bounds from an actual accepted bounded environment decode. Lower-level [`ModuleCodeEntry`](Itasca/ModuleCodeEntry.lean) uses `CodeEntry.Bounds`; this is not the old `env_small` record of all vector/counter bounds. |
| [`validate_code_entry_with_sound`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Sound.v#L5660) | [`module.validate_code_entry_with.wasm_sound`](Itasca/ModuleEntryVisitor.lean) and [`.trace_sound`](Itasca/ModuleEntryTrace.lean) give exact entry bytes, declared type, typed body, and original callback observations. **Additional helper premise:** `CodeEntry.Bounds env`. Both versions require stored type result arity at most one. [`.wasm_sound_of_env`](Itasca/ModuleDecomposed.lean) discharges the environment premises for parsed environments. |
| [`validate_code_entry_complete`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Complete.v#L3997) | [`module.validate_code_entry.complete`](Itasca/ModuleCodeEntryComplete.lean): independently encoded, declaratively typed entries within the actual body/local caps succeed, under index validity, `Wasm1.Environment`, and `CodeEntry.Bounds`. Unlike the old statement, no already-returned evaluation is assumed. The cap covers body bytes, not the entire size-prefixed entry; see below. |
| [`validate_code_entry_driven`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Driven.v#L153) | [`module.validate_code_entry_with.accepted_erase`](Itasca/ModuleEntryVisitor.lean): accepted visiting entry validation transfers to default validation at exactly the same end cursor, without assumptions on unrelated callback runs or on environment bounds. |
| [`validate_code_with_deferred`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Driven.v#L662) | [`module.validate_code_with.deferred_erase`](Itasca/ModuleDeferred.lean): accepted recording code traversal plus successful validation of every pair in the final work observation implies default code acceptance. [`ModuleEntryOrder`](Itasca/ModuleEntryOrder.lean) additionally identifies the exact sequence of defined-function indices. |
| [`validate_module_regions_typed`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Typing.v#L1086) | [`module.validate_module.regions_wasm_sound`](Itasca/ModuleRegions.lean): exact environment/code consumption and accepted tail validation on separate buffers yield the full module certificate for their concatenation. **Different premises:** Lean requires a representing concatenated slice and a combined module-size bound; Rocq concluded typing of a concatenated list without that bound, but required the code buffer to begin with a code-section header. Lean permits an empty code region. |
| [`validate_module_regions_deferred_typed`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Driven.v#L922) | [`module.validate_module.regions_deferred_wasm_sound`](Itasca/ModuleDeferredValidation.lean): same separate-buffer/deferred composition, with the region differences above. Worker obligations refer to the code buffer actually handed to the workers. |

`CodeEntry.Bounds env` says that each stored type's parameter count plus
`MAX_LOCALS` fits `Usize.max`. It is a sufficient allocation/arithmetic bound,
not an additional Wasm type rule. The old accepted-entry theorem did not require
it. [`ModuleEnv.accepted_entry_conditions`](Itasca/ModuleDecomposed.lean)
derives it and the result-arity condition from successful environment parsing
within `MAX_MODULE_BYTES`. It therefore does not impose extra semantic work on
normal decomposed consumers.

The old entry completeness statement assumed an equation showing that the
entry validator had already returned an ordinary result, and bounded the
consumed size-prefixed entry span. The new statement proves exact success
without that equation. [`CodeEncodingWithinLimits`](Itasca/ModuleCodeLimits.lean)
bounds declared locals by 50,000 and the actual instruction body, including its
final `end`, by 7,654,321 bytes. Parameters, encoded local declarations, and the
entry's size prefix are not counted toward those respective limits. Whole-module
completeness additionally bounds all module bytes by 1,073,741,824 through
[`ModuleEncodingWithinLimits`](Itasca/ModuleLimits.lean).

For a whole visiting module with deferred workers,
[`deferred_wasm_sound`](Itasca/ModuleDeferredValidation.lean) uses the **final**
visitor work observation. Custom callbacks must preserve that observation so
tail processing cannot erase an outstanding obligation. Worker completion means
successful actual entry validation, not merely dispatch or worker termination.
No worker scheduling, memory sharing, or foreign-interface pointer safety is
proved.

## Binary determinism: an explicit remaining difference

| Archived binary theorem | Current Lean coverage |
| --- | --- |
| [`repr_ops_det`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Spec_Binary.v#L814) | [`WasmBinaryUnique`](Itasca/WasmBinaryUnique.lean) proves immediate/token/cursor uniqueness and uniqueness of flat tokens consumed over the same span, including branch-table labels. The representations differ, so there is no theorem directly equating these old and new flat-op relations. |
| [`repr_expr_det`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Spec_Expr.v#L542) | **Not ported as a full structured-expression uniqueness theorem.** [`WasmSyntax`](Itasca/WasmSyntax.lean) relates flat tokens to nested instruction trees; the public body proofs produce such a tree, but no theorem here states that all independent encodings of the same body have the same tree. |
| [`repr_module_det`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Spec_Module.v#L933) | **Not ported as a full raw-module uniqueness theorem.** [`ModuleBinary`](Itasca/ModuleBinary.lean) supplies the independent module grammar; soundness and completeness do not constitute a proof of its injective decoding. |

The accepted trace proofs align the independently decoded flat tokens with
those of the typed witness using token uniqueness. They then retain that same
tree in the certificate. This is sufficient for their stated same-body claims;
it does not fill the independent AST/module-determinism gap.

## Additional guarantees and changed specification boundary

The old README explicitly left custom-section ranges unverified. Lean now has
[accepted module traces](Itasca/ModuleTraceValidation.lean), including ordered
custom-section callbacks, byte requests, and entry handoffs, with independent
section/code framing. [Custom range proofs](Itasca/ModuleCustomRanges.lean)
recover the exact strict-UTF-8 name bytes immediately preceding the payload and
prove the payload bounds. A `need_bytes` request is a requested boundary, not a
claim that those bytes are already present; lookahead requests may exceed EOF.

[Entry traces](Itasca/ModuleEntryTrace.lean) additionally preserve the actual
`functionStart` event, signature, size prefix, grouped-local span, and exact
body slice. The function-start positions are offsets in the entry buffer;
operator-state positions are relative to the sliced body. The old flat-op
recording contract treated function-start as observation-preserving.
General module/entry rejection traces remain outside these accepted-run results.

The [Wasm 1.0 profile](Itasca/ModuleProfile.lean) is part of both module soundness
and completeness. It supplies export-name uniqueness, at most one combined
imported/defined table and memory, zero-or-one function results, and recursive
body restrictions. These conditions cannot be replaced by “uses only old
opcodes.” In particular, generated Wasm 2.0 typing permits some polymorphic
`br_table` programs with unequal target types that the Wasm 1.0 implementation
rejects. [WasmCompletenessBoundary](Itasca/WasmCompletenessBoundary.lean) contains
a checked witness; [Wasm1Profile](Itasca/Wasm1Profile.lean) requires exact target
type agreement. The generated module rule alone also does not establish export
name uniqueness or the combined imported/defined memory bound.

[Elaboration](Itasca/ModuleElaboration.lean) resolves binary function type
indices, ties function declarations to code entries, and translates names and
segments. [Body context transport](Itasca/BodyContext.lean) connects the body
validator's context to module contexts with element/data components. These
adapters are proved for the supported syntax, rather than justified by a
general equivalence between the two specification developments.

## Trust comparison and verification scope

- **Extracted program.** Both developments trust Rust-to-LLBC extraction and
  Aeneas translation. Lean uses its separately pinned, newer toolchain and
  source patches. Regeneration checks detect drift; they do not prove that
  either compiler implements Rust semantics correctly.
- **Specification.** Rocq targeted WasmCert-Coq; Lean targets the pinned,
  locally repaired SpecTec-generated definitions. The source repairs and
  upstream status are documented in [UPSTREAM.md](../UPSTREAM.md). The generated
  development still contains unfinished upstream material. Local audited proofs
  cannot depend on its unfinished lemmas or domain-specific axioms. That audit
  does not establish that the full generated specification is faithful or
  complete.
- **Binary syntax and translations.** Both use a handwritten binary grammar.
  Lean's grammar covers section order/framing, custom sections, strict UTF-8,
  nonminimal valid LEBs, grouped locals, active segments, and complete input
  consumption. Semantic adapters, numeric/memory opcode maps, and float-bit
  translation are handwritten and reviewed. Their correctness relative to the
  written WebAssembly standard remains part of the specification trust
  boundary. Decoder correctness against those definitions is proved; full
  grammar determinism has the gaps listed above.
- **Rust library/loop models.** The archived
  [Aeneas_Specs](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Aeneas_Specs.v)
  and [external models](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Itasca_FunsExternal.v)
  supplied domain-specific axioms about library operations and loops. The Lean
  pipeline uses checked Aeneas library proofs and concrete
  [external definitions](Itasca/Generated/FunsExternal.lean) for the missing
  operations. It does not inherit those project axioms; allocation failure
  remains unmodeled.
- **Kernel and axioms.** [`Audit`](Itasca/Audit.lean) checks transitive
  dependencies of imported public Itasca theorems and explicit adapter roots.
  Only `propext`, `Classical.choice`, and `Quot.sound` are allowed; `sorryAx` and
  domain-specific axioms are rejected. Import-coverage checks include new proof
  modules. This is a different trusted foundation from Rocq, so raw assumption
  counts are not comparable. The archived [trust report](baseline/rocq-trust.txt)
  and [revision pins](baseline/revisions.json) preserve the baseline evidence.

The remaining general exclusions are execution semantics, allocation failure,
and a complete classification of which error every malformed input returns.
Specific negative examples and body rejection-trace properties do not claim
that last classification. Neither a full build nor passing Rust/specification
tests proves equivalence between WasmCert, SpecTec, and the prose WebAssembly
specification. The [validation record](baseline/VALIDATION.md) records the
migration checks separately from this theorem comparison.
