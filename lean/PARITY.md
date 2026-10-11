# Rocq-to-Lean guarantee comparison

This review compares the public guarantees in the
[archived README](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/README.md#formal-verification)
with the actual Lean theorem statements and their definitions. The Rocq
baseline is `e7a6ce602de0716de89f955300f711b23bc1403e`, preserved by the
`rocq-baseline` tag. All Rocq links below are pinned to that revision. This is
a statement and trust-boundary review, not an inference from theorem names or
successful builds.

The Lean results cover whole-module validation, body and entry visitors, and
streaming workers for supported modules. The ordinary module API now wraps the
single streaming driver. The old module/code visitor and deferred-worklist APIs
were retired; their streaming successors have different interfaces and contracts.
Some results cover more than the baseline; some helper statements have different
premises. **Literal theorem parity and equivalence of the two complete
specifications have not been proved.** In particular:

- Independent expression and module binary determinism now have Lean
  counterparts for the local grammar, including structured bodies and raw
  modules. These do not assert equivalence with the archived representations.
- Accepted-entry soundness for an arbitrary supplied `Env` has an additional
  parameter-vector bound in Lean. Successful environment parsing derives it
  for the documented consumer workflow.
- Streaming soundness for separate buffers derives the combined
  `MAX_MODULE_BYTES` bound from the accepted driver run. The independent
  semantic region-composition theorem has no module-size premise. The old region
  theorems themselves did not require a combined bound. Lean also permits an
  empty code region when there are no defined functions.
- Completeness now targets generated declarative typing plus an explicit Wasm
  1.0 profile. This is a different specification, not a proved replacement of
  every WasmCert judgment by an equivalent SpecTec judgment.

The streaming interface supports decomposition within the combined module-size
cap, with coherent source views and actual-operation worker provenance. These
contracts replace the old module visitor's callback and final-worklist premises;
they do not establish compatibility of an external embedding. The differences
also matter when quoting old helper statements for fabricated environments,
oversized concatenations.

## Meaning of the new certificate

“Returns” means an ordinary success or validation error in the extracted model,
excluding modeled panic, overflow, out-of-bounds access, and divergence.
Allocation failure is outside the model. “Accepts” means ordinary `Ok`.

[ModuleSound.Validated](Itasca/Module/ModuleSoundness.lean) uses **one raw module
witness** for independent full-byte encoding, elaboration into generated
SpecTec syntax, generated `Module_ok`, the Wasm 1.0 profile, correspondence with
the returned environment/tail, and successful public import/export accessors.
The Rust `Module` does not retain function bodies. The theorem connects its
metadata to this full witness; it does not claim that Rust returns a full AST.
[Matches and AccessorTypes](Itasca/Module/ModuleMetadata.lean) preserve the relevant
declarations, resolved index spaces, import/export order, and external types.

The [body context](Itasca/Body/EnvTranslation.lean) is constructed from the actual
stored types, cached function signatures, globals, tables, memories, locals,
and results. This replaces the seven Rocq `_agree` hypotheses. A standalone
body theorem describes the supplied environment; it does not establish that
the environment came from a valid module. Whole-module proofs establish the
[cache correspondence](Itasca/Module/ModuleEnv.lean) themselves.

## Whole-module public guarantees

In this table and those below, “same contract” describes the API guarantee
after changing the specification and representation. It does not assert a
formal cross-specification equivalence theorem.

| Archived Rocq theorem | Lean theorem and comparison |
| --- | --- |
| [`validate_module_no_panic`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_NoPanic.v#L3125) | [`module.validate_module.wasm_total`](Itasca/Module/ModuleValidation.lean): same unconditional ordinary-return contract for arbitrary input bytes. No valid-input or environment premise. |
| [`validate_module_typed`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Typing.v#L1037) | [`module.validate_module.wasm_sound`](Itasca/Module/ModuleValidation.lean): acceptance implies the full `Validated` certificate, including exact bytes and actual accessor results. Lean additionally exposes the explicit 1.0 profile and cache correspondence in that certificate. |
| [`validate_module_typechecked`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Wasm10.v#L1088) | [`wasm_complete` / `wasm_complete_with_metadata`](Itasca/Module/ModuleCompleteness.lean): independent bounded encoding, `Elaborates`, generated `Module_ok`, and `Profile` imply actual acceptance and matching metadata for the specified raw module. Rocq assumed success of WasmCert's executable module checker, whose completeness against declarative module typing was not available. Lean reaches a declarative target directly, without a parser-success or cache-coherence hypothesis. This strengthening of the target is within the new formalization. |
| [`validate_module_with_no_panic`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Driven.v#L810) | Successor: [`stream.validate_streaming.wasm_total`](Itasca/Stream/StreamDriverTotal.lean), under separate source and scheduler callback-return contracts. Submission callbacks need return only for legitimate bounded seeds with environment bounds derived by parsing. Polls may return arbitrary malformed or unfinished batches. No source coherence, worker provenance, or worker-success premise is needed. The old `validate_module_with` API is retired. |
| [`validate_module_driven`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Sound.v#L6818) | Successor: [`stream.validate_streaming.wasm_sound`](Itasca/Stream/StreamValidation.lean). Accepted execution, coherent source views, and [`Provenance`](Itasca/Stream/StreamScheduler.lean) yield `Validated` for the returned environment and the exact delivered tail. Provenance records actual batch-method reachability; it does not assume successful workers or finish checks. No callback-totality premise is needed. The old module-visitor erasure API is retired. |
| [`validate_module_with_complete`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Driven.v#L840) | Successor: [`stream.validate_streaming.wasm_complete`](Itasca/Stream/StreamDriverComplete.lean), from independent bounded encoding, elaboration, generated typing, and profile, plus canonical source availability and an [`accepting scheduler`](Itasca/Stream/StreamAcceptingScheduler.lean). This sufficient worker policy uses actual `validate_all` execution, supports any positive fixed batching configuration and arbitrary completion order, and derives successful finish checks. Metadata and the actual delivered tail match the same specified raw module. The old module-visitor acceptance-lifting API is retired. |

## Function bodies and opcode visitors

Body soundness needs the context's result vector to have the zero-or-one-result
shape represented by a Wasm 1.0 block type. Body termination does not need that
restriction. Standalone body completeness also requires zero-or-one results
in stored type and function signatures, an independently encoded typed body,
the recursive 1.0 profile, and the body-byte limit.

| Archived Rocq theorem | Lean theorem and comparison |
| --- | --- |
| [`validate_body_no_panic`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/OpIter_NoPanic.v#L177) | [`code.validate_body.wasm_total`](Itasca/Body/WasmSoundness.lean): same unconditional contract for arbitrary bytes, environment, and context. |
| [`validate_body_with_no_panic`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/OpIter_NoPanic.v#L154) | [`code.validate_body_with.wasm_total`](Itasca/Body/WasmSoundness.lean): ordinary return under [`FullVisitor.Total`](Itasca/Visitor/FullVisitor.lean), covering all actual opcode hooks. |
| [`validate_body_with_typed`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/OpIter_Validate.v#L1386) | [`code.validate_body_with.wasm_sound`](Itasca/Visitor/VisitorBodyErasure.lean) and [`wasm1_sound`](Itasca/Body/Wasm1Soundness.lean): arbitrary accepted visitors yield independent exact body bytes and declarative typing in the actual context; the latter also yields the recursive 1.0 profile. No visitor termination or acceptance assumption is used to erase an accepted run. |
| [`validate_body_complete`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/OpIter_Complete.v#L3333) | [`code.validate_body.wasm_complete`](Itasca/Body/WasmComplete.lean): declarative typing plus encoding, profile, signature arities, and size imply acceptance. Rocq used the executable body checker, with equivalence to its declarative body typing available. Lean proves the declarative direction directly; [`VisitorBodyComplete`](Itasca/Visitor/VisitorBodyComplete.lean) lifts it to accepting visitors. |
| [`validate_body_with_trace`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/OpIter_Validate.v#L1287) | [`code.validate_body_with.trace_sound`](Itasca/Visitor/VisitorBodyTrace.lean): an accepted recording visitor sees the exact encoded token sequence belonging to the same typed body witness. Hook identities, original arguments, validator states, and outcomes are retained. The more general `.trace` covers every ordinary result, including rejection and partial branch tables. |
| [`validate_body_trace`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/OpIter_Validate.v#L1511) and [`trace_records`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/OpIter_Table.v#L1046) | [`VisitorRecording`](Itasca/Visitor/VisitorRecording.lean) proves concrete recorder/instrumentation recording contracts; [`VisitorBodyTrace`](Itasca/Visitor/VisitorBodyTrace.lean) proves recorder and instrumentation theorems through the actual API. [`VisitorTraceCorollaries`](Itasca/Visitor/VisitorTraceCorollaries.lean) projects successful observations to flat tokens with no pending branch-table labels. |

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
when comparing the literal statements. Current entry validators remain public;
the old module/code visitor traversal and deferred-worklist contracts have been
replaced by streaming submission, checked retirement, and final draining.

| Archived Rocq theorem | Lean theorem and comparison |
| --- | --- |
| [`validate_module_of_parts`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Driven.v#L747) | [`ModuleSound.assembled_regions`](Itasca/Module/ModuleSoundness.lean) composes independent environment, code, and tail certificates with exact byte tiling into one `Validated` witness. Actual execution is covered by [`stream.validate_streaming.wasm_sound`](Itasca/Stream/StreamValidation.lean). The old adjacent-phase execution-composition helper is retired. |
| [`validate_code_entry_ok`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_NoPanic.v#L2562) | [`module.validate_code_entry.spec_of_env`](Itasca/Module/ModuleDecomposed.lean) derives entry return, byte provenance, and bounds from an actual accepted bounded environment decode. Lower-level [`ModuleCodeEntry`](Itasca/Module/ModuleCodeEntry.lean) uses `CodeEntry.Bounds`; this is not the old `env_small` record of all vector/counter bounds. |
| [`validate_code_entry_with_sound`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Sound.v#L5660) | [`module.validate_code_entry_with.wasm_sound`](Itasca/Module/ModuleEntryVisitor.lean) and [`.trace_sound`](Itasca/Module/ModuleEntryTrace.lean) give exact entry bytes, declared type, typed body, and original callback observations. **Additional helper premise:** `CodeEntry.Bounds env`. Both versions require stored type result arity at most one. [`.wasm_sound_of_env`](Itasca/Module/ModuleDecomposed.lean) discharges the environment premises for parsed environments. |
| [`validate_code_entry_complete`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Complete.v#L3997) | [`module.validate_code_entry.complete`](Itasca/Module/ModuleCodeEntryComplete.lean): independently encoded, declaratively typed entries within the actual body/local caps succeed, under index validity, `Wasm1.Environment`, and `CodeEntry.Bounds`. Unlike the old statement, no already-returned evaluation is assumed. The cap covers body bytes, not the entire size-prefixed entry; see below. |
| [`validate_code_entry_driven`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Driven.v#L153) | [`module.validate_code_entry_with.accepted_erase`](Itasca/Module/ModuleEntryVisitor.lean): accepted visiting entry validation transfers to default validation at exactly the same end cursor, without assumptions on unrelated callback runs or on environment bounds. |
| [`validate_code_with_deferred`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Driven.v#L662) | Successors: [`StreamBatch.Reachable.finished`](Itasca/Stream/StreamBatch.lean) derives exact typed entries from actual worker operations and successful finish; [`StreamScheduler.Partition.code`](Itasca/Stream/StreamPartition.lean) assembles their exact byte coverage and ordered function indices. [Submission](Itasca/Stream/StreamSubmission.lean) and [draining](Itasca/Stream/StreamDrain.lean) derive the completed obligations from accepted execution. No assumed validation of a final recorded worklist is used. The old code-visitor walk is retired. |
| [`validate_module_regions_typed`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Typing.v#L1086) | Successor: [`stream.validate_streaming.wasm_sound`](Itasca/Stream/StreamValidation.lean), with coherent separate environment/code/tail views, worker provenance, and a slice representing their concatenation. Acceptance yields the full certificate and the checked combined module-size bound. Rocq concluded typing of a concatenated list without that bound, but required a code-section header. Lean permits an empty code region for no defined functions. Independent [`assembled_regions`](Itasca/Module/ModuleSoundness.lean) has no combined-size premise. |
| [`validate_module_regions_deferred_typed`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Module_Driven.v#L922) | The same [`stream.validate_streaming.wasm_sound`](Itasca/Stream/StreamValidation.lean) covers deferred workers under [`Provenance`](Itasca/Stream/StreamScheduler.lean), with the region differences above. Worker reachability starts from the exact submitted batch and bytes, and every callback preserves issued history. Successful worker validation is derived at checked retirement. The old separate-buffer/deferred execution API is retired. |

`CodeEntry.Bounds env` says that each stored type's parameter count plus
`MAX_LOCALS` fits `Usize.max`. It is a sufficient allocation/arithmetic bound,
not an additional Wasm type rule. The old accepted-entry theorem did not require
it. [`ModuleEnv.accepted_entry_conditions`](Itasca/Module/ModuleDecomposed.lean)
derives it and the result-arity condition from successful environment parsing
within `MAX_MODULE_BYTES`. It therefore does not impose extra semantic work on
normal decomposed consumers.

The old entry completeness statement assumed an equation showing that the
entry validator had already returned an ordinary result, and bounded the
consumed size-prefixed entry span. The new statement proves exact success
without that equation. [`CodeEncodingWithinLimits`](Itasca/Module/ModuleCodeLimits.lean)
bounds declared locals by 50,000 and the actual instruction body, including its
final `end`, by 7,654,321 bytes. Parameters, encoded local declarations, and the
entry's size prefix are not counted toward those respective limits. Whole-module
completeness additionally bounds all module bytes by 1,073,741,824 through
[`ModuleEncodingWithinLimits`](Itasca/Module/ModuleLimits.lean).

For streaming workers, [`Provenance`](Itasca/Stream/StreamScheduler.lean) preserves
issued history through every callback, including environment/tail custom hooks.
Matching polled batches must be reachable from their submitted seed through
actual batch methods, which may use arbitrary opcode visitors. The driver checks
pending identities and successful finish, so foreign, replayed, and unfinished
batches cannot discharge an obligation. The proof derives complete typed entries
from those checks; dispatch or worker termination alone is insufficient.
[Source contracts](Itasca/Stream/StreamSource.lean) separate coherence of successful
views, availability of valid requests, and ordinary callback return. No worker
scheduling, memory sharing, or foreign-interface pointer safety is proved.

## Binary determinism

| Archived binary theorem | Current Lean coverage |
| --- | --- |
| [`repr_ops_det`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Spec_Binary.v#L814) | [`WasmBinaryUnique`](Itasca/Binary/WasmBinaryUnique.lean) proves immediate/token/cursor uniqueness and uniqueness of flat tokens consumed over the same span, including branch-table labels. The representations differ, so there is no theorem directly equating these old and new flat-op relations. |
| [`repr_expr_det`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Spec_Expr.v#L542) | [`WasmSyntaxUnique`](Itasca/Binary/WasmSyntaxUnique.lean) proves `Emits.unique` and `BodyTokens.unique` for nested trees. [`WasmBinaryUnique`](Itasca/Binary/WasmBinaryUnique.lean) lifts this to `Wasm.BodyEncoding.unique` for complete body bytes. [`WasmBinaryPrefix`](Itasca/Binary/WasmBinaryPrefix.lean) also proves `ModuleBinary.BodyEncoding.unique` for unbounded byte lists. |
| [`repr_module_det`](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Spec_Module.v#L933) | [`ModuleBinaryUnique`](Itasca/Binary/ModuleBinaryUnique.lean) proves `ModuleBinary.ModuleEncoding.unique`: two independent encodings of the same bytes have the same raw module AST. It accounts for custom sections, omitted fields, and grouped locals without typing or implementation-size premises. |

The accepted trace proofs align the independently decoded flat tokens with
those of the typed witness using token uniqueness. They then retain that same
tree in the certificate. The independent uniqueness theorems also establish that
any other decoding of those body or module bytes yields the same tree.

## Additional guarantees and changed specification boundary

The old README explicitly left custom-section ranges unverified. Retained
[custom trace proofs](Itasca/Module/ModuleCustomTrace.lean) describe accepted environment
and tail callbacks against independent section framing.
[Custom range proofs](Itasca/Module/ModuleCustomRanges.lean) recover the exact strict-UTF-8
name bytes immediately preceding the payload and prove the payload bounds.
The old module-wide callback trace, `need_bytes`, and code-entry handoff contracts
were retired with their APIs. [`StreamRun.Accepted`](Itasca/Stream/StreamRun.lean) instead
records the actual streaming phases, submission, tail delivery, and draining;
it is not a replacement theorem for that entire former callback-event trace.

[Entry traces](Itasca/Module/ModuleEntryTrace.lean) additionally preserve the actual
`functionStart` event, signature, size prefix, grouped-local span, and exact
body slice. The function-start positions are offsets in the entry buffer;
operator-state positions are relative to the sliced body. The old flat-op
recording contract treated function-start as observation-preserving.
General module/entry rejection traces remain outside these accepted-run results.

The [Wasm 1.0 profile](Itasca/Module/ModuleProfile.lean) is part of both module soundness
and completeness. It supplies export-name uniqueness, at most one combined
imported/defined table and memory, zero-or-one function results, and recursive
body restrictions. These conditions cannot be replaced by “uses only old
opcodes.” In particular, generated Wasm 2.0 typing permits some polymorphic
`br_table` programs with unequal target types that the Wasm 1.0 implementation
rejects. [WasmCompletenessBoundary](Itasca/Examples/WasmCompletenessBoundary.lean) contains
a checked witness; [Wasm1Profile](Itasca/Body/Wasm1Profile.lean) requires exact target
type agreement. The generated module rule alone also does not establish export
name uniqueness or the combined imported/defined memory bound.

[Elaboration](Itasca/Module/ModuleElaboration.lean) resolves binary function type
indices, ties function declarations to code entries, and translates names and
segments. [Body context transport](Itasca/Module/BodyContext.lean) connects the body
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
  boundary. Decoder correctness and structured-body/raw-module decoding
  uniqueness against those definitions are proved.
- **Rust library/loop models.** The archived
  [Aeneas_Specs](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Aeneas_Specs.v)
  and [external models](https://github.com/eqrion/itasca/blob/e7a6ce602de0716de89f955300f711b23bc1403e/theories/Itasca_FunsExternal.v)
  supplied domain-specific axioms about library operations and loops. The Lean
  pipeline uses checked Aeneas library proofs and concrete
  [external definitions](Itasca/Generated/FunsExternal.lean) for the missing
  operations. It does not inherit those project axioms; allocation failure
  remains unmodeled.
- **Kernel and axioms.** [`Audit`](Itasca/Audit.lean) checks transitive
  dependencies of every declaration originating in an imported Itasca module,
  including private helpers and adapters in other namespaces.
  Only `propext`, `Classical.choice`, and `Quot.sound` are allowed; `sorryAx` and
  domain-specific axioms are rejected. Import-coverage checks include new proof
  modules. This is a different trusted foundation from Rocq, so raw assumption
  counts are not comparable. The archived [trust report](baseline/rocq-trust.txt)
  and [revision pins](baseline/revisions.json) preserve the baseline evidence.

The streaming consolidation does not add trusted axioms or change these trust
boundaries. The remaining general exclusions are execution semantics, allocation
failure, and a complete classification of which error every malformed input returns.
Specific negative examples and body rejection-trace properties do not claim
that last classification. Neither a full build nor passing Rust/specification
tests proves equivalence between WasmCert, SpecTec, and the prose WebAssembly
specification. The [validation record](baseline/VALIDATION.md) records the
migration checks separately from this theorem comparison.
