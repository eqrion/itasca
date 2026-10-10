# Streaming verification and validation core consolidation

Prove the actual extracted streaming validator, make the ordinary whole-module
API a synchronous wrapper over it, and remove the legacy module/code-section
drivers. The final implementation and proof hierarchy must share one module
orchestrator and the existing environment, entry, body, and tail validation core.

Completed on 2026-10-10. The streaming driver and concrete slice adapter now
have soundness, totality, completeness, and exact metadata proofs. The public
whole-module API delegates to that driver, and duplicate orchestration is removed.
Final `just verify` passed (2,004 integrated Lean jobs; 7,829 audited theorem
declarations), with no trust-base change. The verification record below tracks
the implementation; the design and original snapshot are retained for context.

## Decisions and scope

The user wants one validation core, with SpiderMonkey expected to use the
streaming interface. The agreed direction is:

- Prove streaming soundness, totality, and completeness before switching the
  ordinary whole-module entry point.
- Keep `validate_streaming` as the sole module driver. Make `validate_module`
  its synchronous contiguous-buffer wrapper.
- Retire `validate_module_with` and the legacy `CodeVisitor` code-section walk.
  Do not preserve those APIs merely to preserve their old proofs.
- Keep component validation and the custom-section/opcode visitors they use.
  Convenience functions may supply empty visitors to the same core.
- Preserve the existing ordinary whole-module theorem statements, independent
  specification, implementation limits, exact metadata guarantees, and trust
  discipline.
- Compose semantic certificates directly. Do not base the streaming proof on
  replaying the old driver or on assuming that workers already validated all
  submitted functions.

The implementation review found no necessary runtime simplification before
proof work. Preserve the two batch cursors, sticky errors, bounded pending-ID
vector, current batching policy, and extraction-motivated helper boundaries.
If proof development uncovers an actual defect, fix it with the corresponding
extraction and regression checks rather than weakening the specification.

Actual thread scheduling, compiler IR correctness, network progress, and FFI
memory safety are outside this proof task. Keep their embedding obligations
explicit. Updating an external Firefox checkout is not part of this handoff.

## Repository snapshot

Snapshot taken on 2026-10-10:

- Repository: `/Users/ryanhunt/src/itasca`.
- Branch: `lean-port`.
- HEAD: `04a6cb73f754dfc13d2b550b68d903c2534ec283`.
- Before this handoff was written, `DEVELOPMENT.md` contained uncommitted design
  changes from this conversation. This handoff moves the detailed plan here and
  leaves a summary/link there.
- `patches/UPSTREAM_REPORTS.md` was already untracked and is unrelated. Preserve
  it; do not assume it is disposable or include it in this work accidentally.
- No Rust implementation, generated extraction, or Lean proof was changed by
  the planning work.

The review ran `cargo test --test stream` and
`cargo test --no-default-features --test stream`; all 13 streaming tests passed
in each configuration, including the specification corpus comparison. These
are review results, not a fresh full-project proof/build baseline. Documentation
links and whitespace were also checked. Reinspect the working tree and establish
current build status when resuming; do not assume this snapshot is still exact.

## Read before editing

Read [AGENTS.md](AGENTS.md), [DEVELOPMENT.md](DEVELOPMENT.md), the
[public guarantees and trust base](README.md#formal-verification), and
[Lean verification guide](lean/README.md). Consult [UPSTREAM.md](UPSTREAM.md)
for local toolchain patches and [lean/PARITY.md](lean/PARITY.md) for the archived
Rocq comparison. The active task has no Rocq build requirement.

Inspect these source groups before choosing the first proof edit:

| Source | Why it matters |
| --- | --- |
| [src/stream.rs](src/stream.rs) | The actual driver, batch operations, source trait, slice splitter, and synchronous visitor. |
| [src/module.rs](src/module.rs), [src/code.rs](src/code.rs), [src/limits.rs](src/limits.rs) | Shared components, legacy APIs to retire, body callbacks, and enforced bounds. |
| [Generated Types](lean/Itasca/Generated/Types.lean), [Generated Funs](lean/Itasca/Generated/Funs.lean) | Exact extracted signatures, callback records, loop states, and returned environment/visitor values. Read only; regenerate after Rust edits. |
| `ModuleRegions` (retired), [ModuleSoundness](lean/Itasca/ModuleSoundness.lean), [ModuleCompleteness](lean/Itasca/ModuleCompleteness.lean) | Existing public certificate, semantic assembly, and independent completeness premises. |
| [ModuleDecomposed](lean/Itasca/ModuleDecomposed.lean), [ModuleEntryVisitor](lean/Itasca/ModuleEntryVisitor.lean), [ModuleCodeEntryComplete](lean/Itasca/ModuleCodeEntryComplete.lean) | Environment-derived entry conditions, visitor erasure, and entry completeness. |
| `ModuleCodeSection` (retired), `ModuleCodeEntries` (retired), `ModuleCode` (retired), [ModuleLayout](lean/Itasca/ModuleLayout.lean) | Reusable framing/typing/layout facts currently mixed with legacy driver proofs. |
| [ModuleCustomVisitor](lean/Itasca/ModuleCustomVisitor.lean), [ModuleCustomObservation](lean/Itasca/ModuleCustomObservation.lean) | Custom-hook erasure and preserving observations through environment/tail callbacks. |
| [tests/stream.rs](tests/stream.rs), [tests/wasm_tests.rs](tests/wasm_tests.rs) | Current protocol regressions and legacy API callers to migrate. |
| [Audit](lean/Itasca/Audit.lean), [audit coverage checker](lean/scripts/check_audit.py) | Import coverage and transitive axiom checks. |

## Target API hierarchy

The intended endpoint is one module driver, `validate_streaming`, with
`validate_module(bytes)` as its synchronous convenience wrapper. The current
`validate_module_slice` implementation becomes the internal slice adapter;
there is no need for two public names for the same convenience operation.

```text
validate_module(bytes)
  -> slice adapter + SyncVisitor
     -> validate_streaming(source, StreamingVisitor, environment storage)
        -> validate_env_with(ModuleVisitor)
        -> code framing, batch submission, and retirement
           -> CodeBatch::validate_func(OpVisitor)
              -> validate_code_entry_with(OpVisitor)
                 -> validate_body_with(OpVisitor)
        -> validate_tail_with(ModuleVisitor)
```

The recommendation is to remove the old `validate_module_with`, rather than
retain its `ModuleVisitor + CodeVisitor` contract. Streaming consumers, including
the intended SpiderMonkey integration, use `StreamingVisitor`; synchronous
callers use `validate_module`. If a contiguous-buffer convenience API with a
`StreamingVisitor` is needed later, it must be a thin adapter over that same
driver and preserve its storage, module-identity, and worker-lifetime contract.
It cannot simply keep the old `(&[u8], &mut visitor) -> Module` shape: an arbitrary
visitor can retain batches borrowing the environment, including after errors.
The current synchronous adapter can own the environment locally because its
private visitor never leaves workers holding those borrows.

Remove the parallel legacy orchestration too: `validate_code_with`,
`validate_code_entries_with`, `validate_code`, and `CodeVisitor` /
`ValidatingCodeVisitor`. Once their callers are migrated, retire the legacy
`code_section` reader and its unused Rust types/helpers. Keep framing primitives
used by the streaming driver. Hiding the old walk would leave a second
implementation to maintain and prove, so it is not the target architecture.

Keep `ModuleVisitor` as the shared custom-section hook for the environment and
tail parsers, and keep `OpVisitor` for entry/body validation. The streaming
driver and workers call those same component implementations. Non-visiting
environment, tail, entry, and body functions may remain as wrappers supplying
empty visitors; their public visibility is independent of having one core
implementation. Calling such a component alone does not certify a whole module
or discharge an outstanding batch; workers advance the batch through
`CodeBatch::validate_func`.

Only after the slice soundness, totality, and completeness proofs land should
`validate_module` switch implementations. Preserve its public theorem statements
and metadata guarantees as corollaries of the slice adapter. Migrate tests and
examples, then remove the retired APIs and proofs specific to their execution.
Retain reusable body, entry, custom-section, encoding, and typing facts. Replace
legacy deferred-code and module-trace contracts with batch-provenance and
streaming-protocol contracts as needed; the old callback order and byte-request
trace are not compatibility requirements for a removed API. Update the public
guarantee tables and audit imports to reflect that change explicitly.

The existing Rust callers of `validate_module_with` found in this repository
are tests, including the temporary differential oracle in `tests/stream.rs`.
Keep that comparison until cutover. Afterwards, remove or replace it so tests
do not compare two wrappers around the same driver and call that differential
coverage. Retain corpus expectations and the independent wasmparser fuzz oracle.
External consumers need to migrate separately; this repository search does not
establish that no external caller uses the legacy APIs.

## Proof architecture

This is a design for new proofs, not a statement that they already exist.
The implementation review found no necessary runtime refactor. Keep the
independent dispatch and validation cursors, sticky error, bounded pending-ID
vector, and extracted helper boundaries. In particular, preserve the
`validate_remaining` lifetime boundary and separate retirement loop: they
already solve extraction constraints.

The main simplification is to assemble semantic certificates directly with
[`ModuleSound.assembled_regions`](lean/Itasca/ModuleSoundness.lean). Do not first
prove that the streaming execution replays the old `validate_code_with` loop.
That would introduce unnecessary equivalence proofs between different buffer
offsets, framing reads, and callback schedules. The new proof should survive
removal of the old whole-module orchestration.

## Public statements and assumptions

Keep soundness, totality, and completeness separate:

| Proposed statement | Premises and conclusion |
| --- | --- |
| `stream.validate_streaming.wasm_sound` | An actual accepted extracted run, a coherent source, and batch provenance imply `ModuleSound.Validated` for the concatenated regions, the actual output environment, and the actual tail passed to `tail_ready`. No premise says that all entries have already validated, and no termination premise concerns unexecuted callbacks. |
| `stream.validate_streaming.wasm_total` | Returning source/visitor callbacks imply an ordinary success/error result on arbitrary bytes. Returning unfinished, foreign, or otherwise malformed batch records need not satisfy provenance: retirement only compares IDs, searches the pending vector, and checks `finish`. This theorem does not certify acceptance. |
| `stream.validate_streaming.wasm_complete` | Independent module encoding within the existing limits, elaboration, generated typing, the Wasm 1.0 profile, the prescribed source split, available reads, and an accepting worker/scheduler policy imply acceptance. |
| `stream.validate_module_slice.wasm_total`, `.wasm_sound`, `.wasm_complete` | Discharge the source and scheduler premises for `SliceSource` and `SyncVisitor`. Expose the same byte/typing/limit premises and `ModuleSound.Validated` conclusion as the existing whole-module API. |

The generic API returns `()` and the updated environment, not a `Tail`.
Its soundness proof must retain the decoded tail as a witness of the actual
`tail_ready` call. Do not assume an arbitrary visitor stores that tail in its
final state. The slice adapter proves that its concrete visitor does store it
and returns exactly that environment/tail pair.

Define source coherence against fixed logical byte lists `E`, `C`, and `T`:
successful environment/tail reads equal `E`/`T`, the reported code length is
`C.length`, and each successful in-range code read equals the corresponding
slice of `C`. Soundness allows ordinary read errors and does not assume valid
bytes or a canonical split. Availability and canonical splitting belong to
completeness. Returning callbacks belong to totality. The successful driver's
`add_offset` checks establish the size bound on `E ++ C ++ T`.

## Batch provenance and validation

Use proof-only definitions for an immutable issued descriptor and batch
reachability. The descriptor fixes module ID, batch ID, environment, bytes,
code offset, first function, and function count. It records exactly the batch
constructed by `submit_code_batches`, including zeroed cursors and no error.
`BatchReachable issued current` is the finite closure of actual extracted
`next_entry` and `validate_func` calls, with arbitrary opcode visitors and
ordinary success or error results. Read-only accessors preserve it;
`validate_all` must be proved to produce such a path. No constructor may set
validation counters directly or assume that `finish` succeeds.

Prove the following invariant by induction over reachability:

- Immutable fields still equal the issued descriptor. Both cursor counts are
  bounded by `num_funcs`; their byte offsets are within the batch bytes.
- The validation prefix is a chain of successful default
  `module.validate_code_entry` executions from byte zero, for exactly
  `first_func .. first_func + num_validated`. Derive each link using
  [`validate_code_entry_with.accepted_erase`](lean/Itasca/ModuleEntryVisitor.lean).
- Dispatch operations preserve that chain. Validation does not require prior
  dispatch. Keep dispatch framing facts separate from validation evidence.
- Once an error is stored, every later `validate_func` returns that same error
  without extending the validated prefix. A rejected extra validation after
  the last function therefore poisons the batch too.

From reachability and successful `finish`, derive exact byte consumption and
exactly `num_funcs` successful entry validations. Then apply
[`ModuleDecomposed`](lean/Itasca/ModuleDecomposed.lean) and
``ModuleCodeEntries`` (retired) to obtain a batch-local
`Rep CodeEncoding` and `EntriesTyped env first_func`. Environment bounds and
result arities come from the driver's actual environment decode.

The scheduler contract must connect the extracted visitor state to issued
descriptors; Rust private fields are public record fields in Lean. Use a
relation such as `Tracks module_id issued visitorState`. Submission extends
the history with the exact seed. A returned batch whose IDs match an issued
batch of this invocation must be reachable from that seed. Every intervening
callback preserves the relation, including `code_end`, `custom_region`, tail
custom-section hooks, and `tail_ready`. Callback implementations may advance
workers during any of these calls.

For soundness, do not require the returned batch to be finished, or require
that every submitted batch will eventually be returned. The driver checks
these conditions on a successful run. Keep the issued history after retirement
so this contract can even allow replay of a legitimately derived batch;
the runtime pending-ID check must prove duplicate rejection. Unknown or foreign
IDs may also be returned and rejected. Fresh module IDs justify the initial
provenance relation when a real scheduler can hold older invocations' batches.
No assumption about a scheduler already validating every function replaces
this relation.

## Framing, submission, and retirement

Prove `read_len` from the existing LEB reader contracts, and `read_exact` from
its length check plus source coherence. Add reusable byte-span transport
lemmas between a batch slice, its code region, and the concatenated module.
Transport independent encodings, rather than whole validator executions.

For `read_code_header`, establish either absent code with no defined functions,
or a `ModuleCode.Section` over the logical code region whose end is exactly
`C.length`. Include nonminimal LEBs and the distinction between an absent
section and a present zero-entry section. A five-byte LEB is enough for an
entry prefix, and eleven bytes for the code header; prove the bounded-view
facts once, without requiring the entire code region to have arrived.

For `get_next_batch`, prove progress and contiguous framing under its actual
call-site preconditions: `first_func < num_funcs`, `start <= code_len`, and
the driver-established module bound. Successful output advances the function
index by at least one and frames that many consecutive entries. Its byte
budget counts the declared entry contents, including locals but excluding
size prefixes. It is not `MAX_FUNCTION_BYTES`, which excludes locals.
Retain the present batching policy; changing to a threshold check only after
adding the next entry changes batch grouping and is unnecessary for the proof.

Use the following ghost state for `submit_code_batches` and retirement:

- An ordered list of issued descriptors partitions the code-entry prefix in
  both byte order and defined-function order. Its length is the next batch ID;
  its final boundaries are the loop's `pos` and `func`.
- `pending` has distinct IDs, all issued. Retired IDs and pending IDs partition
  issued IDs. Every successfully retired ID has a complete batch certificate.
- The visitor satisfies `Tracks` for the issued history. The actual pending
  vector has length at most `max_batches`; no per-function runtime ledger is
  introduced.

Prove the pending search and swap-with-last/pop operation as a small list
lemma: on success it removes exactly the matching ID and preserves all other
members and distinctness. Retirement combines that fact, provenance, and
`finish` soundness. The implementation removes the ID before `finish`; maintain
the retired-certificate invariant on successful helper returns only. On error
the driver exits, so there is no need to rearrange those Rust statements or
pretend the failed batch acquired a certificate.

Submission success establishes `func = num_funcs` and `pos = code_len`.
Final draining establishes an empty pending vector. Assemble certificates in
submission order, regardless of return order, concatenate their independent
entry encodings, and use `EntriesTyped` to obtain the function/type pairing.
Combine this with the checked header through `ModuleCode.Section.encoding`
and the padded encoding required by `assembled_regions`.

For totality, prove the arithmetic and decreasing measures explicitly:
`num_funcs - func` for framing/submission, remaining pending length for
draining, remaining search length for retirement, and remaining validation
count (with the stopping flag) for `validate_all`. The framing loop maintains
`batch_bytes <= pos - start`; a continuing nonfirst iteration additionally has
`batch_bytes < threshold`, justifying subtraction even for extreme configs.
The module cap gives room for `pos + MAX_LEB_BYTES`. Each nonempty batch
advances a function, bounding batch IDs and vector growth. Zero-length entry
contents still consume a nonempty size prefix. Do not add implementation caps
just to make these arithmetic proofs easier.

## Composition, completeness, and the concrete adapter

Erase custom callbacks using
[`ModuleCustomVisitor`](lean/Itasca/ModuleCustomVisitor.lean), recover the
environment and tail semantic certificates, and apply `assembled_regions` to
the completed code certificate. This gives encoding, generated `Module_ok`,
the Wasm 1.0 profile, cache/index correspondence, and public metadata together.
Preserve the scheduler relation through custom callbacks with a separate
state-preservation lemma; acceptance erasure alone does not preserve ghost
work observations.

Completeness starts with the same independent premises as
[`ModuleCompleteness`](lean/Itasca/ModuleCompleteness.lean). Reuse
`ModuleLayout.normalize`, environment completeness, typed-entry completeness,
and tail completeness on the appropriate region slices. Show every framed
batch of a valid module can validate its next function repeatedly using
accepting opcode hooks. An accepting scheduler policy returns an outstanding
batch after those calls, accepts other hooks, and chooses positive config
values. State this as an operational worker policy and prove its successful
completion from entry completeness; do not assume successful completion as
the evidence of module validity. Reordering requires no additional typing
argument because each batch has its own fixed environment and interval.

For `find_code_region`, first prove arbitrary-byte termination and
`0 <= code_start <= code_end <= bytes.length`, including inputs shorter than
eight bytes and malformed/truncated section lengths. The three resulting
slices always concatenate to the input, which suffices for slice soundness.
Only completeness requires proving that its split matches the normalized
layout of a valid module. Its scan precedes the module-size guard, so its
totality proof must work for arbitrary slice lengths.

For `SyncVisitor`, prove that submission uses `validate_all` and preserves batch
provenance, polling returns and clears the stored batch, and tail delivery
stores the exact tail. The driver invariant with `max_batches = 1` ensures
`completed` is empty before every submission, so assignment cannot discard an
outstanding batch. This concrete contract removes scheduler/fresh-ID premises
from `validate_module_slice`; the constant ID is internal to a fresh visitor.

## Contract details to settle in Lean

Use the actual extracted functions as the subject of every execution theorem.
A relation describing a run is a proof witness for those functions, not a new
executable validator whose correctness substitutes for theirs. Distinguish
Aeneas's outer result, which includes modeled failure/divergence, from Rust's
inner `Ok`/`Err`: totality must produce an ordinary outer success containing
either Rust result, not merely characterize the accepting case.

Separate the contracts rather than building one oversized predicate:

| Contract | Required content |
| --- | --- |
| Source coherence | Successful views agree with fixed `E`, `C`, `T`; successful code-length results equal `C.length`. It does not require successful reads. |
| Source availability | The reads needed for completeness return the prescribed bytes. Actual blocking/network progress remains an embedding assumption. |
| Callback totality | Callbacks reached by the driver return ordinary modeled results. This permits Rust errors and rejected batches. |
| Batch provenance | A batch with an issued identity is reachable from that exact seed by batch methods; validation success is derived separately. |
| Accepting scheduler policy | Positive configuration, accepting administrative/custom hooks, and legal next-function validation using accepting opcode hooks before returning an outstanding batch. Derive completion from entry completeness. |

For batch seeds, retain explicit arithmetic bounds:
`first_func + num_funcs <= env.func_type_indices.len()`, positive `num_funcs`
for every actually submitted batch, and
`code_offset + code.len() <= code_len <= MAX_MODULE_BYTES`.
Reachability alone from an arbitrary hand-built Lean record does not establish
these facts. Prove them at construction and preserve them through batch calls.
Accessor and batch-operation totality should be stated for such legitimate
states, rather than for every possible extracted record.

A scheduler relation such as `Tracks module_id issued v` can use an immutable
history indexed by batch ID. Its successful submission rule extends the history
with the exact argument before accounting for any work performed during the
callback. Its successful polling rule preserves history and supplies reachability
when the returned identity matches a historical seed. Other callbacks preserve
history while allowing worker progress. The driver, not the contract, checks
whether that identity is still pending and whether the returned state is finished.

Keep proofs on successful driver/helper paths distinct from error-state
invariants. For example, retirement removes an ID before inspecting `finish`;
there is no complete certificate for that removal if `finish` rejects. No later
acceptance path follows that error. The API also does not join all workers on
error, and its totality theorem must not imply that it does.

Generic soundness needs a witness identifying the actual decoded tail and the
actual `tail_ready` invocation. An accepted-run relation or a preservation proof
carrying that witness is appropriate. An existentially chosen unrelated tail,
or a predicate on final visitor state that arbitrary callbacks may erase, is
not a replacement for that link.

The source coherence wording in `DEVELOPMENT.md` was corrected during review.
The older rustdoc in `src/stream.rs` still says Rust borrows enforce the regional
byte-view condition. During the Rust migration, clarify that borrows protect an
individual immutable view; they do not force different calls to return coherent
ranges. Keep this assumption visible in the generic theorem and discharge it
for `SliceSource`.

## Implementation milestones

Complete these in order, retaining a buildable audited checkpoint at each
milestone. Names below are suggestions; choose module boundaries around actual
imports and proof reuse. Record finished theorem names, commands, and remaining
work in this document as implementation proceeds.

### Milestone 0 Establish the baseline

- Inspect `git status` and preserve existing changes.
- Read the instructions and source map above. Confirm that extraction still
  matches the implementation before diagnosing proof problems against it.
- Run `just prove` for the existing baseline. Run `just extract-check` when
  establishing extraction consistency; keep regeneration output in its normal
  ignored build directories.
- If a baseline check fails, record the failure and determine whether it is
  pre-existing, environmental, or introduced by local changes before proceeding.

Exit criterion: current baseline status and working-tree ownership are known.
No dependency or build caches have been deleted.

### Milestone 1 Separate semantic foundations from the old driver

This is the first implementation task. The import direction matters:

- `ModuleRegions` currently imports `ModuleValidation`.
- `ModuleSoundness` currently imports `ModulePipeline` and `ModuleCode`.
- `ModuleDecomposed` currently imports `ModuleRegions` to obtain facts that can
  instead be derived from environment and entry component theorems.
- `ModuleCodeSection`, `ModuleCodeEntries`, and `ModuleCode` mix independent
  extent/section/entry-typing/encoding facts with legacy execution theorems.
- `ModuleLayout` imports `ModuleCodeComplete` and contains `CodeAt.complete`;
  `ModuleCodeTypedComplete` mixes typing facts with old code-driver completeness.

Move `ModuleSound.Validated` and `assembled_regions` into driver-independent
foundations. Preserve their names when practical so existing consumers only
need import changes. Move semantic `Extent`, `EntriesTyped`, ordered encoding
composition, and environment-derived entry conditions similarly. Separate
layout normalization and typed-code facts from theorems that execute the old
code walk. Keep legacy execution proofs importing these foundations until
cutover, so this milestone changes proof organization without deleting APIs.

`ModuleCode.Section` currently mentions the generated `module.CodeSection`
Rust type. That type may disappear with the old reader. Make the retained
semantic section predicate use explicit header/count/end fields or a handwritten
semantic record, and adapt the old proofs temporarily. Do not retain a dead
Rust API solely to keep a semantic predicate's argument type alive.

Exit criterion: the assembly, batch-entry, and layout facts needed by streaming
can be imported without the old whole-module execution proofs. Existing proofs
and audit still pass. This prevents a cycle when the old public theorem names
later become corollaries of streaming.

### Milestone 2 Source views and framing

Suggested modules: `StreamSource`, `StreamFraming`.

Implement source predicates, successful-read contracts, ordinary-return
contracts, and byte-span transport. Prove the extracted `read_len`, `read_exact`,
`read_code_header`, `frame_entry`, and `get_next_batch` results and progress.
Use a semantic header witness compatible with the foundations from milestone 1.
Do not equate a successful frame with a valid function body.

Exit criterion: successful framing has exact range and function-count evidence;
helper totality and arithmetic work under driver-established bounds; malformed
input and ordinary source errors remain covered.

### Milestone 3 Batch operations

Suggested module: `StreamBatch`.

Define legitimate seed descriptors, actual-operation reachability, and the
validated-prefix chain. Prove preservation for `next_entry`, `validate_next`,
`validate_func`, and accessors as relevant; prove sticky errors and independence
of dispatch from validation. Prove `validate_all` terminates, is reachable,
and completes a valid batch using the existing entry completeness theorem.
Prove successful `finish` yields exact ordered batch typing and byte coverage.

Exit criterion: a reachable batch cannot finish successfully without validation
of every one of its entries, while arbitrary opcode visitors are permitted in
acceptance soundness. Accepting/returning visitors are separate hypotheses for
completeness/totality.

### Milestone 4 Scheduler and driver

Suggested modules: `StreamScheduler`, `StreamDriver`, `StreamValidation`.

Define the visitor-state/history relation and contracts for every callback.
Prove pending-vector search/removal, retirement, bounded submission, complete
partitioning, and final draining. Carry the relation through code-end and tail
processing, not only submit/poll calls. Assemble accepted batch certificates in
issuance order and apply the semantic region theorem.

Prove generic `validate_streaming.wasm_sound` and `.wasm_total`. For totality,
keep batch provenance unnecessary when returned records are only inspected by
retirement; a returning callback can hand back malformed records that the driver
rejects or inspects without arithmetic. Do not inadvertently claim totality for
worker code unless its callback-return premise has been discharged.

Exit criterion: actual driver acceptance establishes the full module certificate
under explicit source/provenance assumptions. The ordinary-return theorem
covers arbitrary bytes under returning callback assumptions. Tail metadata is
tied to the actual handoff, and no hypothesis prevalidates all submitted bodies.

### Milestone 5 Independent completeness

Suggested module: `StreamComplete`.

Start from `ModuleEncodingWithinLimits`, `Elaborates`, generated `Module_ok`,
and `Profile`, as in the existing ordinary module completeness theorem.
Derive the decoded environment, exact region encodings, valid framed batches,
and tail data. Prove the accepting worker policy succeeds by entry completeness
and reaches successful retirement for arbitrary permitted batch sizes and
return orders. Treat absent code and explicit zero-entry code separately.

Exit criterion: the generic completeness theorem exposes independent
encoding/typing/profile/limit premises plus source and callback policy
obligations; it exposes no assumed parser acceptance, fabricated environment
cache, or successful body-validation premises.

### Milestone 6 Concrete slice adapter

Suggested module: `StreamSlice`.

Prove splitter totality/bounds on arbitrary inputs and canonical splitting for
valid encodings. Prove `SliceSource` coherence, availability, and totality.
Discharge the scheduler contracts for `SyncVisitor`, including its one-slot
invariant, validation on submission, clearing on polling, and exact tail storage.
Then prove `validate_module_slice.wasm_sound`, `.wasm_total`, and `.wasm_complete`,
including metadata correspondence matching the ordinary API's guarantees.

Exit criterion: the actual contiguous entry point has the required public
contracts with no source-coherence, module-freshness, or scheduler assumptions
left for its callers. This is the gate before changing `validate_module`.

### Milestone 7 Cut over and remove duplicate orchestration

1. Implement `validate_module` through the proved slice adapter and make the
   adapter internal if no separate public use remains. Keep it extracted.
2. Rewrite the existing ordinary module soundness/totality/completeness/spec
   theorems as corollaries; preserve metadata variants and their semantics.
3. Migrate callers/tests off `validate_module_with` and `CodeVisitor`. Remove
   the legacy whole-module and code-section drivers, traits, and unused helpers.
4. Regenerate extraction after the Rust change. Update or remove Lean execution
   proofs whose subjects disappeared, preserving reusable facts from milestone 1.
   Regeneration and proof updates may need to be one coherent change because
   removed generated names otherwise leave imports uncompilable.
5. Update audit imports and explicit adapter checks; do not leave orphan proof
   modules merely to retain old theorem counts.
6. Update README, crate rustdoc, Lean guide, development notes, examples, and
   guarantee tables. Clearly describe removed API contracts and newly proved
   streaming guarantees. Fix the source-coherence rustdoc wording.

Exit criterion: production Rust has one module driver and one set of component
validators; all retained proof modules compile and are audited against the new
extraction. No exported ordinary module guarantee was weakened to make cutover
possible. External Firefox migration, if needed, is reported separately.

### Milestone 8 Regressions and final integration

Suggested module: `StreamExamples`, added incrementally during earlier milestones.

Add kernel-checked examples for source/batch/driver contracts and meaningful
runtime regressions where existing coverage is missing. After cutover, replace
comparisons against wrappers around the same driver with corpus expectations,
protocol assertions, and the independent wasmparser fuzz oracle. Preserve
existing independent body/entry trace results.

A full new streaming callback trace theorem is a separate layer if needed.
At minimum retain the actual phase/issuance/tail witnesses necessary for
soundness, and test the exposed callback behavior. Do not claim the old
`validate_module_with` callback-order or readiness-trace theorem automatically
applies to the new protocol.

Exit criterion: required checks pass, public docs match proved guarantees, and
the final report identifies API removals, theorem coverage, remaining embedding
obligations, and any trust-base change.

## Regression matrix

Prioritize cases that exercise a contract boundary rather than merely mirror
the implementation. Many have Rust coverage already; inspect before adding.

| Boundary | Cases and expected property |
| --- | --- |
| Regions | Empty module; missing code with defined functions; explicit empty code; noncanonical/misplaced splits; extra code bytes; invalid or truncated tail. Accepted concatenations must still encode a whole valid module. |
| Framing | Nonminimal valid LEBs; truncated/oversized prefixes; zero-length entry contents; counts shorter or longer than the region; header reads of at most eleven bytes and entry-prefix reads of at most five. |
| Batching | Several functions per batch; a single entry above the target; exact target; target one; large positive config values; zero config rejection; bounded out-of-order completion. |
| Validation | Validation without dispatch; partial dispatch; wrong index; repeated validation; missing final validation; invalid opcode; rejecting compiler hook; sticky first error. |
| Identity | Foreign invocation; historical replay; unknown batch ID; correctly finished batch with matching issued identity. Duplicate rejection must follow from pending membership, not a contract forbidding duplicates. |
| Tail and callbacks | Outstanding batches survive custom hooks and tail delivery; bad tail rejects even if all functions validate; early errors may leave jobs for the embedding to join. |
| Concrete adapter | No stored batch is overwritten; polling clears it; exact output environment/tail; splitter bounds before the size guard; truncation at every position in selected examples. |
| Proof assumptions | A forged extracted Lean batch demonstrates why provenance is necessary. Incoherent equal-length source views are excluded by coherence, not by Rust borrowing or `read_exact`'s length check. |

A malformed body may frame successfully and be dispatched, then fail worker
validation. This is expected and must not invalidate the framing invariant.
The batch threshold counts declared contents including locals; the function-body
limit counts instruction bytes excluding locals. Keep the two quantities distinct.

## Verification and extraction discipline

Follow [AGENTS.md](AGENTS.md) if its requirements change. At this snapshot:

| Change | Required checks |
| --- | --- |
| Documentation only | Check local links and `git diff --check`. |
| Handwritten Lean proofs or adapters | Focused `just check Itasca.ModuleName` while iterating, then `just prove`. |
| Rust or extraction inputs | `cargo test`, `cargo test --no-default-features`, `just extract`, `just extract-check`, `just prove`. |
| Aeneas source patches or pins | The Rust/extraction checks plus `just regressions`. |
| SpecTec sources, patches, or pins | Regenerate with `make -C lean spec-update`, then `just spec-check` and `just prove`. |

`just verify` runs the complete Rust/regeneration/regression/proof sequence.
`just trust` reruns the transitive axiom report. Run the appropriate required
checks at each integration checkpoint and a final complete verification after
the API cutover. Record failures honestly rather than treating planned checks
as completed checks.

Never hand-edit `lean/Itasca/Generated/Types.lean`, `Funs.lean`, or the generated
SpecTec specification. `FunsExternal.lean` is handwritten, but this task should
not require changes to its standard-library models. Never import the generated
external template. Preserve `lean/.lake/` and `lean/.build/`; use `$TMPDIR` for
scratch proofs outside the source tree.

Do not add axioms, `sorry`, `admit`, `native_decide`, unsafe proof shortcuts,
or kernel bypasses. Audit all new modules transitively and explicitly audit
new public predicates and proof-bearing adapters: source contracts, batch
reachability, scheduler contracts, acceptance witnesses, and concrete adapters.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. No trust-base
extension is planned. Explicit generic theorem hypotheses are not new axioms;
the slice theorem must discharge the source and scheduler hypotheses concretely.

Stay within the documented Rust extraction subset. Avoid introducing iterators,
closures, `.clone()`, bitwise operations, `String`, or new borrowing/indexing
patterns without evaluating extraction and proof impact. In particular, retain
`validate_remaining` and the separate final-retirement helper unless a tested
extraction change demonstrates that their lifetime/loop constraints are solved.

## Implementation verification record

### 2026-10-10: baseline and semantic foundations

- Initial working tree was clean. Preserved dependency/build caches.
- Baseline `just extract-check` passed; generated types/functions match Rust.
- Baseline `just prove` passed (1,982 jobs; 7,329 theorem declarations audited).
- Milestone 1 completed: `ModuleSoundness` now owns both `Validated` and
  `assembled_regions` without legacy driver imports; `ModuleDecomposed` derives
  its prerequisites directly from environment and entry proofs.
- `ModuleCodeSemantic` owns semantic extents, handwritten `Header`/`Section`,
  ordered entry typing and encoding composition; `ModuleCodeFraming` retains
  the shared extent-reader contracts. `ModuleLayout` and `ModuleCodeTyped` are
  independent of old code execution; `ModuleLayoutComplete` holds the legacy
  execution theorem. Existing public theorem names/statements are preserved.
- Focused foundation checks passed. Transitive import inspection confirms that
  `ModuleSoundness`, `ModuleDecomposed`, `ModuleCodeSemantic`, `ModuleLayout`,
  and `ModuleCodeTyped` do not import legacy module/code driver proof modules.
- Integrated `just prove` passed (1,989 jobs; 7,475 theorem declarations),
  including initial `StreamSource`, `StreamFraming`, and `StreamSliceSplit`.
  Explicit semantic/source adapter checks were added. No trust-base change.
- Initial streaming leaves proved: source coherence/availability/callback
  totality; `limits.add_offset.spec/total/complete`; `stream.read_len` and
  `stream.read_exact` contracts; concrete `SliceSource` source contracts;
  byte-span/LEB slice transport; `stream.frame_entry` contracts;
  `stream.find_code_region.spec/total/bounds/slices` on arbitrary bytes.
- The remaining milestones are still in progress. In particular this record
  does not establish streaming driver soundness, totality, or completeness,
  and does not authorize the API cutover before milestone 6 is proved.

### 2026-10-10: streaming proof composition

- Focused checks passed for source/header/batch framing soundness, totality and
  completeness, batch reachability and exact successful-finish certificates,
  actual submission/retirement soundness, and ordered byte/function partitioning.
- `stream.validate_streaming.wasm_total` now proves ordinary return on arbitrary
  bytes under returning callbacks, without source coherence or batch provenance.
- `stream.validate_streaming.wasm_sound` now assembles `ModuleSound.Validated`
  directly from accepted execution, coherent source views and callback provenance.
  It retains `StreamRun.Accepted` with the actual `tail_ready` call and proves the
  concatenated module size bound. No worker-success or unused-callback totality
  premise was introduced.
- `stream.validate_module_slice.wasm_total`, `.wasm_sound` and `.wasm_spec`
  compile. `StreamSync` discharges provenance, callback totality and exact tail
  storage. `StreamSyncComplete.accepts` (declared as `StreamSync.accepts`)
  discharges the accepting policy using its one-slot queue and actual worker run.
- `StreamCompleteRegions.prepare` derives canonical regions, independent bounded
  typed entries, actual regional parsing, `Matches` and `AccessorTypes` from the
  ordinary encoding/elaboration/generated-typing/profile premises.
- Import inspection confirms `StreamValidation`, `StreamSlice`,
  `StreamCompleteRegions` and `StreamSyncComplete` have no legacy module/code
  driver proof dependencies. Generic and slice completeness remain in progress;
  Rust/API cutover has not begun. These focused results await the next integrated
  `just prove` checkpoint.

### 2026-10-10: proof gate and API migration

- Milestones 2–6 passed the integrated gate: `just prove` completed 2,019 jobs
  and audited 8,017 theorem declarations. No nonstandard axiom was introduced.
- Generic completeness is `stream.validate_streaming.wasm_complete`, under
  independent encoding/elaboration/typing/profile premises, canonical available
  reads and `StreamAcceptingScheduler.Accepts`. The policy executes actual
  `validate_all` workers on independently typed bounded seeds and permits
  arbitrary positive configuration and completion order. It is one sufficient
  accepting policy, not a characterization of every worker strategy.
- `stream.validate_module_slice.wasm_complete` and
  `.wasm_complete_with_metadata` discharge all source/scheduler premises, with
  the actual delivered tail retained through concrete final draining.
- Kernel-checked `StreamExamples` cover forged finished records and their
  unreachability, incoherent overlapping views despite successful exact-length
  reads, one-slot polling, replay/foreign rejection, and empty-buffer rejection.
- After the gate, `validate_module` was switched to the internal synchronous
  streaming adapter; duplicate module/code drivers and traits were removed from
  Rust. `just extract` passed, regenerating the committed model normally.
  Public ordinary theorem statements are now slice corollaries. Legacy proof,
  test and documentation migration and final required checks remain in progress.

### 2026-10-10: consolidation and regression migration

- `validate_module` now delegates to the private synchronous streaming adapter.
  Removed the legacy whole-module visitor, code-section walk, their traits and
  header type, and 17 proof modules tied to their execution. Retained independent
  semantic/layout, body, entry, custom-section, and metadata facts.
- Public `wasm_spec`, `wasm_total`, `wasm_sound`, `wasm_complete`, and
  `wasm_complete_with_metadata` statements are unchanged and compile as slice
  corollaries against the regenerated extraction.
- Migrated module/consumer/custom-trace examples compile through the actual new
  driver. The concrete truncated-code-count regression now records streaming's
  `UnexpectedEof` variant rather than the legacy reader-wrapped variant; the
  public acceptance and metadata guarantees are unchanged.
- `cargo test` and `cargo test --no-default-features` passed, including 19 stream
  protocol regressions, 114 module tests, and independent wasmparser corpus and
  metadata checks. Legacy same-driver differential comparisons were replaced
  with independent verdicts, exact fixture bounds and protocol assertions.
- `just extract`, `just extract-check`, `cargo doc --no-deps`, focused migrated
  proof checks, import coverage (289 modules), local documentation
  links, and `git diff --check` passed. Every retained proof module is reachable
  from Audit. Final `just verify` subsequently passed, as recorded below; the trust base is unchanged.

## Completion checklist

- [x] Driver-independent assembly, layout, and entry facts are separated from legacy execution proofs.
- [x] Source/framing proofs cover exact bytes, malformed inputs, and arithmetic bounds.
- [x] Batch reachability derives validation and sticky-error behavior from actual methods.
- [x] Scheduler contracts preserve provenance across every relevant callback.
- [x] Driver soundness proves complete byte/function coverage before acceptance.
- [x] Driver totality covers arbitrary bytes under returning callbacks.
- [x] Driver completeness starts from independent specification premises.
- [x] Concrete slice soundness, totality, completeness, and metadata are proved.
- [x] `validate_module` delegates to the streaming core and retains its public guarantees.
- [x] Legacy module/code-section orchestration and its obsolete proof-only dependencies are removed.
- [x] Tests, examples, public documentation, audit imports, and adapter checks are updated.
- [x] Required verification passes and trust-base status is reported.

## Final verification

- `just verify` passed after the API migration: both Rust test configurations,
  regenerated Rust and specification consistency checks, toolchain regressions,
  and the integrated Lean build and transitive axiom audit.
- The integrated build completed 2,004 jobs and audited 7,829 theorem declarations
  plus explicit semantic, source, batch, scheduler and execution-witness adapters.
  Only `propext`, `Classical.choice`, and `Quot.sound` occur in the allowed trust
  base. No generated model or specification was edited by hand.
- Final documentation clarifies that the batch target counts entry contents,
  including locals; it remains distinct from the instruction-body limit.
  `cargo doc --no-deps`, local documentation file links, and `git diff --check`
  passed. The post-documentation `just extract-check` reconfirms model consistency.
- All milestones are complete. Thread scheduling, network progress, compiler IR,
  FFI memory safety and external Firefox migration remain outside this task,
  as scoped above.
