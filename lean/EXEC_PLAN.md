# Execution proof simplification and merge plan

## Current work: shared validator and compiler proofs

Updated 2026-10-29. The library/extraction merge and
[phase 10](#phase-10-consolidate-files-and-naming) and
[phase 11](#phase-11-share-validator-and-compiler-proofs) are complete: related
proofs are consolidated, validator/compiler reader certificates are shared, and
the guides give concrete reading paths. The execution guarantees are unchanged.
The earlier phases below retain the implementation history and design rationale;
their old `Exec` paths and commands are historical, not current instructions.
Phase 10's scope and checks supersede the historical ground rules for this work.

Phases 1, 2, 3, 5 and 9 landed; phase 4's bundles landed, while output/API
redesign is deferred. Phase 6 was abandoned for a semantic reason: compiled code
does not uniquely determine its source. Phase 7's organization work is folded
into phase 10; replacing the abstract transition system is deferred. Phase 8 is
only triggered by measured build problems. Phase 11 follows the merge and
shares reader proofs while preserving the public contracts.

Goal: a manageable proof base for the runtime, then one unified library.
First simplify what the execution theorems claim and delete the machinery
only the removed claims need. Then merge `Exec/` into `Itasca/` as
`Itasca.Runtime`, mirroring `src/runtime`, with one extraction and one build
target. Interpreter performance work waits until this plan is done.

Work happens on the `interp` branch in the main checkout.

## Starting point

The previous plan (same file, 2026-10-23/24) finished its phases 0 to 6 and
most of phase 8: measurement tools (`just exec-stats`, `just dead`), the
`Main`/`Contracts`/`Results` layout, dead-proof removal, the fragment and
emission towers, one code relation, profile-generic reader proofs (Wasm 1.0
runs the Wasm 2.0 reader plus filters), flat dispatch heads, and the `Instr`
matcher-equation fix. Commits `5e4fdd9`..`759c368`.

After `759c368`: 3,264 handwritten files / 251,673 lines; 8,808 theorems /
1,919 definitions; olean 1.57 GiB, 11 > 10 MiB; `maxHeartbeats` /
`maxRecDepth` overrides 279 / 316.

Size by area (2026-10-28, lines including generated code): `Code` ~90k
(`Body/Reader` 27k in 378 files), `Interp` ~65k, `Theorems` ~30k
(`Host/Open` 10.6k), `Store` ~30k, `Abs` + `Spec` ~30k, `Generated` ~51k.

## Findings behind this plan (2026-10-28)

Paths are relative to `lean/Exec` unless noted.

Why the proofs are large:

- Soundness and chosen completeness are proved per instruction family, twice:
  `Theorems/Composition/Supported/Supported{Scalar,Drop,Read,Simd,...}Execution`
  vs `...ChosenExecution`, `Abs/Sim/{Basic,Call,...}` vs `Chosen{Basic,Call,...}`,
  plus `Interp/StructuredMachine/*Chosen*`, `Theorems/Api/*Chosen*`,
  `Theorems/Host/Chosen`, `Theorems/Host/Open/Source/Chosen`. 253 files
  mention `SourceChoices`/`ChoiceStep`/`ChosenSteps`; `Spec/Choices` has 74.
- Composition layers were grown by widening (Core → Supported → Stateful →
  Uniform → Eventful → World → Executable) instead of being replaced, so they
  stay reachable and `just dead` does not flag them.
- Public statements repeat seven platform/host premises; `sound`,
  `recorded_sound` and `recorder_sound` say nearly the same thing
  (`ExecutableWorldInvocationOutcome` vs `ExecutableWorldRecordedOutcome` in
  `Theorems/Invocation/ExecutableWorldOutcomes.lean`).

Why errors need resource causes (phase 1):

- `EventfulInvocationError` (`Theorems/Composition/Eventful/EventfulErrors.lean`)
  justifies `Exhausted`/`Terminated` by any reachable source configuration, so
  a runtime that always returned `Exhausted` would satisfy plain soundness.
- The resource causes close this: `WorldDefinedSourceResourceCause`
  (`Theorems/Invocation/InvokeWorldResources.lean`),
  `InitialHostSourceResourceCause`
  (`Theorems/Invocation/PublicEventfulSourceResources.lean`),
  `ExecutableWorldInvocationSourceCause`
  (`Theorems/Invocation/ExecutableWorldSourceCause.lean`). Each cause is a real
  limit excess, an allocator refusal, a callback stack overflow, or an
  interrupt `Terminate`.
- The limits are `StoreLimits.max_frames` (default 1024, call depth) and
  `max_values` (default 1,000,000, 64-bit slots; `v128` takes two) in
  `src/runtime/store.rs`. Frames reserve locals plus static peak operand
  height at entry. Source-side demand is `SourceCanonicalFunctionCapacity`
  (`Interp/Relations/SourceCanonicalCapacity.lean`), defined on source code
  only, with a proved bound on the compiled `slot_count`.
- **The predicate phase 1 needs lives in a chosen file.** `SourceWorldResources`
  and `EventfulSourceResourceCause.excludes_boundary` are in
  `Theorems/Composition/World/ChosenWorldResourceBounds.lean`; move them out
  before deleting chosen files. `Theorems/Api/InitialHostResourcesAdequate.lean`
  also uses `SourceWorldResources`.

Why exact recording stays (phase 3):

- `StepH.host_return` (`SpecExt/Host.lean`) accepts any well-typed reply and
  any store extension. With `∃ events`, the source run could invent host
  replies, so soundness would not constrain which host calls the runtime made.
  Recording fixes the events to the actual calls, arguments and replies.
- Mechanism: `recordedInvokeWith` (`Interp/Invocation/InvokeRecording.lean`)
  is a hand copy of extracted `invoke_with` that logs events, plus an erasure
  proof. ~93 files / ~9k lines mention recording, mostly threading events,
  which any mechanism needs. A wrapper platform (`P × List HostEvent`) still
  needs one erasure lemma; it is not free.

Why the host driver can go (phase 2):

- Reentrancy is already covered when a callback returns: the host call is one
  atomic source step, and an inner `invoke_with` is covered by applying the
  theorem again.
- The driver (`Theorems/Host/Open`, `OpenReentrantControl`, callbacks as Lean
  `Selector` programs) exists for callbacks that never return (JS calling a
  looping Wasm function) and as a satisfiability witness
  (`returning_package`). It does not verify real Rust/C++ callbacks.
- The gap it covered is `HostWorldSound`'s requirement that every callback
  returns normally; phase 2 removes that requirement instead.

What `Abs` is (phase 7):

- `Abs.AState` (`Abs/State.lean`) is a flat frame/label/value-stack view over
  spec values; `Abs.decode` (`Abs/Decode.lean`) rebuilds SpecTec's nested
  `LABEL_`/`FRAME_` term. Proofs go interpreter → `Abs` → `StepH (decode s)
  (decode s')`. Load-bearing: 135 files use `Abs.decode`.
- `Abs.astep`/`AResult` (`Abs/Step.lean`) is a second, executable transition
  left from the integer vertical slice; 64 files use it. Candidate for removal.

Code interpretation (phase 6):

- `CodeInterpretation := Nat → ExecutableModule → Nat → funccode`
  (`Representation/Store.lean`) maps instance index, module and function to
  source code. It is ghost because callbacks publish code, hence `∃ afterCode`
  plus `CodeAgreesOn` (`Store/Invariant/FunctionTables.lean`) in every result.
  `installCode` says existing instance keys keep their interpretation "even
  when their compiled modules coincide"; that is the open question.

Extraction split (phase 9):

- `lean/Makefile`: `extract` = `extract-exec`, which first runs
  `extract-primary` (validator, namespace `Itasca`, `Itasca/Generated`), then
  `scripts/extract_execution.py llbc` / `translate`.
- `extract_execution.py`: Charon with `--cfg=charon --cfg=charon_exec`,
  `--start-from=itasca::runtime`, `--opaque=itasca::{code,module,stream,
  signature,types,error}`, excludes all `Clone`/`Copy` impls except for `u8`,
  pinned `RUSTUP_TOOLCHAIN=nightly-2026-09-17`; Aeneas with `-strict-joins
  -sequential -abort-on-error -skip-bottom-storage-dead -reuse-definitions`
  (mapping from `scripts/execution_reuse.py`), namespace `Exec`, output
  `Exec/Generated`. Nobody remembers why each flag was added.
- `Exec/Generated/Funs.lean` 49k lines (926 `runtime.*` defs);
  `Itasca/Generated/Funs.lean` 16k. `Exec/Generated/FunsExternal.lean` holds
  236 `@[rust_fun]` adapters, nearly all aliases of validator functions;
  `count_ones`/`trailing_zeros` are the real primitives.
- `src/lib.rs`: `#[cfg(any(not(charon), charon_exec))] pub mod runtime;`.
  `Cargo.toml` and the `lib.rs` crate docs still describe a validator only.

Compiler/validator coupling (phase 11):

- `FunctionCompiler` implements the validator's `OpVisitor`
  (`src/runtime/compiler/callbacks.rs`; trait in `src/code.rs`); each callback
  receives the validator's `&OpIterState`. Exec imports `Itasca.Visitor.*`
  and `Itasca.Stream.*`.
- `Code/Body/Reader/*` file names (`ReaderMemoryAcceptance`, `...Types`,
  `...Stacks`, `...Safety`) suggest it re-derives reader facts the validator
  already proves. Unconfirmed.

## Target

Public results, all over one bundled premise set:

| Entry point | Results |
| --- | --- |
| `compile_with` | `profile_sound`, `profile_spec`, `profile_complete` (unchanged) |
| `instantiate_with` | `spec`: total; links and initializes, never runs code |
| `invoke_with` | `behaves`, `terminates`, `no_spurious_errors` |

- `behaves`: on return, the exact recorded source outcome (values, trap,
  justified resource error, or unchanged-state API rejection) with the
  retained invariant; on divergence, an infinite source run or a diverging
  host call. Replaces `sound`, `recorded_sound`, `recorder_sound` and
  `diverges`.
- `terminates`: no infinite source run and no diverging host call implies an
  ordinary result.
- `no_spurious_errors`: if every source run from the invocation fits
  `max_frames`/`max_values`, the allocator grants requests, interrupts
  continue and callbacks report no stack overflow, every returned error is a
  trap. Replaces `chosen_complete`.
- Exact recording stays: the source run's host events are the calls the
  runtime actually made, in order, with the actual replies.
- Contracts: `Platform.Laws` (float, alloc, memory, interrupts) and
  `HostLaws` (callback invariant preservation, store extension and typing,
  frame prefix, extern retention, issued results). Callbacks may diverge.

Layout after the merge:

```
lean/
  SpecTec/  SpecExt/          specification (unchanged location)
  Itasca/
    Main.lean  Contracts.lean  Results/   one entry point, all results
    Binary/ Module/ Stream/ ...           validator (unchanged)
    Runtime/                              mirrors src/runtime
      Compiler/ Interp/ Store/ Platform/ ...
    Generated/                            one extraction of the whole crate
```

## Decisions

- Dropping chosen-run completeness is approved (2026-10-28). Its "matches
  exactly this preselected run" form needs the whole `SourceChoices`
  machinery and assumes the platform agrees with a fixed oracle.
- The weakened divergence clause ("source diverges or a host call diverged")
  is approved. The certified host driver (`OpenReentrantControl`) goes; a
  small example platform shows the contracts are satisfiable.
- Rust API changes are allowed.
- One library and build target. The validator must still not depend on
  `SpecExt` or runtime proofs; this becomes an audited layer rule.
- Namespace `Itasca.Runtime.*`, mirroring `src/runtime`. `SpecExt/` stays
  beside `SpecTec/`.
- Order: simplify statements and delete first, merge infrastructure second.
  The merge renames every generated name, so every deletion before it shrinks
  the mechanical churn. No simplification phase depends on the merge; only
  compiler sharing (phase 11) does.
- Supersedes the previous plan's phase 11 (separate `lean_lib`, namespace
  `Itasca.Exec`) and its phase 12 plain/chosen analysis (the chosen variant
  is deleted instead of unified).

## Ground rules

- One phase per commit series. Split refactor, propagation and deletion
  commits when large. Rust changes land with the proofs they break; docs are
  separate commits.
- Statement changes to `Results/*` are limited to the ones listed in this
  plan. Stop and ask before weakening any other conclusion or adding a
  premise.
- Every commit: `just prove-exec` (and `just prove` when `Itasca`/`SpecExt`
  change), `just audit-imports`, `git diff --check`. Rust commits add the
  full Rust/extraction list from `AGENTS.md`.
- After each phase: `just exec-stats`, `just dead Exec`; record numbers in
  the commit message or here.
- Delete superseded code in the same series that replaces it. No shims.
- Never `unfold` or `simp [f]` a function whose body is a full `Instr` match
  while the instruction is a variable; `cases` first, then rewrite with the
  equations from `Exec/Generated/Equations`.

## Phase 0: re-baseline

1. Extend `scripts/reachability.lean` to report, per headline theorem, the
   declarations and files reachable only through it (exclusive cone).
2. Record exclusive cones of `chosen_complete`, the host-driver results,
   `recorded_sound` vs `sound`, and `Store.instantiate_with.*`.
3. Measure overlap between `Exec/Code/Body/Reader` and `Itasca/Visitor`,
   `Itasca/Handler` (facts re-derived about the same reader), and between
   `Itasca/Spec` and `Exec/Spec/Typing`. Inputs to phase 11.

Exit: numbers recorded here; phase order confirmed.

Results (2026-10-28, `just dead --cone A,B,...`; declaration lines only;
`Examples/` are roots, so host-driver cones are lower bounds until phase 2):

| Cone | Decls (thms) | Lines | Modules (entire) |
| --- | --- | --- | --- |
| `invoke_with.chosen_complete` alone | 24 (20) | 1,044 | 19 (14) |
| + driver `invoke.chosen_complete`, `invoke_chosen_complete` | 310 (278) | 5,202 | 101 (82) |
| all 8 host-driver results | 835 (673) | 16,824 | 287 (263) |
| all chosen + all host-driver | 1,632 (1,391) | 36,234 | 578 (546) |
| `invoke_with.sound` | 2 | 48 | 2 (1) |
| `recorded_sound`, `recorder_sound`, `diverges` | 0 each | 0 | 0 |
| `invoke_with.finite_progress` | 69 (64) | 2,606 | 43 (40) |
| `instantiate_with.sound` | 2 | 55 | 2 (1) |
| `instantiate_with.recorded_sound` | 106 (68) | 3,963 | 42 (39) |

- `sound` is a thin corollary of the recorded proof: keep the recorder model
  (phase 3), a wrapper platform would not be smaller.
- Reader overlap (sampled): ~70 of 378 `Code/Body/Reader` files (~4.4k lines)
  are validator-only; ~8-10k lines of validator-level content in total. Most
  have an `Itasca` near-equivalent, but stated forward (`code.step ⦃ ⦄` under
  a total visitor) while Reader needs the inverse from an accepted step. An
  exact per-opcode characterization for any callback could remove ~6-9k lines.
  Examples: `ReaderUnreachable` vs `Wasm2/Scalar/Step.step_unreachable`,
  `ReaderFloatConstant` vs `Handler/ScalarConst`, `ReaderTypedSelect` vs
  `Wasm2/References/Step`, `ReaderPopPrefix` vs `Handler/Stack`.
- `Itasca/Spec` (670 lines, instruction validation) vs `Exec/Spec/Typing`
  (4.8k lines, runtime/admin typing): no shared names, different judgments,
  at most a few dozen lines of subtyping helpers. Phase 11 step 3 is moot.
- Phase order confirmed.

## Phase 1: replace chosen completeness

1. Move `SourceWorldResources` and `excludes_boundary` out of
   `ChosenWorldResourceBounds.lean` into a non-chosen module.
2. Define the all-runs resource premise: every `StepsH`-reachable state from
   the invocation configuration satisfies `SourceWorldResources` for the
   store's `max_values`/`max_frames`. (Today's `ChosenWorldResources` is the
   same over `ChosenStepsN` only.)
3. Prove `invoke_with.no_spurious_errors` from `recorded_sound` and the
   resource causes: each non-trap error cause contradicts one premise
   (`excludes_boundary` already does this per dispatch, using allocation
   availability, continuing interrupts and no callback stack overflow).
   Shape: `invoke_with ... ⦃ out => ∀ e, out.1 = .Err e → e is Trap ⦄div`.
   The step from dispatch-level causes to the whole run may need a loop
   lemma; `ChosenWorldResourceLoop.lean` has the chosen version to adapt.
4. Delete the roots `invoke_with.chosen_complete`, the host driver's
   `invoke_chosen_*` and `invoke.chosen_complete`, then run `just dead Exec`
   and delete what it reports. Do not delete `Spec/Choices` or `*Chosen*`
   files by name: some (`Redex*`, `Normalization`, determinism lemmas) may
   still feed kept proofs. Expected to go: most of `Spec/Choices`, `*Chosen*`
   files in `Abs/Sim`, `Interp/StructuredMachine`, `Theorems/{Api,
   Composition,Invocation}`, `Theorems/Host/Chosen`, `Host/Open/Source/Chosen`,
   and the contracts `SourceChoices.Admissible`, `GrowthChoicesCompatible`,
   `HostWorldChosenSound`, `ChosenWorldResources`, `ChosenSourceResources`.
   `NoHostStackOverflow` survives as a `no_spurious_errors` premise.
5. `ExecutableResourceInv` (value/frame limits below the store's) exists for
   chosen completeness; delete it if unreachable, otherwise phase 4 merges it.
6. Update `Results/Invoke`, `Results/Host`, `Main`, `Contracts`, READMEs
   (`lean/README.md` "Execution boundary", `Exec/README.md`).

Exit: no `Chosen`/`SourceChoices` declarations remain.

Done (`b0a3b92`). 2,709 files / 208,551 lines; 7,369 theorems / 1,847
definitions; olean 1.28 GiB; overrides 217 / 311.
- `no_spurious_errors` needs one premise chosen completeness carried inside
  `ExecutableResourceInv`: callbacks keep `store.limits` (`limitsKept`). Rust
  makes `limits` `pub(super)`, so this holds for real callbacks; phase 4
  can fold it into `FrameStorePrefix`.
- Also takes `owner`, `owned`, `InvocationArgumentsTyped`; the resource
  premise is `SourceResourcesFit` (signature, entry frame, frame depth of
  every reachable config, call sites of every reachable state).
- `ExecutableWorldRecordedOutcome` early rejection now carries
  `InvocationRejected` (the failed check). `WorldInvocationLaws` deleted.
- Pruning by `just dead` misses `rfl` lemmas used only via `simp only [n]`;
  skip declarations whose name is still mentioned.

## Phase 2: diverging callbacks, remove the host driver

1. Weaken the callback contract: `call_host` is partial (`⦃ ... ⦄div`)
   instead of returning normally. Preservation laws apply on return.
2. Extend the divergence conclusion: `.div` implies an infinite source run or
   a reachable host call that diverges. Adjust `terminates` premises.
3. Delete `Theorems/Host/Open`, `Theorems/Host/Reentrant`, `Results/Host` and
   the `Selector` action language, keeping only what the generic theorems
   use.
4. Add an `Examples/` platform: a trivial host and allocator discharging
   every contract, built against `Main` only.

Exit: one host story; `Results/Host` gone.

Steps 3 and 4 done first (commits `bcecca9f`, `1eb19598`). Steps 1 and 2 done
after phases 5, 4 and 3. `HostWorldSound` is `⦃⦄div`. New `DivSpec cause m P`
(`Platform/DivSpec`, registered with `step`, lifts `spec`) is "returns with P or
diverges and `cause`". Host chain concludes `DivSpec (HostDiverges hooks store)`
per step; `world_loop_infinite` splits classically on a reachable world whose
store has a diverging callback. Public clause: `HostCallDiverged hooks view
initial` = a `StepsH` run from `initial` reaches `⟨⟨decodeStore view code store,
_⟩, _⟩` with `HostDiverges hooks store`. `terminates` gains
`¬ HostCallDiverged`; `TrapHost.trapHost_returns` discharges it. `DivSpec`
also replaced `InvocationWP allowDivergence` (`False` = spec, `True` = dspec),
and `loop_trace_dspec`/`execution_loop_*` take partial bodies.

## Phase 3: `behaves`

1. Define `Behaves initial` over the Aeneas result:

   ```lean
   def Behaves (initial : config) : Result Out → Prop
     | .div    => InfiniteSourceWithEvents initial ∨ (a reachable host call diverges)
     | .ok out => RecordedOutcome initial out   -- Ok: source returns these values
                                                -- Trap: source traps
                                                -- Exhausted/Terminated: resource cause
                                                -- BadArguments/WrongStore: state unchanged
     | .fail _ => False
   ```

   The `.ok` case is today's `ExecutableWorldRecordedOutcome` plus the
   resource-cause clause of `recorded_sound`.
2. State `invoke_with.behaves`; derive `terminates` from it.
3. Delete `sound`, `recorder_sound`, `diverges` and the non-recorded
   `ExecutableWorldInvocationOutcome`. Keep the `recordedInvokeWith` model
   unless phase 0 shows a wrapper platform plus one erasure lemma is smaller.
4. Demote `finite_progress` to an internal lemma behind divergence.
5. Same treatment for instantiation if anything of it survives phase 5.

Done before phase 2 (it shrinks phase 2 to three public theorems).
`InvocationBehaves` (`Theorems/Invocation/PublicBehaves`) is the `⦃⦄div`
recorded outcome with resource causes plus `outcome = .div → infinite source`;
`terminates` is `InvocationBehaves.returns` and now also carries resource
causes. `finite_progress` was not behind divergence (that uses the decreasing
stutter of `world_loop_infinite`), so it and the whole uniform progress chain
(41 modules) were deleted rather than demoted. Instantiation has nothing left
to merge. Stats after: 2,595 files / 198,301 lines, 7,170 theorems / 1,744
definitions.

## Phase 4: bundles and output structs (previous plan's phase 7)

1. Rust: named structs for `invoke_with`, `instantiate_with` and
   `call_host` results instead of nested tuples; `@[simp]` projection lemmas.
2. `Platform.Ops` and `Platform.Laws` bundles; `HostLaws` bundle replacing
   the ~200 inline copies of the four host premises.
3. Merge `ExecutableResourceInv` into `ExecutableInv` (limits already live in
   `store.limits`).
4. `variable`/`include` sections for repeated binders.

Risk: bundling can slow `simp` if accessors are not reducible; profile one
hot file first.

Done: steps 2 and 3. `Platform.Laws` (`Platform/Laws.lean`) and `HostLaws`
(`sound`, `retains : ∀ code store, Inv code store → ∀ host, HostRetention hooks
store host`) replace seven premises in `Results/Invoke` and the world layers
(26 files). Per-store host proofs take `HostRetention hooks store host`.
`Platform.Ops` dropped: generated functions take the four instances
positionally, so a bundle could not be passed to them. `ExecutableResourceInv`
deleted: `no_spurious_errors` uses `ExecutableInv view c s ∧ s.limits =
store.limits` locally. No simp slowdown (`Prop` structures, no unfolding).

Not done, needs a decision:
- Step 1. The nested tuples are Aeneas's encoding of `&mut` arguments
  (`&mut Execution`, `&mut Store`, `&mut P`, `&mut [Value]`), not Rust tuples.
  Rust output structs would require a by-value API, including the embedder's
  `Platform::call_host`. A Lean-side accessor layer is possible but is a shim
  over generated code.
- Step 4. `variable` sections would make headline statements in `Results/`
  stop being self-contained; internal use gains little after the bundles.

## Phase 5: instantiate without the start function

1. Rust: `instantiate_with` links and initializes, then returns the start
   function (if any); the caller invokes it with `invoke_with`.
2. Instantiation proofs lose host calls, publication, divergence and the
   start-specific outcome split; the result becomes total.
3. Delete `EventfulInstantiationSourceOutcome`,
   `RecordedInstantiationSourceOutcome`, `recordedInstantiateWith` and the
   start-execution parts of `Store/Instantiation` and
   `Theorems/Instantiation`. Rollback before publication stays.

Done (ran before phases 2 and 4 to cut churn). Rust returns
`Instantiated { instance, start }`; wast/differential/bench drivers invoke the
start function. `Results/Instantiate` is one total theorem
`instantiate_with.spec`: premises are only memory laws, the alloc law,
`ExecutableInv`, issued imports and the accepted compilation (no host, interrupt
or float laws). The final interpretation is explicit
(`installCode oldCode before.instances.length (Code.sourceFunctions raw)`), so no
`afterCode` existential here. Success reaches `CALL_ADDR start` in the source
instantiation (`InitializedSource`), the start address is resolved and issued
(`StartResolved`), and resource causes are merged into the same theorem.
Built in `Theorems/Instantiation/InstantiateSource`; 39 modules deleted.
Stats after: 2,636 files / 201,629 lines, 7,238 theorems / 1,748 definitions.

## Phase 6: canonical code interpretation

1. Find out why `installCode` keeps distinct interpretations for coinciding
   compiled modules (`Store/Invariant/FunctionTables`).
2. If nothing depends on it, define the interpretation from each instance's
   compilation certificate (`Classical.choose`), so `decodeStore` takes no
   ghost argument.
3. Delete `afterCode` existentials, `CodeAgreesOn` and the `∀ code` binders
   in host laws.

Exit or abandon: record the `installCode` finding here either way.

Abandoned. Compilation is not injective on source code: `Lower::op` returns
before emitting when the current point is unreachable
(`src/runtime/compiler/lower.rs`), and blocks emit nothing. So
`unreachable; i32.const 1; drop` and `unreachable; i32.const 2; drop` (same
encoded length, so same source offsets) compile to the same
`ExecutableModule`. A choice from the compilation certificate can pick the
wrong source body, and `instantiate_with.spec`, which relates
`fun_instantiate` of the user's module, would become false. The ghost
interpretation has to come from the module the user instantiated, which is
what `installCode … (Code.sourceFunctions raw)` does. Host-published instances
keep the `afterCode` existentials for the same reason. Phase 5 already made
instantiation's interpretation explicit.

## Phase 7: flatten composition layers

Fresh analysis first: phases 1 to 6 remove many of the layers' reasons to
exist.

1. Prove the world-level relation directly; delete the remaining
   `Theorems/Composition/{Supported,Stateful,Uniform,Eventful,Cumulative,
   Certified,Core,Executable}` layers and the leftovers under
   `Interp/{Core,FloatCore,Cumulative,Machines}`.
2. Remove `Abs.astep` and `AResult`; relate interpreter steps to `StepH`
   through `Abs.decode` only. Fix the stale "integer vertical slice" header.
3. `StepPost`: name the `∃ nextPC nextPending after, ...` bodies of the
   remaining `Advance` relations.
4. Ordinary-op descriptions: prove reader-prefix lemmas once per opcode
   description instead of per opcode.

Fresh analysis (after phases 1 to 6): the uniform and certified-host layers are
gone. What remains under `Theorems/Composition` (~5k lines, 90 files) is one
pipeline: `Core` (ownership/contents), `Cumulative` (store-mutation
certificate and outcomes), `Stateful` (bulk memory/table ops), `Supported`
(per-instruction dispatch), `Eventful`/`World` (host-aware loop). They are
stages, not alternative versions, so step 1 is file merging and renaming, done
with phase 10. Step 2 (`Abs.astep`, used in 87 files as the executable source
step with its own correctness proof against `StepH`) is a deep re-proof with no
statement gain; not started. Steps 3 and 4 not started.

## Phase 8: build-cost leftovers (previous plan's phase 8)

Do when they block iteration, not before.

1. `SimdDispatch` (34 MiB): move the core `FunctionCompiler.op` match into
   its own Rust function; give the 297 closer sites one `op_core` rewrite.
2. Remaining > 5 MiB files and heartbeat/recursion overrides.
3. Optional: Lean module-system experiment on one subtree.

## Phase 9: merge into `Itasca`

1. One extraction configuration for the whole crate. Find why the runtime
   pass uses `-strict-joins`, `-sequential`, `-abort-on-error`,
   `-skip-bottom-storage-dead` and excludes `Clone`/`Copy` impls (git
   history, then experiment). Prefer Rust changes (explicit copy helpers)
   over validator-wide flags when a flag changes the validator's generated
   shape.
2. Rust: remove the `charon_exec` cfg on `pub mod runtime` and its "not
   covered by the validator proofs" comment.
3. Extract once into `Itasca/Generated` (namespace `Itasca`, so the runtime
   is `Itasca.runtime.*`). Delete `extract_execution.py`,
   `execution_reuse.py`, `patches/aeneas-reuse-definitions.patch` and the
   236 adapters in `Exec/Generated/FunsExternal.lean`; real primitives
   (`count_ones`, `trailing_zeros`, ...) move to the single
   `FunsExternal.lean`. Run `just regressions`.
4. Move `Exec/` to `Itasca/Runtime/`, mirroring `src/runtime`. One mechanical
   commit.
5. One library and target in `lakefile.lean`; one `Main`, `Contracts`,
   `Results/`, `Audit`, `Examples/`. `check_audit.py`: the validator layers
   never import `Itasca.Runtime` or `SpecExt`.
6. Update `just` recipes (`prove`/`prove-exec`, `extract`, `dead`, `trust`),
   `AGENTS.md`, `DEVELOPMENT.md`, READMEs, `PROOF_GUIDE.md`, and the crate
   description in `Cargo.toml`/`lib.rs` (docs commits).

Risk: large rename; land when no other branch touches `Exec`.

Done (`d1d60c2b`, `13a7e8d0`, docs after). Step 1: none of the four runtime
flags changes the output for this crate (byte-identical single-pass output with
and without them), so the single pass uses the validator flags plus the two
`u8` `Copy`/`Clone` includes; the validator's generated definitions are
unchanged. The reuse patch, its probes and fixtures (`tests/extraction`) are
deleted, and the vendored Aeneas no longer carries it. Runtime definitions
differ from the two-pass output only in binder names and in calling
`Itasca.module.Env.impl.*` directly; proofs drop unfolds of the deleted adapters.
Steps 4-5 landed together, since a separate library audit cannot survive the
move. Deviation: the runtime contracts stay in `Itasca/Runtime/Contracts.lean`,
because validator modules import `Itasca.Contracts` and a merged file would put
the runtime and `SpecExt` into the validator's import closure. `Equations` moved
to `Itasca/Runtime/Equations.lean`. `vec_index_given` lost its global `@[step]`
(all uses are explicit; through `Main` it broke validator examples); other
runtime `@[step]` lemmas on validator functions are still global but break
nothing. Reachability: 35 unused (the previous 23 + 12).
Stats after phase 9: 2,587 files / 197,245 lines (median 60); 7,164 theorems /
1,506 definitions; 133 module docstrings.

Stopped before phase 10. Step 1 re-files essentially all of `Itasca/Runtime`
(2,493 of 2,587 files are under 200 lines, 1,376 at depth 4-5, 117 directories)
and needs a docstring per new file; step 2 renames thousands of theorems. Both
need a decision on how to group concepts before starting.

## Phase 10: consolidate files and naming

### Scope and invariants

Primary scope: handwritten `Itasca/Runtime` modules, their internal declaration
names, importers, audit rules, and documentation. Update validator-side files
only where they refer to moved runtime modules or declarations. Keep `Main`,
`Results`, the two contract entry points, the single extraction, and library
boundaries. A repository-wide validator naming pass is not part of this phase.

Preserve public theorem names, types, premises, conclusions and attributes.
Preserve the exact-recording, resource-cause, divergence, rollback, source-code
interpretation and profile distinctions inside their constructions. In
particular, do not remove `afterCode`, replace `Abs.astep`, weaken host laws,
change Rust APIs, or re-prove compiler/validator sharing as part of a file move.
No new axioms, placeholders, audit exceptions or reachability exemptions.

The organizing principle is a proof concept with a readable argument: its
relation or invariant, supporting lemmas, and the result those lemmas establish.
Rust ownership informs the major areas, but source semantics and representation
certificates need their own areas. Do not force them into a Rust-shaped tree.

### Baseline and concrete problems

Filesystem inventory on 2026-10-28, after the merge; physical lines, including
imports and blank lines, in handwritten runtime `.lean` files:

| Area | Files | Lines | Files under 100 lines |
| --- | ---: | ---: | ---: |
| `Code` | 1,186 | 88,912 | 947 |
| `Interp` | 564 | 43,348 | 451 |
| `Store` | 320 | 27,548 | 207 |
| `Abs` | 185 | 14,517 | 141 |
| `Spec` | 159 | 9,932 | 137 |
| `Theorems` | 148 | 11,252 | 119 |
| `Representation`, `Platform`, root files | 25 | 1,739 | 19 |
| **Total** | **2,587** | **197,245** | **2,021** |

These are file statistics, not a new elaboration/performance baseline. Reader
proofs alone occupy 378 files; `Interp/StructuredMachine` has 126;
`Theorems/Composition` has 83. Names often repeat their entire directory path
or record an earlier expansion of the instruction subset. The current README
also still describes instantiation as running start code, despite the completed
phase 5. Both the map and the prose need to describe the checked construction.

### Proposed ownership and target layout

Paths below are relative to `Itasca/Runtime`. They describe destinations, not
permission to move a declaration above its dependencies. Confirm each group
against its imports before merging it.

| Current area | Target | Ownership and grouping |
| --- | --- | --- |
| `Spec` | `Spec` | Source-rule algebra and typing, grouped by operation or judgment. Keep independent of the extracted runtime. |
| `Abs` | `SourceMachine` | Flat source state, decoding, transitions, typing and simulation. Retain the transition system; give the model a descriptive name. |
| `Equations` | `Equations` | Keep the generated-equation gateway separate, however small. |
| `Platform` | `Platform` | Allocator, memory, float and host contracts; separate independently consumed contracts. |
| `Representation` | `Representation` | Shared encoding, decoding, layout and capacity certificates. Keep below their compiler/interpreter/store consumers. |
| `Code/Local` | `Compiler/Local` | Per-operation emission, callbacks, source relations and capacity arguments. |
| `Code/Body` | `Compiler/Body` | Reader replay, structured control, and whole-body certificates. |
| `Code/Module` | `Compiler/Module` | Entry assembly, scheduling, finalization and module certificates. |
| `Interp` | `Interp` | Operation proofs, machine relations and machine steps; keep invocation integration separate. |
| `Store` | `Store` | API operations, invariant preservation, linking, preparation, initialization and instantiation. |
| `Theorems` | `Integration` | Constructions joining compiler, interpreter, store and host proofs; organized by the API or execution concept they establish. |
| `Contracts` | `Contracts` | Stable entry point for embedder obligations; keep independent of constructions assuming those obligations. |

Retain Local → Body → Module as enforced compiler stages. Within a stage,
prefer a topic directory containing a few substantial modules. For example:

```text
Runtime/
  Spec/                 SourceMachine/
  Equations.lean        Platform/             Representation/
  Compiler/
    Local/              # Emission, Control, Capacity, ...
    Body/
      Reader/           # Calls, Memory, Table, Control, Replay, ...
      Relations/        # independent body certificates and their lemmas
    Module/
  Interp/
    Relations/          # shared machine contracts
    Machine/            # frames, control, instruction-family steps
    Invocation/         # setup, loop, recording, readback
  Store/
    Invariant/          Api/                  Linking/
    Preparation/        Initialization/       Instantiation/
  Integration/
    Api/                Compilation/         Invocation/
    Instantiation/      Host/                Execution/
  Contracts.lean
```

`Interp/Machine` is the proposed home for `StructuredMachine` and the adapters
currently spread across `Core`, `FloatCore`, `Cumulative` and `Machines`.
Do not merge different relations just because they have similar names. Describe
which grammar, ownership, store-mutation or host premise distinguishes them.
Keep genuinely independent contracts in `Interp/Relations` and combine their
proof adapters by operation family where the dependency graph permits.

`Integration/Execution` replaces the historical `Composition` stage names with
concepts such as `Ownership`, `Mutation`, `Dispatch`, `Resources`, `History`,
and `World`. `Integration/Api` initially retains `Theorems/Api` intact. The
special contract dependency on `ExecutableInv` must remain precise; relocating
that invariant to a lower layer requires an import-closure check and is not a
reason to allow `Contracts` to import all of `Integration`.

Prefer about three directory levels below `Runtime`, but allow an extra level
when it distinguishes useful families or enforced stages. Do not flatten
`Compiler/Body/Reader` into an enormous directory merely to meet a depth limit.

### Consolidation rules

1. Merge by argument and shared consumers, not by alphabetical adjacency or
   line count. A definition plus its inversion, preservation and final step
   lemmas often belongs together. A small contract used widely can stay small.
2. Around 200–600 lines is a useful starting point for a cohesive module, not
   a minimum, maximum or acceptance test. Keep a coherent 100-line contract or
   900-line proof when splitting it would harm navigation. Never pad a file.
3. Keep cheap foundational statements separate from expensive constructions
   when their consumers differ. Do not make every reader import every opcode,
   or every invariant user import the full invocation proof.
4. Before merging a set, contract it in the import graph and check for cycles.
   A path from one member through an external module back to another member
   can make a merge cyclic even though the original graph is acyclic. Expand
   the group only if it remains conceptually coherent; otherwise keep the split.
5. Preserve declaration order and namespace/section boundaries. Review local
   notation, `open`, variables, options, attributes and private helper names:
   concatenating files can change elaboration scope and cause name collisions.
6. Do not add import-only facades for every deleted file. Remove superseded
   modules and update consumers in the same buildable batch. Guides provide
   navigation; imports should express actual dependencies.
7. Start each resulting module with a short module docstring: what question it
   answers, the main relation/result, and where its construction is consumed.
   Use section comments inside larger files to show the proof progression.

### Concrete consolidation candidates

These are starting groups for dependency review, not blind filename globs.

| Existing cluster | Proposed grouping | Boundary to preserve |
| --- | --- | --- |
| `Store/Api/MemoryFillEffect`, `MemoryFillMutation`, `MemoryFillSemantics` | `Store/Api/MemoryFill` | Handler effect → metadata/mutation → decoded source effect. Check whether low-level consumers need the effect without the source-semantics imports. |
| `Store/Api/TableFill{Loop,Lists,Effect,Mutation,Semantics}` | `Store/Api/TableFill`, or `TableFill` plus a separately consumed loop module | Keep independent list/loop helpers low enough for other operations. |
| `Interp/StructuredMachine/IntegerConstant{Point,Capacity,Bounded,Step,ExecutionOwned}` | `Interp/Machine/IntegerConstant` | Fetch/inversion → capacity → step → ownership. Do the analogous float group separately before considering shared constants. |
| `Code/Body/Reader/Calls/Reader*` and call acceptance modules | `Compiler/Body/Reader/Calls`, with `IndirectCalls` or `CallAcceptance` only when useful | Separate direct/indirect lookup obligations and accepted-step versus successful replay directions. |
| Reader table/control prefix, dormant-scope and compiler-step files | Topic modules under `Compiler/Body/Reader/Control` and `Table` | A table of labels/control maps is not a Wasm table operation. Classify by definitions before relocating misleadingly named files. |
| `Theorems/Composition/Stateful/StatefulMemoryFill*` | `Integration/Execution/MemoryFill` | Join the operation, source step and dispatch lifting, while keeping the store operation below integration. Repeat per bulk operation. |
| `Composition/Eventful/*`, `Composition/World/*` | `Integration/Execution/{World,History,Resources,Loop}` as dependencies permit | Retain exact recorded events, resource causes and the diverging-host alternative. |
| `Theorems/Invocation/Public*` and associated outcomes | `Integration/Invocation/{Outcomes,Resources,Divergence,Behaves}` | Shared outcome definitions must remain below proofs using them; public `Results/Invoke` remains a small projection. |

Begin with the memory-fill cluster as a pilot: its effect, mutation and source
meaning form an inspectable argument. Then try integer constants to exercise a
more connected interpreter family. If either merge increases import cost or
creates cycles, record the retained boundary and apply that lesson before
consolidating the compiler's much larger reader tree.

### Naming policy

Write these conventions into `PROOF_GUIDE.md` and the runtime guide before the
first declaration-rename batch, with examples from the pilots:

- Module names use `UpperCamelCase` and identify their subject. Omit redundant
  directory prefixes: `Compiler/Body/Reader/Memory.lean`, not another
  `ReaderMemory...` basename at every level. Keep a qualifier when it actually
  distinguishes two concepts.
- Namespaces identify semantic owners. Module paths identify dependency
  placement; they need not match exactly. A store decoder can still belong to
  `Store` while its definition lives under `Representation`.
- Adopt `Compiler` for handwritten compiler concepts and `SourceMachine` for
  the abstract source model, replacing handwritten `Code` and `Abs` qualifiers
  in a separate mechanical pass. Do not rename extracted `Itasca.code` or
  `Itasca.runtime.*`, SpecTec identifiers, or third-party declarations.
- Types, structures, inductives and named predicates use `UpperCamelCase`.
  Computational definitions use `lowerCamelCase` (for example `decodeStore`);
  theorem basenames use `snake_case`. Do not capitalize every `def`: predicates
  and computations serve different roles.
- Facts about an extracted function remain under its extracted Rust name;
  facts about a relation belong under that relation where practical. Preserve
  public names such as `runtime.interp.invoke_with.behaves`.
- Name the conclusion: `preserves_*`, `*_eq`, `*_iff`, `*_sound`,
  `*_complete`, `*_spec`, or an informative operation name. These are examples,
  not mandatory suffixes. Preserve Wasm spellings such as `br_if` and
  `call_indirect`; do not force extracted owner segments into another style.
- Replace historical adjectives (`Core`, `Supported`, `Cumulative`, `Eventful`,
  `Executable`) only after documenting what each means. Use a concrete subject
  such as ownership, mutation, dispatch or host events when that is the real
  distinction. If a name identifies a retained grammar/invariant, document it
  rather than incorrectly erasing the distinction.
- Avoid new catch-all names such as `Misc`, `Extra`, `Aux`, `Old` or `New`.
  Existing `Common`/`Generic` modules should acquire a specific responsibility
  or have their helpers moved to their consumers; no mechanical word ban.

Maintain explicit old → new module and declaration mappings per migration batch
in its review description. Rename identifiers using token-aware edits or exact
qualified replacements, then inspect comments, tactic registrations, quoted
names and reachability roots separately. Avoid a repository-wide textual
replacement of words such as `Code`, `Core` or `World`.

### Implementation sequence and exit criteria

**10.1 — Inventory and freeze the contract.** Capture `just exec-stats`,
`just dead`, current public theorem statements and attributes, and the import
graph using the existing tokenizer/audit machinery. Record tiny-file clusters,
fan-in, expensive modules and candidate cycles. Start with a passing
`just prove`, or record an existing failure before attributing it to cleanup.
Prepare the first two pilot mappings, including retained small files and why.
Exit: a reproducible baseline and concrete, acyclic pilot groups.

**10.2 — Prove the grouping policy on two pilots.** Merge memory-fill files,
then integer-constant files, retaining current directory and declaration names
where possible. Add docstrings and update all importers. Compare targeted
elaboration with warm dependencies and inspect the expanded import closure.
Exit: both groups read as complete arguments, required checks pass, and any
cost-driven exceptions are documented. A lower file count alone is insufficient.

**10.3 — Establish the major owners.** Move `Code` → `Compiler`, `Abs` →
`SourceMachine`, and `Theorems` → `Integration`, one owner per buildable batch.
Keep internal declaration namespaces unchanged until their rename batches.
Update `RUNTIME_LAYERS`, compiler stage checks, the precise contract exception,
audit sinks, scripts and documentation alongside each move. Preserve or
strengthen restrictions; never temporarily allow unrestricted runtime imports.
Exit: the new major map is enforced and no active imports use the old paths.

**10.4 — Consolidate from foundations to consumers.** Work through source
semantics/source machine, representation/platform, compiler Local → Body →
Module, interpreter relations/operations/machine, store, then integration.
Within an area, migrate coherent dependency groups, not an entire tree at once.
The pilots need not be repeated. Compiler reader work is several batches:
shared contracts/replay, scalar/float, memory/table, calls/control, SIMD, then
whole-body composition. Interleave a lower shared helper with its consumers
when needed to keep every batch buildable. Record the new reading path after
each area. Exit: the candidate families are consolidated, old modules removed,
and remaining small files have clear independent responsibilities.

**10.5 — Normalize internal names by owner.** Use separate rename commits after
the relevant file consolidation so reviewers can distinguish movement from
naming. Rename namespace owners before basenames within each affected family;
update all references atomically, including tactic and reachability metadata.
Compare public theorem types against the baseline modulo the explicit internal
renaming map. A successful build alone does not establish unchanged statements.
Exit: consistent internal vocabulary, stable public names, no stale references.

**10.6 — Finish documentation and integration.** Update the runtime guide's
layer table, compiler stages and public-construction links. Correct stale
instantiation/start prose against `Results/Instantiate`. Add three concrete
reading paths: compilation, invocation, and instantiation, each from `Results`
through its construction to the foundational certificates. Update `lean/README`,
`PROOF_GUIDE` and any affected root documentation; keep historical paths clearly
marked as history. Record final metrics and any deferred clusters in this plan.
Exit: a reader can follow a representative operation through its complete proof
without hunting through a succession of single-lemma files.

### Verification and completion

For each proof migration batch:

1. Run targeted `just check` commands while iterating, including affected
   consumers, not only the newly merged module.
2. Run `just audit-imports` after additions, moves or deletions. If audit rules
   change, run the existing checker regression tests and preserve tests that
   reject upward imports, contract cycles and validator/runtime leakage.
3. Run `just prove` for integration. It includes audit coverage, transitive axiom
   checks and reachability. Investigate dead reports alongside explicit name
   references; do not delete a lemma solely because automation hid its use.
4. Check updated documentation links and `git diff --check`.
5. Record files/lines, import closure and relevant timing changes for the area.
   Profile only when new changes or regressions warrant it; preserve caches.

No Cargo or extraction run is needed for handwritten-proof-only moves. If the
scope expands to Rust, extraction, toolchain or specification inputs, apply the
full corresponding checks in `AGENTS.md` and `DEVELOPMENT.md`.

Final acceptance is qualitative and checked: coherent ownership, readable proof
units, documented distinctions, unchanged public guarantees, enforced import
boundaries, and passing integrated proofs. Report the reduction in files under
100 lines and in navigation hops for the three reading paths, but impose no
file-count quota, hard size limit or arbitrary percentage reduction. Investigate
material build regressions rather than trading away dependency hygiene for size.

### Execution record

The baseline `just prove` passed before proof edits: 81,305 declarations audited,
35 unreachable declarations in 16 modules, and no unused modules outside the
existing documented allowlist.
The baseline contains 2,587 runtime files / 197,245 lines, including 2,021 files
under 100 lines; compiled runtime oleans total 1.25 GiB. All 51 theorem types in
the result modules, including generated auxiliaries, were captured from Lean's
elaborated environment for the final comparison.

The memory-fill pilot combines `MemoryFillEffect`, `MemoryFillMutation`, and
`MemoryFillSemantics` into `Store/Api/MemoryFill`. The integer-constant pilot
combines `IntegerConstant{Point,Capacity,Step,Bounded,ExecutionOwned}` into
`Interp/StructuredMachine/IntegerConstant`. Both passed targeted checks and
`just prove`, retaining the baseline audit and reachability counts. Warm isolated
re-elaboration took about 6.5 seconds versus 18 seconds across the old memory-fill
files, and 6.3 seconds versus 30 seconds across the old integer-constant files.
These timings include import loading; they are not whole-build speedups.

The memory-fill merge adds five source-semantics modules to `StoreMutationFacts`
and none to its execution consumer. Integer constants add none to their consumer.
The broader reviewed consolidation graph is acyclic; its maximum cumulative
expansion for a retained runtime module is 26 original modules. Shared table-fill
loops, prepared-run relations, staging contracts, and SIMD primitives stay below
their larger constructions.

The `Compiler`, `SourceMachine`, and `Integration` module-owner moves each passed
`just prove`, with unchanged audit and reachability counts. The consolidation
combines 911 files into 321 argument modules, in addition to the two pilots,
and makes 745 topic moves. Five declaration-free facades were removed, with their
imports inlined. Shared table-fill loops, cheap prepared-run relations, source
instruction descriptors, SIMD packing primitives, and recorded/unrecorded entry
boundaries remain separate because their consumers or proof premises differ;
merging the first two would add 151 and 316 dependency modules respectively.

The consolidation build passed `just prove`. A token-preservation check against
the starting commit verified all 2,550,126 original runtime body tokens, excluding
comments and imports; the only additional tokens were anonymous scope wrappers.
All 51 result-module kernel theorem types were exactly identical before naming.
The audit counted 80,492 declarations rather than 81,305, with the handwritten
inventory unchanged. Preserved compiled artifacts show generated-helper reuse:
a sample of 246 groups accounts for 748 fewer generated constants. For example,
`BranchSkipSafety` retains all six source declarations while 27 private
matcher/equation helpers are generated once rather than three times. Overwritten
artifacts prevent reconstructing the entire count difference from that sample.
Reachability remained 35 declarations in 16 modules, with no unused modules.

The naming pass changes semantic owners first, then 667 theorem basenames using
Lean's resolved definition/reference positions. All 47 unmatched textual names
were reviewed as local bindings or a foreign constructor case; no tactic or
reachability metadata required renaming. Comment repairs cover all 64 stale
theorem references plus the public owner/path references. All 11 frozen public
source files preserve their body tokens and attributes, apart from 14 intended
internal namespace references. Grammar types use explicit `ModuleBinary.Code`
qualification where a bare `Code` would be confused with the compiler owner;
one inline tactic block was reindented for the longer namespace names.
[PHASE10_MAP.json](PHASE10_MAP.json) records module,
namespace, private-name, and theorem mappings.

The final source inventory is 1,986 files / 207,748 lines, including 1,268 files
under 100 lines and 446 single-theorem files. The handwritten inventory remains
7,164 theorems and 1,506 definitions. Module documentation covers 993 files,
including every one of the 323 consolidated units. Added documentation and
scope boundaries account for the line increase. The namespace statistics now
count reopened namespaces once per file.

The three fixed-endpoint shortest import paths are:

| Public result → foundation | Baseline hops | Final hops |
| --- | ---: | ---: |
| Compilation → reader call safety | 5 | 5 |
| Invocation → memory-fill effect | 6 | 5 |
| Instantiation → precheck witness | 5 | 4 |

These measure import edges, not proof complexity. The runtime guide provides
complete compilation, invocation, instantiation and operation reading paths.
All 215 guide links and anchors resolve. Audit coverage and all 41 script tests
pass; the checker now rejects reachable import cycles and restricts the contract
exception to the exact API invariant module.

Final targeted result builds and `just prove` pass, including all 80,492
declarations in the axiom audit. All 51 result-module kernel theorem types match
the baseline modulo the five recorded namespace prefixes and 667 exact theorem
mappings; public names, attributes, binders, universes and premises are unchanged.
The final reachability inventory matches all 35 baseline declarations by mapped
name, not just by count. Active runtime oleans total 1.20 GiB versus 1.25 GiB at
baseline; dependency and obsolete build caches were preserved. Whitespace checks
include the staged moved files as well as the working-tree diff.

The structural changes are committed as `559079ca`; the separate namespace and
theorem naming changes are committed as `cad21817`. This plan's pre-existing edits
and completion record remain uncommitted. Import rewriting also removes one
duplicate `Handler.NumericDispatch` import from `Wasm2/Scalar/Total`; its proof
body is unchanged. Rust, extraction outputs, specification sources and pins are
unchanged. The trust boundary is unchanged. Phase 10 is complete; phase 11 had
not been started at that point.

## Phase 11: share validator and compiler proofs

Phase 11 is complete. Work compared `Runtime/Compiler/Body/Reader` with
`Visitor/`, `Handler/`, and `Wasm2/`. Phase 0's line estimates are historical
sampling results, not a deletion target. Its specification-typing comparison
found no substantial overlap, so merging `Spec/` with `Runtime/Spec/Typing`
is outside this phase.

The shared interface must retain exact decoded arguments, callback equations,
stack effects, and advancement of the original source prefix. Existing forward
validator theorems often retain only `Pending.After`; compiler inversion needs
the stronger evidence. Successful-step inversion must not acquire totality or
universal callback-acceptance premises. Compiler completeness must continue to
construct actual acceptance from independent source and allocation premises.

1. Remove confirmed duplicate inversion lemmas and move visitor-only replay
   helpers out of Runtime. Preserve exact callback state and arguments.
2. Pilot shared reader postconditions on the four scalar constants and
   `unreachable`. Derive validator forward preservation and compiler inversion
   from the same reader proofs, covering both profiles. Keep compiler emission,
   capacity, checking and publication obligations in Runtime.
3. Before broader rollout, pilot a control instruction and `br_table`. The
   latter has repeated label callbacks and a distinct final callback; a
   single-callback interface cannot replace its loop correspondence.
4. Expand by instruction family only where both consumers can reuse the same
   facts. Delete superseded proofs in each batch. Record actual changes in
   proof size and import dependencies rather than counting moves as deletion.

Keep validator imports independent of Runtime and SpecExt. Shared handler and
visitor helpers must respect existing downward-layer rules. Preserve public
theorem statements and contracts; compare elaborated result-module types as
well as source statements. Run targeted checks while iterating, refresh audit
imports after file changes, and finish each batch with `just prove` and
documentation/whitespace checks. These handwritten-proof changes do not need
Rust or extraction checks.

### Pilot record

The starting `just prove` passes, with 35 unreachable declarations in 16
modules and no unused modules. All 51 result-module kernel theorem types were
captured before edits for exact comparison. The first batch shares scalar
reader facts and removes generic callback duplication. The rollout record below
continues that baseline through control and the other instruction families.

The shared interface is `Wasm2.ReaderPost` in
`Wasm2/Scalar/ReaderPost.lean`, generalized from the compiler's
`ReaderPostWasm2` to both profiles. `Pending.append_reader` replaces
`Compiler.reader_append_wasm2`; Wasm 1.0 callers supply their independent
grammar and instruction restriction. `Wasm2/Scalar/BasicReader.lean` proves
the four constant readers and `unreachable` once. Existing validator forward
theorems project `Pending.After`; compiler adapters retain the exact decoded
argument, read equation, callback equation, stack effect and shared certificate.
Runtime-specific extensions of the certificate follow its new namespace.

`Runtime/Compiler/Body/Reader/Replay/Run.lean` is removed: every use of
`Compiler.reader_run_success` now uses the existing `CoreVisitor.run.accepted`.
`Runtime/Compiler/Local/Capacity/ReaderAcceptance.lean` moves to
`Visitor/ReaderAcceptance.lean` without changing its declaration names or
statements. Its reached-state lifting proof now composes `run.accepted` with
`run.available_of_read`. No compatibility facades remain.

The sampled import closures add only the two new shared scalar modules.
`Wasm2/Scalar/Step` grows from 84 to 86 dependencies; compiler replay Post,
float ConstantPrefix, and TerminalInstructionPrefix each gain one net module,
because the duplicate runtime Run module disappears. No existing dependency
family is newly pulled into those consumers. Audit coverage still enforces
validator/runtime separation and downward imports.

The pilot's handwritten Lean source grows by 15 lines overall, including its
shared interfaces and documentation. It establishes reuse for these five
instructions and removes the duplicate inversion proof; it does not establish
the historical 6–9k-line reduction estimate. Most touched runtime files only
update the certificate name or replace the duplicate inversion lemma.

The pilot is checked: targeted validator/compiler consumer builds, all 41
checker tests, `just audit-imports`, and `just prove` pass. The axiom audit
checks 80,484 Itasca declarations using only the permitted logical foundations.
All 51 result-module kernel theorem types exactly match the baseline; public
result and contract source files are unchanged. Reachability remains 35 unused
declarations in 16 modules, with no unused modules. All 75 local links/anchors
in the edited guides resolve and `git diff --check` passes. Rust, generated
models, specification sources, pins, and the trust boundary are unchanged.
This was the scalar pilot; the following rollout completes the phase.

### Rollout record

The shared certificates now cover control entry, exact parent resumption at
`end`/`else`, return, direct/indirect calls, ordinary branches and `br_table`.
`Pending.enter_reader`, `end_reader`, `return_reader`, `call_reader`,
`call_indirect_reader`, `branch_reader`, `branch_if_reader` and
`branch_table_reader` retain the stronger source facts. The existing forward
preservation statements are projections. Compiler inversion separately recovers
the actual callback and identifies its metadata with the independently decoded
bytes; it acquires no universal callback-success premise.

The scalar rollout adds `nop`, `drop`, `select`, numeric/sign-extension/saturating
operations, local/global index effects and scalar memory source posts. Reference,
table and bulk instructions reuse the metadata reader certificate; `ref.func`
and `ref.is_null` now share their exact source-post proofs too. SIMD uses the
shared fixed-operand certificate, with a separate shared shuffle reader retaining
its lane bounds and bytes. Three obsolete scalar visitor-lifting proofs and the
compiler-only `Replay/Metadata` and `Simd/SimdFixed` modules are removed.

Generic successful control-reader replay lives in `Wasm2/Trace/Acceptance`;
reached `br_table` replay lives in `Wasm2/Visitor/AcceptedTable`; generic body
replay lives in `Visitor/BodyReplay`. Their old runtime files are removed.
`br_table` retains its loop correspondence and distinct terminal callback.
Its reached-state relation and the existing universal visitor transfer theorem
serve different premises and remain separate. Compiler emission, allocation,
source demand, checking and control-layout proofs also remain separate. Scalar
memory size/grow keep their profile-generic reserved-byte proof and the
compiler's richer metadata-effect adapter; both reuse the lower reader facts.
The phase-0 specification-typing comparison found no substantial duplication,
so there is no speculative `Spec`/runtime typing merge.

Measured against the pre-pilot checkout, handwritten `Itasca` Lean source changes
from 274,941 to 274,825 lines, a net reduction of 116 lines including shared
interfaces and module comments. The rollout alone removes 131 net lines:
Runtime shrinks by 1,037, while shared Visitor/Wasm2 code grows by 906. Moves are
included in both sides and are not counted as deletions. The historical 6–9k
estimate is not the achieved reduction.

The sampled import closures change from 84 to 90 for `Wasm2/Scalar/Step`,
237 to 244 for compiler `Replay/Post`, 383 to 391 for `Float/ConstantPrefix`,
and 429 to 437 for `Control/TerminalInstructionPrefix`. The additions are the
shared reader modules and control acceptance; the duplicate runtime Run module
is removed. Validator imports remain independent of Runtime and SpecExt, and
audit coverage checks the downward-layer rules.

Final validation passes: targeted shared-family checks, `just audit-imports`,
all 41 checker tests and `just prove`. The transitive axiom audit checks 80,460
Itasca declarations using only the permitted logical foundations. Reachability
remains at the baseline of 35 unused declarations in 16 modules and zero unused
modules. All 51 result-module kernel theorem types exactly match the pre-pilot
snapshot; public result and contract source files are unchanged. All 81 local
documentation links/anchors resolve, and `git diff --check` passes. Rust,
extracted models, specification sources and pins are unchanged. No trust-boundary
change was introduced. Phase 11 is complete.

## Leftovers from the previous plan

- `ExecutableInv.source_typed` is presented in `Exec/README.md` but is not a
  result; decide in phase 3.
- The `br_table` trace and completeness examples of the old Wasm 1.0 track
  were not ported.
- `just prove-exec` runs `just dead --check`; allowlist in
  `scripts/reachability.lean`.
- A full Exec rebuild takes 5 to 28 minutes; build
  `SpecExt.Audit Exec.Audit Exec.Main`, not `lake build Exec`.

## Risks

- Phase 1's all-runs premise quantifies over arbitrary typed host replies
  (`StepH.host_return`), so it is stronger than necessary for a specific
  host. Acceptable for now; can later be relativized to the host laws.
- Phase 2: a diverging callback inside a reentrant call must be reflected
  without the driver's combined semantics; check how the divergence proof
  uses callback normal return first.
- Phase 6 may be blocked by the `installCode` design.
- Phase 9 flag unification may change the validator's generated code and
  break validator proofs.

## Unrelated state

- The `worktree-perf-proto` worktree (`.claude/worktrees/perf-proto`) holds an
  uncommitted interpreter performance prototype. Ignore it; performance is a
  later project.
- This plan file is untracked; commit it or keep a copy.

## Unresolved questions

1. `Exec/Spec` and `Exec/Abs` are proofs about the specification, not
   mirrors of `src/runtime`. Proposal: `Itasca/Runtime/Spec` and
   `Itasca/Runtime/Abs`. Alternative: merge `Exec/Spec` into `Itasca/Spec`.
2. Does anything outside the repo (papers, talks, external docs) cite the
   `chosen_complete` or host-driver theorem names?
