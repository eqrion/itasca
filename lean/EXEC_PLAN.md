# Execution proof simplification and merge plan

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

## Phase 10: consolidate files and naming (previous plan's phases 9, 10)

1. One file per concept, ~200-600 lines, module docstring on every file,
   directory depth ≤ 3 under `Itasca/Runtime`. Leaves first.
2. Naming scheme into `PROOF_GUIDE.md` (docs commit), then rename by
   directory:
   - namespaces name concepts, not layers;
   - facts about extracted functions hang off the Rust path
     (`runtime.interp.invoke_with.behaves`);
   - `snake_case` theorems, `UpperCamelCase` definitions, spec mnemonics with
     `_` (`br_if`, `call_indirect`);
   - result suffixes `_sound`, `_complete`, `_preserves`, `_inv`, `_eq`,
     `_spec`;
   - banned: `Extra`, `Legacy`, `Old`, `New`, `Aux`, `Misc`, `Generic`.
3. Resolve the deferred `Wasm2`/`_wasm2` tags (51 files, 361 declarations)
   and `Itasca/Wasm1/Complete` naming.
4. Lint in `scripts/` for banned words and camelCase theorem segments.

## Phase 11: share validator and compiler proofs

Depends on the merge and on phase 0's overlap numbers.

1. Read `Code/Body/Reader` against `Itasca/Visitor`/`Itasca/Handler`. The
   compiler's callbacks already receive the validator's `&OpIterState`.
2. If the reader facts are re-derived: parameterize the validator's
   per-opcode lemmas by a generic callback contract; the compiler proves only
   its callback obligation per opcode.
3. Deduplicate `Itasca/Spec` and `Runtime/Spec/Typing` where they overlap.

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
