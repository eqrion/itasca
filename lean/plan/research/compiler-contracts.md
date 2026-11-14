<!-- Research notes gathered on 2026-11-12 by a read-only research agent for PLAN.md. Statements marked [V] were read in the code; [I] are the agent's inferences and were not compiled. Line numbers refer to commit 81347267 and will drift. -->

# Catalog for the "one contract per extracted function" pilot (emit, enter, op)

Paths are relative to the repository root. Paths below are relative to it. Abbreviations: `C/` = `lean/Itasca/Runtime/Compiler/`, `L/` = `C/Local/`, `B/` = `C/Body/`, `Funs` = `lean/Itasca/Generated/Funs.lean`.

Tags: **[V]** verified by reading or grep, **[I]** inferred. Nothing was built or modified. Scratch files were only in `$TMPDIR` and are removed. Untracked `lean/PROOF_ENGINEERING.md`, `lean/plan/`, `lean/scripts/` appeared during the session and are not mine.

## Headline findings

1. **Your counts reproduce exactly [V].** `emit` 14 sites / 13 files, `enter` 20 / 18, `op` 508 / 69. All are plain `unfold`; there are no `simp`/`rw` sets containing these names, and no `Itasca.`-prefixed variants.
2. **Each facet has its own copy of the same inversion-walk tactic [V].** There are 34 `*_step` macros, 33 `*_effect` tables and 22 `*_close` macros. They differ only in a head-constant to lemma table and a closing simp set.
3. **Helpers are not re-unfolded inside facet proofs [V].** Facet proofs for `enter` and `op` use per-facet lemmas about `emit`, `pc`, `observe`, `copy`, `pair`, `patch`, `finish_op`. The cost is one lemma per helper per facet (observe 25, copy 17, pc 13, patch 13, pair 12, finish_op 10, emit about 24).
4. **`emit` already has three near-contracts [V]:** `Emitted` with `compiler_emit` (WP form), `compiler_emit_success` (inversion form), and `compiler_emit_available_frame` (availability form). Most facets ignore them and re-unfold.
5. **`op` breaks down as 204 dead-branch sites, 297 live-arm sites, 7 other [V].** The dead-branch sites are all `unfold op at h; rw [if_neg ..] at h`. No equation `op = observe` for the dead case exists, so one such lemma removes 204 sites.
6. **A pure equation `f ops c args = .ok (.Ok (), g c args)` is impossible for `emit` and `enter` [V].** `Budget.push` calls the abstract trait method `ops.reserve` (Funs:21159). `AllocCorrect` (`lean/Itasca/Runtime/Platform/Alloc.lean:12`) only says contents are preserved, so the answer is free.

## 1. Per-function catalog

### 1.1 `runtime.compiler.FunctionCompiler.emit`

**(a) Source and shape [V].** Rust: `src/runtime/compiler/mod.rs:635-643`. It does `self.pc()?; charge(Instructions)?; push(code, instruction)?; push(source_offsets, body_start + next_source)`. Lean: Funs:21413-21470 (def at 21415). The body is `pc`, `Budget.charge .Instructions`, `Budget.push` (code), a checked add, `Budget.push` (sources), with three `?` matches and four result paths. There is no match on `Instr`.

**(b) Theorems that unfold it [V]** (line is the theorem; "any" means arbitrary `status`):

| # | File:line | Theorem | Style | Conclusion | Facet |
|---|---|---|---|---|---|
| 1 | `L/Source/SourceCursor.lean:6` | `compiler_emit_cursor` | inversion, any, no law | `after.next_source = before.next_source` | cursor |
| 2 | `L/Callbacks/CodeGrowth/CompilerCodeMonotone.lean:13` | `compiler_emit_code_mono` | inversion, any, law | code length `≤` | monotonicity |
| 3 | `L/Callbacks/Metadata/CompilerOrdinaryResults.lean:35` | `compiler_emit_ordinary_result` | inversion, any, no law | `CompilerOrdinaryStable before after` | metadata |
| 4 | `L/Callbacks/Table/CompilerTablePreservation.lean:8` | `compiler_emit_tables` | inversion, any, no law | `CompilerTables.ofFunction` equal | tables |
| 5 | `L/Capacity/CapacityHelpers.lean:12` | `compiler_emit_capacity_metadata` | inversion, any, no law | `capacityMetadata` equal | capacity |
| 6 | `L/Capacity/EmissionFrameAvailability.lean:10` | `compiler_emit_available_frame` | postcondition, `AllocationAvailable` + 7 bounds | `out.1 = .Ok () ∧ ∃ used code sources, out.2 = {compiler with budget := {.. instructions := used}, function := {.. code, source_offsets}} ∧ ...` | acceptance |
| 7 | `L/Capacity/EmissionGrowth.lean:5` | `compiler_emit_code_success` | inversion, Ok, law | `code = before.code ++ [instruction]` | exact emission |
| 8 | `L/Capacity/EmissionGrowth.lean:65` | `compiler_emit_growth` | inversion, any, law | `after.len ≤ before.len + 1` | growth bound |
| 9 | `L/Lowering/Emission/Emit.lean:63` | `compiler_emit` (`@[step]`) | postcondition, law + 3 fit premises | `out.1 = .Ok () → Emitted compiler out.2 instruction` | exact emission and totality |
| 10 | `L/Relations/Control/BranchReachable.lean:8` | `compiler_emit_reachable` | inversion, any, no law | `reachable` equal | reachability |
| 11 | `L/Relations/Control/BranchSuccessEmit.lean:7` | `compiler_emit_success` | inversion, Ok, law | `Emitted before after instruction` | exact emission |
| 12 | `L/Relations/Emission/EmissionSources.lean:11` | `compiler_emit_source_length_success` | inversion, Ok, law | sources length + 1 | source lengths |
| 13 | `L/Relations/Table/BranchTableBuild.lean:22` | `compiler_emit_branch_height` | inversion, any, no law | `height` equal | height |
| 14 | `L/Relations/Table/TableDepths.lean:8` | `compiler_emit_depths` | inversion, any, no law | `table_depths` equal | scratch |

Derived without unfolding [V]:
- `compiler_emit_sources` and `_sources_result` (`L/Source/SourceLengths.lean:26`, `:125`), from #7 and #12.
- `compiler_emit_source_coordinates` and `_result` (`L/Coordinates/SourceCoordinateCallbacks.lean:139`, `:302`), from #7, #12, #9.
- `compiler_emit_code_strict_result` (`L/Coordinates/TableCallbackTargetBounds.lean:20`), from #11.
- `emit_paid` (private, `L/Callbacks/Control/FixupBranchPreservation.lean:7`), from #7.
- `emit_auxiliary_result` (private, `L/Capacity/SimdAuxiliaryGrowth.lean:8`), from #4.
- `compiler_emit_map_publication` (`L/Publication/OrdinaryMapPublication.lean:20`), from #3, #2, #1.
- `compiler_emit_available_effect` (`L/Capacity/CopyBudgetAvailability.lean:8`), from #6.

**(c) Predicates [V]:**
- `Emitted` (`L/Lowering/Emission/Emit.lean:54`): `after = {before with budget, function := {.. code, source_offsets}}`, code appended, coordinate appended. The budget is existential.
- `CompilerOrdinaryStable` (`L/Callbacks/Metadata/CompilerOrdinaryMetadata.lean:17`): `compilerMetadata`, `frames`, `controls` equal, and `slot_count` monotone.
- `CompilerStable` and `compilerMetadata` (`L/Callbacks/Metadata/CompilerMetadata.lean:23`, `:17`): the same over signatures, func_param_slots, batch_start, type_index, locals, param_slots, local_slots, body_start, body_end, local_offsets.
- `CompilerTables.ofFunction` (`L/Callbacks/Table/CompilerTables.lean:6`, `:17`): indirect, simd, v128_pool, jump_tables.
- `capacityMetadata` (`L/Capacity/CapacityHelpers.lean:9`): `(local_slots, slot_count)`.
- `SourceProgress` (`L/Source/SourceLengths.lean:7`): code and source_offsets grow by the same count.
- `SourceCoordinates` (`L/Coordinates/SourceCoordinateCallbacks.lean:18`): offsets inside the body interval, at most the cursor, pairwise ordered.
- `CompilationBudgetEffect` (`L/Capacity/BudgetEffects.lean:8`): limits and error equal, each counter grows by at most an allowance.

**(d) Existing full-effect theorems [V].** #9, #11 and #6 above. Usage counts including tactic tables: `compiler_emit` 32 uses / 20 files, `compiler_emit_success` 22 / 10, `compiler_emit_available_frame` 7 / 7. The other 11 theorems re-unfold. `compiler_emit_success` sits late in the import order (it imports `EmissionSources`, `ControlHeightSuccess`, `Copy`), so early files could not use it [I]. In-repo precedent for the target pattern: `ObserveFrame` and `compiler_observe_frame` (`L/Callbacks/Observation/Frame.lean:15`, `:18`), from which `compiler_observe_sources` is derived by `rw [frame]; rfl` (`SourceLengths.lean:35-43`).

### 1.2 `runtime.compiler.control.FunctionCompiler.enter`

**(a) Source and shape [V].** Rust: `src/runtime/compiler/control.rs:107-169`. Steps: reject an empty control stack; read the last ctrl; `block_signature`; `stack_height`; `source_start`; if `reachable && Then` then `operand(1)?` and `emit(JumpIfZero)?`; `pc()?`; if `reachable && Loop` then `emit(LoopHead)?`; `charge(Controls)?`; push a `ControlMap`; push a `Frame`; `observe(st)`.

Lean: Funs:33963-34826 (def at 33965), 862 lines. Aeneas duplicates the continuation, so there are 9 leaf paths and 35 `?` matches. Call occurrences: `Budget.push` 18, `Budget.charge` 9, `observe` 9, `emit` 4, `pc` 3, `operand` 1, `block_signature` 1, `stack_height` 1. `self.reachable && label` is extracted as nested `if`s, and `selfN.reachable` is re-read after `emit` (Funs:34023, 34307, 34571). `on_block`, `on_loop`, `on_if` are definitionally `enter` with a fixed kind; proofs pass `on_block` hypotheses to `enter` lemmas by `exact` (`L/Callbacks/Calls/CallbackCapacity.lean:96`).

**(b) Theorems that unfold it [V]:**

| # | File:line | Theorem | Style | Conclusion | Facet (tactic) |
|---|---|---|---|---|---|
| 1 | `L/Callbacks/Control/CompilerCodeMonotoneControl.lean:15` | `compiler_enter_code_mono` | inversion, Ok | code length `≤` | monotonicity (`code_mono_step`) |
| 2 | `L/Callbacks/Control/EnterBlock.lean:45` | `enter_block` `@[step]` | postcondition, `.Block`, live, 9 premises | `out.1=.Ok () →` code unchanged, reachable, `∃ height source`, frames and controls appended | exact effect |
| 3 | `L/Callbacks/Control/EnterIf.lean:6` | `enter_if` `@[step]` | postcondition, `.Then`, live, `CompilerLayout` | code `++ [.JumpIfZero cond U32.MAX]`, frame with `if_pc := some len`, map | exact effect |
| 4 | `L/Callbacks/Control/EnterLoop.lean:6` | `enter_loop` `@[step]` | postcondition, `.Loop`, live | code `++ [.LoopHead]`, frame, map | exact effect |
| 5 | `L/Callbacks/Fixups/FixupPreservation.lean:121` | `compiler_enter_fixup_budget` | inversion, Ok | `FixupBudget` before implies after | invariant (`fixup_step`) |
| 6 | `L/Callbacks/Function/EnterDead.lean:13` | `enter_dead` `@[step]` | postcondition, `reachable = false`, any kind | code unchanged, frame and map appended | exact effect |
| 7 | `L/Callbacks/Function/EnterSafety.lean:10` | `enter_if_raw` `@[step]` | postcondition, `.Then`, live, raw `conditionAt` | as #3 with `condition = conditionWord` | exact effect |
| 8 | `L/Callbacks/Function/EnterSafety.lean:115` | `enter_if_empty` (private) | postcondition | `⦃ _ => True ⦄` when `before.before = []` | totality |
| 9 | `L/Callbacks/Metadata/CompilerEnterMetadata.lean:15` | `compiler_enter_stable_result` | inversion, any | `CompilerStable` | metadata (`metadata_step`) |
| 10 | `L/Callbacks/Table/CompilerTableScratchControl.lean:6` | `compiler_enter_depths` | inversion, Ok | `table_depths` equal | scratch (`scratch_preservation_step`) |
| 11 | `L/Capacity/ControlCapacity.lean:6` | `compiler_enter_capacity` | inversion, Ok | `CapacityStep before after state` | capacity (`capacity_step`) |
| 12 | `L/Capacity/EnterAvailability.lean:169` | `compiler_enter_without_emission_available` | postcondition, `AllocationAvailable` + `ScopeDemand` | `out.1 = .Ok () ∧ CompilationBudgetEffect` (controls +1) | acceptance |
| 13 | `L/Capacity/ScopeAvailability.lean:21` | `compiler_enter_if_available` | postcondition | same, instructions and controls +1 | acceptance |
| 14 | `L/Capacity/ScopeAvailability.lean:108` | `compiler_enter_loop_available` | postcondition | same | acceptance |
| 15 | `L/Coordinates/ControlSourceCoordinates.lean:9` | `compiler_enter_source_coordinates` | inversion, Ok | `SourceCoordinates` before implies after | invariant (`coordinates_step`) |
| 16 | `L/Relations/Control/ControlCursor.lean:6` | `compiler_enter_cursor` | inversion, Ok | `after.next_source = state.pos` | cursor (`cursor_step`) |
| 17 | `L/Relations/Control/ControlEntrySuccess.lean:9` | `control_entry_coordinates` | inversion, Ok, no law | `local_slots + stackWords (take base vals) ≤ U32.max ∧ body_start + next_source ≤ Usize.max` | bounds implied by success |
| 18 | `L/Relations/Control/ControlObservation.lean:39` | `compiler_enter_observation` | inversion, Ok, no law | `∃ middle, observe ops middle state = .ok (.Ok (), after)` | intermediate state (`observation_step`) |
| 19 | `L/Relations/Control/ControlSources.lean:6` | `compiler_enter_sources` | inversion, Ok | `SourceProgress` | source lengths (`sources_step`) |
| 20 | `L/Relations/Table/ControlTablePreservation.lean:6` | `compiler_enter_tables` | inversion, Ok | `CompilerTables` equal | tables (`table_preservation_step`) |

Composed without unfolding [V]:
- `compiler_enter_total` (`L/Callbacks/Function/EnterSafety.lean:148`): proves `⦃ _ => True ⦄` by cases over #2, #4, #7, #8, #6, then inverts through #18 and `compiler_observe_stack`. Lines 189-196 are the in-repo precedent for "totality plus inversion gives a WP spec".
- `compiler_enter_available` (`L/Capacity/ScopeAvailability.lean:198`): cases over #12, #13, #14.
- `callback_block`, `callback_loop`, `callback_if`.
- `compiler_block_effects`, `compiler_loop_effects`, `compiler_if_effects` (`L/Callbacks/Control/ControlEffects.lean:36-66`).

**(c) Additional predicates [V]:**
- `CapacityStep` (`L/Capacity/CapacityHelpers.lean:236`): local_slots fixed, slot_count at most the max of the old value and the observed height.
- `FixupBudget` (`L/Callbacks/Fixups/FixupBudget.lean:14`): every frame's fixups length is at most the code length.
- `ObservedStack` (`L/Callbacks/Calls/CallbackSafety.lean:9`): `before` and `height` equal the observed offsets and height.
- `SignatureAt` (`L/Callbacks/Control/EnterBlock.lean:9`): relational result of `block_signature`.
- `ScopeDemand` (`L/Capacity/ScopeDemand.lean:9`) and `CallbackDemand` (`L/Capacity/CallbackAvailability.lean:11`): numeric preconditions for acceptance.
- `ControlMapPublication` (`L/Publication/ControlMapPublication.lean:21`): map ownership and bounds invariant.
- `ControlEffects` (`L/Callbacks/Control/ControlEffects.lean:22`): bundle of tables, depths, code_mono, fixups, capacity.

**(d) Existing full-effect theorems [V].** #2, #3, #4, #6, #7 are per-case, success-conditional effect specs. Each repeats the same roughly 20-line prologue and the same charge, push, push, observe suffix. They cover code, reachable, frames and controls. They do not cover budget, cursor, operand layout, or the frame condition on other fields. Consumers therefore combine them with separate facets. Example: `L/Publication/ScopeEntryPublication.lean:71-76` uses `enter_block`, `compiler_enter_stable_result`, `compiler_enter_code_mono` and `compiler_enter_cursor` on the same `called`. No theorem covers all kinds at once. Eleven facets (#1, #5, #9, #10, #11, #15-#20) unfold independently of the effect specs.

There is also a handwritten copy of the extracted suffix: `scopePublication` (`L/Capacity/EnterAvailability.lean:22`). It is connected by `change scopePublication ...` at `EnterAvailability.lean:214`, `ScopeAvailability.lean:75` and `:153`. Any edit to the Rust tail of `enter` breaks those `change`s.

### 1.3 `runtime.compiler.lower.FunctionCompiler.op`

**(a) Source and shape [V].** Rust: `src/runtime/compiler/lower.rs:105-321`, with `finish_op` at 95-98. Lean: Funs:21850-29065 (def at 21852), 7214 lines. Shape: `if self.reachable then match opcode with <448 literal arms> | _ => Err OutOfMemory else observe`. Call occurrences: `operand` 326, `simd_op` 256, `finish_op` 187, `make_scalar` 136, `scalar_binary` 136, `make_load` 14, `make_store` 9, `observe` 6, `copy` 3, `pair` 3, `width` 3, `top_is_v128` 1. There are 510 `?` matches.

**(b) The 261 theorems (508 sites) in 9 groups [V].** 369 sites are `unfold ... at h` (inversion), 139 are goal-side.

*G1. Per-opcode private rules for the 33 non-numeric opcodes* (`sourceCoordinateScalarOpcodes`, `L/Coordinates/ScalarSourceCoordinates.lean:11`). 99 theorems, 264 sites.
- `L/Publication/ScalarMapPublication.lean`: 33 theorems `scalar_maps_N`, 4 unfolds each. Representative (`:10`, `:16`): `ScalarMapRule ops N#u16 := ∀ before after state a b bits, ControlMapPublication before → before.next_source.val ≤ state.pos.val → op ops before state N#u16 a b bits = .ok (.Ok (), after) → ControlMapPublication after`. Each proof unfolds the body three times for stable, growth, cursor, plus once for the dead branch.
- `L/Coordinates/ScalarTargetEffects.lean`: 33 theorems, 3 unfolds each. Conclusion: `jump_tables` equal and code length monotone.
- `L/Coordinates/ScalarSourceCoordinates.lean`: 33 theorems, 1 unfold each. Conclusion: `SourceCoordinates after`.

*G2. Literal family, 8 opcodes (65, 66, 32, 33, 34, 16, 1, 26) times 7 facets.* 56 theorems, 112 sites. Each theorem restates a hand-copied arm body as `have run : op ... N#u16 ... = (do ...)`, proved by `unfold; rw [if_pos]; rfl`, then unfolds again for the dead branch. Representative: `compiler_op65_cursor` (`L/Lowering/Literal/LiteralCursor.lean:13`), inversion, `after.next_source = state.pos`. Files:
- `L/Lowering/Literal/LiteralCursor.lean`
- `L/Lowering/Literal/LiteralSources.lean`
- `L/Capacity/LiteralCapacity.lean`
- `L/Lowering/Table/LiteralTablePreservation.lean`
- `L/Callbacks/Table/CompilerTableScratchLiteral.lean`
- `L/Callbacks/Metadata/CompilerLiteralMetadata.lean`
- `L/Callbacks/CodeGrowth/CompilerCodeMonotoneLiteral.lean`

*G3. Class-level facets that use a dispatch equation for the live branch and unfold only for the dead branch.* 42 theorems, 42 sites. Representative: `compiler_numeric_cursor` (`L/Lowering/Integer/NumericEffects.lean:44`), inversion over `op ops before state (integerOpcode op) 0 0 0`, conclusion `after.next_source = state.pos`. Files and theorem counts:
- `L/Lowering/Integer/NumericEffects.lean` (4)
- `L/Lowering/Float/FloatEffects.lean` (4)
- `L/Relations/Emission/CoreLoweringEffects.lean` (4)
- `L/Relations/Stateful/StatefulEffects.lean` (4)
- `L/Relations/Calls/IndirectCallMetadata.lean` (4)
- `L/Lowering/Simd/SimdEffects.lean` (1; `compiler_lower_simd_effects` already returns the 4-facet conjunction)
- `L/Callbacks/CodeGrowth/CompilerCodeMonotoneScalar.lean` (3), `...Stateful.lean` (2), `L/Callbacks/Simd/CompilerCodeMonotoneSimd.lean` (1)
- `L/Callbacks/Table/CompilerTableScratchScalar.lean` (3), `...Stateful.lean` (2), `L/Callbacks/Simd/CompilerTableScratchSimd.lean` (1)
- `L/Lowering/Table/ScalarTablePreservation.lean` (3)
- `L/Relations/Table/StatefulAuxiliaryTables.lean` (2)
- `L/Lowering/Simd/SimdStaticTables.lean` (1)
- `L/Capacity/AuxiliaryGrowth.lean` (1), `StatefulAuxiliaryGrowth.lean` (1), `SimdAuxiliaryGrowth.lean` (1)

*G4. Dispatch and arm equations (goal-side unfolds).* 13 theorems, 28 sites. Shape: `op ops c st (classOpcode x) a b 0 = classLowering ops c st x`, proved by `cases x <;> unfold op <;> rw [if_pos reachable] <;> rfl`. The `classLowering` defs are hand-copied arm bodies.
- `lower_numeric_dispatch` (`L/Lowering/Integer/NumericLowering.lean:62`, def `numericLowering` `:15`)
- `lower_float_dispatch` (`L/Lowering/Float/FloatLowering.lean:55`)
- `lower_core_dispatch` (`L/Relations/Emission/CoreLoweringEffects.lean:53`)
- `lower_memory_load_dispatch`, `lower_memory_store_dispatch` (`L/Relations/Memory/MemoryEmission.lean:60`, `:115`)
- `lower_stateful_dispatch` (`L/Relations/Stateful/StatefulLowering.lean:275`)
- `lower_indirect_call_dispatch` (`L/Relations/Calls/IndirectCallLowering.lean:64`)
- `lower_global_get_eq`, `lower_global_set_eq` (`L/Relations/Global/GlobalLowering.lean:49`, `:67`)
- `lower_select_eq` (`L/Relations/Select/SelectLowering.lean:65`)
- `lower_empty_eq` (`L/Lowering/Emission/LoweringEmpty.lean:35`)
- `callback_float32_eq`, `callback_float64_eq` (`B/Reader/Float/FloatConstantLowering.lean:16`, `:24`)

`lower_simd_dispatch` (`L/Lowering/Simd/SimdDispatch.lean:9`) avoids `unfold`; see section 6.

*G5. `@[step]` lowering specs.* 5 theorems, 5 sites. Conclusion `out.1 = .Ok () → Lowered compiler out.2 instr stack`. `lower_const32`, `lower_const64` (`L/Lowering/Emission/Lowering.lean:59`, `:84`), `lower_call` (`L/Lowering/Calls/LoweringCall.lean:10`), `lower_local_get`, `lower_local_write` (`L/Lowering/Local/LoweringLocal.lean:44`, `:117`).

*G6. Totality and safety.* 21 theorems, 30 sites. Postcondition `out.1 = .Ok () → ObservedStack out.2 state.vals.val`. Representative: `compiler_numeric_total` (`L/Lowering/Integer/NumericSafety.lean:17`). Others:
- `L/Lowering/Float/FloatSafety.lean:7`
- `L/Lowering/Simd/SimdSafetyCallbacks.lean:105`
- `L/Relations/Calls/CallSafety.lean:10`, `:50`
- `L/Relations/Global/GlobalSafety.lean:31`, `:48`
- `L/Relations/Local/LocalSafety.lean:21`, `:69`
- `L/Relations/Memory/MemorySafety.lean:6`, `:30`
- `L/Relations/Select/SelectSafety.lean:44`
- `L/Relations/Stateful/StatefulSafety.lean:13`, `:47`
- `L/Lowering/Literal/LiteralSafety.lean` (6 theorems, 10 sites)
- `B/Reader/Safety/Run.lean:41`

*G7. Acceptance.* 15 theorems, 17 sites. Postcondition `out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget (instructions +1)` under `AllocationAvailable` and `CallbackDemand`. Representative: `compiler_global_get_available` (`L/Capacity/GlobalAvailability.lean:10`). Others:
- `L/Capacity/FinishBudgetAvailability.lean:34`, `:61`
- `L/Capacity/LiteralBudgetAvailability.lean:48`
- `L/Capacity/CallAvailability.lean:13`, `:69`
- `L/Capacity/GlobalAvailability.lean:30`
- `L/Capacity/MemoryAvailability.lean:9`, `:31`
- `L/Capacity/SelectAvailability.lean:9`, `:32`
- `L/Capacity/StatefulAvailability.lean:11`
- `L/Capacity/LocalVariableAvailability.lean:8`, `:65`, `:135`

*G8. Dead code and Body-level checking.* 10 theorems, 10 sites, all `unfold; rw [if_neg]`.
- `compiler_op_dead` (`L/Relations/Operations/DeadCode.lean:21`, postcondition `ObserveFrame`)
- `compiler_dead_op_frame` (`L/Callbacks/Metadata/CompilerDeadMetadata.lean:14`)
- `compiler_dead_source_coordinates` (`L/Coordinates/OrdinarySourceCoordinates.lean:10`)
- `compiler_dead_op_open_instructions` (`L/Checking/BranchCallbackInstructionPrefix.lean:62`)
- `compiler_dead_op_checked_prefix` (`L/Checking/DeadInstructionPrefix.lean:9`)
- `compiler_nop_drop_open_instructions` (`L/Checking/NoopInstructionPrefix.lean:9`)
- `StructuredCompilerPrefix.dead_op` (`B/Control/Table/StructuredCompilerPrefixObserve.lean:8`)
- `ReaderPost.simd_dead_prefix` (`B/Reader/Simd/Prefix.lean:20`)
- `StatefulReaderPost.instruction_prefix` (`B/Reader/Checking/StatefulInstructionPrefix.lean:21`)
- `SimdReaderEvent.instruction_prefix` (`B/Reader/Simd/SimdInstructionPrefix.lean:18`)

**(c) Additional predicates [V]:**
- `Lowered` (`L/Lowering/Emission/Lowering.lean:12`): code appended, `CompilerLayout after stack`, locals and reachable equal, slot_count monotone.
- `ObserveFrame` (`L/Callbacks/Observation/Frame.lean:15`).
- `AuxiliaryGrowth` (`L/Capacity/AuxiliaryGrowth.lean:12`): indirect, simd and pool growth each at most code growth.
- `compilerAuxiliaryTables` (`L/Callbacks/Table/CompilerAuxiliaryTables.lean:7`).
- `CompilerInstructionPrefix` (`L/Checking/OpenInstructionCompiler.lean:290`), `FrameExitSlotBounds` (`L/Checking/FrameExitSlotBounds.lean:9`).
- `OrdinaryEffects` (`L/Callbacks/Effects/OrdinaryEffects.lean:13`): bundle of tables, depths, code_mono, stable, capacity. It is assembled per callback in `B/Reader/Replay/OrdinaryEffects.lean` (659 lines) from separately proven facets.

**(d) Existing characterizations [V].** The G4 equations are the only ones. They cover numeric, float, select, global, memory, stateful, indirect call, simd and nop/drop. G3 uses them for the live branch. G1 and G2 (155 theorems, 376 sites) bypass them. G1 unfolds the full body and reduces the match with `coordinates_head`. G2 re-states arm bodies inline. No general lemma gives `reachable = false → op ... = observe ...`; `lower_empty_eq` covers only opcodes 1 and 26.

## 2. Custom tactics, macros, simprocs

No `declare_simp_like_tactic`, `register_simp_attr`, `syntax` or `declare_syntax_cat` exists under `C/` or `lean/Itasca/Support/` [V].

**Support [V]**
- `lean/Itasca/Support/Result.lean:15` `bind_ok_inv`: the theorem every walk uses. `(read >>= next) = .ok b → ∃ a, read = .ok a ∧ next a = .ok b`.
- `lean/Itasca/Support/LiteralDispatch.lean:19` `reduceLiteralDispatch`, with simprocs `reduceConvertTypes`, `reduceBinaryTypes`, `reduceVisitNumeric`, `reduceVisitMemory`, `reduceStepMemory`, `reduceStep` (`:30-35`): unfold a validator dispatcher when the opcode argument is a literal, with an `Eq.refl` proof.
- `:39` `reduceScalarMatcher`: reduces any single-discriminant matcher on a `UScalar` literal.
- These target `code.*`. None targets `lower.FunctionCompiler.op`.

**`coordinates_step` precisely** (`L/Coordinates/SourceCoordinateTactic.lean`) **[V]**
- `coordinates_close` (`:10`): `first | assumption | (simp_all [SourceCoordinates, compilerOrdinaryMetadata, compilerMetadata, snapshotCompiler, Prod.mk.injEq, source_unit_eq]; try omega)`.
- `coordinates_head h` (`:18`): requires `h : lhs = rhs`, computes `whnfCore lhs`, fails if unchanged, and replaces `h` via `changeLocalDecl`. The comment says it reduces only the outer opcode match so the inactive arms are never traversed.
- `coordinates_effect h using ops, law` (`:28`): reads the head constant of `h`'s left side and adds `have coordinates := <lemma> ... h (by coordinates_close) ...`. Table: `observe` → `compiler_observe_source_coordinates_result`; `emit` → `compiler_emit_source_coordinates_result`; `copy` → `compiler_copy_..._result`; `finish_op` → `compiler_finish_op_..._result`; `pair`, `pc`, `patch`, `on_end_loop0`, `on_end_loop1` → their `_source_coordinates` lemmas. It then runs `try metadata_effect` and `try cursor_effect` on the same hypothesis.
- `coordinates_step h using ops, law` (`:61`) is a `first` of, in order:
  1. `h` is `Result.ok _ = _`: close with `coordinates_close`.
  2. `coordinates_head h`.
  3. `dsimp only at h`, if it makes progress.
  4. `h` is a tail call to a known helper: `coordinates_effect h; coordinates_close`.
  5. Terminal again, after extracting `after = ...` with `cases`.
  6. `simp only [Std.uncurry, CoreOpsTry.branch, from_residual, FromSame, bind_ok, bind_tc_ok] at h`.
  7. `h` is a bind: `obtain ⟨value, called, rest⟩ := bind_ok_inv _ _ _ h`, rename `rest` back to `h`, split a pair `value`, `try coordinates_effect called`, `cases` the status, `simp only [uncurry_apply_pair] at h`.
  8. `sources_split h` (`split at h` when the head is `ite`, `dite` or a matcher).
- It is used as `repeat' coordinates_step called using ops, law`. Each step relies on hypotheses literally named `held`, `inside`, `forward` being in scope for `coordinates_close`.

**Shared walk helpers** (`L/Source/SourceLengthsTactic.lean`) **[V]**: `sources_nonterminal` (`:46`, head is `bind`), `sources_terminal` (`:53`, head is `Result.ok`), `sources_split` (`:60`), `source_unit_eq` (`:40`).

**Facet families [V].** Each is `X_effect` (head-constant table), `X_close` (closing simp set), `X_step` (the same eight-way `first` as above).

| Tactic stem | File:line of `_effect` | Facet |
|---|---|---|
| `sources` | `L/Source/SourceLengthsTactic.lean:9` | `SourceProgress` |
| `cursor` | `L/Source/SourceCursorTactic.lean:8` | `next_source` |
| `start_frame` | `L/Source/SourceStartFrame.lean:29` | `SourceStartFrame` through the locals loop |
| `metadata` | `L/Callbacks/Metadata/CompilerMetadataTactic.lean:18` | `CompilerOrdinaryStable` or `CompilerStable` |
| `metadata_control` | `L/Callbacks/Calls/CompilerCallbackMetadata.lean:9` | `metadata` plus `branch` |
| `code_mono` | `L/Callbacks/CodeGrowth/CompilerCodeMonotoneTactic.lean:14` | code length monotone |
| `strict_code` | `L/Coordinates/TableCallbackTargetBounds.lean:32` | `code_mono` plus strict growth on `emit` |
| `growth` | `L/Capacity/GrowthTactic.lean:11` | code length at most +1 |
| `growth_control` | `L/Callbacks/Calls/CallbackGrowth.lean:7` | `growth` plus `branch` |
| `capacity` | `L/Capacity/CapacityTactic.lean:8` | `capacityMetadata`, `CapacityStep` |
| `control_capacity` | `L/Callbacks/Calls/CallbackCapacity.lean:17` | `capacity` plus `branch` |
| `auxiliary_growth` | `L/Capacity/AuxiliaryGrowth.lean:58` | `AuxiliaryGrowth` |
| `simd_auxiliary` | `L/Capacity/SimdAuxiliaryGrowth.lean:52` | simd and pool growth |
| `table_preservation` | `L/Callbacks/Table/CompilerTableTactic.lean:8` | `CompilerTables` equal |
| `control_tables` | `L/Callbacks/Table/CallbackTables.lean:17` | plus `branch` |
| `auxiliary_tables` | `L/Callbacks/Table/CompilerAuxiliaryTables.lean:44` | `compilerAuxiliaryTables` equal |
| `scratch_preservation` | `L/Callbacks/Table/CompilerTableScratch.lean:128` | `table_depths` equal |
| `table_entry_metadata` | `L/Callbacks/Table/CompilerTableScratchEntry.lean:18` | locals loop |
| `depths` | `L/Relations/Table/TableDepths.lean:97` | `table_depths` (takes `ops` only) |
| `branch_height` | `L/Relations/Table/BranchTableBuild.lean:112` | `height` equal |
| `table_sources` | `L/Relations/Table/TableSources.lean:69` | `sources` through the table loop |
| `reachable` | `L/Relations/Control/BranchReachable.lean:107` | `reachable` equal |
| `maps` | `L/Relations/Control/ControlMapCounts.lean:17` | controls length |
| `observation` | `L/Relations/Control/ControlObservation.lean:8` (`observation_finish`), `:16` | exhibits the final `observe` call |
| `owners` | `L/Publication/BranchMapOwners.lean:36` | `activeControlMaps` |
| `fixup` | `L/Callbacks/Fixups/FixupPreservation.lean:57` | `FixupBudget` |
| `paid_fixup` | `L/Callbacks/Control/FixupBranchPreservation.lean:16` | `fixup` plus `emit_paid` |
| `coordinates` | `L/Coordinates/SourceCoordinateTactic.lean:28` | `SourceCoordinates` |
| `control_coordinates` | `L/Coordinates/CallbackSourceCoordinates.lean:22` | plus `branch` |
| `control_cursor` | `L/Callbacks/Calls/CallbackCursor.lean:17` | `cursor` plus `branch` |
| `control_sources` | `L/Callbacks/Calls/CallbackSources.lean:17` | `sources` plus `branch` |
| `environment_frame` | `L/Relations/Function/FunctionEnvironment.lean:24` | `FunctionEnvironment` through the locals loop |
| `indirect`, `control_indirect` | `L/Callbacks/Calls/CompilerIndirectTactic.lean:8`, `CallbackIndirect.lean:8` | unused; see section 6 |

Occurrence counts of the main `_step` macros across `C/`, definitions included: `code_mono_step` 92, `cursor_step` 56, `metadata_step` 54, `coordinates_step` 43, `auxiliary_tables_step` 36, `capacity_step` 25, `scratch_preservation_step` 25, `table_preservation_step` 21, `sources_step` 19.

**Others [V]**
- `simd_constructor_case` (local macro, `L/Lowering/Simd/SimdConstructor.lean:14`): checks one `make_simd` to constructor case by `change`, `subst`, `with_unfolding_all rfl`.
- `reader_opcode`, `reader_opcode_cases` (`L/Relations/Syntax/ReaderOpcode.lean:140`, `:150`): close `ReaderOpcode profile opcode` for a concrete byte by `decide +revert`.
- `stateful_capacity` (`L/Relations/Instructions/StatefulInstructionAcceptance.lean:18`): simp and `omega` closer for slot-capacity side goals.

## 3. How `enter`'s helpers are handled in facet proofs

Facet proofs use per-facet lemmas about helpers. They do not unfold `emit` again [V]. Three examples:

1. **Inversion facet.** `compiler_enter_source_coordinates` (`L/Coordinates/ControlSourceCoordinates.lean:17-18`) is `unfold enter at called; repeat' coordinates_step called using ops, law`. When the walk reaches `emit`, `coordinates_effect` applies `compiler_emit_source_coordinates_result` (`SourceCoordinateTactic.lean:37-39`). For `pc` it applies `compiler_pc_source_coordinates` (`:48`), for `observe` `compiler_observe_source_coordinates_result` (`:34`).
2. **Postcondition facet.** `enter_if` (`L/Callbacks/Control/EnterIf.lean`): `:55` `step with compiler_operand`, `:61` `step with compiler_emit ... codeFits offsetsFit sourceFits`, `:71` `rw [compiler_pc_eq ...]`, `:75` `step with charge_control`, `:83` and `:88` `step with budget_push`, `:94` `step with compiler_observe`.
3. **Acceptance facet.** `compiler_enter_if_available` (`L/Capacity/ScopeAvailability.lean`): `:62` `step with compiler_emit_available_frame`, `:71` `step with compiler_pc_available`, `:75` `change scopePublication ...`, `:88` `scope_publication_available`.

`Budget.charge`, `Budget.push`, `block_signature` and `stack_height` have no entry in most `_effect` tables. The walk binds their results opaquely, and the closing `simp_all` reads the unchanged fields off the final `{selfN with budget := .., frames := .., function := {.. controls := ..}}` literal. Only `fixup_effect` (`FixupPreservation.lean:57-72`) and `simd_auxiliary_effect` handle `Budget.push`.

## 4. How callers consume the `enter` facets

92 call sites in 28 files: Local 63 sites / 17 files, Body 29 sites / 11 files, Module 0 [V]. All 12 non-comment uses of `compiler_enter_stable_result` pass `(.Ok ())`, so the arbitrary-`status` generality is unused.

| Facet | Call sites |
|---|---|
| `compiler_enter_code_mono` (10) | `L/Coordinates/LoweringTargetBounds.lean:73`; `L/Checking/ScopeEntryInstructionPrefix.lean:29`; `L/Callbacks/Fixups/FixupPreservation.lean:128`; `L/Publication/ScopeEntryPublication.lean:75,110,147,181`; `L/Callbacks/Calls/CompilerCodeMonotoneCallbacks.lean:50,57,64` |
| `enter_block` (5) | `L/Callbacks/Control/EnterBlock.lean:154`; `L/Callbacks/Function/EnterSafety.lean:172`; `L/Checking/ScopeEntryInstructionPrefix.lean:32`; `L/Checking/ScopeEntryExitSlots.lean:19`; `L/Publication/ScopeEntryPublication.lean:71` |
| `enter_if` (4) | `L/Callbacks/Control/EnterIf.lean:142`; `ScopeEntryInstructionPrefix.lean:50`; `ScopeEntryExitSlots.lean:33`; `ScopeEntryPublication.lean:143` |
| `enter_loop` (5) | `L/Callbacks/Control/EnterLoop.lean:131`; `EnterSafety.lean:174`; `ScopeEntryInstructionPrefix.lean:39`; `ScopeEntryExitSlots.lean:26`; `ScopeEntryPublication.lean:106` |
| `enter_dead` (6) | `L/Callbacks/Calls/ScopeCallbackDead.lean:43,96,149`; `EnterSafety.lean:187`; `ScopeEntryInstructionPrefix.lean:73`; `ScopeEntryExitSlots.lean:40`; `ScopeEntryPublication.lean:177` |
| `enter_if_raw`, `enter_if_empty` (1 each) | `L/Callbacks/Function/EnterSafety.lean:183`, `:177` |
| `compiler_enter_total` (1) | `B/Reader/Control/EnterSafety.lean:278` |
| `compiler_enter_stable_result` (12) | `ScopeEntryInstructionPrefix.lean:28`; `ScopeEntryExitSlots.lean:16`; `ScopeEntryPublication.lean:74,109,146,180`; `B/Reader/Control/BlockPrefix.lean:59`, `BlockDormantPrefix.lean:56`, `LoopPrefix.lean:64`, `LoopDormantPrefix.lean:56`, `IfPrefix.lean:61`, `IfDormantPrefix.lean:56` |
| `compiler_enter_fixup_budget` (3) | `L/Callbacks/Control/ControlEffects.lean:44,55,66` |
| `compiler_enter_depths` (3) | `L/Callbacks/Table/CompilerTableScratchCallbacks.lean:50,57,64` |
| `compiler_enter_capacity` (3) | `L/Callbacks/Calls/CallbackCapacity.lean:96,103,110` |
| `compiler_enter_tables` (5) | `ScopeEntryInstructionPrefix.lean:27`; `LoweringTargetBounds.lean:72`; `L/Callbacks/Table/CallbackTables.lean:96,103,110` |
| `compiler_enter_source_coordinates` (1) | `ScopeEntryPublication.lean:248` |
| `compiler_enter_cursor` (10) | `ScopeEntryPublication.lean:76,111,148,182`; `B/Reader/Control/BlockPrefix.lean:65`, `BlockDormantPrefix.lean:58`, `LoopPrefix.lean:70`, `LoopDormantPrefix.lean:58`, `IfPrefix.lean:67`, `IfDormantPrefix.lean:58` |
| `compiler_enter_sources` (6) | the same six `B/Reader/Control/*Prefix.lean` files, lines 64, 57, 69, 57, 66, 57 |
| `control_entry_coordinates` (9) | the six `*Prefix.lean` files (lines 49, 46, 54, 46, 50, 46); `B/Reader/Control/EnterInstructionPrefixWasm2.lean:37`; `EnterExitSlotsWasm2.lean:37`; `EnterPublicationWasm2.lean:40` |
| `compiler_enter_observation` (2) | `L/Callbacks/Function/EnterSafety.lean:194`; `L/Relations/Control/ControlObservedLayout.lean:13` |
| availability (4) | `L/Capacity/ScopeAvailability.lean:223,228,230`; `B/Reader/Control/ReachedEnterAcceptance.lean:49` |

If the pilot keeps the facet theorem names and statements as corollaries of the contract, none of these 92 sites change. Only the roughly 18 defining files do.

## 5. Proposed contract forms

**Recommendation.** Use (ii), an effect structure with one inversion theorem, as the primary contract for `emit` and `enter`. Add one totality lemma and one availability lemma per function. Use (i), in the form of arm equations, for `op`. Keep (iii) as a derived layer.

Reasons [V unless noted]:
- Pure (i) cannot be stated for `emit` or `enter` (headline finding 6). Only the availability form is deterministic, and it has a different premise (`AllocationAvailable`, no `AllocCorrect`). `B/Reader/Control/ReachedEnterAcceptance.lean:20-49` carries `available` but no `law`, so acceptance cannot be derived from a law-based inversion contract.
- Consumers are mostly inversion style: 12 of 14 `emit` sites, 11 of 20 `enter` sites, 369 of 508 `op` sites. The repo already has this pattern in `Emitted`, `ObserveFrame`, `Lowered`.
- (iii) exists (`OrdinaryEffects`, `ControlEffects`, `compiler_lower_simd_effects`) but is assembled from separately proven facets. It cannot serve facets that need intermediate states (`compiler_enter_observation`, `control_entry_coordinates`). It should become a corollary, for example `Entered → ControlEffects`.
- A WP-form spec per function can be recovered from totality plus inversion with one generic lemma. `L/Callbacks/Function/EnterSafety.lean:189-196` does this inline.

**Facet classification for derivation:**
- *Frame facts* (field unchanged; immediate from an effect description): cursor, reachable, height, table_depths, `CompilerTables`, `capacityMetadata`, `CompilerStable`, `CompilerOrdinaryStable`.
- *Two-state arithmetic*: code monotone, growth at most +1, `SourceProgress`, `CapacityStep`, `AuxiliaryGrowth`, `CompilationBudgetEffect`.
- *Invariants `P before → P after`*: `SourceCoordinates`, `FixupBudget`, `ControlMapPublication`, `CompilerInstructionPrefix ∧ FrameExitSlotBounds`, and the Body-level `StructuredCompilerPrefix`. Transport lemmas already exist: `SourceCoordinates.advance`, `Emitted.source_coordinates`, `FixupBudget.ordinary`, `.mono`, `.push`, `ControlMapPublication.ordinary`, `.retained`, `.enter_effect` (used at `ScopeEntryPublication.lean:81`).
- *Not derivable from a success inversion*: totality (`⦃ _ => True ⦄`) and acceptance.

### Draft: `emit` (three traversals replace 14)

```lean
/-- Fields emit can touch, for any status. Needs no allocator law. -/
def EmitFrame {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  after = { before with
    budget := after.budget,
    function := { before.function with
      code := after.function.code, source_offsets := after.function.source_offsets } }

/-- Exact successful emission, budget included.
Same shape as the postcondition of `compiler_emit_available_frame`. -/
def EmittedExact {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (instruction : runtime.bytecode.Instr) : Prop :=
  ∃ used code sources,
    after = { before with
      budget := { before.budget with instructions := used },
      function := { before.function with code, source_offsets := sources } } ∧
    used.val = before.budget.instructions.val + 1 ∧
    code.val = before.function.code.val ++ [instruction] ∧
    sources.val.map (fun w => w.val) =
      before.function.source_offsets.val.map (fun w => w.val) ++
        [before.function.body_start.val + before.next_source.val]

theorem EmittedExact.emitted : EmittedExact before after i → Emitted before after i

structure EmitEffect {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError) : Prop where
  frame : EmitFrame before after
  limits : after.budget.limits = before.budget.limits
  code : after.function.code.val = before.function.code.val ∨
    after.function.code.val = before.function.code.val ++ [instruction]
  ok : status = .Ok () → EmittedExact before after instruction

/-- Law-free: serves cursor, reachable, height, depths, tables, capacity, ordinary_result. -/
theorem emit_frame {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status, after)) :
    EmitFrame before after

/-- The contract. Serves code_mono, growth, code_success, success, source_length_success. -/
theorem emit_effect {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status, after)) :
    EmitEffect before after instruction status

theorem emit_total {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (compiler : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.emit ops compiler instruction ⦃ _ => True ⦄

/-- Generic glue. Precedent: EnterSafety.lean:189-196. -/
theorem spec_of_total_inv {α : Type} {f : Result α} {P : α → Prop}
    (total : f ⦃ _ => True ⦄) (inv : ∀ out, f = .ok out → P out) : f ⦃ P ⦄
```

Notes:
- `emit_frame` must stay law-free because seven facets and `depths_step` take no `law`. It can be a second short traversal, or `emit_effect` can be split so the frame field needs no law.
- `after.budget = {before.budget with instructions := used}` holds on success without the law [I]. Reading Funs:21323-21341, 21367-21376, 21159-21173: `pc` returns `self` on Ok, `charge` sets only `instructions`, `push` returns the budget unchanged on Ok. The law is needed only for vector contents.
- Keep `Emitted` unchanged. It has 30 uses in 25 files, many destructured positionally.
- `compiler_emit_available_frame` stays as the third traversal, restated as `⦃ out => out.1 = .Ok () ∧ EmittedExact compiler out.2 instruction ⦄`.

### Draft: `enter` (three traversals replace 20, and `scopePublication` goes away)

```lean
def enterPrefix (reachable : Bool) (kind : Itasca.code.LabelKind) (condition : U32) :
    List runtime.bytecode.Instr :=
  match reachable, kind with
  | true, .Then => [.JumpIfZero condition core.num.U32.MAX]
  | true, .Loop => [.LoopHead]
  | _, _ => []

def enterIfPc (reachable : Bool) (kind : Itasca.code.LabelKind) (pc : Usize) : Option Usize :=
  match reachable, kind with
  | true, .Then => some pc
  | _, _ => none

/-- State after entry's emission and publication, before the final observation. -/
structure EnterPublished {A : Type} (before middle : runtime.compiler.FunctionCompiler A)
    (kind : Itasca.code.LabelKind) (ctrl : Itasca.code.Ctrl)
    (signature : runtime.compiler.Signature)
    (height startPc condition : U32) (source : Usize) : Prop where
  frame : middle = { before with
    budget := middle.budget, frames := middle.frames,
    function := { before.function with
      code := middle.function.code, source_offsets := middle.function.source_offsets,
      controls := middle.function.controls } }
  code : middle.function.code.val =
    before.function.code.val ++ enterPrefix before.reachable kind condition
  sources : middle.function.source_offsets.val.map (fun w => w.val) =
    before.function.source_offsets.val.map (fun w => w.val) ++
      (enterPrefix before.reachable kind condition).map
        (fun _ => before.function.body_start.val + before.next_source.val)
  startPc : startPc.val = middle.function.code.val.length
  controls : middle.function.controls.val = before.function.controls.val ++
    [⟨kind, source, 0#usize, UScalar.cast .Usize startPc, 0#usize,
      ctrl.value_stack_base, signature.params, signature.results⟩]
  frames : middle.frames.val = before.frames.val ++
    [⟨alloc.vec.Vec.len before.function.controls, kind, height, signature.param_slots,
      signature.result_slots, startPc,
      enterIfPc before.reachable kind (alloc.vec.Vec.len before.function.code),
      before.reachable, false, alloc.vec.Vec.new Usize⟩]
  limits : middle.budget.limits = before.budget.limits ∧ middle.budget.error = before.budget.error
  charged : middle.budget.controls.val = before.budget.controls.val + 1 ∧
    middle.budget.instructions.val = before.budget.instructions.val +
      (enterPrefix before.reachable kind condition).length ∧
    middle.budget.branches = before.budget.branches ∧
    middle.budget.locals = before.budget.locals

/-- The contract: successful entry is "publish, then observe". -/
theorem enter_effect {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (called : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt =
      .ok (.Ok (), after)) :
    ∃ prior ctrl signature height startPc condition source middle,
      state.ctrls.val = prior ++ [ctrl] ∧
      runtime.compiler.control.block_signature before.signatures bt = .ok signature ∧
      runtime.compiler.control.stack_height state.vals.deref ctrl.value_stack_base
        before.function.local_slots = .ok height ∧
      source.val = before.function.body_start.val + before.next_source.val ∧
      (before.reachable = true → kind = .Then →
        runtime.compiler.FunctionCompiler.operand ops before 1#usize = .ok (.Ok condition)) ∧
      EnterPublished before middle kind ctrl signature height startPc condition source ∧
      runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after)

theorem enter_total ...   -- premises of compiler_enter_total (EnterSafety.lean:148-166), ⦃ _ => True ⦄
theorem enter_available ... -- premises of compiler_enter_available (ScopeAvailability.lean:198-211)
```

Design points:
- Keep the pure helper calls (`block_signature`, `stack_height`, `operand`) as raw `= .ok _` equations. Consumers then apply the existing success lemmas: `control_stack_height_success` and `control_add_success` (`L/Relations/Control/ControlHeightSuccess.lean:17`, `:8`), `compiler_operand`, `compiler_condition`. This keeps the contract free of premises such as `valuesFit` or `CompilerLayout`, which the 11 inversion facets do not have.
- The frame and map literals match the existing statements field for field (`EnterBlock.lean:65-70`, `EnterIf.lean:31-37`, `EnterDead.lean:33-38`). `enter_block`, `enter_loop`, `enter_if`, `enter_if_raw`, `enter_dead` become `spec_of_total_inv` plus `simp [enterPrefix, enterIfPc]`.
- The remaining facets become `EnterPublished` plus the existing `compiler_observe_*` lemma for the final observe.
- `compiler_enter_observation` is the last conjunct. `control_entry_coordinates` follows from conjuncts 3 and 4.
- Success-only is enough (section 4). Requiring `law` is fine [V]: every caller of the two law-free facets (`control_entry_coordinates`, `compiler_enter_observation`) has `law` in scope, for example `B/Reader/Control/BlockPrefix.lean:49` and `:59`.

### Draft: `op` (form (i) as arm equations)

```lean
/-- Removes the 204 dead-branch unfold sites. -/
theorem op_dead {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (opcode : U16) (a b : U32) (bits : U128) (dead : before.reachable = false) :
    runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits =
      runtime.compiler.FunctionCompiler.observe ops before state
```

For the live branch, keep one equation per opcode class (the existing G4 lemmas, plus the eight literal arms now restated in 56 places), collected in one file that is the only place `op` is unfolded. Then prove one bundled effect per tail (`finish_op`, `observe`, `copy; observe`, `pair; finish_op`, `simd_op`) and derive all facets per class by rewriting with the arm equation. I would not start the pilot with a single universal `op` effect theorem: indirect calls and SIMD append to `indirect`, `simd`, `v128_pool`, so no one frame fits all arms [I].

## 6. What makes this hard

1. **Proof-term size for `op` [V].** The body is 7214 lines. `L/Lowering/Simd/SimdDispatch.lean:17-18` warns that letting `if_pos` infer both branches "retains the entire dispatcher in every proof term". That proof fixes the branches first and uses `interval_cases` with `maxRecDepth 32768`. `coordinates_head` exists for the same reason. Arm equations should be proved once, by `unfold; rw [if_pos]; rfl` or the `choose` trick.
2. **The 432-constructor `Instr` matcher [V].** `lean/Itasca/Runtime/Equations.lean` pre-generates equation lemmas because they are quadratic (about 45 MiB). `emit` and `enter` never match on `Instr`, so their contracts are safe. An `op` contract must keep `instruction` abstract and must not case on `Instr`. `Instr.retarget` (used by `patch`) is in the Equations list, which matters for a later `branch`/`on_end` pilot.
3. **Two allocator premises [V].** Inversion facets use `AllocCorrect`. Acceptance facets use `AllocationAvailable` with no `law`. Some facets and `depths_step` use neither. A contract that requires `law` forces signature changes in law-free facets and their tactic tables.
4. **Facets that depend on intermediate states [V].** `compiler_enter_observation` (the pre-observe state), `control_entry_coordinates` (arithmetic that must have succeeded), `enter_if` versus `enter_if_raw` (two descriptions of `operand(1)`), and the re-read of `reachable` after `emit` in the extracted body.
5. **Totality is a separate obligation [V].** Vec push at `Usize.max`, coordinate overflow and height overflow are `.fail`, not `Err`. `compiler_enter_total` currently proves totality by going through the five per-case effect specs, so reaching three traversals needs a direct totality proof. It also restricts `kind` to Block, Loop, Then (`EnterSafety.lean:166`).
6. **Hand-copied extracted bodies [V].** `scopePublication` (`EnterAvailability.lean:22`), `numericLowering`, `floatLowering`, `coreLowering`, `statefulLowering`, `indirectCallLowering`, and the 56 inline `run` equations in the Literal files. They are tied to extraction output by `rfl` or `change`, and break on any Rust edit, including reordering.
7. **Tactic tables fail silently [V by grep, not by build].** `_effect` runs under `try`. Several tables name lemmas that do not exist: `compiler_emit_indirect`, `compiler_copy_indirect`, `compiler_observe_indirect`, `compiler_finish_op_indirect`, `compiler_pc_indirect`, `compiler_patch_indirect`, `compiler_fixups_indirect`, `compiler_fixups_after_if_indirect`, `compiler_branch_indirect_result`, `compiler_finish_op_growth`, `compiler_simd_growth`. `indirect_step` and `control_indirect_step` have no uses outside their definitions, though `CallbackIndirect.lean` is imported by `B/Control/Control/CumulativePointControl.lean:19`. A renamed lemma during the refactor will show up as a slow or failing `repeat'`, not as a clear error.
8. **Hygiene-dependent tactics [V].** `_close` macros use hypotheses by literal name: `held`, `inside`, `forward` for coordinates; `budget`, `growth` in `fixup_step` (`FixupPreservation.lean:103`). `_effect` introduces fixed names (`effect`, `coordinates`, `metadataEq`, `capacity`, `framesEq`). Proofs often finish with `all_goals try (casesm* core.result.Result Never _ <;> try casesm* Never)` and a second `repeat'`.
9. **Heartbeats [V].** Occurrences in `C/`: 118 at 2,000,000; 39 at 4,000,000; 7 at 8,000,000; `maxRecDepth 4096` in 255 places. The `op` facet files are at 2M to 4M, and `FixupBranchPreservation.lean` is at 8M. A contract proof for `enter` (9 leaf paths, 35 `?`) will be the heaviest single proof in the pilot [I]. Proving the shared publication suffix once as its own lemma, then the three prefixes, avoids walking the suffix nine times.
10. **Private lemmas [V].** There are 279 `private` declarations in 79 files under `C/`. Relevant ones: `enter_if_empty`, `emit_paid`, `emit_auxiliary_result`, `index_frame`, `push_fixup`, `popped_frames`, and all 99 `scalar_*_N` rules.
11. **Import order [V for `compiler_emit_success`, I for the layout].** The contract file must sit as low as `L/Lowering/Emission/Emit.lean`, which imports only `LayoutProofs` and `CompileInv`. `compiler_emit_success` lives in `L/Relations/Control/` and imports `InitializerExpression` (for `budget_push_success`) and `ControlHeightSuccess`. Moving `budget_push_success` and `control_add_success` down next to `budget_push` (`L/Relations/Layout/LayoutProofs.lean:32`) is a prerequisite.
12. **Whether failure-path facts are consumed [not verified].** 160 theorem signatures in 56 files take an arbitrary `status`. The step tactics need that for helpers, because `_effect` runs before the status is case-split. I confirmed only for `compiler_enter_stable_result` that top-level callers always pass `.Ok ()`. I did not check `op`-level and callback-level any-status theorems such as `compiler_numeric_ordinary_result`.
