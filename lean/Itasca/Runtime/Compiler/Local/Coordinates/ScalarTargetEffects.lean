import Itasca.Runtime.Compiler.Local.Lowering.Control.UnreachableContracts
import Itasca.Runtime.Compiler.Local.Coordinates.ControlSourceCoordinates
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableSafetyEffects
import Itasca.Runtime.Compiler.Local.Coordinates.ScalarSourceCoordinates
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdDispatch
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.CompilerCodeMonotoneLiteral

/-!
Sections, each formerly its own module: TableSourceCoordinates, NumericSourceCoordinates, SimdSourceCoordinates, CallbackSourceCoordinates, ScalarTargetEffects.
-/

/-! ## TableSourceCoordinates -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Every separately streamed label retains the complete coordinate vector
and cursor, including the labels collected by the Wasm 1 reader. -/
theorem compiler_table_label_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (held : SourceCoordinates before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops before state depth = .ok (.Ok (),after)) : SourceCoordinates after := by
  obtain ⟨budget,depths,frame,_⟩ := compiler_table_label_success ops law before after state depth called
  simpa only [SourceCoordinates,frame] using held

/-- Each actual table stub retains the source origin while adding its branch. -/
theorem compiler_table_branch_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (lookup : before.table_depths.val[index.val]? = some depth)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (called : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    SourceCoordinates after := by
  obtain ⟨target,budget,table,_,_,branch⟩ := compiler_table_branch_success ops law before after index depth lookup called
  let staged := {before with budget,function := {before.function with jump_tables := table}}
  change runtime.compiler.control.FunctionCompiler.branch ops staged depth 1#u32 false = .ok (.Ok (),after) at branch
  exact compiler_branch_source_coordinates ops law staged after depth 1#u32 false
    (by simpa only [SourceCoordinates,staged] using held) (by simpa only [staged] using inside) branch

/-- Finite table lowering retains one source origin for all of its stubs. -/
theorem TableBranchRun.source_coordinates {A : Type} {ops : runtime.platform.Alloc A}
    (law : Platform.AllocCorrect ops) {before after : runtime.compiler.FunctionCompiler A}
    {index : Nat} (run : TableBranchRun ops before index after) :
    SourceCoordinates before →
    before.function.body_start.val+before.next_source.val < before.function.body_end.val →
    SourceCoordinates after ∧ after.next_source = before.next_source := by
  induction run with
  | done => intro held _; exact ⟨held,rfl⟩
  | @cons before middle after index inbounds called rest ih =>
    intro held inside
    let depth := before.table_depths.val[index.val]
    have lookup : before.table_depths.val[index.val]? = some depth := List.getElem?_eq_getElem inbounds
    have coordinates := compiler_table_branch_source_coordinates ops law before middle index depth lookup held inside called
    have cursor := compiler_table_branch_cursor ops law before middle index depth lookup called
    obtain ⟨_,_,_,_,_,_,_,start,finish,_⟩ := (compiler_table_branch_fixed ops law before middle index depth lookup called).stable.fields
    obtain ⟨final,finalCursor⟩ := ih coordinates (by rw [start,finish,cursor]; exact inside)
    exact ⟨final,finalCursor.trans cursor⟩

/-- The dispatch instruction and every target stub preserve the coordinate
invariant of the actual table lowerer, with no loop-acceptance assumption. -/
theorem compiler_lower_table_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (called : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before = .ok (.Ok (),after)) :
    SourceCoordinates after ∧ after.next_source = before.next_source := by
  obtain ⟨start,len,selector,emitted,_,_,_,emission,run⟩ := compiler_lower_table_success ops law before after called
  have coordinates := emission.source_coordinates held inside
  obtain ⟨budget,code,sources,frame,_,_⟩ := emission
  obtain ⟨final,cursor⟩ := run.source_coordinates law coordinates (by simpa only [frame] using inside)
  exact ⟨final,by simpa only [frame] using cursor⟩

/-- Collecting labels changes budget and scratch only; final dispatch and
observation preserve the actual source-coordinate publication bounds. -/
theorem compiler_br_table_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types = .ok (.Ok (),after)) : SourceCoordinates after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table at called
  obtain ⟨⟨result,labeled⟩,labelCalled,rest⟩ := bind_ok_inv _ _ _ called
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok unit =>
    cases unit
    obtain ⟨budget,depths,frame,_⟩ := compiler_table_label_success ops law before labeled state fallback labelCalled
    have coordinates : SourceCoordinates labeled := by simpa only [SourceCoordinates,frame] using held
    have cursor : labeled.next_source = before.next_source := by rw [frame]
    have active : labeled.function.body_start.val+labeled.next_source.val < labeled.function.body_end.val := by
      simpa only [frame] using inside
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
    split at rest
    · obtain ⟨⟨result,lowered⟩,lowerCalled,rest⟩ := bind_ok_inv _ _ _ rest
      cases result with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok unit =>
        cases unit
        obtain ⟨loweredCoordinates,loweredCursor⟩ :=
          compiler_lower_table_source_coordinates ops law labeled lowered coordinates active lowerCalled
        simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
        obtain ⟨cleared,_,observed⟩ := bind_ok_inv _ _ _ rest
        exact compiler_observe_source_coordinates ops law {lowered with reachable := false,table_depths := cleared} after state
          (by simpa only [SourceCoordinates] using loweredCoordinates)
          (by simpa only [loweredCursor,cursor] using forward) observed
    · obtain ⟨cleared,_,observed⟩ := bind_ok_inv _ _ _ rest
      exact compiler_observe_source_coordinates ops law {labeled with table_depths := cleared} after state
        (by simpa only [SourceCoordinates] using coordinates) (by simpa only [cursor] using forward) observed

end Itasca.Runtime.Compiler

end

/-! ## NumericSourceCoordinates -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Actual numeric lowering preserves source coordinates through
its checked descriptor dispatch, independently of source operand typing. -/
theorem compiler_numeric_dispatch_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : SourceMachine.Numeric.Instruction)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (integerOpcode op) 0#u32 0#u32 0#u128 =
      .ok (.Ok (),after)) : SourceCoordinates after := by
  by_cases live : before.reachable = true
  · rw [lower_numeric_dispatch ops before state op live] at called
    unfold numericLowering at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

/-- Actual float lowering preserves source coordinates through
its checked descriptor dispatch, independently of source operand typing. -/
theorem compiler_float_dispatch_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : SourceMachine.Float.Instruction)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (floatOpcode op) 0#u32 0#u32 0#u128 =
      .ok (.Ok (),after)) : SourceCoordinates after := by
  by_cases live : before.reachable = true
  · rw [lower_float_dispatch ops before state op live] at called
    unfold floatLowering at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

/-- Actual memory load lowering preserves source coordinates through
its checked descriptor dispatch, independently of source operand typing. -/
theorem compiler_memory_load_dispatch_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : SourceMachine.Memory.Load) (offset alignment : U32)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (memoryLoadOpcode op) offset alignment 0#u128 =
      .ok (.Ok (),after)) : SourceCoordinates after := by
  by_cases live : before.reachable = true
  · rw [lower_memory_load_dispatch ops before state op offset alignment live] at called
    unfold memoryLoadLowering at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

/-- Actual memory store lowering preserves source coordinates through
its checked descriptor dispatch, independently of source operand typing. -/
theorem compiler_memory_store_dispatch_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : SourceMachine.Memory.Store) (offset alignment : U32)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (memoryStoreOpcode op) offset alignment 0#u128 =
      .ok (.Ok (),after)) : SourceCoordinates after := by
  by_cases live : before.reachable = true
  · rw [lower_memory_store_dispatch ops before state op offset alignment live] at called
    unfold memoryStoreLowering at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

end Itasca.Runtime.Compiler

end

/-! ## SimdSourceCoordinates -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Actual SIMD allocation, construction, emission, and observation retain
ordered source coordinates, including constants, shuffles, and memory lanes. -/
theorem compiler_simd_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a : U32) (bits : U128)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.simd.FunctionCompiler.simd_op ops before state opcode a bits = .ok (.Ok (),after)) :
    SourceCoordinates after := by
  unfold runtime.compiler.simd.FunctionCompiler.simd_op at called
  repeat' coordinates_step called using ops, law

/-- The actual ordinary dispatcher preserves coordinates for the entire SIMD
interval, including its unreachable path. -/
theorem compiler_simd_op_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (lower : 512 ≤ opcode.val) (upper : opcode.val < 768)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    SourceCoordinates after := by
  by_cases live : before.reachable = true
  · rw [lower_simd_dispatch ops before state opcode a b bits live lower upper] at called
    exact compiler_simd_source_coordinates ops law before after state opcode a bits held inside forward called
  · exact compiler_dead_source_coordinates ops law before after state opcode a b bits
      (by cases h : before.reachable <;> simp_all) held forward called

end Itasca.Runtime.Compiler

end

/-! ## CallbackSourceCoordinates -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

theorem compiler_branch_source_coordinates_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool) (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status,after))
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val) :
    status = .Ok () → SourceCoordinates after := by
  intro accepted
  subst status
  exact compiler_branch_source_coordinates ops law before after depth skip conditional held inside called

open Lean Meta Elab Tactic in
elab "control_coordinates_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  if lhs.getAppFn.constName? = some ``runtime.compiler.control.FunctionCompiler.branch then
    evalTactic (← `(tactic| have coordinates := compiler_branch_source_coordinates_result $ops $law _ _ _ _ _ _ $h
      (by coordinates_close) (by coordinates_close)))
    evalTactic (← `(tactic| have cursor := compiler_branch_cursor_result $ops $law _ _ _ _ _ _ $h))
    evalTactic (← `(tactic| have stable := compiler_branch_stable_result $ops $law _ _ _ _ _ _ $h))
    evalTactic (← `(tactic| have metadataEq := stable.metadata))
  else
    evalTactic (← `(tactic| coordinates_effect $h using $ops, $law))

macro "control_coordinates_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; coordinates_close)
  | coordinates_head $h
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (control_coordinates_effect $h using $ops, $law; coordinates_close)
  | solve | (sources_terminal $h; have output := (Prod.mk.inj (Result.ok.injEq.mp $h)).2; cases output; coordinates_close)
  | (fail_if_no_progress simp only [Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame,bind_ok,bind_tc_ok] at $h:ident)
  | (sources_nonterminal $h
     obtain ⟨value,called,rest⟩ := bind_ok_inv _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue,secondValue⟩)
     | skip
     try control_coordinates_effect called using $ops, $law
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | sources_split $h)

/-- The actual unreachable callback retains source-coordinate publication bounds. -/
theorem compiler_unreachable_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
      ops before state = .ok (.Ok (),after)) : SourceCoordinates after := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable.inv ops before after state (.Ok ()) called with
  | dead dead observed => exact compiler_observe_source_coordinates ops law before after state held forward observed
  | @emitted middle _ _ live emitted observed =>
    have coordinates := compiler_emit_source_coordinates ops law before middle .Unreachable held inside emitted
    have cursor := compiler_emit_cursor ops before middle .Unreachable (.Ok ()) emitted
    exact compiler_observe_source_coordinates ops law {middle with reachable := false} after state coordinates
      (by simpa only [cursor] using forward) observed

/-- The actual return callback retains source-coordinate publication bounds. -/
theorem compiler_return_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
      ops before state = .ok (.Ok (),after)) : SourceCoordinates after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return at called
  repeat' control_coordinates_step called using ops, law

/-- The actual br callback retains source-coordinate publication bounds. -/
theorem compiler_br_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (resultType : Itasca.signature.ResultType)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth resultType = .ok (.Ok (),after)) : SourceCoordinates after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br at called
  repeat' control_coordinates_step called using ops, law

/-- The actual br_if callback retains source-coordinate publication bounds. -/
theorem compiler_br_if_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (resultType : Itasca.signature.ResultType)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth resultType = .ok (.Ok (),after)) : SourceCoordinates after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at called
  repeat' control_coordinates_step called using ops, law

end Itasca.Runtime.Compiler

end

/-! ## ScalarTargetEffects -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

private def ScalarTargetEffects {A : Type} (ops : runtime.platform.Alloc A) (opcode : U16) : Prop :=
  ∀ (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (a b : U32) (bits : U128),
    runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after) →
      after.function.jump_tables.val = before.function.jump_tables.val ∧
      before.function.code.val.length ≤ after.function.code.val.length

private theorem scalar_target_effects_0 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 0#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_1 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 1#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_16 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 16#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_17 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 17#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_26 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 26#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_27 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 27#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_28 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 28#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_32 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 32#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_33 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 33#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_34 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 34#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_35 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 35#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_36 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 36#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_37 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 37#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_38 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 38#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_63 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 63#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_64 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 64#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_65 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 65#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_66 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 66#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_67 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 67#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_68 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 68#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_208 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 208#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_209 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 209#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_210 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 210#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_264 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 264#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_265 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 265#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_266 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 266#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_267 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 267#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_268 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 268#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_269 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 269#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_270 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 270#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_271 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 271#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_272 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 272#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_273 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 273#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

/-- Nonnumeric ordinary lowering preserves the complete jump table and grows
code monotonically, independently of every immediate and source stack. -/
theorem compiler_scalar_target_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (supported : opcode ∈ sourceCoordinateScalarOpcodes)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    after.function.jump_tables.val = before.function.jump_tables.val ∧
      before.function.code.val.length ≤ after.function.code.val.length := by
  simp only [sourceCoordinateScalarOpcodes,List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact scalar_target_effects_0 ops law before after state a b bits called
  · exact scalar_target_effects_1 ops law before after state a b bits called
  · exact scalar_target_effects_16 ops law before after state a b bits called
  · exact scalar_target_effects_17 ops law before after state a b bits called
  · exact scalar_target_effects_26 ops law before after state a b bits called
  · exact scalar_target_effects_27 ops law before after state a b bits called
  · exact scalar_target_effects_28 ops law before after state a b bits called
  · exact scalar_target_effects_32 ops law before after state a b bits called
  · exact scalar_target_effects_33 ops law before after state a b bits called
  · exact scalar_target_effects_34 ops law before after state a b bits called
  · exact scalar_target_effects_35 ops law before after state a b bits called
  · exact scalar_target_effects_36 ops law before after state a b bits called
  · exact scalar_target_effects_37 ops law before after state a b bits called
  · exact scalar_target_effects_38 ops law before after state a b bits called
  · exact scalar_target_effects_63 ops law before after state a b bits called
  · exact scalar_target_effects_64 ops law before after state a b bits called
  · exact scalar_target_effects_65 ops law before after state a b bits called
  · exact scalar_target_effects_66 ops law before after state a b bits called
  · exact scalar_target_effects_67 ops law before after state a b bits called
  · exact scalar_target_effects_68 ops law before after state a b bits called
  · exact scalar_target_effects_208 ops law before after state a b bits called
  · exact scalar_target_effects_209 ops law before after state a b bits called
  · exact scalar_target_effects_210 ops law before after state a b bits called
  · exact scalar_target_effects_264 ops law before after state a b bits called
  · exact scalar_target_effects_265 ops law before after state a b bits called
  · exact scalar_target_effects_266 ops law before after state a b bits called
  · exact scalar_target_effects_267 ops law before after state a b bits called
  · exact scalar_target_effects_268 ops law before after state a b bits called
  · exact scalar_target_effects_269 ops law before after state a b bits called
  · exact scalar_target_effects_270 ops law before after state a b bits called
  · exact scalar_target_effects_271 ops law before after state a b bits called
  · exact scalar_target_effects_272 ops law before after state a b bits called
  · exact scalar_target_effects_273 ops law before after state a b bits called

end Itasca.Runtime.Compiler

end
