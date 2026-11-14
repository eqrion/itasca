import Itasca.Runtime.Compiler.Local.Callbacks.Control.BranchTableCallbacks
import Itasca.Runtime.Compiler.Local.Callbacks.Control.BranchCallbacks
import Itasca.Runtime.Compiler.Local.Lowering.Control.ReturnContracts
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
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table.inv ops before after state fallback types (.Ok ()) called with
  | @live labeled lowered cleared _ _ labelCall live lowerCall clearCall observed =>
    have frame := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.inv ops before labeled state fallback (.Ok ()) labelCall).frame
    have coordinates : SourceCoordinates labeled := by
      rw [frame]
      exact held
    have cursor : labeled.next_source = before.next_source := by rw [frame]
    have active : labeled.function.body_start.val + labeled.next_source.val < labeled.function.body_end.val := by
      rw [frame]
      exact inside
    obtain ⟨loweredCoordinates, loweredCursor⟩ := compiler_lower_table_source_coordinates ops law labeled lowered coordinates active lowerCall
    exact compiler_observe_source_coordinates ops law {lowered with reachable := false, table_depths := cleared} after state
      (by simpa only [SourceCoordinates] using loweredCoordinates) (by simpa only [loweredCursor, cursor] using forward) observed
  | @dead labeled cleared _ _ labelCall dead clearCall observed =>
    have frame := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.inv ops before labeled state fallback (.Ok ()) labelCall).frame
    have coordinates : SourceCoordinates labeled := by
      rw [frame]
      exact held
    have cursor : labeled.next_source = before.next_source := by rw [frame]
    exact compiler_observe_source_coordinates ops law {labeled with table_depths := cleared} after state
      (by simpa only [SourceCoordinates] using coordinates) (by simpa only [cursor] using forward) observed

end Itasca.Runtime.Compiler

end

/-! ## NumericSourceCoordinates -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

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
  obtain ⟨staged, instruction, allocated, finished⟩ :=
    (runtime.compiler.simd.FunctionCompiler.simd_op.inv ops before after state opcode a bits (.Ok ()) called).execution.success
  have frame := allocated.frame
  apply compiler_finish_op_source_coordinates ops law staged after state instruction ?_ ?_ ?_ finished
  · rw [frame]
    exact held
  · rw [frame]
    exact inside
  · rw [frame]
    exact forward

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
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return.inv ops before after state (.Ok ()) called with
  | dead dead observed => exact compiler_observe_source_coordinates ops law before after state held forward observed
  | @emitted frame source middle _ _ live selected position emitted observed =>
    have coordinates := compiler_emit_source_coordinates ops law before middle (.Return source frame.results) held inside emitted
    have cursor := compiler_emit_cursor ops before middle (.Return source frame.results) (.Ok ()) emitted
    exact compiler_observe_source_coordinates ops law {middle with reachable := false} after state coordinates
      (by simpa only [cursor] using forward) observed

/-- The actual br callback retains source-coordinate publication bounds. -/
theorem compiler_br_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (resultType : Itasca.signature.ResultType)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth resultType = .ok (.Ok (),after)) : SourceCoordinates after := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br.inv ops before after state depth resultType (.Ok ()) called with
  | dead dead observed => exact compiler_observe_source_coordinates ops law before after state held forward observed
  | @branched middle _ _ live branched observed =>
    have kept := compiler_branch_source_coordinates ops law before middle depth 0#u32 false held inside branched
    have cursor := compiler_branch_cursor ops law before middle depth 0#u32 false branched
    exact compiler_observe_source_coordinates ops law {middle with reachable := false} after state
      kept (by simpa only [cursor] using forward) observed

/-- The actual br_if callback retains source-coordinate publication bounds. -/
theorem compiler_br_if_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (resultType : Itasca.signature.ResultType)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth resultType = .ok (.Ok (),after)) : SourceCoordinates after := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if.inv ops before after state depth resultType (.Ok ()) called with
  | dead dead observed => exact compiler_observe_source_coordinates ops law before after state held forward observed
  | @branched middle _ _ live branched observed =>
    have kept := compiler_branch_source_coordinates ops law before middle depth 1#u32 true held inside branched
    have cursor := compiler_branch_cursor ops law before middle depth 1#u32 true branched
    exact compiler_observe_source_coordinates ops law middle after state
      kept (by simpa only [cursor] using forward) observed

end Itasca.Runtime.Compiler

end

/-! ## ScalarTargetEffects -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

private def ScalarTargetEffects {A : Type} (ops : runtime.platform.Alloc A) (opcode : U16) : Prop :=
  ∀ (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (a b : U32) (bits : U128),
    runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after) →
      after.function.jump_tables.val = before.function.jump_tables.val ∧
      before.function.code.val.length ≤ after.function.code.val.length

private theorem scalar_target_group_0 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (opcode : U16)
    (supported : opcode ∈ [0#u16, 1#u16, 16#u16, 17#u16, 26#u16, 27#u16]) : ScalarTargetEffects ops opcode := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro before after state a b bits called
    by_cases live : before.reachable = true
    · first
      | rw [runtime.compiler.lower.FunctionCompiler.op.unreachable ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.nop ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.call ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.call_indirect ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.drop ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.select ops before state 27#u16 a b bits live (by decide)] at called
      constructor
      · repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
      · repeat' first | coordinates_head called | code_mono_step called using ops, law
    · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
      exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
        compiler_observe_code_mono ops law before after state (.Ok ()) called⟩
private theorem scalar_target_group_1 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (opcode : U16)
    (supported : opcode ∈ [28#u16, 32#u16, 33#u16, 34#u16, 35#u16, 36#u16]) : ScalarTargetEffects ops opcode := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro before after state a b bits called
    by_cases live : before.reachable = true
    · first
      | rw [runtime.compiler.lower.FunctionCompiler.op.select ops before state 28#u16 a b bits live (by decide)] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.local_get ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.local_set ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.local_tee ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.global_get ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.global_set ops before state a b bits live] at called
      constructor
      · repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
      · repeat' first | coordinates_head called | code_mono_step called using ops, law
    · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
      exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
        compiler_observe_code_mono ops law before after state (.Ok ()) called⟩
private theorem scalar_target_group_2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (opcode : U16)
    (supported : opcode ∈ [37#u16, 38#u16, 63#u16, 64#u16, 65#u16, 66#u16]) : ScalarTargetEffects ops opcode := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro before after state a b bits called
    by_cases live : before.reachable = true
    · first
      | rw [runtime.compiler.lower.FunctionCompiler.op.table_get ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.table_set ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.memory_size ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.memory_grow ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.i32_const ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.i64_const ops before state a b bits live] at called
      constructor
      · repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
      · repeat' first | coordinates_head called | code_mono_step called using ops, law
    · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
      exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
        compiler_observe_code_mono ops law before after state (.Ok ()) called⟩
private theorem scalar_target_group_3 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (opcode : U16)
    (supported : opcode ∈ [67#u16, 68#u16, 208#u16, 209#u16, 210#u16, 264#u16]) : ScalarTargetEffects ops opcode := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro before after state a b bits called
    by_cases live : before.reachable = true
    · first
      | rw [runtime.compiler.lower.FunctionCompiler.op.f32_const ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.f64_const ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.ref_null ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.ref_is_null ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.ref_func ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.memory_init ops before state a b bits live] at called
      constructor
      · repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
      · repeat' first | coordinates_head called | code_mono_step called using ops, law
    · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
      exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
        compiler_observe_code_mono ops law before after state (.Ok ()) called⟩
private theorem scalar_target_group_4 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (opcode : U16)
    (supported : opcode ∈ [265#u16, 266#u16, 267#u16, 268#u16, 269#u16, 270#u16]) : ScalarTargetEffects ops opcode := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro before after state a b bits called
    by_cases live : before.reachable = true
    · first
      | rw [runtime.compiler.lower.FunctionCompiler.op.data_drop ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.memory_copy ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.memory_fill ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.table_init ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.elem_drop ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.table_copy ops before state a b bits live] at called
      constructor
      · repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
      · repeat' first | coordinates_head called | code_mono_step called using ops, law
    · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
      exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
        compiler_observe_code_mono ops law before after state (.Ok ()) called⟩
private theorem scalar_target_group_5 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (opcode : U16)
    (supported : opcode ∈ [271#u16, 272#u16, 273#u16]) : ScalarTargetEffects ops opcode := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl
  all_goals
    intro before after state a b bits called
    by_cases live : before.reachable = true
    · first
      | rw [runtime.compiler.lower.FunctionCompiler.op.table_grow ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.table_size ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.table_fill ops before state a b bits live] at called
      constructor
      · repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
      · repeat' first | coordinates_head called | code_mono_step called using ops, law
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
  all_goals
    first
    | exact scalar_target_group_0 ops law _ (by decide) before after state a b bits called
    | exact scalar_target_group_1 ops law _ (by decide) before after state a b bits called
    | exact scalar_target_group_2 ops law _ (by decide) before after state a b bits called
    | exact scalar_target_group_3 ops law _ (by decide) before after state a b bits called
    | exact scalar_target_group_4 ops law _ (by decide) before after state a b bits called
    | exact scalar_target_group_5 ops law _ (by decide) before after state a b bits called

end Itasca.Runtime.Compiler

end