import Itasca.Runtime.Compiler.Local.Callbacks.Control.BranchTableCallbacks
import Itasca.Runtime.Compiler.Local.Coordinates.ScalarSourceCoordinates
import Itasca.Runtime.Compiler.Local.Publication.ScopeEntryPublication
import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.CompilerCodeMonotoneLiteral
import Itasca.Runtime.Compiler.Local.Publication.StartMapPublication
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableSafetyEffects

/-!
Sections, each formerly its own module: ScalarMapPublication, TableMapPublication.
-/

/-! ## ScalarMapPublication -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

private def ScalarMapRule {A : Type} (ops : runtime.platform.Alloc A) (opcode : U16) : Prop :=
  ∀ (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (a b : U32) (bits : U128),
    ControlMapPublication before → before.next_source.val ≤ state.pos.val →
    runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after) →
    ControlMapPublication after

private theorem scalar_maps_group_0 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (opcode : U16)
    (supported : opcode ∈ [0#u16, 1#u16, 16#u16, 17#u16, 26#u16, 27#u16]) : ScalarMapRule ops opcode := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro before after state a b bits held forward called
    by_cases live : before.reachable = true
    · first
      | rw [runtime.compiler.lower.FunctionCompiler.op.unreachable ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.nop ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.call ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.call_indirect ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.drop ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.select ops before state 27#u16 a b bits live (by decide)] at called
      have stable : CompilerOrdinaryStable before after := by
        repeat' first | coordinates_head called | metadata_step called using ops, law
      have growth : before.function.code.val.length ≤ after.function.code.val.length := by
        repeat' first | coordinates_head called | code_mono_step called using ops, law
      have cursor : after.next_source = state.pos := by
        repeat' first | coordinates_head called | cursor_step called using ops, law
      apply held.ordinary stable growth
      rw [cursor]
      exact forward
    · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
      exact compiler_observe_map_publication ops law before after state held forward called
private theorem scalar_maps_group_1 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (opcode : U16)
    (supported : opcode ∈ [28#u16, 32#u16, 33#u16, 34#u16, 35#u16, 36#u16]) : ScalarMapRule ops opcode := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro before after state a b bits held forward called
    by_cases live : before.reachable = true
    · first
      | rw [runtime.compiler.lower.FunctionCompiler.op.select ops before state 28#u16 a b bits live (by decide)] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.local_get ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.local_set ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.local_tee ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.global_get ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.global_set ops before state a b bits live] at called
      have stable : CompilerOrdinaryStable before after := by
        repeat' first | coordinates_head called | metadata_step called using ops, law
      have growth : before.function.code.val.length ≤ after.function.code.val.length := by
        repeat' first | coordinates_head called | code_mono_step called using ops, law
      have cursor : after.next_source = state.pos := by
        repeat' first | coordinates_head called | cursor_step called using ops, law
      apply held.ordinary stable growth
      rw [cursor]
      exact forward
    · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
      exact compiler_observe_map_publication ops law before after state held forward called
private theorem scalar_maps_group_2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (opcode : U16)
    (supported : opcode ∈ [37#u16, 38#u16, 63#u16, 64#u16, 65#u16, 66#u16]) : ScalarMapRule ops opcode := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro before after state a b bits held forward called
    by_cases live : before.reachable = true
    · first
      | rw [runtime.compiler.lower.FunctionCompiler.op.table_get ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.table_set ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.memory_size ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.memory_grow ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.i32_const ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.i64_const ops before state a b bits live] at called
      have stable : CompilerOrdinaryStable before after := by
        repeat' first | coordinates_head called | metadata_step called using ops, law
      have growth : before.function.code.val.length ≤ after.function.code.val.length := by
        repeat' first | coordinates_head called | code_mono_step called using ops, law
      have cursor : after.next_source = state.pos := by
        repeat' first | coordinates_head called | cursor_step called using ops, law
      apply held.ordinary stable growth
      rw [cursor]
      exact forward
    · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
      exact compiler_observe_map_publication ops law before after state held forward called
private theorem scalar_maps_group_3 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (opcode : U16)
    (supported : opcode ∈ [67#u16, 68#u16, 208#u16, 209#u16, 210#u16, 264#u16]) : ScalarMapRule ops opcode := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro before after state a b bits held forward called
    by_cases live : before.reachable = true
    · first
      | rw [runtime.compiler.lower.FunctionCompiler.op.f32_const ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.f64_const ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.ref_null ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.ref_is_null ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.ref_func ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.memory_init ops before state a b bits live] at called
      have stable : CompilerOrdinaryStable before after := by
        repeat' first | coordinates_head called | metadata_step called using ops, law
      have growth : before.function.code.val.length ≤ after.function.code.val.length := by
        repeat' first | coordinates_head called | code_mono_step called using ops, law
      have cursor : after.next_source = state.pos := by
        repeat' first | coordinates_head called | cursor_step called using ops, law
      apply held.ordinary stable growth
      rw [cursor]
      exact forward
    · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
      exact compiler_observe_map_publication ops law before after state held forward called
private theorem scalar_maps_group_4 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (opcode : U16)
    (supported : opcode ∈ [265#u16, 266#u16, 267#u16, 268#u16, 269#u16, 270#u16]) : ScalarMapRule ops opcode := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro before after state a b bits held forward called
    by_cases live : before.reachable = true
    · first
      | rw [runtime.compiler.lower.FunctionCompiler.op.data_drop ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.memory_copy ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.memory_fill ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.table_init ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.elem_drop ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.table_copy ops before state a b bits live] at called
      have stable : CompilerOrdinaryStable before after := by
        repeat' first | coordinates_head called | metadata_step called using ops, law
      have growth : before.function.code.val.length ≤ after.function.code.val.length := by
        repeat' first | coordinates_head called | code_mono_step called using ops, law
      have cursor : after.next_source = state.pos := by
        repeat' first | coordinates_head called | cursor_step called using ops, law
      apply held.ordinary stable growth
      rw [cursor]
      exact forward
    · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
      exact compiler_observe_map_publication ops law before after state held forward called
private theorem scalar_maps_group_5 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (opcode : U16)
    (supported : opcode ∈ [271#u16, 272#u16, 273#u16]) : ScalarMapRule ops opcode := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl
  all_goals
    intro before after state a b bits held forward called
    by_cases live : before.reachable = true
    · first
      | rw [runtime.compiler.lower.FunctionCompiler.op.table_grow ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.table_size ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.table_fill ops before state a b bits live] at called
      have stable : CompilerOrdinaryStable before after := by
        repeat' first | coordinates_head called | metadata_step called using ops, law
      have growth : before.function.code.val.length ≤ after.function.code.val.length := by
        repeat' first | coordinates_head called | code_mono_step called using ops, law
      have cursor : after.next_source = state.pos := by
        repeat' first | coordinates_head called | cursor_step called using ops, law
      apply held.ordinary stable growth
      rw [cursor]
      exact forward
    · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
      exact compiler_observe_map_publication ops law before after state held forward called

/-- Every finite nonnumeric ordinary opcode preserves control-map bounds,
including all immediate bits and unreachable code. -/
theorem compiler_scalar_op_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (supported : opcode ∈ sourceCoordinateScalarOpcodes)
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  simp only [sourceCoordinateScalarOpcodes,List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | exact scalar_maps_group_0 ops law _ (by decide) before after state a b bits held forward called
    | exact scalar_maps_group_1 ops law _ (by decide) before after state a b bits held forward called
    | exact scalar_maps_group_2 ops law _ (by decide) before after state a b bits held forward called
    | exact scalar_maps_group_3 ops law _ (by decide) before after state a b bits held forward called
    | exact scalar_maps_group_4 ops law _ (by decide) before after state a b bits held forward called
    | exact scalar_maps_group_5 ops law _ (by decide) before after state a b bits held forward called

end Itasca.Runtime.Compiler

end

/-! ## TableMapPublication -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Emitted code extends the target range without changing map owners or source bounds. -/
theorem Emitted.control_maps {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction : runtime.bytecode.Instr} (emitted : Emitted before after instruction)
    (held : ControlMapPublication before) : ControlMapPublication after := by
  have stable := emitted.ordinary_stable
  obtain ⟨budget,code,sources,rfl,codeAppend,_⟩ := emitted
  apply held.ordinary stable
  · change before.function.code.val.length ≤ code.val.length
    rw [codeAppend]
    simp
  · exact le_rfl

/-- Streamed labels retain all map bounds, including Wasm 1 label collection. -/
theorem compiler_table_label_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (held : ControlMapPublication before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops before state depth = .ok (.Ok (),after)) : ControlMapPublication after := by
  obtain ⟨budget,depths,frame,_⟩ := compiler_table_label_success ops law before after state depth called
  rw [frame]
  exact held.retained ⟨rfl,le_rfl⟩ rfl rfl le_rfl le_rfl

/-- Each actual table stub preserves map publication bounds. -/
theorem compiler_table_branch_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (lookup : before.table_depths.val[index.val]? = some depth)
    (held : ControlMapPublication before)
    (called : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  obtain ⟨target,budget,table,_,_,branch⟩ := compiler_table_branch_success ops law before after index depth lookup called
  let staged := {before with budget,function := {before.function with jump_tables := table}}
  change runtime.compiler.control.FunctionCompiler.branch ops staged depth 1#u32 false = .ok (.Ok (),after) at branch
  exact compiler_branch_map_publication ops law staged after depth 1#u32 false
    (held.retained ⟨rfl,le_rfl⟩ rfl rfl le_rfl le_rfl) branch

/-- Every branch in a finite table-lowering run retains map bounds. -/
theorem TableBranchRun.control_maps {A : Type} {ops : runtime.platform.Alloc A}
    (law : Platform.AllocCorrect ops) {before after : runtime.compiler.FunctionCompiler A}
    {index : Nat} (run : TableBranchRun ops before index after) :
    ControlMapPublication before →
    ControlMapPublication after ∧ after.next_source = before.next_source := by
  induction run with
  | done => intro held; exact ⟨held,rfl⟩
  | @cons before middle after index inbounds called rest ih =>
    intro held
    let depth := before.table_depths.val[index.val]
    have lookup : before.table_depths.val[index.val]? = some depth := List.getElem?_eq_getElem inbounds
    have coordinates := compiler_table_branch_map_publication ops law before middle index depth lookup held called
    have cursor := compiler_table_branch_cursor ops law before middle index depth lookup called
    obtain ⟨final,finalCursor⟩ := ih coordinates
    exact ⟨final,finalCursor.trans cursor⟩

/-- Dispatch and every target stub preserve map bounds in the actual lowerer. -/
theorem compiler_lower_table_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (held : ControlMapPublication before)
    (called : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before = .ok (.Ok (),after)) :
    ControlMapPublication after ∧ after.next_source = before.next_source := by
  obtain ⟨start,len,selector,emitted,_,_,_,emission,run⟩ := compiler_lower_table_success ops law before after called
  have coordinates := emission.control_maps held
  obtain ⟨budget,code,sources,frame,_,_⟩ := emission
  obtain ⟨final,cursor⟩ := run.control_maps law coordinates
  exact ⟨final,by simpa only [frame] using cursor⟩

/-- The actual full branch-table callback preserves all map publication bounds. -/
theorem compiler_br_table_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (held : ControlMapPublication before)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types = .ok (.Ok (),after)) : ControlMapPublication after := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table.inv ops before after state fallback types (.Ok ()) called with
  | @live labeled lowered cleared _ _ labelCall live lowerCall clearCall observed =>
    have frame := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.inv ops before labeled state fallback (.Ok ()) labelCall).frame
    have coordinates : ControlMapPublication labeled := by
      rw [frame]
      exact held.retained ⟨rfl, le_rfl⟩ rfl rfl le_rfl le_rfl
    have cursor : labeled.next_source = before.next_source := by rw [frame]
    obtain ⟨loweredCoordinates, loweredCursor⟩ := compiler_lower_table_map_publication ops law labeled lowered coordinates lowerCall
    exact compiler_observe_map_publication ops law {lowered with reachable := false, table_depths := cleared} after state
      (loweredCoordinates.retained ⟨rfl, le_rfl⟩ rfl rfl le_rfl le_rfl) (by simpa only [loweredCursor, cursor] using forward) observed
  | @dead labeled cleared _ _ labelCall dead clearCall observed =>
    have frame := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.inv ops before labeled state fallback (.Ok ()) labelCall).frame
    have coordinates : ControlMapPublication labeled := by
      rw [frame]
      exact held.retained ⟨rfl, le_rfl⟩ rfl rfl le_rfl le_rfl
    have cursor : labeled.next_source = before.next_source := by rw [frame]
    exact compiler_observe_map_publication ops law {labeled with table_depths := cleared} after state
      (coordinates.retained ⟨rfl, le_rfl⟩ rfl rfl le_rfl le_rfl) (by simpa only [cursor] using forward) observed

end Itasca.Runtime.Compiler

end