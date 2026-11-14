import Itasca.Runtime.Compiler.Local.Coordinates.ControlSourceCoordinates
import Itasca.Runtime.Compiler.Local.Capacity.UnreachableAvailability

/-!
Sections, each formerly its own module: OrdinarySourceCoordinates, ScalarSourceCoordinates.
-/

/-! ## OrdinarySourceCoordinates -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Dead ordinary instructions only advance the observed source cursor. -/
theorem compiler_dead_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (dead : before.reachable = false) (held : SourceCoordinates before)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    SourceCoordinates after := by
  rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (dead)] at called
  exact compiler_observe_source_coordinates ops law before after state held forward called

end Itasca.Runtime.Compiler

end

/-! ## ScalarSourceCoordinates -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

/-- Finite nonnumeric ordinary families: stack/local/global operations, calls,
constants, references, and bulk table/memory operations. -/
def sourceCoordinateScalarOpcodes : List U16 :=
  [0#u16, 1#u16, 16#u16, 17#u16, 26#u16, 27#u16, 28#u16, 32#u16, 33#u16, 34#u16, 35#u16, 36#u16, 37#u16, 38#u16, 63#u16, 64#u16, 65#u16, 66#u16, 67#u16, 68#u16, 208#u16, 209#u16, 210#u16, 264#u16, 265#u16, 266#u16, 267#u16, 268#u16, 269#u16, 270#u16, 271#u16, 272#u16, 273#u16]

private def ScalarCoordinateRule {A : Type} (ops : runtime.platform.Alloc A) (opcode : U16) : Prop :=
  ∀ (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (a b : U32) (bits : U128),
    SourceCoordinates before →
    before.function.body_start.val+before.next_source.val < before.function.body_end.val →
    before.next_source.val ≤ state.pos.val →
    runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after) →
    SourceCoordinates after

private theorem scalar_coordinates_group_0 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (opcode : U16)
    (supported : opcode ∈ [0#u16, 1#u16, 16#u16, 17#u16, 26#u16, 27#u16]) : ScalarCoordinateRule ops opcode := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro before after state a b bits held inside forward called
    by_cases live : before.reachable = true
    · first
      | rw [runtime.compiler.lower.FunctionCompiler.op.unreachable ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.nop ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.call ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.call_indirect ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.drop ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.select ops before state 27#u16 a b bits live (by decide)] at called
      repeat' coordinates_step called using ops, law
    · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
        (by cases h : before.reachable <;> simp_all) held forward called
private theorem scalar_coordinates_group_1 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (opcode : U16)
    (supported : opcode ∈ [28#u16, 32#u16, 33#u16, 34#u16, 35#u16, 36#u16]) : ScalarCoordinateRule ops opcode := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro before after state a b bits held inside forward called
    by_cases live : before.reachable = true
    · first
      | rw [runtime.compiler.lower.FunctionCompiler.op.select ops before state 28#u16 a b bits live (by decide)] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.local_get ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.local_set ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.local_tee ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.global_get ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.global_set ops before state a b bits live] at called
      repeat' coordinates_step called using ops, law
    · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
        (by cases h : before.reachable <;> simp_all) held forward called
private theorem scalar_coordinates_group_2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (opcode : U16)
    (supported : opcode ∈ [37#u16, 38#u16, 63#u16, 64#u16, 65#u16, 66#u16]) : ScalarCoordinateRule ops opcode := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro before after state a b bits held inside forward called
    by_cases live : before.reachable = true
    · first
      | rw [runtime.compiler.lower.FunctionCompiler.op.table_get ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.table_set ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.memory_size ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.memory_grow ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.i32_const ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.i64_const ops before state a b bits live] at called
      repeat' coordinates_step called using ops, law
    · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
        (by cases h : before.reachable <;> simp_all) held forward called
private theorem scalar_coordinates_group_3 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (opcode : U16)
    (supported : opcode ∈ [67#u16, 68#u16, 208#u16, 209#u16, 210#u16, 264#u16]) : ScalarCoordinateRule ops opcode := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro before after state a b bits held inside forward called
    by_cases live : before.reachable = true
    · first
      | rw [runtime.compiler.lower.FunctionCompiler.op.f32_const ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.f64_const ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.ref_null ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.ref_is_null ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.ref_func ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.memory_init ops before state a b bits live] at called
      repeat' coordinates_step called using ops, law
    · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
        (by cases h : before.reachable <;> simp_all) held forward called
private theorem scalar_coordinates_group_4 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (opcode : U16)
    (supported : opcode ∈ [265#u16, 266#u16, 267#u16, 268#u16, 269#u16, 270#u16]) : ScalarCoordinateRule ops opcode := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro before after state a b bits held inside forward called
    by_cases live : before.reachable = true
    · first
      | rw [runtime.compiler.lower.FunctionCompiler.op.data_drop ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.memory_copy ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.memory_fill ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.table_init ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.elem_drop ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.table_copy ops before state a b bits live] at called
      repeat' coordinates_step called using ops, law
    · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
        (by cases h : before.reachable <;> simp_all) held forward called
private theorem scalar_coordinates_group_5 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (opcode : U16)
    (supported : opcode ∈ [271#u16, 272#u16, 273#u16]) : ScalarCoordinateRule ops opcode := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl
  all_goals
    intro before after state a b bits held inside forward called
    by_cases live : before.reachable = true
    · first
      | rw [runtime.compiler.lower.FunctionCompiler.op.table_grow ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.table_size ops before state a b bits live] at called
      | rw [runtime.compiler.lower.FunctionCompiler.op.table_fill ops before state a b bits live] at called
      repeat' coordinates_step called using ops, law
    · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
        (by cases h : before.reachable <;> simp_all) held forward called

/-- Each remaining ordinary opcode is reduced through its actual dispatcher
branch before composing emission and observation. Invalid metadata still
cannot produce an accepted callback with malformed source coordinates. -/
theorem compiler_scalar_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (supported : opcode ∈ sourceCoordinateScalarOpcodes)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    SourceCoordinates after := by
  simp only [sourceCoordinateScalarOpcodes,List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | exact scalar_coordinates_group_0 ops law _ (by decide) before after state a b bits held inside forward called
    | exact scalar_coordinates_group_1 ops law _ (by decide) before after state a b bits held inside forward called
    | exact scalar_coordinates_group_2 ops law _ (by decide) before after state a b bits held inside forward called
    | exact scalar_coordinates_group_3 ops law _ (by decide) before after state a b bits held inside forward called
    | exact scalar_coordinates_group_4 ops law _ (by decide) before after state a b bits held inside forward called
    | exact scalar_coordinates_group_5 ops law _ (by decide) before after state a b bits held inside forward called

end Itasca.Runtime.Compiler

end