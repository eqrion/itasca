import Exec.Code.Local.Coordinates.SourceCoordinateTactic
import Exec.Code.Local.Coordinates.OrdinarySourceCoordinates

namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

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

private theorem scalar_coordinates_0 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 0#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_1 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 1#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_16 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 16#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_17 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 17#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_26 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 26#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_27 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 27#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_28 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 28#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_32 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 32#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_33 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 33#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_34 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 34#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_35 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 35#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_36 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 36#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_37 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 37#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_38 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 38#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_63 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 63#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_64 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 64#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_65 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 65#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_66 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 66#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_67 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 67#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_68 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 68#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_208 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 208#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_209 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 209#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_210 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 210#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_264 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 264#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_265 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 265#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_266 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 266#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_267 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 267#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_268 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 268#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_269 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 269#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_270 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 270#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_271 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 271#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_272 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 272#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

private theorem scalar_coordinates_273 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarCoordinateRule ops 273#u16 := by
  intro before after state a b bits held inside forward called
  by_cases live : before.reachable = true
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_pos live] at called
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
  · exact scalar_coordinates_0 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_1 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_16 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_17 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_26 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_27 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_28 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_32 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_33 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_34 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_35 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_36 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_37 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_38 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_63 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_64 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_65 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_66 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_67 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_68 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_208 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_209 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_210 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_264 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_265 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_266 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_267 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_268 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_269 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_270 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_271 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_272 ops law before after state a b bits held inside forward called
  · exact scalar_coordinates_273 ops law before after state a b bits held inside forward called

end Exec.Code
