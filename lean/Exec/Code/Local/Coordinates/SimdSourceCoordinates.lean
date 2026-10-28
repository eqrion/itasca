import Exec.Code.Local.Coordinates.SourceCoordinateTactic
import Exec.Code.Local.Coordinates.OrdinarySourceCoordinates
import Exec.Code.Local.Lowering.Simd.SimdDispatch

namespace Itasca.Runtime.Code
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

end Itasca.Runtime.Code
