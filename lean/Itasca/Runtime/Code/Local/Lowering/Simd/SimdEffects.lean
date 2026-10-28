import Itasca.Runtime.Code.Local.Lowering.Simd.SimdDispatch
import Itasca.Runtime.Code.Local.Callbacks.Simd.CompilerSimdMetadata
import Itasca.Runtime.Code.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Code.Local.Source.SourceCursorTactic
import Itasca.Runtime.Code.Local.Capacity.CapacityTactic
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

section
variable {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
  (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
  (opcode : U16) (a : U32) (bits : U128)
  (accepted : runtime.compiler.simd.FunctionCompiler.simd_op ops before state opcode a bits = .ok (.Ok (),after))

include accepted law

theorem compiler_simd_sources : SourceProgress before after := by
  unfold runtime.compiler.simd.FunctionCompiler.simd_op at accepted
  repeat' sources_step accepted using ops, law

theorem compiler_simd_cursor : after.next_source = state.pos := by
  unfold runtime.compiler.simd.FunctionCompiler.simd_op at accepted
  repeat' cursor_step accepted using ops, law

theorem compiler_simd_capacity : CapacityStep before after state := by
  unfold runtime.compiler.simd.FunctionCompiler.simd_op at accepted
  repeat' capacity_step accepted using ops, law
end

/-- The actual callback path retains source and capacity facts in both live
and dormant code; no SIMD allocation premise is supplied. -/
theorem compiler_lower_simd_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (lower : 512 ≤ opcode.val) (upper : opcode.val < 768)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
      after.next_source = state.pos ∧ CapacityStep before after state := by
  by_cases reachable : before.reachable = true
  · rw [lower_simd_dispatch ops before state opcode a b bits reachable lower upper] at accepted
    exact ⟨compiler_simd_ordinary_result ops law before after state opcode a bits (.Ok ()) accepted,
      compiler_simd_sources ops law before after state opcode a bits accepted,
      compiler_simd_cursor ops law before after state opcode a bits accepted,
      compiler_simd_capacity ops law before after state opcode a bits accepted⟩
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reachable] at accepted
    have capacity := compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted
    exact ⟨compiler_observe_ordinary_result ops law before after state (.Ok ()) accepted,
      compiler_observe_sources ops law before after state (.Ok ()) accepted,
      compiler_observe_cursor ops law before after state (.Ok ()) accepted rfl,
      capacity.1,capacity.2 rfl⟩
end Itasca.Runtime.Code
