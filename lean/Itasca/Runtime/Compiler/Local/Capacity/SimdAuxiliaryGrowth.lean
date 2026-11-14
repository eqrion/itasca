import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdDispatch
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdBitsCallbacks
import Itasca.Runtime.Compiler.Local.Capacity.EmissionGrowth

/-!
Sections, each formerly its own module: SimdMeaningBound, SimdAuxiliaryGrowth.
-/

/-! ## SimdMeaningBound -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.Wasm2.Simd
set_option maxRecDepth 4096

theorem SimdImmediateMeaning.opcode_bound {C opcode immediate input source output}
    (meaning : SimdImmediateMeaning C opcode immediate input source output) : opcode.val < 256 := by
  cases meaning with
  | pure opcode immediate op meaning => exact pure_bound meaning
  | lane opcode immediate op meaning lane position =>
    unfold laneMeaning at meaning
    split at meaning <;> first | contradiction | omega
  | memory opcode immediate op meaning argument lane memory available offset position =>
    unfold memoryMeaning at meaning
    split at meaning <;> first | contradiction | omega
  | shuffle => decide
end Itasca.Runtime.Compiler

end

/-! ## SimdAuxiliaryGrowth -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096



private theorem observe_auxiliary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after)) :
    after.function.simd = before.function.simd ∧
    after.function.v128_pool = before.function.v128_pool ∧
    after.function.indirect = before.function.indirect ∧
    after.function.code = before.function.code := by
  have frame := compiler_observe_frame ops law before state
  rw [accepted, WP.spec_ok] at frame
  change ObserveFrame before after at frame
  rw [frame]
  exact ⟨rfl, rfl, rfl, rfl⟩



/-- Every accepted SIMD callback emits one instruction. Its immediate record
or vector-constant pool grows by at most one; rejected prefixes are excluded. -/
theorem compiler_simd_auxiliary_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a : U32) (bits : U128)
    (accepted : runtime.compiler.simd.FunctionCompiler.simd_op ops before state opcode a bits = .ok (.Ok (),after)) :
    after.function.code.val.length = before.function.code.val.length + 1 ∧
    after.function.simd.val.length ≤ before.function.simd.val.length + 1 ∧
    after.function.v128_pool.val.length ≤ before.function.v128_pool.val.length + 1 ∧
    after.function.indirect = before.function.indirect ∧
    (opcode ≠ 524#u16 → after.function.v128_pool = before.function.v128_pool) := by
  obtain ⟨staged, instruction, allocated, finished⟩ :=
    (runtime.compiler.simd.FunctionCompiler.simd_op.inv ops before after state opcode a bits (.Ok ()) accepted).execution.success
  have frame := allocated.frame
  have bounds := allocated.bounds law
  have tables := compiler_finish_op_tables ops law staged after state instruction (.Ok ()) finished
  have simds := congrArg CompilerTables.simd tables
  have pools := congrArg CompilerTables.constants tables
  have indirect := congrArg CompilerTables.indirect tables
  change after.function.simd.val = staged.function.simd.val at simds
  change after.function.v128_pool.val = staged.function.v128_pool.val at pools
  change after.function.indirect.val = staged.function.indirect.val at indirect
  obtain ⟨middle, emitted, observed⟩ :=
    (runtime.compiler.lower.FunctionCompiler.finish_op.inv ops staged after state instruction (.Ok ()) finished).success
  have code : after.function.code.val.length = staged.function.code.val.length + 1 := by
    rw [compiler_observe_code_result ops law middle after state (.Ok ()) observed,
      compiler_emit_code_success ops law staged middle instruction emitted]
    simp only [List.length_append, List.length_singleton]
  rw [frame] at code
  refine ⟨code, ?_, ?_, ?_, ?_⟩
  · rw [simds]
    exact bounds.1
  · rw [pools]
    exact bounds.2.1
  · apply alloc.vec.Vec.ext
    rw [indirect, frame]
  · intro nonconstant
    apply alloc.vec.Vec.ext
    rw [pools]
    have notLiteral : decide (opcode = 524#u16) = false := by
      simp only [nonconstant, decide_false]
    exact congrArg alloc.vec.Vec.val (bounds.2.2 notLiteral)

/-- Successful live or dormant SIMD dispatch preserves auxiliary-table
headroom relative to actual emitted code. Vector constants use the pool;
all other SIMD instructions preserve that pool exactly. -/
theorem compiler_lower_simd_auxiliary_growth {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (lower : 512 ≤ opcode.val) (upper : opcode.val < 768)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    before.function.code.val.length ≤ after.function.code.val.length ∧
    after.function.simd.val.length ≤ before.function.simd.val.length +
      (after.function.code.val.length - before.function.code.val.length) ∧
    after.function.v128_pool.val.length ≤ before.function.v128_pool.val.length +
      (after.function.code.val.length - before.function.code.val.length) ∧
    after.function.indirect = before.function.indirect ∧
    (opcode ≠ 524#u16 → after.function.v128_pool = before.function.v128_pool) := by
  by_cases reachable : before.reachable = true
  · rw [lower_simd_dispatch ops before state opcode a b bits reachable lower upper] at accepted
    obtain ⟨code, simd, pool, indirect, poolEq⟩ :=
      compiler_simd_auxiliary_success ops law before after state opcode a bits accepted
    exact ⟨by omega, by omega, by omega, indirect, poolEq⟩
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reachable)] at accepted
    obtain ⟨simd, pool, indirect, code⟩ :=
      observe_auxiliary_result ops law before after state (.Ok ()) accepted
    simp [simd, pool, indirect, code]

end Itasca.Runtime.Compiler

end
