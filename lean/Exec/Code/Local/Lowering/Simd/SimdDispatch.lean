import Exec.Code.Local.Lowering.Simd.SimdLowered
namespace Exec.Code
open Aeneas Aeneas.Std

set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

/-- The checked 0xfd compiler opcode interval delegates to SIMD lowering. -/
theorem lower_simd_dispatch {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (opcode : U16) (a b : U32) (bits : U128)
    (reachable : before.reachable = true) (lower : 512 ≤ opcode.val) (upper : opcode.val < 768) :
    runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits =
      runtime.compiler.simd.FunctionCompiler.simd_op ops before state opcode a bits := by
  interval_cases value : opcode.val
  all_goals
    have literal : opcode = ⟨BitVec.ofNat 16 opcode.val⟩ := by
      apply UScalar.eq_of_val_eq
      change opcode.val = opcode.val % 2^16
      exact (Nat.mod_eq_of_lt opcode.hBounds).symm
    rw [value] at literal
    rw [literal]
    unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_pos reachable]
    rfl

end Exec.Code
