import Exec.Code.Local.Lowering.Simd.SimdOperandCounts
namespace Exec.Code
open Aeneas Aeneas.Std

theorem simd_opcode_reduction (opcode : U16) (sub : U32)
    (number : opcode.val = 512 + sub.val) :
    ∃ reduced : U16, (opcode - 512#u16) = Result.ok reduced ∧ sub = UScalar.cast .U32 reduced := by
  obtain ⟨reduced,subtracted,value⟩ := WP.spec_imp_exists
    (UScalar.sub_spec (x := opcode) (y := 512#u16) (by scalar_tac))
  refine ⟨reduced,subtracted,?_⟩
  apply UScalar.eq_of_val_eq
  have bound := reduced.hBounds
  rw [UScalar.cast_val_eq]
  scalar_tac
end Exec.Code
