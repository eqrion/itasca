import Exec.Interp.Simd.Integer.SimdIntegerBinaryLoop
import Exec.Spec.SimdSaturation
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Exec.Spec.Simd

theorem hcast_lane (x : I128) (width : Nat) (bound : width ≤ 64) :
    (IScalar.hcast .U64 x).bv.setWidth width = BitVec.ofInt width x.val := by
  rw [IScalar.hcast_bv_eq,BitVec.signExtend_eq_setWidth_of_le _ (by decide),UScalarTy.U64_numBits_eq,
    BitVec.setWidth_setWidth_of_le _ bound,
    ←BitVec.signExtend_eq_setWidth_of_le _ (by omega : width ≤ 128)]
  rfl

@[step] theorem saturate (x : I128) (width : U32) (signed : Bool)
    (supported : width.val ∈ [8,16,32]) :
    runtime.interp.simd.sat x width signed ⦃ result =>
      result.bv.setWidth width.val = BitVec.ofInt width.val (clampLane width.val signed x.val) ⦄ := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with supported | supported | supported
  all_goals first
    | have eq : width = 8#u32 := UScalar.eq_of_val_eq supported
    | have eq : width = 16#u32 := UScalar.eq_of_val_eq supported
    | have eq : width = 32#u32 := UScalar.eq_of_val_eq supported
  all_goals subst width
  all_goals cases signed
  all_goals unfold runtime.interp.simd.sat
  all_goals simp only [Bool.false_eq_true,Bool.true_eq,↓reduceIte,bind_ok]
  all_goals step*
  all_goals try rw [hcast_lane _ _ (by decide)]
  all_goals simp_all [I128.size,I128.numBits,I128.min,I128.max,Int.bmod,Int.shiftLeft_eq,clampLane,IScalar.min,IScalar.lt_equiv]
  all_goals try omega
  all_goals split_ifs <;> (try simp_all) <;> omega

end Exec.Interp.Simd
