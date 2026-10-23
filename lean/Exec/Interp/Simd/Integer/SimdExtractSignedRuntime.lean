import Exec.Interp.Simd.Integer.SimdSigned
import Exec.Interp.Simd.Common.SimdSplatSound
import Exec.Spec.IntegerShift
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

def extractSignedOpcode (ty : packtype) : U32 :=
  match ty with
  | .I8 => 21#u32
  | .I16 => 24#u32

@[step] theorem extract_signed_access (ty : packtype) (index : U32) (a b : U128)
    (valid : index.val < 128/psize ty) :
    runtime.interp.simd.access_lane (extractSignedOpcode ty) index a b ⦃ result =>
      ∃ value, result = .Ok value ∧
        value.val = (SpecExt.Builtins.signedValue (psize ty)
          (a.val / 2^(psize ty*index.val) % 2^psize ty) % (2^32 : Int)).toNat ⦄ := by
  cases ty <;> unfold runtime.interp.simd.access_lane extractSignedOpcode
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) ⦃ _ ⦄
  all_goals rw [bind_ok]
  all_goals step as ⟨count, countEq⟩
  all_goals norm_num [psize] at valid countEq
  all_goals have fits : ¬ index ≥ count := by scalar_tac
  all_goals rw [if_neg fits]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok false) _) ⦃ _ ⦄
  all_goals rw [bind_ok]
  all_goals simp only [Bool.false_eq_true, ite_false]
  all_goals step with lane as ⟨laneValue, laneEq⟩
  all_goals with_unfolding_all change (Aeneas.Std.bind (runtime.interp.simd.signed _ _) _) ⦃ _ ⦄
  all_goals step with signed as ⟨signedValue, signedEq⟩
  all_goals simp only [lift, bind_ok, WP.spec_ok]
  all_goals refine ⟨_, rfl, ?_⟩
  all_goals rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt (by scalar_tac)]
  all_goals rw [IScalar.hcast_val_eq, signedEq, ←Spec.signedValue_bitvec, BitVec.toNat_setWidth]
  all_goals change (SpecExt.Builtins.signedValue _ (laneValue.val % _) % _).toNat = _
  all_goals rw [laneEq]
  all_goals simp [psize, UScalarTy.numBits]

end Exec.Interp.Simd
