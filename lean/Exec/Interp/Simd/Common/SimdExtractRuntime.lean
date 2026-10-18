import Exec.Interp.Simd.Common.SimdSplatSound
import Exec.Interp.Simd.Integer.SimdSigned
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

def extractOpcode (ty : lanetype) : U32 :=
  match ty with
  | .I8 => 22#u32
  | .I16 => 25#u32
  | .I32 => 27#u32
  | .I64 => 29#u32
  | .F32 => 31#u32
  | .F64 => 33#u32

@[step] theorem extract_access (ty : lanetype) (index : U32) (a b : U128)
    (valid : index.val < 128/lsize ty) :
    runtime.interp.simd.access_lane (extractOpcode ty) index a b ⦃ result =>
      ∃ value, result = .Ok value ∧
        value.val = a.val / 2^(lsize ty*index.val) % 2^lsize ty ⦄ := by
  cases ty <;> unfold runtime.interp.simd.access_lane extractOpcode
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) ⦃ _ ⦄
  all_goals rw [bind_ok]
  all_goals step as ⟨count, countEq⟩
  all_goals norm_num [lsize, size, valtype_numtype, psize] at valid countEq
  all_goals have fits : ¬ index ≥ count := by scalar_tac
  all_goals rw [if_neg fits]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok false) _) ⦃ _ ⦄
  all_goals rw [bind_ok]
  all_goals simp only [Bool.false_eq_true, ite_false]
  all_goals step with lane as ⟨value, valueEq⟩
  all_goals simp only [runtime.interp.simd.from_u32, runtime.interp.simd.from_u64, lift, bind_ok]
  all_goals with_unfolding_all change (Result.ok _) ⦃ _ ⦄
  all_goals simp only [WP.spec_ok]
  all_goals refine ⟨_, rfl, ?_⟩
  all_goals simp only [UScalar.cast_val_eq]
  all_goals norm_num only [UScalar.size, UScalarTy.numBits]
  all_goals simp only [valueEq]
  all_goals norm_num [lsize, size, valtype_numtype, psize]
  all_goals omega

end Exec.Interp.Simd
