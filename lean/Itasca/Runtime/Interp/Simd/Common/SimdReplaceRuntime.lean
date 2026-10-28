import Itasca.Runtime.Interp.Simd.Common.SimdSplatSound
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

def replaceOpcode (ty : lanetype) : U32 :=
  match ty with
  | .I8 => 23#u32
  | .I16 => 26#u32
  | .I32 => 28#u32
  | .I64 => 30#u32
  | .F32 => 32#u32
  | .F64 => 34#u32

@[step] theorem replace_access (ty : lanetype) (index : U32) (a b : U128)
    (valid : index.val < 128/lsize ty) :
    runtime.interp.simd.access_lane (replaceOpcode ty) index a b ⦃ result =>
      ∃ value, result = .Ok value ∧
        value.bv = writeLaneBits (lsize ty) index.val a.bv (splatInput ty b).bv ⦄ := by
  cases ty <;> unfold runtime.interp.simd.access_lane replaceOpcode
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) ⦃ _ ⦄
  all_goals rw [bind_ok]
  all_goals step as ⟨count, countEq⟩
  all_goals norm_num [lsize, size, valtype_numtype, psize] at valid countEq
  all_goals have fits : ¬ index ≥ count := by scalar_tac
  all_goals rw [if_neg fits]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok true) _) ⦃ _ ⦄
  all_goals rw [bind_ok]
  all_goals simp only [ite_true, lift, bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) ⦃ _ ⦄
  all_goals rw [bind_ok]
  all_goals step with put as ⟨value, bits⟩
  all_goals first
    | exact ⟨value, rfl, bits⟩
    | (simp only [bind_ok, WP.spec_ok]; exact ⟨value, rfl, bits⟩)

end Itasca.Runtime.Interp.Simd
