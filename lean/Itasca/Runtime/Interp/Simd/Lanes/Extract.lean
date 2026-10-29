import Itasca.Runtime.Interp.Simd.Lanes.SplatSound
import Itasca.Runtime.Interp.Simd.Integer.Signed
import Itasca.Runtime.Spec.Simd.Extract

/-!
Lane extraction: scalar word calculations, lane iteration, packing and source correspondence. The final handler facts feed SIMD dispatch and machine execution; independently consumed primitives remain below this construction.
-/

/-! ## Simd Extract Runtime -/

section

namespace Itasca.Runtime.Interp.Simd
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
  all_goals simp only [lift, bind_ok]
  all_goals with_unfolding_all change (Result.ok _) ⦃ _ ⦄
  all_goals simp only [WP.spec_ok]
  all_goals refine ⟨_, rfl, ?_⟩
  all_goals simp only [UScalar.cast_val_eq]
  all_goals norm_num only [UScalar.size, UScalarTy.numBits]
  all_goals simp only [valueEq]
  all_goals norm_num [lsize, size, valtype_numtype, psize]
  all_goals omega

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Extract Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

theorem extract_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : lanetype) (offset laneIndex : U32) (bits a b c : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (extractOpcode ty) offset laneIndex bits a b c memory =
      Aeneas.Std.bind (runtime.interp.simd.access_lane (extractOpcode ty) laneIndex a b)
        (fun result => Result.ok (result, memory)) := by
  cases ty <;> unfold runtime.interp.simd.simd extractOpcode <;> with_unfolding_all rfl

end Itasca.Runtime.Interp.Simd

end
