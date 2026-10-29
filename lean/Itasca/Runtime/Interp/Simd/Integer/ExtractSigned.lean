import Itasca.Runtime.Interp.Simd.Integer.Signed
import Itasca.Runtime.Interp.Simd.Lanes.SplatSound
import Itasca.Runtime.Spec.IntegerShift
import Itasca.Runtime.Spec.Simd.ExtractSigned

/-!
Signed lane extraction: scalar word calculations, lane iteration, packing and source correspondence. The final handler facts feed SIMD dispatch and machine execution; independently consumed primitives remain below this construction.
-/

/-! ## Simd Extract Signed Runtime -/

section

namespace Itasca.Runtime.Interp.Simd
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

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Extract Signed Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

@[step] theorem extract_signed_access_sound (ty : packtype) (index : U32) (a b : U128)
    (valid : index.val < 128/psize ty) :
    runtime.interp.simd.access_lane (extractSignedOpcode ty) index a b ⦃ result =>
      ∃ value, result = .Ok value ∧
        Step_pure [.VCONST .V128 (.mk_uN a.val),
          .VEXTRACT_LANE (Spec.Simd.shapeOf (lanetype_packtype ty)) (some .S) (.mk_uN index.val)]
          [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (extract_signed_access ty index a b valid)
  rintro result ⟨value, exactResult, bits⟩
  refine ⟨value, exactResult, ?_⟩
  rw [bits]
  exact Spec.Simd.extract_signed_step ty index.val a.bv valid

theorem extract_signed_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : packtype) (offset laneIndex : U32) (bits a b c : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (extractSignedOpcode ty) offset laneIndex bits a b c memory =
      Aeneas.Std.bind (runtime.interp.simd.access_lane (extractSignedOpcode ty) laneIndex a b)
        (fun result => Result.ok (result, memory)) := by
  cases ty <;> unfold runtime.interp.simd.simd extractSignedOpcode <;> with_unfolding_all rfl

@[step] theorem extract_signed_dispatch_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : packtype) (offset laneIndex : U32) (bits a b c : U128)
    (memory : Option (Slice U8)) (valid : laneIndex.val < 128/psize ty) :
    runtime.interp.simd.simd floats (extractSignedOpcode ty) offset laneIndex bits a b c memory
      ⦃ result => ∃ value, result = (.Ok value, memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN a.val),
          .VEXTRACT_LANE (Spec.Simd.shapeOf (lanetype_packtype ty)) (some .S) (.mk_uN laneIndex.val)]
          [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  rw [extract_signed_dispatch_eq]
  step with extract_signed_access_sound ty laneIndex a b valid as ⟨result, value, exactResult, source⟩
  exact ⟨value, by rw [exactResult], source⟩

end Itasca.Runtime.Interp.Simd

end
