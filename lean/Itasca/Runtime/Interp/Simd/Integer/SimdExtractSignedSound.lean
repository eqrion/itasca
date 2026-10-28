import Itasca.Runtime.Interp.Simd.Integer.SimdExtractSignedRuntime
import Itasca.Runtime.Spec.SimdExtractSigned
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
