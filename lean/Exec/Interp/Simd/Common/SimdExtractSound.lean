import Exec.Interp.Simd.Common.SimdExtractRuntime
import Exec.Spec.SimdExtract
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

@[step] theorem extract_access_sound (ty : lanetype) (index : U32) (a b : U128)
    (valid : index.val < 128/lsize ty) :
    runtime.interp.simd.access_lane (extractOpcode ty) index a b ⦃ result =>
      ∃ value, result = .Ok value ∧
        Step_pure [.VCONST .V128 (.mk_uN a.val),
          .VEXTRACT_LANE (Spec.Simd.shapeOf ty) (Spec.Simd.extractSign ty) (.mk_uN index.val)]
          [.CONST (unpack ty) (Spec.Simd.scalarOutput ty value.val)] ⦄ := by
  apply WP.spec_mono (extract_access ty index a b valid)
  rintro result ⟨value, exactResult, bits⟩
  refine ⟨value, exactResult, ?_⟩
  rw [bits]
  exact Spec.Simd.extract_step ty index.val a.bv valid

theorem extract_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : lanetype) (offset laneIndex : U32) (bits a b c : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (extractOpcode ty) offset laneIndex bits a b c memory =
      Aeneas.Std.bind (runtime.interp.simd.access_lane (extractOpcode ty) laneIndex a b)
        (fun result => Result.ok (result, memory)) := by
  cases ty <;> unfold runtime.interp.simd.simd extractOpcode <;> with_unfolding_all rfl

@[step] theorem extract_dispatch_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : lanetype) (offset laneIndex : U32) (bits a b c : U128)
    (memory : Option (Slice U8)) (valid : laneIndex.val < 128/lsize ty) :
    runtime.interp.simd.simd floats (extractOpcode ty) offset laneIndex bits a b c memory
      ⦃ result => ∃ value, result = (.Ok value, memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN a.val),
          .VEXTRACT_LANE (Spec.Simd.shapeOf ty) (Spec.Simd.extractSign ty) (.mk_uN laneIndex.val)]
          [.CONST (unpack ty) (Spec.Simd.scalarOutput ty value.val)] ⦄ := by
  rw [extract_dispatch_eq]
  step with extract_access_sound ty laneIndex a b valid as ⟨result, value, exactResult, source⟩
  exact ⟨value, by rw [exactResult], source⟩

end Exec.Interp.Simd
