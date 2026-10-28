import Itasca.Runtime.Interp.Simd.Common.SimdReplaceRuntime
import Itasca.Runtime.Interp.Simd.Common.SimdReplacePacking
import Itasca.Runtime.Spec.SimdReplace
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

@[step] theorem replace_access_sound (ty : lanetype) (index : U32) (a b : U128)
    (valid : index.val < 128/lsize ty) :
    runtime.interp.simd.access_lane (replaceOpcode ty) index a b ⦃ result =>
      ∃ value, result = .Ok value ∧
        Step_pure [.VCONST .V128 (.mk_uN a.val),
          .CONST (unpack ty) (Spec.Simd.scalarInput ty (UScalar.cast .U64 b).bv),
          .VREPLACE_LANE (Spec.Simd.shapeOf ty) (.mk_uN index.val)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  apply WP.spec_mono (replace_access ty index a b valid)
  rintro result ⟨value, exactResult, bits⟩
  refine ⟨value, exactResult, ?_⟩
  have packed := (congrArg (fun (v : BitVec 128) => uN.mk_uN v.toNat) bits).trans
    (packLanes_write ty index.val a.bv (splatInput ty b).bv valid)
  have source := Spec.Simd.replace_step ty index.val a.bv value.bv (splatInput ty b).bv valid packed
  rw [splatInput_source] at source
  exact source

theorem replace_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : lanetype) (offset laneIndex : U32) (bits a b c : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (replaceOpcode ty) offset laneIndex bits a b c memory =
      Aeneas.Std.bind (runtime.interp.simd.access_lane (replaceOpcode ty) laneIndex a b)
        (fun result => Result.ok (result, memory)) := by
  cases ty <;> unfold runtime.interp.simd.simd replaceOpcode <;> with_unfolding_all rfl

@[step] theorem replace_dispatch_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : lanetype) (offset laneIndex : U32) (bits a b c : U128)
    (memory : Option (Slice U8)) (valid : laneIndex.val < 128/lsize ty) :
    runtime.interp.simd.simd floats (replaceOpcode ty) offset laneIndex bits a b c memory
      ⦃ result => ∃ value, result = (.Ok value, memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN a.val),
          .CONST (unpack ty) (Spec.Simd.scalarInput ty (UScalar.cast .U64 b).bv),
          .VREPLACE_LANE (Spec.Simd.shapeOf ty) (.mk_uN laneIndex.val)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [replace_dispatch_eq]
  step with replace_access_sound ty laneIndex a b valid as ⟨result, value, exactResult, source⟩
  exact ⟨value, by rw [exactResult], source⟩

end Itasca.Runtime.Interp.Simd
