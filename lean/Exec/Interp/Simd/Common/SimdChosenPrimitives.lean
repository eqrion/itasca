import Exec.Interp.Simd.Float.SimdFloatUnaryChosen
import Exec.Interp.Simd.Float.SimdFloatBinaryChosen
import Exec.Interp.Simd.Float.SimdFloatResizeChosen
import Exec.Interp.Simd.Common.SimdConversionChosen
import Exec.Spec.Choices.ChosenPure
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Exec.Spec Platform

theorem float_unary_simd_chosen_pure {F : Type} (floats : runtime.platform.FloatOps F)
    {choices : SourceChoices} (vector : choices.vector = firstVectorChoice) (occurrence : Nat)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vunop_Fnn_N) (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (floatUnaryOpcode ty op) offset laneIndex bits x y z memory ⦃ out =>
      ∃ value, out = (.Ok value,memory) ∧ ChosenPure choices occurrence
        (VectorRequest.instructions (.unary (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.floatUnarySource ty op) (.mk_uN x.val))) (vectorOutput (some (.mk_uN value.val))) ⦄ := by
  apply WP.spec_mono (float_unary_simd_chosen floats laws occurrence ty op offset laneIndex bits x y z memory)
  rintro out ⟨value,returned,chosen⟩
  refine ⟨value,returned,ChosenPure.vector ?_⟩
  simpa only [vector] using chosen

theorem float_binary_simd_chosen_pure {F : Type} (floats : runtime.platform.FloatOps F)
    {choices : SourceChoices} (vector : choices.vector = firstVectorChoice) (occurrence : Nat)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vbinop_Fnn_N) (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (floatBinaryOpcode ty op) offset laneIndex bits x y z memory ⦃ out =>
      ∃ value, out = (.Ok value,memory) ∧ ChosenPure choices occurrence
        (VectorRequest.instructions (.binary (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.floatBinarySource ty op) (.mk_uN x.val) (.mk_uN y.val))) (vectorOutput (some (.mk_uN value.val))) ⦄ := by
  apply WP.spec_mono (float_binary_simd_chosen floats laws occurrence ty op offset laneIndex bits x y z memory)
  rintro out ⟨value,returned,chosen⟩
  refine ⟨value,returned,ChosenPure.vector ?_⟩
  simpa only [vector] using chosen

theorem float_resize_simd_chosen_pure {F : Type} (floats : runtime.platform.FloatOps F)
    {choices : SourceChoices} (vector : choices.vector = firstVectorChoice) (occurrence : Nat)
    (laws : FloatOpsCorrect floats) (kind : Spec.Simd.FloatResize) (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (floatResizeOpcode kind) offset laneIndex bits x y z memory ⦃ out =>
      ∃ value, out = (.Ok value,memory) ∧ ChosenPure choices occurrence
        (VectorRequest.instructions (.convert (Spec.Simd.shapeOf (lanetype_Fnn kind.input)) (Spec.Simd.shapeOf (lanetype_Fnn kind.output)) (Spec.Simd.floatResizeSource kind) (.mk_uN x.val))) (vectorOutput (some (.mk_uN value.val))) ⦄ := by
  apply WP.spec_mono (float_resize_simd_chosen floats laws occurrence kind offset laneIndex bits x y z memory)
  rintro out ⟨value,returned,chosen⟩
  refine ⟨value,returned,ChosenPure.vector ?_⟩
  simpa only [vector] using chosen

theorem convert_integer_simd_chosen_pure {F : Type} (floats : runtime.platform.FloatOps F)
    {choices : SourceChoices} (vector : choices.vector = firstVectorChoice) (occurrence : Nat)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (signed : Bool) (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (convertIntegerOpcode ty signed) offset laneIndex bits x y z memory ⦃ out =>
      ∃ value, out = (.Ok value,memory) ∧ ChosenPure choices occurrence
        (VectorRequest.instructions (.convert (Spec.Simd.shapeOf .I32) (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.convertIntegerSource ty (if signed then .S else .U)) (.mk_uN x.val))) (vectorOutput (some (.mk_uN value.val))) ⦄ := by
  apply WP.spec_mono (convert_integer_simd_chosen floats laws occurrence ty signed offset laneIndex bits x y z memory)
  rintro out ⟨value,returned,chosen⟩
  refine ⟨value,returned,ChosenPure.vector ?_⟩
  simpa only [vector] using chosen

theorem trunc_sat_simd_chosen_pure {F : Type} (floats : runtime.platform.FloatOps F)
    {choices : SourceChoices} (vector : choices.vector = firstVectorChoice) (occurrence : Nat)
    (ty : Fnn) (signed : Bool) (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (truncSatOpcode ty signed) offset laneIndex bits x y z memory ⦃ out =>
      ∃ value, out = (.Ok value,memory) ∧ ChosenPure choices occurrence
        (VectorRequest.instructions (.convert (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.shapeOf .I32) (Spec.Simd.truncSatSource ty (if signed then .S else .U)) (.mk_uN x.val))) (vectorOutput (some (.mk_uN value.val))) ⦄ := by
  apply WP.spec_mono (trunc_sat_simd_chosen floats occurrence ty signed offset laneIndex bits x y z memory)
  rintro out ⟨value,returned,chosen⟩
  refine ⟨value,returned,ChosenPure.vector ?_⟩
  simpa only [vector] using chosen

theorem extend_simd_chosen_pure {F : Type} (floats : runtime.platform.FloatOps F)
    {choices : SourceChoices} (vector : choices.vector = firstVectorChoice) (occurrence : Nat)
    (ty : Spec.Simd.WidenWidth) (high signed : Bool) (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (widenOpcode ty false high signed) offset laneIndex bits x y z memory ⦃ out =>
      ∃ value, out = (.Ok value,memory) ∧ ChosenPure choices occurrence
        (VectorRequest.instructions (.convert (Spec.Simd.shapeOf (lanetype_Jnn ty.input)) (Spec.Simd.shapeOf (lanetype_Jnn ty.output)) (Spec.Simd.extendOperation ty high signed) (.mk_uN x.val))) (vectorOutput (some (.mk_uN value.val))) ⦄ := by
  apply WP.spec_mono (extend_simd_chosen floats occurrence ty high signed offset laneIndex bits x y z memory)
  rintro out ⟨value,returned,chosen⟩
  refine ⟨value,returned,ChosenPure.vector ?_⟩
  simpa only [vector] using chosen
end Exec.Interp.Simd
