import Exec.Spec.Choices.VectorFirstChoice
import Exec.Spec.SimdConvertIntegerStep
import Exec.Spec.SimdTruncSatStep
import Exec.Spec.SimdExtendSource
namespace Exec.Spec.Simd
open SpecExt.Builtins

/-- Integer-to-float vector conversion consumes the independently computed
source conversion result, with no NaN alternatives. -/
theorem convert_integer_chosen (occurrence : Nat) (ty : Fnn) (sign : sx) (x result : BitVec 128)
    (packed : uN.mk_uN result.toNat = convertIntegerResult ty sign x) :
    ChosenVector firstVectorChoice occurrence
      (.convert (shapeOf .I32) (shapeOf (lanetype_Fnn ty)) (convertIntegerSource ty sign) (.mk_uN x.toNat))
      (some (.mk_uN result.toNat)) := by
  apply chosen_vector_from_first occurrence
  · apply VectorResultAllowed.convert (convert_integer_vector_relation ty sign x result packed)
    · exact const_wf x
    · exact .admininstr_case_39 _ _ _ (shapeOf_wf _) (shapeOf_wf _) (convert_integer_source_wf ty sign)
    · exact const_wf result
  · change vectorConversionFirst (convertIntegerSource ty sign) (.mk_uN x.toNat) = some (some (.mk_uN result.toNat))
    have input : BitVec.ofNat 128 x.toNat = x := by rw [BitVec.ofNat_toNat,BitVec.setWidth_eq]
    cases ty <;> simp only [convertIntegerSource,convertIntegerCount,convertIntegerHalf,lanetype_Fnn,lanetype_Jnn,lsize,psize,size,valtype_numtype,Option.get!_some,Nat.reduceDiv,vectorConversionFirst,proj_uN_0,input,←packed]

theorem trunc_sat_chosen (occurrence : Nat) (ty : Fnn) (sign : sx) (x result : BitVec 128)
    (packed : uN.mk_uN result.toNat = truncSatResult ty sign x) :
    ChosenVector firstVectorChoice occurrence
      (.convert (shapeOf (lanetype_Fnn ty)) (shapeOf .I32) (truncSatSource ty sign) (.mk_uN x.toNat))
      (some (.mk_uN result.toNat)) := by
  apply chosen_vector_from_first occurrence
  · apply VectorResultAllowed.convert (trunc_sat_vector_relation ty sign x result packed)
    · exact const_wf x
    · exact .admininstr_case_39 _ _ _ (shapeOf_wf _) (shapeOf_wf _) (trunc_sat_source_wf ty sign)
    · exact const_wf result
  · change vectorConversionFirst (truncSatSource ty sign) (.mk_uN x.toNat) = some (some (.mk_uN result.toNat))
    have input : BitVec.ofNat 128 x.toNat = x := by rw [BitVec.ofNat_toNat,BitVec.setWidth_eq]
    cases ty <;> simp only [truncSatSource,truncSatCount,truncSatZero,lanetype_Fnn,lanetype_Jnn,lsize,psize,size,valtype_numtype,Option.get!_some,Nat.reduceDiv,vectorConversionFirst,proj_uN_0,input,←packed]

theorem extend_chosen_vector (occurrence : Nat) (ty : WidenWidth) (high signed : Bool) (x result : BitVec 128)
    (packed : uN.mk_uN result.toNat = widenResult ty false high signed x x) :
    ChosenVector firstVectorChoice occurrence
      (.convert (shapeOf (lanetype_Jnn ty.input)) (shapeOf (lanetype_Jnn ty.output))
        (extendOperation ty high signed) (.mk_uN x.toNat)) (some (.mk_uN result.toNat)) := by
  apply chosen_vector_from_first occurrence
  · apply VectorResultAllowed.convert (extend_vector ty high signed x result packed)
    · exact const_wf x
    · simpa only [extendOperation,widenSource,Bool.false_eq_true,ite_false] using extend_source_wf ty high signed
    · exact const_wf result
  · change vectorConversionFirst (extendOperation ty high signed) (.mk_uN x.toNat) = some (some (.mk_uN result.toNat))
    have input : BitVec.ofNat 128 x.toNat = x := by rw [BitVec.ofNat_toNat,BitVec.setWidth_eq]
    cases ty <;> cases high <;> cases signed
    all_goals simp only [extendOperation,WidenWidth.input,WidenWidth.output,WidenWidth.width,WidenWidth.count,
      widenHalf,widenSign,Bool.false_eq_true,Bool.true_eq,ite_false,ite_true,lanetype_Fnn,lanetype_Jnn,lsize,psize,size,valtype_numtype,Option.get!_some,Nat.reduceDiv,vectorConversionFirst,proj_uN_0,input,←packed]
end Exec.Spec.Simd
