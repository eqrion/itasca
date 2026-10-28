import Itasca.Runtime.Spec.SimdConvertIntegerSource
import Itasca.Runtime.Spec.SimdFloatUnaryChoices
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem convert_integer_packed (ty : Fnn) (sign : sx) (x result : BitVec 128)
    (allowed : ∀ j, j < convertIntegerCount ty →
      floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) result j).toNat =
        convert__ 32 (lsize (lanetype_Fnn ty)) sign (.mk_uN (laneWord .I32 x j).toNat)) :
    uN.mk_uN result.toNat = convertIntegerResult ty sign x := by
  rw [←lanes_roundtrip (lanetype_Fnn ty) result]
  apply congrArg (inv_lanes_ (shapeOf (lanetype_Fnn ty)))
  rw [lanes_map_words]
  unfold convertIntegerWords
  apply List.map_congr_left
  intro j member
  have chosen := allowed j (List.mem_range.mp member)
  cases ty <;> exact congrArg (lane_.mk_lane__1 _) chosen

theorem convert_integer_step (ty : Fnn) (sign : sx) (x result : BitVec 128)
    (allowed : ∀ j, j < convertIntegerCount ty →
      floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) result j).toNat =
        convert__ 32 (lsize (lanetype_Fnn ty)) sign (.mk_uN (laneWord .I32 x j).toNat)) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),
      .VCVTOP (shapeOf (lanetype_Fnn ty)) (shapeOf .I32) (convertIntegerSource ty sign)]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  have packed := convert_integer_packed ty sign x result allowed
  apply Step_pure.vcvtop _ _ _ _ _ (some (.mk_uN result.toNat))
  · exact convert_integer_vector_relation ty sign x result packed
  · simp
  · rfl
  · exact const_wf x
  · apply wf_admininstr.admininstr_case_39
    · exact shapeOf_wf _
    · exact shapeOf_wf _
    · exact convert_integer_source_wf ty sign
  · exact const_wf result

end Itasca.Runtime.Spec.Simd
