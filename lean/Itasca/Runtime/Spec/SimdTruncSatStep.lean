import Itasca.Runtime.Spec.SimdTruncSatSource
import Itasca.Runtime.Spec.SimdFloatUnaryChoices
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem trunc_sat_packed (ty : Fnn) (sign : sx) (x result : BitVec 128)
    (allowed : ∀ j, j < truncSatCount ty →
      uN.mk_uN (laneWord .I32 result j).toNat = truncSatWord (lsize (lanetype_Fnn ty)) sign
        (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat))
    (zeroed : ∀ j, truncSatCount ty ≤ j → j < 4 → laneWord .I32 result j = 0) :
    uN.mk_uN result.toNat = truncSatResult ty sign x := by
  rw [←lanes_roundtrip .I32 result]
  apply congrArg (inv_lanes_ (shapeOf .I32))
  rw [lanes_map_words]
  change (List.range 4).map _ = _
  have mapped : (List.range 4).map (fun j => laneOfBits .I32 (laneWord .I32 result j).toNat) =
      (List.range 4).map (fun j => if j < truncSatCount ty then truncSatLane ty sign
        (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat)
        else .mk_lane__0 .I32 (.mk_uN 0)) := by
    apply List.map_congr_left
    intro j member
    by_cases valid : j < truncSatCount ty
    · rw [if_pos valid]
      exact congrArg (lane_.mk_lane__0 .I32) (allowed j valid)
    · rw [if_neg valid,zeroed j (by omega) (List.mem_range.mp member)]
      rfl
  rw [mapped]
  cases ty <;> rfl

theorem trunc_sat_step (ty : Fnn) (sign : sx) (x result : BitVec 128)
    (allowed : ∀ j, j < truncSatCount ty →
      uN.mk_uN (laneWord .I32 result j).toNat = truncSatWord (lsize (lanetype_Fnn ty)) sign
        (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat))
    (zeroed : ∀ j, truncSatCount ty ≤ j → j < 4 → laneWord .I32 result j = 0) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),
      .VCVTOP (shapeOf .I32) (shapeOf (lanetype_Fnn ty)) (truncSatSource ty sign)]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  have packed := trunc_sat_packed ty sign x result allowed zeroed
  apply Step_pure.vcvtop _ _ _ _ _ (some (.mk_uN result.toNat))
  · exact trunc_sat_vector_relation ty sign x result packed
  · simp
  · rfl
  · exact const_wf x
  · apply wf_admininstr.admininstr_case_39
    · exact shapeOf_wf _
    · exact shapeOf_wf _
    · exact trunc_sat_source_wf ty sign
  · exact const_wf result

end Itasca.Runtime.Spec.Simd
