import Itasca.Runtime.Spec.Simd.Shift
import SpecExt.Builtins.Counts

/-!
Lane-word and source interpretations of population count.

Main declarations: `popcountWords` and `popcountSource`. A direct consumer is `Interp.Simd.Integer.PopcountSound`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def popcountWords (bits : BitVec 128) : List uN :=
  (List.range 16).map (fun j => .mk_uN (population (integerBits 8 (vectorLane .I8 bits j).toNat)))

def popcountSource : admininstr :=
  .VUNOP (shapeOf .I8) (.mk_vunop__0 .I8 16 .POPCNT)

theorem popcount_step (bits result : BitVec 128)
    (packed : uN.mk_uN result.toNat = inv_lanes_ (shapeOf .I8)
      ((popcountWords bits).map (lane_.mk_lane__0 .I8))) :
    Step_pure [.VCONST .V128 (.mk_uN bits.toNat),popcountSource]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  let inputs := (List.range 16).map
    (fun j => lane_.mk_lane__0 .I8 (.mk_uN (vectorLane .I8 bits j).toNat))
  have inputEq : inputs = lanes_ (shapeOf .I8) (.mk_uN bits.toNat) := by
    rw [vector_lanes]; rfl
  have projected : Forall (fun lane => proj_lane__0 lane ≠ none) inputs := by
    intro lane member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    simp [proj_lane__0]
  have resultEq : uN.mk_uN result.toNat = inv_lanes_ (shapeOf .I8)
      (inputs.map (fun lane => lane_.mk_lane__0 .I8 (ipopcnt_ 8 (Option.get! (proj_lane__0 lane))))) := by
    simpa only [popcountWords,inputs,List.map_map,Function.comp_def,ipopcnt_,ibits_,proj_lane__0,Option.get!,proj_uN_0] using packed
  have resultWf : Forall (fun lane => wf_lane_ .I8
      (.mk_lane__0 .I8 (ipopcnt_ 8 (Option.get! (proj_lane__0 lane))))) inputs := by
    intro lane member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    apply laneOfBits_wf .I8
    have bound := population_bits_le 8 (vectorLane .I8 bits j).toNat
    change population (integerBits 8 (vectorLane .I8 bits j).toNat) < 256
    omega
  have related : fun_vunop_ (shapeOf .I8) (.mk_vunop__0 .I8 16 .POPCNT)
      (.mk_uN bits.toNat) (some [.mk_uN result.toNat]) :=
    .fun_vunop__case_10 _ _ _ inputs _ inputEq projected resultEq (shapeOf_wf _) projected resultWf rfl
  apply Step_pure.vunop _ _ _ _ (some [.mk_uN result.toNat]) related
  · simp
  · simp
  · simp
  · exact const_wf bits
  · apply wf_admininstr.admininstr_case_25 _ _ (shapeOf_wf _)
    apply wf_vunop_.vunop__case_0 _ .I8 16 .POPCNT _ rfl
    exact .vunop_Jnn_N_case_2 _ _ rfl
  · exact const_wf result
end Itasca.Runtime.Spec.Simd
