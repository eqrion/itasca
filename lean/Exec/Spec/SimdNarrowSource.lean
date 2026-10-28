import Exec.Spec.SimdNarrow
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem narrow_lanes_map (ty : NarrowWidth) (signed : Bool) (x : BitVec 128) :
    Map (fun a => narrow__ (lsize (lanetype_Jnn ty.input)) ty.width (if signed then .S else .U)
      (Option.get! (proj_lane__0 a))) (lanes_ (shapeOf (lanetype_Jnn ty.input)) (.mk_uN x.toNat)) =
        narrowWords ty signed x := by
  rw [lanes_map_words]
  simp only [Map,List.map_map,narrowWords,NarrowWidth.count]
  apply List.map_congr_left
  intro j member
  cases ty <;> exact (narrow_bits_source _ signed (laneWord _ x j)).symm

theorem integer_lanes_wf (ty : Jnn) (x : BitVec 128) :
    Forall (wf_lane_ (lanetype_Jnn ty)) (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat)) := by
  rw [lanes_map_words]
  intro lane member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  have wf := unsigned_wf_of_lt (lsize (lanetype_Jnn ty)) (laneWord (lanetype_Jnn ty) x j).toNat (BitVec.isLt _)
  cases ty <;> exact .lane__case_0 _ _ _ wf rfl

theorem narrow_words_wf (ty : NarrowWidth) (signed : Bool) (x : BitVec 128) :
    Forall (fun word => wf_lane_ (lanetype_Jnn ty.output) (.mk_lane__0 ty.output word)) (narrowWords ty signed x) := by
  intro word member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  have wf := unsigned_wf_of_lt ty.width (narrowBits ty.width signed (laneWord (lanetype_Jnn ty.input) x j)).toNat (BitVec.isLt _)
  cases ty <;> exact .lane__case_0 _ _ _ wf rfl

theorem narrow_step (ty : NarrowWidth) (signed : Bool) (x y result : BitVec 128)
    (packed : uN.mk_uN result.toNat = narrowResult ty signed x y) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),narrowSource ty signed]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vnarrow (.mk_uN x.toNat) (.mk_uN y.toNat) ty.output _ ty.input _
    (if signed then .S else .U) (.mk_uN result.toNat)
    (lanes_ (shapeOf (lanetype_Jnn ty.input)) (.mk_uN x.toNat))
    (lanes_ (shapeOf (lanetype_Jnn ty.input)) (.mk_uN y.toNat))
    (narrowWords ty signed x) (narrowWords ty signed y)
  · rfl
  · rfl
  · exact integer_lanes_nonempty _ x
  · exact (narrow_lanes_map ty signed x).symm
  · exact integer_lanes_nonempty _ y
  · exact (narrow_lanes_map ty signed y).symm
  · exact packed
  · exact integer_lanes_wf _ x
  · exact integer_lanes_wf _ y
  · exact const_wf x
  · exact const_wf y
  · exact narrow_source_wf ty signed
  · exact const_wf result
  · exact shapeOf_wf _
  · exact shapeOf_wf _
  · exact narrow_words_wf ty signed x
  · exact narrow_words_wf ty signed y

end Itasca.Runtime.Spec.Simd
