import Itasca.Runtime.Spec.Simd.Shuffle
import Itasca.Runtime.Spec.Simd.ByteSelect

/-!
The source lane-word interpretation of swizzle.

Main declarations: `swizzleWords`. A direct consumer is `Interp.Simd.Lanes.Swizzle`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins
set_option maxRecDepth 4096

def swizzleWords (bits : BitVec 128) : List uN := byteWords bits ++ List.replicate 240 (.mk_uN 0)

@[simp] theorem swizzle_words_length (bits : BitVec 128) : (swizzleWords bits).length = 256 := by
  simp only [swizzleWords,List.length_append,byte_words_length,List.length_replicate]

theorem swizzle_words_wf (bits : BitVec 128) :
    Forall (fun word => wf_lane_ .I8 (.mk_lane__0 .I8 word)) (swizzleWords bits) := by
  intro word member
  rcases List.mem_append.mp member with left | right
  · exact byte_words_wf bits word left
  · obtain ⟨_,rfl⟩ := List.mem_replicate.mp right
    exact .lane__case_0 _ _ _ (unsigned_wf_of_lt 8 0 (by decide)) rfl

theorem byte_lane_index (bits : BitVec 128) (index : Nat) (valid : index < 16) :
    proj_uN_0 (Option.get! (proj_lane__0 ((lanes_ (shapeOf .I8) (.mk_uN bits.toNat))[index]!))) =
      byteAt bits index := by
  rw [byte_lanes_get bits index valid]
  rfl

theorem swizzle_step (x y result : BitVec 128)
    (packed : uN.mk_uN result.toNat = inv_lanes_ (shapeOf .I8)
      ((List.range 16).map (fun k => lane_.mk_lane__0 .I8 ((swizzleWords x)[byteAt y k]!)))) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),.VSWIZZLE byteShape]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vswizzle (.mk_uN x.toNat) (.mk_uN y.toNat) .I8 16 (.mk_uN result.toNat)
    (lanes_ (shapeOf .I8) (.mk_uN y.toNat)) (swizzleWords x) 0
  · rfl
  · exact byte_lanes_integer x
  · change swizzleWords x = Map (fun lane => Option.get! (proj_lane__0 lane))
      (lanes_ (shapeOf .I8) (.mk_uN x.toNat)) ++ List.replicate 240 (.mk_uN 0)
    rw [byte_lanes_unwrap]
    rfl
  · intro k member
    rw [byte_lane_index y k (List.mem_range.mp member),swizzle_words_length]
    exact byte_at_bound y k
  · intro k member
    rw [byte_lanes_get y k (List.mem_range.mp member)]
    simp [proj_lane__0]
  · intro k member
    simpa [lanes_,shapeOf,unpackLanes_length,lsize,psize] using List.mem_range.mp member
  · rw [packed]
    congr 1
    apply List.map_congr_left
    intro k member
    rw [byte_lane_index y k (List.mem_range.mp member)]
    rfl
  · exact const_wf x
  · exact const_wf y
  · exact .admininstr_case_31 _ byte_shape_wf rfl
  · exact const_wf result
  · exact shape_of_wf .I8
  · exact unsigned_wf_of_lt 8 0 (by decide)
  · intro k member
    rw [byte_lane_index y k (List.mem_range.mp member)]
    apply swizzle_words_wf
    have valid : byteAt y k < (swizzleWords x).length := by simpa using byte_at_bound y k
    rw [_root_.getElem!_pos (swizzleWords x) (byteAt y k) valid]
    exact List.getElem_mem _

end Itasca.Runtime.Spec.Simd

namespace Itasca.Runtime.Spec.Simd

theorem swizzle_words_get (bits : BitVec 128) (index : Nat) (valid : index < 256) :
    (swizzleWords bits)[index]! = if index < 16 then .mk_uN (byteAt bits index) else .mk_uN 0 := by
  simp only [swizzleWords,List.getElem!_eq_getElem?_getD,List.getElem?_append,byte_words_length]
  by_cases first : index < 16
  · simpa only [if_pos first,List.getElem!_eq_getElem?_getD] using byte_words_get bits index first
  · simp only [if_neg first,List.getElem?_replicate,if_pos (show index-16 < 240 by omega),Option.getD_some]

end Itasca.Runtime.Spec.Simd
