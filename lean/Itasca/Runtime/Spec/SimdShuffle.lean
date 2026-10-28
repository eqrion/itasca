import Itasca.Runtime.Spec.SimdByteView
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def byteShape : ishape := .mk_ishape (shapeOf .I8)

theorem byteShape_wf : wf_ishape byteShape :=
  .ishape_case_0 .I8 _ (shapeOf_wf .I8) rfl

theorem shuffle_step (x y result : BitVec 128) (indices : List laneidx)
    (lengthEq : indices.length = 16)
    (bounded : ∀ index ∈ indices, proj_uN_0 index < 32)
    (packed : uN.mk_uN result.toNat = inv_lanes_ (shapeOf .I8)
      ((List.range 16).map (fun k => lane_.mk_lane__0 .I8
        ((byteWords x ++ byteWords y)[proj_uN_0 indices[k]!]!)))) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat), .VCONST .V128 (.mk_uN y.toNat),
      .VSHUFFLE byteShape indices] [.VCONST .V128 (.mk_uN result.toNat)] := by
  have indexBound (k : Nat) (hk : k < 16) : proj_uN_0 indices[k]! < 32 := by
    apply bounded
    rw [_root_.getElem!_pos indices k (by omega)]
    exact List.getElem_mem _
  have wordsWf : Forall (fun word => wf_lane_ .I8 (.mk_lane__0 .I8 word)) (byteWords x ++ byteWords y) := by
    intro word member
    rcases List.mem_append.mp member with left | right
    · exact byteWords_wf x word left
    · exact byteWords_wf y word right
  apply Step_pure.vshuffle (.mk_uN x.toNat) (.mk_uN y.toNat) .I8 16 indices
    (.mk_uN result.toNat) (byteWords x ++ byteWords y) 0
  · change (byteWords x ++ byteWords y).map (lane_.mk_lane__0 .I8) = _
    rw [List.map_append,byteWords_lanes,byteWords_lanes]
    rfl
  · intro k member
    simpa using indexBound k (List.mem_range.mp member)
  · intro k member
    simpa [lengthEq] using List.mem_range.mp member
  · exact packed
  · exact const_wf x
  · exact const_wf y
  · apply wf_admininstr.admininstr_case_32 _ _ byteShape_wf
    · intro index member
      have bound := bounded index member
      cases index with
      | mk_uN n =>
        exact unsigned_wf_of_lt 8 n (by change n < 32 at bound; omega)
    · exact ⟨rfl,lengthEq⟩
  · exact const_wf result
  · exact wordsWf
  · exact shapeOf_wf .I8
  · intro k member
    apply wordsWf
    have bound : proj_uN_0 indices[k]! < (byteWords x ++ byteWords y).length := by
      simpa using indexBound k (List.mem_range.mp member)
    rw [_root_.getElem!_pos (byteWords x ++ byteWords y) (proj_uN_0 indices[k]!) bound]
    exact List.getElem_mem _

end Itasca.Runtime.Spec.Simd
