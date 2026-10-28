import Exec.Spec.SimdFloatBinarySource
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem float_binary_result_member (ty : Fnn) (op : vbinop_Fnn_N) (x y result : BitVec 128)
    (allowed : ∀ j, j < 128/lsize (lanetype_Fnn ty) →
      floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) result j).toNat ∈
        floatBinaryChoices (lsize (lanetype_Fnn ty)) op
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat)
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) y j).toNat)) :
    uN.mk_uN result.toNat ∈ floatBinaryResults ty op x y := by
  apply List.mem_map.mpr
  refine ⟨lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN result.toNat),?_,lanes_roundtrip _ result⟩
  rw [lanes_map_words,lanes_map_words,lanes_map_words]
  rw [map2_map]
  apply mem_setproduct_map
  intro j member
  have chosen := allowed j (List.mem_range.mp member)
  cases ty <;> exact List.mem_map.mpr ⟨_,chosen,rfl⟩

theorem float_binary_step (ty : Fnn) (op : vbinop_Fnn_N) (x y result : BitVec 128)
    (allowed : ∀ j, j < 128/lsize (lanetype_Fnn ty) →
      floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) result j).toNat ∈
        floatBinaryChoices (lsize (lanetype_Fnn ty)) op
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat)
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) y j).toNat)) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),
      .VBINOP (shapeOf (lanetype_Fnn ty)) (floatBinarySource ty op)] [.VCONST .V128 (.mk_uN result.toNat)] := by
  have chosen := float_binary_result_member ty op x y result allowed
  apply Step_pure.vbinop_val _ _ _ _ _ (some (floatBinaryResults ty op x y)) (float_binary_relation ty op x y)
  · exact List.length_pos_of_mem chosen
  · simp
  · simpa only [Option.get!_some,List.contains_iff_mem] using chosen
  · exact const_wf x
  · exact const_wf y
  · exact .admininstr_case_26 _ _ (shapeOf_wf _) (float_binary_source_wf ty op)
  · exact const_wf result

end Itasca.Runtime.Spec.Simd
