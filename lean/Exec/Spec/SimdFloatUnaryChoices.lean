import Exec.Spec.SimdFloatUnarySource
namespace Exec.Spec.Simd
open SpecExt.Builtins

theorem lanes_roundtrip (ty : lanetype) (bits : BitVec 128) :
    inv_lanes_ (shapeOf ty) (lanes_ (shapeOf ty) (.mk_uN bits.toNat)) = .mk_uN bits.toNat := by
  change uN.mk_uN (packLanes ty (unpackLanes ty (128/lsize ty) bits.toNat)) = _
  rw [pack_unpackLanes,shapeOf_covers,Nat.mod_eq_of_lt bits.isLt]

theorem float_unary_result_member (ty : Fnn) (op : vunop_Fnn_N) (x result : BitVec 128)
    (allowed : ∀ j, j < 128/lsize (lanetype_Fnn ty) →
      floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) result j).toNat ∈
        floatUnaryChoices (lsize (lanetype_Fnn ty)) op
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat)) :
    uN.mk_uN result.toNat ∈ floatUnaryResults ty op x := by
  apply List.mem_map.mpr
  refine ⟨lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN result.toNat),?_,lanes_roundtrip _ result⟩
  rw [lanes_map_words,lanes_map_words]
  change List.map _ _ ∈ setproduct_ _ (List.map _ (List.map _ _))
  rw [List.map_map]
  apply mem_setproduct_map
  intro j member
  have chosen := allowed j (List.mem_range.mp member)
  cases ty <;> exact List.mem_map.mpr ⟨_,chosen,rfl⟩

theorem float_unary_step (ty : Fnn) (op : vunop_Fnn_N) (x result : BitVec 128)
    (allowed : ∀ j, j < 128/lsize (lanetype_Fnn ty) →
      floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) result j).toNat ∈
        floatUnaryChoices (lsize (lanetype_Fnn ty)) op
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat)) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),
      .VUNOP (shapeOf (lanetype_Fnn ty)) (floatUnarySource ty op)] [.VCONST .V128 (.mk_uN result.toNat)] := by
  have chosen := float_unary_result_member ty op x result allowed
  apply Step_pure.vunop _ _ _ _ (some (floatUnaryResults ty op x)) (float_unary_relation ty op x)
  · exact List.length_pos_of_mem chosen
  · simp
  · simpa only [Option.get!_some,List.contains_iff_mem] using chosen
  · exact const_wf x
  · exact .admininstr_case_25 _ _ (shapeOf_wf _) (float_unary_source_wf ty op)
  · exact const_wf result

end Exec.Spec.Simd
