import Exec.Spec.SimdFloatBinaryChoices
import Exec.Spec.Choices.SimdFirstProduct
import Exec.Spec.Choices.VectorFirstChoice
namespace Exec.Spec.Simd
open SpecExt.Builtins

theorem float_binary_result_first (ty : Fnn) (op : vbinop_Fnn_N) (x y result : BitVec 128)
    (allowed : ∀ j, j < 128/lsize (lanetype_Fnn ty) →
      (floatBinaryChoices (lsize (lanetype_Fnn ty)) op
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat)
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) y j).toNat)).head? =
        some (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) result j).toNat)) :
    (floatBinaryResults ty op x y).head? = some (uN.mk_uN result.toNat) := by
  have tuple : (setproduct_ lane_ (Map₂ (floatBinaryLaneChoices ty op)
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat))
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN y.toNat)))).head? =
      some (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN result.toNat)) := by
    rw [lanes_map_words,lanes_map_words,lanes_map_words]
    rw [map2_map]
    apply head_setproduct_map
    intro j member
    have chosen := allowed j (List.mem_range.mp member)
    cases ty
    all_goals simp only [Function.comp_def,floatBinaryLaneChoices,Map,laneOfBits,lanetype_Fnn,lsize,size,valtype_numtype,proj_lane__1,Option.get!_some,List.head?_map] at chosen ⊢
    all_goals rw [chosen]
    all_goals rfl
  try simp only [Map] at tuple
  simp only [floatBinaryResults,Map,List.head?_map,tuple,Option.map_some,lanes_roundtrip]

theorem float_binary_chosen (occurrence : Nat) (ty : Fnn) (op : vbinop_Fnn_N) (x y result : BitVec 128)
    (first : ∀ j, j < 128/lsize (lanetype_Fnn ty) →
      (floatBinaryChoices (lsize (lanetype_Fnn ty)) op
        (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat)
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) y j).toNat)).head? =
        some (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) result j).toNat)) :
    ChosenVector firstVectorChoice occurrence
      (.binary (shapeOf (lanetype_Fnn ty)) (floatBinarySource ty op) (.mk_uN x.toNat) (.mk_uN y.toNat))
      (some (.mk_uN result.toNat)) := by
  have head := float_binary_result_first ty op x y result first
  apply chosen_vector_from_first occurrence
  · apply VectorResultAllowed.binary (float_binary_relation ty op x y)
    · obtain ⟨tail,eq⟩ := List.head?_eq_some_iff.mp head
      rw [eq]
      simp
    · exact const_wf x
    · exact const_wf y
    · exact .admininstr_case_26 _ _ (shapeOf_wf _) (float_binary_source_wf ty op)
    · exact const_wf result
  · exact ⟨_,float_binary_relation ty op x y,head⟩
end Exec.Spec.Simd
