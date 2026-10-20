import Exec.Spec.SimdFloatUnaryChoices
import Exec.Spec.Choices.SimdFirstProduct
import Exec.Spec.Choices.VectorFirstChoice
namespace Exec.Spec.Simd
open SpecExt.Builtins

theorem float_unary_result_first (ty : Fnn) (op : vunop_Fnn_N) (x result : BitVec 128)
    (allowed : ∀ j, j < 128/lsize (lanetype_Fnn ty) →
      (floatUnaryChoices (lsize (lanetype_Fnn ty)) op
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat)).head? =
        some (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) result j).toNat)) :
    (floatUnaryResults ty op x).head? = some (uN.mk_uN result.toNat) := by
  have tuple : (setproduct_ lane_ (Map (floatUnaryLaneChoices ty op)
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat)))).head? =
      some (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN result.toNat)) := by
    rw [lanes_map_words,lanes_map_words]
    simp only [Map,List.map_map]
    apply head_setproduct_map
    intro j member
    have chosen := allowed j (List.mem_range.mp member)
    cases ty
    all_goals simp only [Function.comp_def,floatUnaryLaneChoices,Map,laneOfBits,lanetype_Fnn,lsize,size,valtype_numtype,proj_lane__1,Option.get!_some,List.head?_map] at chosen ⊢
    all_goals rw [chosen]
    all_goals rfl
  simp only [Map] at tuple
  simp only [floatUnaryResults,Map,List.head?_map,tuple,Option.map_some,lanes_roundtrip]

theorem float_unary_chosen (occurrence : Nat) (ty : Fnn) (op : vunop_Fnn_N) (x result : BitVec 128)
    (first : ∀ j, j < 128/lsize (lanetype_Fnn ty) →
      (floatUnaryChoices (lsize (lanetype_Fnn ty)) op
        (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat)).head? =
        some (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) result j).toNat)) :
    ChosenVector firstVectorChoice occurrence
      (.unary (shapeOf (lanetype_Fnn ty)) (floatUnarySource ty op) (.mk_uN x.toNat))
      (some (.mk_uN result.toNat)) := by
  have head := float_unary_result_first ty op x result first
  apply chosen_vector_from_first occurrence
  · apply VectorResultAllowed.unary (float_unary_relation ty op x)
    · obtain ⟨tail,eq⟩ := List.head?_eq_some_iff.mp head
      rw [eq]
      simp
    · exact const_wf x
    · exact .admininstr_case_25 _ _ (shapeOf_wf _) (float_unary_source_wf ty op)
    · exact const_wf result
  · exact ⟨_,float_unary_relation ty op x,head⟩
end Exec.Spec.Simd
