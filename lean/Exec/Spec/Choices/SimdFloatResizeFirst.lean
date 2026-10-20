import Exec.Spec.SimdFloatResizeStep
import Exec.Spec.Choices.SimdFirstProduct
import Exec.Spec.Choices.VectorFirstChoice
namespace Exec.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

theorem float_resize_product_first (kind : FloatResize) (x result : BitVec 128)
    (allowed : ∀ j, j < 2 →
      (floatResizeChoices kind (floatOfBits (lsize (lanetype_Fnn kind.input)) (laneWord (lanetype_Fnn kind.input) x j).toNat)).head? =
        some (floatOfBits (lsize (lanetype_Fnn kind.output)) (laneWord (lanetype_Fnn kind.output) result j).toNat))
    (zeroed : ∀ j, 2 ≤ j → j < 128/lsize (lanetype_Fnn kind.output) → laneWord (lanetype_Fnn kind.output) result j = 0) :
    (floatResizeProducts kind x).head? = some (lanes_ (shapeOf (lanetype_Fnn kind.output)) (.mk_uN result.toNat)) := by
  rw [lanes_map_words]
  cases kind
  · change (setproduct_ lane_ ((List.range 4).map (fun j =>
      if j < 2 then floatResizeLaneChoices .demote (floatOfBits 64 (laneWord .F64 x j).toNat)
      else [.mk_lane__1 .F32 (floatOfBits 32 0)]))).head? = some ((List.range 4).map _)
    apply head_setproduct_map
    intro j member
    by_cases valid : j < 2
    · rw [if_pos valid]
      have head := allowed j valid
      change (floatResizeChoices .demote (floatOfBits 64 (laneWord .F64 x j).toNat)).head? = some (floatOfBits 32 (laneWord .F32 result j).toNat) at head
      simp only [floatResizeLaneChoices,Map,List.head?_map]
      rw [head]
      rfl
    · rw [if_neg valid]
      have zero := zeroed j (by omega) (List.mem_range.mp member)
      change laneWord .F32 result j = 0 at zero
      change _ = some (lane_.mk_lane__1 .F32 (floatOfBits 32 (laneWord .F32 result j).toNat))
      rw [zero]
      rfl
  · change (setproduct_ lane_ ((List.range 2).map (fun j =>
      floatResizeLaneChoices .promote (floatOfBits 32 (laneWord .F32 x j).toNat)))).head? = some ((List.range 2).map _)
    apply head_setproduct_map
    intro j member
    have head := allowed j (List.mem_range.mp member)
    change (floatResizeChoices .promote (floatOfBits 32 (laneWord .F32 x j).toNat)).head? = some (floatOfBits 64 (laneWord .F64 result j).toNat) at head
    simp only [floatResizeLaneChoices,Map,List.head?_map]
    rw [head]
    rfl

theorem float_resize_chosen (occurrence : Nat) (kind : FloatResize) (x result : BitVec 128)
    (allowed : ∀ j, j < 2 →
      (floatResizeChoices kind (floatOfBits (lsize (lanetype_Fnn kind.input)) (laneWord (lanetype_Fnn kind.input) x j).toNat)).head? =
        some (floatOfBits (lsize (lanetype_Fnn kind.output)) (laneWord (lanetype_Fnn kind.output) result j).toNat))
    (zeroed : ∀ j, 2 ≤ j → j < 128/lsize (lanetype_Fnn kind.output) → laneWord (lanetype_Fnn kind.output) result j = 0) :
    ChosenVector firstVectorChoice occurrence
      (.convert (shapeOf (lanetype_Fnn kind.input)) (shapeOf (lanetype_Fnn kind.output))
        (floatResizeSource kind) (.mk_uN x.toNat)) (some (.mk_uN result.toNat)) := by
  have head := float_resize_product_first kind x result allowed zeroed
  have member : lanes_ (shapeOf (lanetype_Fnn kind.output)) (.mk_uN result.toNat) ∈ floatResizeProducts kind x := by
    obtain ⟨tail,eq⟩ := List.head?_eq_some_iff.mp head
    rw [eq]
    simp
  apply chosen_vector_from_first occurrence
  · apply VectorResultAllowed.convert (float_resize_vector_relation kind x result member)
    · exact const_wf x
    · exact .admininstr_case_39 _ _ _ (shapeOf_wf _) (shapeOf_wf _) (float_resize_source_wf kind)
    · exact const_wf result
  · change vectorConversionFirst (floatResizeSource kind) (.mk_uN x.toNat) = some (some (.mk_uN result.toNat))
    have input : BitVec.ofNat 128 x.toNat = x := by rw [BitVec.ofNat_toNat,BitVec.setWidth_eq]
    cases kind
    all_goals simp only [vectorConversionFirst,floatResizeSource,proj_uN_0,input,head,Option.map_some,lanes_roundtrip]
end Exec.Spec.Simd
