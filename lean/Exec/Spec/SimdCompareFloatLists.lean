import Exec.Spec.SimdCompareFloat
namespace Exec.Spec.Simd
open SpecExt.Builtins

theorem forall2_map {I A B : Type} (items : List I) (f : I → A) (g : I → B)
    (P : A → B → Prop) (each : ∀ i ∈ items, P (f i) (g i)) :
    Forall₂ P (items.map f) (items.map g) := by
  induction items with
  | nil => simp [Forall₂]
  | cons head tail ih =>
    have atHead := each head (by simp)
    have atTail := ih (by intro i member; exact each i (by simp [member]))
    simpa [Forall₂] using And.intro atHead atTail

theorem map2_map {I A B C : Type} (items : List I) (f : I → A) (g : I → B) (h : A → B → C) :
    Map₂ h (items.map f) (items.map g) = items.map (fun i => h (f i) (g i)) := by
  induction items with
  | nil => rfl
  | cons head tail ih => simpa [Map₂,List.ap] using congrArg (List.cons (h (f head) (g head))) ih

def floatComparisonMasks (ty : Fnn) (op : vrelop_Fnn_N) (x y : BitVec 128) : List uN :=
  Map₂ (fun a b => extend__ 1 (lsize (lanetype_Fnn ty)) .S
    (.mk_uN (proj_uN_0 (floatComparisonValue (lsize (lanetype_Fnn ty)) op
      (Option.get! (proj_lane__1 a)) (Option.get! (proj_lane__1 b))))))
    (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat))
    (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN y.toNat))

theorem float_lanes_nonempty (ty : Fnn) (x : BitVec 128) :
    Forall (fun lane => proj_lane__1 lane ≠ none) (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat)) := by
  rw [lanes_map_words]
  intro lane member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  cases ty <;> simp [laneOfBits,lanetype_Fnn,proj_lane__1]

theorem float_comparison_answers_wf (ty : Fnn) (op : vrelop_Fnn_N) (x y : BitVec 128) :
    Forall₂ (fun a b => wf_uN 1 (.mk_uN (proj_uN_0
      (floatComparisonValue (lsize (lanetype_Fnn ty)) op
        (Option.get! (proj_lane__1 a)) (Option.get! (proj_lane__1 b))))))
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat))
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN y.toNat)) := by
  intro pair member
  rw [float_comparison_value]
  cases floatComparisonBool (lsize (lanetype_Fnn ty)) op
    (Option.get! (proj_lane__1 pair.1)) (Option.get! (proj_lane__1 pair.2)) <;>
      apply wf_uN.uN_case_0 <;> decide

theorem float_comparison_masks_wf (ty : Fnn) (op : vrelop_Fnn_N) (x y : BitVec 128) :
    Forall (fun mask => wf_lane_ (lanetype_Inn (floatCompareInteger ty))
      (.mk_lane__0 (Jnn_Inn (floatCompareInteger ty)) (.mk_uN (proj_uN_0 mask))))
      (floatComparisonMasks ty op x y) := by
  unfold floatComparisonMasks
  rw [lanes_map_words,lanes_map_words,map2_map]
  intro mask member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  rw [float_comparison_value]
  simp only [proj_uN_0,boolean_extend]
  cases ty <;> constructor
  all_goals first | rfl | exact unsigned_wf_of_lt _ _ (BitVec.isLt _)

end Exec.Spec.Simd
