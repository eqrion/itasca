import Exec.Spec.SimdCompareShape
import SpecExt.Builtins.LaneMap
namespace Exec.Spec.Simd
open SpecExt.Builtins

theorem forall3_map {I A B C : Type} (items : List I) (f : I → A) (g : I → B) (h : I → C)
    (P : A → B → C → Prop) (each : ∀ i ∈ items, P (f i) (g i) (h i)) :
    Forall₃ P (items.map f) (items.map g) (items.map h) := by
  induction items with
  | nil => simp [Forall₃]
  | cons head tail ih =>
    have atHead := each head (by simp)
    have atTail := ih (by intro i member; exact each i (by simp [member]))
    simpa [Forall₃] using And.intro atHead atTail

def laneWord (ty : lanetype) (bits : BitVec 128) (j : Nat) : BitVec (lsize ty) :=
  (bits >>> (lsize ty*j)).setWidth (lsize ty)

theorem lanes_map_words (ty : lanetype) (bits : BitVec 128) :
    lanes_ (shapeOf ty) (.mk_uN bits.toNat) =
      (List.range (128/lsize ty)).map (fun j => laneOfBits ty (laneWord ty bits j).toNat) := by
  apply unpackLanes_eq_map
  intro j valid
  simp [proj_uN_0,laneWord,BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]

def comparisonAnswers (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) : List uN :=
  (List.range (128/lsize (lanetype_Jnn ty))).map (fun j =>
    .mk_uN (nat_of_bool (integerLaneCompare op (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j))))

theorem integer_lanes_nonempty (ty : Jnn) (x : BitVec 128) :
    Forall (fun lane => proj_lane__0 lane ≠ none) (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat)) := by
  rw [lanes_map_words]
  intro lane member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  cases ty <;> simp [laneOfBits,lanetype_Jnn,proj_lane__0]

theorem comparison_answers_relation (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) :
    Forall₃ (fun answer a b => IntegerLaneRel op (lsize (lanetype_Jnn ty))
      (Option.get! (proj_lane__0 a)) (Option.get! (proj_lane__0 b)) answer)
      (comparisonAnswers ty op x y)
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat))
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN y.toNat)) := by
  rw [lanes_map_words,lanes_map_words]
  apply forall3_map
  intro j member
  have relation := integer_lane_compare_relation op (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j)
  cases ty <;> exact relation

theorem comparison_answers_length (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) :
    (comparisonAnswers ty op x y).length = 128/lsize (lanetype_Jnn ty) := by
  simp [comparisonAnswers]

theorem comparison_answers_wf (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) :
    Forall (fun answer => wf_uN 1 (.mk_uN (proj_uN_0 answer))) (comparisonAnswers ty op x y) := by
  intro answer member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  cases integerLaneCompare op (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j) <;>
    apply wf_uN.uN_case_0 <;> decide

end Exec.Spec.Simd
