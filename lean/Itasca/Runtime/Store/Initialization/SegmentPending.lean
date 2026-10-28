import Itasca.Runtime.Store.Initialization.BulkTable
import Itasca.Runtime.Spec.SegmentInitCases
import Itasca.Runtime.Spec.Context

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

def segmentValue (word : U64) : val := .CONST .I32 (.mk_num__0 .I32 (.mk_uN (bulkWord word).val))
def segmentPending (slots : List U64) (count : Nat) : List val := (slots.take count).map segmentValue

theorem segmentValue_wf (word : U64) : wf_val (segmentValue word) := by
  constructor
  exact .num__case_0 .I32 .I32 _ (by decide) (Spec.Segment.index_wf _ (by scalar_tac)) rfl

theorem segmentPending_wf (slots : List U64) (count : Nat) : Forall wf_val (segmentPending slots count) := by
  intro value member
  obtain ⟨word,_,rfl⟩ := List.mem_map.mp member
  exact segmentValue_wf word

theorem segmentPending_zero (slots : List U64) : segmentPending slots 0 = [] := rfl

theorem segmentPending_set (slots : List U64) (count : Nat) (bits : U32) (inside : count < slots.length) :
    segmentPending (slots.set count (UScalar.cast .U64 bits)) (count+1) =
      segmentPending slots count ++ [.CONST .I32 (.mk_num__0 .I32 (.mk_uN bits.val))] := by
  have bound : count < (slots.set count (UScalar.cast .U64 bits)).length := by simpa using inside
  unfold segmentPending
  rw [List.take_succ_eq_append_getElem bound,List.take_set_of_le (Nat.le_refl count)]
  simp only [List.map_append,List.map_cons,List.map_nil,List.getElem_set_self]
  congr 2
  unfold segmentValue
  have exactBits : (bulkWord (UScalar.cast .U64 bits)).val = bits.val := by scalar_tac
  rw [exactBits]

theorem segmentPending_three (slots : List U64) (a b c : U64)
    (first : slots[0]? = some a) (second : slots[1]? = some b) (third : slots[2]? = some c) :
    vals (segmentPending slots 3) = Spec.Segment.operands (bulkWord a).val (bulkWord b).val (bulkWord c).val := by
  cases slots with
  | nil => simp at first
  | cons x xs =>
    simp only [List.getElem?_cons_zero,Option.some.injEq] at first
    subst x
    cases xs with
    | nil => simp at second
    | cons y ys =>
      simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at second
      subst y
      cases ys with
      | nil => simp at third
      | cons z zs =>
        simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at third
        subst z
        rfl

end Itasca.Runtime.Store
