import Exec.Spec.TableFillAlgebra
import Exec.Spec.SegmentCopySlice
namespace Exec.Spec.Segment

theorem fillInto_effect {T : Type} (before : List T) (dst count : Nat) (value : T)
    (targetBound : dst+count ≤ before.length) :
    (∀ j, j < count → (fillInto before dst value count)[dst+j]? = some value) ∧
    (∀ j, j < dst ∨ dst+count ≤ j → (fillInto before dst value count)[j]? = before[j]?) := by
  induction count generalizing before dst with
  | zero => simp [fillInto]
  | succ count ih =>
    obtain ⟨filled,outside⟩ := ih (before.set dst value) (dst+1)
      (by simpa using (show dst+1+count ≤ before.length by omega))
    constructor
    · intro j bound
      cases j with
      | zero =>
        have first := outside dst (Or.inl (by omega))
        have targetInside : dst < before.length := by omega
        simpa [fillInto,targetInside] using first
      | succ j =>
        have previous := filled j (by omega)
        simpa only [fillInto,Nat.add_assoc,Nat.add_comm 1 j] using previous
    · intro j bound
      have tailOutside := outside j (by omega)
      have distinct : dst ≠ j := by omega
      simpa only [fillInto,List.getElem?_set,distinct,if_false] using tailOutside

theorem fillInto_eq_setSlice {T : Type} (before : List T) (dst count : Nat) (value : T)
    (targetBound : dst+count ≤ before.length) :
    fillInto before dst value count = before.setSlice! dst (List.replicate count value) := by
  obtain ⟨filled,outside⟩ := fillInto_effect before dst count value targetBound
  apply List.ext_getElem?
  intro index
  by_cases first : index < dst
  · rw [List.setSlice!_getElem?_prefix _ _ _ _ first]
    exact outside index (Or.inl first)
  · by_cases last : dst+count ≤ index
    · rw [List.setSlice!_getElem?_suffix _ _ _ _ (by simp; omega)]
      exact outside index (Or.inr last)
    · rw [List.setSlice!_getElem?_middle _ _ _ _ (by simp; omega)]
      have equal : dst+(index-dst) = index := by omega
      simpa only [equal,List.getElem?_replicate,show index-dst<count from by omega,if_true] using filled (index-dst) (by omega)
end Exec.Spec.Segment
