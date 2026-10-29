import Itasca.Runtime.Spec.SegmentCopy
import Aeneas.Data.List.List
namespace Itasca.Runtime.Spec.Segment

/-- The sequential source writes copy the selected interval and preserve every
position outside it. The source list is independent of the destination. -/
theorem copy_into_effect {T : Type} [Inhabited T] (before source : List T) (dst src count : Nat)
    (sourceBound : src + count ≤ source.length) (targetBound : dst + count ≤ before.length) :
    (∀ j, j < count → (copyInto before source dst src count)[dst + j]? = source[src + j]?) ∧
    (∀ j, j < dst ∨ dst + count ≤ j → (copyInto before source dst src count)[j]? = before[j]?) := by
  induction count generalizing before dst src with
  | zero => simp [copyInto]
  | succ count ih =>
    obtain ⟨copied, outside⟩ := ih (before.set dst source[src]!) (dst+1) (src+1)
      (by omega) (by simpa using (show dst+1+count ≤ before.length by omega))
    constructor
    · intro j bound
      cases j with
      | zero =>
        have first := outside dst (Or.inl (by omega))
        have sourceInside : src < source.length := by omega
        have targetInside : dst < before.length := by omega
        simpa [copyInto, sourceInside, targetInside] using first
      | succ j =>
        have previous := copied j (by omega)
        simpa only [copyInto, Nat.add_assoc, Nat.add_comm 1 j] using previous
    · intro j bound
      have tailOutside := outside j (by omega)
      have distinct : dst ≠ j := by omega
      simpa only [copyInto, List.getElem?_set, distinct, if_false] using tailOutside

/-- Source byte-at-a-time initialization equals the slice replacement used by
the extracted memory-buffer operation. -/
theorem copy_into_eq_set_slice {T : Type} [Inhabited T] (before source : List T) (dst src count : Nat)
    (sourceBound : src + count ≤ source.length) (targetBound : dst + count ≤ before.length) :
    copyInto before source dst src count = before.setSlice! dst (source.slice src (src+count)) := by
  have sliceLength : (source.slice src (src+count)).length = count := by
    rw [List.slice_length]
    omega
  obtain ⟨copied, outside⟩ := copy_into_effect before source dst src count sourceBound targetBound
  apply List.ext_getElem?
  intro index
  by_cases first : index < dst
  · rw [List.setSlice!_getElem?_prefix _ _ _ _ first]
    exact outside index (Or.inl first)
  · by_cases last : dst+count ≤ index
    · rw [List.setSlice!_getElem?_suffix _ _ _ _ (by omega)]
      exact outside index (Or.inr last)
    · rw [List.setSlice!_getElem?_middle _ _ _ _ (by omega),
        List.getElem?_slice _ _ _ _ (by omega)]
      have equal : dst + (index-dst) = index := by omega
      simpa only [equal] using copied (index-dst) (by omega)
end Itasca.Runtime.Spec.Segment
