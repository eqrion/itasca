import Itasca.Runtime.Spec.CopySnapshot
import Itasca.Runtime.Spec.SegmentCopySlice
namespace Itasca.Runtime.Spec.Segment

def copyForwardPlain {T : Type} [Inhabited T] (words : List T) (dst src : Nat) : Nat → List T
  | 0 => words
  | n+1 => copyForwardPlain (words.set dst words[src]!) (dst+1) (src+1) n

theorem copyForwardPlain_snapshot {T : Type} [Inhabited T] (before current : List T) (dst src index remaining count : Nat)
    (state : CopyPrefix before current dst src index) (progress : index+remaining=count)
    (direction : dst ≤ src) (sourceBound : src+count ≤ before.length) (targetBound : dst+count ≤ before.length) :
    copyForwardPlain current (dst+index) (src+index) remaining = before.setSlice! dst (before.slice src (src+count)) := by
  induction remaining generalizing current index with
  | zero =>
    have last : index=count := by omega
    exact (last ▸ state).complete sourceBound targetBound
  | succ remaining ih =>
    have fresh := state.write direction (by omega) (by omega)
    simpa only [copyForwardPlain,Nat.add_assoc] using ih _ (index+1) fresh (by omega)

def copyBackwardFrom {T : Type} [Inhabited T] (words source : List T) (dst src : Nat) : Nat → List T
  | 0 => words
  | n+1 => copyBackwardFrom (words.set (dst+n) source[src+n]!) source dst src n

@[simp] theorem copyBackwardFrom_length {T : Type} [Inhabited T] (words source : List T) (dst src count : Nat) :
    (copyBackwardFrom words source dst src count).length = words.length := by
  induction count generalizing words with
  | zero => rfl
  | succ n ih => simp only [copyBackwardFrom,ih,List.length_set]

theorem copyBackwardFrom_effect {T : Type} [Inhabited T] (before source : List T) (dst src count : Nat)
    (sourceBound : src+count ≤ source.length) (targetBound : dst+count ≤ before.length) :
    (∀ j, j < count → (copyBackwardFrom before source dst src count)[dst+j]? = source[src+j]?) ∧
    (∀ j, j < dst ∨ dst+count ≤ j → (copyBackwardFrom before source dst src count)[j]? = before[j]?) := by
  induction count generalizing before with
  | zero => simp [copyBackwardFrom]
  | succ n ih =>
    obtain ⟨copied,outside⟩ := ih (before.set (dst+n) source[src+n]!) (by omega) (by simp; omega)
    constructor
    · intro j bound
      by_cases last : j=n
      · subst j
        have old := outside (dst+n) (Or.inr (by omega))
        have sourceInside : src+n < source.length := by omega
        have targetInside : dst+n < before.length := by omega
        simpa [copyBackwardFrom,sourceInside,targetInside] using old
      · simpa only [copyBackwardFrom] using copied j (by omega)
    · intro j bound
      have old := outside j (by omega)
      have distinct : dst+n ≠ j := by omega
      simpa only [copyBackwardFrom,List.getElem?_set,distinct,if_false] using old

theorem copyBackwardFrom_snapshot {T : Type} [Inhabited T] (before source : List T) (dst src count : Nat)
    (sourceBound : src+count ≤ source.length) (targetBound : dst+count ≤ before.length) :
    copyBackwardFrom before source dst src count = before.setSlice! dst (source.slice src (src+count)) := by
  have sliceLength : (source.slice src (src+count)).length = count := by rw [List.slice_length]; omega
  obtain ⟨copied,outside⟩ := copyBackwardFrom_effect before source dst src count sourceBound targetBound
  apply List.ext_getElem?
  intro index
  by_cases first : index < dst
  · rw [List.setSlice!_getElem?_prefix _ _ _ _ first]
    exact outside index (Or.inl first)
  · by_cases last : dst+count ≤ index
    · rw [List.setSlice!_getElem?_suffix _ _ _ _ (by omega)]
      exact outside index (Or.inr last)
    · rw [List.setSlice!_getElem?_middle _ _ _ _ (by omega),List.getElem?_slice _ _ _ _ (by omega)]
      have equal : dst+(index-dst)=index := by omega
      simpa only [equal] using copied (index-dst) (by omega)
end Itasca.Runtime.Spec.Segment
