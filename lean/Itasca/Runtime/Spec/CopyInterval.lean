import Itasca.Runtime.Spec.SegmentCopySlice
namespace Itasca.Runtime.Spec.Segment

/-- A left-to-right in-place copy has written exactly its completed prefix.
Reads from the remaining source interval still refer to the original list. -/
structure CopyPrefix {T : Type} (before current : List T) (dst src copied : Nat) : Prop where
  length : current.length = before.length
  written : ∀ j, j < copied → current[dst+j]? = before[src+j]?
  outside : ∀ j, j < dst ∨ dst+copied ≤ j → current[j]? = before[j]?

theorem CopyPrefix.initial {T : Type} (before : List T) (dst src : Nat) : CopyPrefix before before dst src 0 := by
  exact ⟨rfl,by intros; omega,by intros; rfl⟩

theorem CopyPrefix.source {T : Type} [Inhabited T] {before current : List T} {dst src copied : Nat}
    (state : CopyPrefix before current dst src copied) (direction : dst ≤ src) :
    current[src+copied]! = before[src+copied]! := by
  simp only [List.getElem!_eq_getElem?_getD,state.outside (src+copied) (Or.inr (by omega))]

theorem CopyPrefix.write {T : Type} [Inhabited T] {before current : List T} {dst src copied : Nat}
    (state : CopyPrefix before current dst src copied) (direction : dst ≤ src)
    (sourceBound : src+copied < before.length) (targetBound : dst+copied < before.length) :
    CopyPrefix before (current.set (dst+copied) current[src+copied]!) dst src (copied+1) := by
  refine ⟨by simp [state.length],?_,?_⟩
  · intro j bound
    by_cases last : j=copied
    · subst j
      rw [state.source direction]
      simp [List.getElem?_set,state.length,targetBound,List.getElem!_eq_getElem?_getD,
        List.getElem?_eq_getElem sourceBound]
    · have distinct : dst+copied ≠ dst+j := by omega
      simp only [List.getElem?_set,distinct,if_false]
      exact state.written j (by omega)
  · intro j bound
    have distinct : dst+copied ≠ j := by omega
    simp only [List.getElem?_set,distinct,if_false]
    exact state.outside j (by omega)

theorem CopyPrefix.complete {T : Type} {before current : List T} {dst src count : Nat}
    (state : CopyPrefix before current dst src count) (sourceBound : src+count ≤ before.length)
    (targetBound : dst+count ≤ before.length) :
    current = before.setSlice! dst (before.slice src (src+count)) := by
  have sliceLength : (before.slice src (src+count)).length = count := by rw [List.slice_length]; omega
  apply List.ext_getElem?
  intro index
  by_cases first : index < dst
  · rw [List.setSlice!_getElem?_prefix _ _ _ _ first]
    exact state.outside index (Or.inl first)
  · by_cases last : dst+count ≤ index
    · rw [List.setSlice!_getElem?_suffix _ _ _ _ (by omega)]
      exact state.outside index (Or.inr last)
    · rw [List.setSlice!_getElem?_middle _ _ _ _ (by omega),List.getElem?_slice _ _ _ _ (by omega)]
      have same : dst+(index-dst)=index := by omega
      simpa only [same] using state.written (index-dst) (by omega)

/-- A right-to-left in-place copy has written exactly its completed suffix. -/
structure CopySuffix {T : Type} (before current : List T) (dst src remaining count : Nat) : Prop where
  length : current.length = before.length
  written : ∀ j, remaining ≤ j → j < count → current[dst+j]? = before[src+j]?
  outside : ∀ j, j < dst+remaining ∨ dst+count ≤ j → current[j]? = before[j]?

theorem CopySuffix.initial {T : Type} (before : List T) (dst src count : Nat) : CopySuffix before before dst src count count := by
  exact ⟨rfl,by intros; omega,by intros; rfl⟩

theorem CopySuffix.source {T : Type} [Inhabited T] {before current : List T} {dst src remaining count : Nat}
    (state : CopySuffix before current dst src remaining count) (direction : src ≤ dst) (positive : 0 < remaining) :
    current[src+(remaining-1)]! = before[src+(remaining-1)]! := by
  simp only [List.getElem!_eq_getElem?_getD,state.outside (src+(remaining-1)) (Or.inl (by omega))]

theorem CopySuffix.write {T : Type} [Inhabited T] {before current : List T} {dst src remaining count : Nat}
    (state : CopySuffix before current dst src remaining count) (direction : src ≤ dst)
    (positive : 0 < remaining) (bounded : remaining ≤ count)
    (sourceBound : src+remaining ≤ before.length) (targetBound : dst+remaining ≤ before.length) :
    CopySuffix before (current.set (dst+(remaining-1)) current[src+(remaining-1)]!) dst src (remaining-1) count := by
  refine ⟨by simp [state.length],?_,?_⟩
  · intro j lower upper
    by_cases last : j=remaining-1
    · subst j
      have srcInside : src+(remaining-1) < before.length := by omega
      have dstInside : dst+(remaining-1) < before.length := by omega
      rw [state.source direction positive]
      simp [List.getElem?_set,state.length,dstInside,List.getElem!_eq_getElem?_getD,
        List.getElem?_eq_getElem srcInside]
    · have distinct : dst+(remaining-1) ≠ dst+j := by omega
      simp only [List.getElem?_set,distinct,if_false]
      exact state.written j (by omega) upper
  · intro j outside
    have distinct : dst+(remaining-1) ≠ j := by omega
    simp only [List.getElem?_set,distinct,if_false]
    exact state.outside j (by omega)

theorem CopySuffix.complete {T : Type} {before current : List T} {dst src count : Nat}
    (state : CopySuffix before current dst src 0 count) (sourceBound : src+count ≤ before.length)
    (targetBound : dst+count ≤ before.length) :
    current = before.setSlice! dst (before.slice src (src+count)) := by
  apply CopyPrefix.complete (count:=count) (src:=src) (dst:=dst) (before:=before) (current:=current) _ sourceBound targetBound
  exact ⟨state.length,fun j bound => state.written j (by omega) bound,by simpa using state.outside⟩
end Itasca.Runtime.Spec.Segment
