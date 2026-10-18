import Exec.Abs.ReferenceBounds

namespace Exec.Interp

theorem integer_reference_bound (bound : Nat) (ty : Inn) (bits : Nat) :
    Abs.ReferenceBound bound (Abs.integerVal ty bits) := by
  cases ty <;> trivial

theorem frame_references_numeric (f : Abs.AFrame) (front old : List val) (ty : Inn) (bits : Nat)
    (shape : f.vals = front ++ old) (bound : Nat) (bounded : Abs.FrameReferencesBound bound f) :
    Abs.ValuesBound bound f.locals ∧ Abs.ValuesBound bound (front ++ [Abs.integerVal ty bits]) := by
  have values := bounded.2
  rw [shape] at values
  exact ⟨bounded.1, Abs.valuesBound_append.mpr ⟨(Abs.valuesBound_append.mp values).1,
    by simpa using integer_reference_bound bound ty bits⟩⟩

theorem frame_references_localGet (f : Abs.AFrame) (index : Nat) (value : val)
    (found : f.locals[index]? = some value) (bound : Nat) (bounded : Abs.FrameReferencesBound bound f) :
    Abs.ValuesBound bound f.locals ∧ Abs.ValuesBound bound (f.vals ++ [value]) := by
  exact ⟨bounded.1, Abs.valuesBound_append.mpr ⟨bounded.2,
    by simpa using bounded.1 value (List.mem_of_getElem? found)⟩⟩

theorem frame_references_localWrite (f : Abs.AFrame) (index : Nat) (front : List val) (value : val)
    (keep : Bool) (shape : f.vals = front ++ [value]) (bound : Nat) (bounded : Abs.FrameReferencesBound bound f) :
    Abs.ValuesBound bound (f.locals.set index value) ∧
      Abs.ValuesBound bound (if keep then front ++ [value] else front) := by
  have values := bounded.2
  rw [shape] at values
  obtain ⟨frontBound, valueBound⟩ := Abs.valuesBound_append.mp values
  have kept : Abs.ReferenceBound bound value := by simpa using valueBound
  refine ⟨bounded.1.set kept index, ?_⟩
  cases keep <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> assumption

theorem values_references_prefix (f : Abs.AFrame) (front suffix : List val)
    (shape : f.vals = front ++ suffix) (bound : Nat) (bounded : Abs.ValuesBound bound f.vals) :
    Abs.ValuesBound bound front := by
  rw [shape] at bounded
  exact (Abs.valuesBound_append.mp bounded).1

theorem values_references_branch (f : Abs.AFrame) (front discarded results : List val)
    (shape : f.vals = front ++ discarded ++ results) (bound : Nat) (bounded : Abs.ValuesBound bound f.vals) :
    Abs.ValuesBound bound (front ++ results) := by
  rw [shape] at bounded
  obtain ⟨prior, final⟩ := Abs.valuesBound_append.mp bounded
  exact Abs.valuesBound_append.mpr ⟨(Abs.valuesBound_append.mp prior).1, final⟩

end Exec.Interp
