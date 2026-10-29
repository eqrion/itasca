import Itasca.Runtime.SourceMachine.ReferenceBounds

namespace Itasca.Runtime.Interp

theorem integer_reference_bound (bound : Nat) (ty : Inn) (bits : Nat) :
    SourceMachine.ReferenceBound bound (SourceMachine.integerVal ty bits) := by
  cases ty <;> trivial

theorem frame_references_numeric (f : SourceMachine.AFrame) (front old : List val) (ty : Inn) (bits : Nat)
    (shape : f.vals = front ++ old) (bound : Nat) (bounded : SourceMachine.FrameReferencesBound bound f) :
    SourceMachine.ValuesBound bound f.locals ∧ SourceMachine.ValuesBound bound (front ++ [SourceMachine.integerVal ty bits]) := by
  have values := bounded.2
  rw [shape] at values
  exact ⟨bounded.1, SourceMachine.values_bound_append.mpr ⟨(SourceMachine.values_bound_append.mp values).1,
    by simpa using integer_reference_bound bound ty bits⟩⟩

theorem frame_references_local_get (f : SourceMachine.AFrame) (index : Nat) (value : val)
    (found : f.locals[index]? = some value) (bound : Nat) (bounded : SourceMachine.FrameReferencesBound bound f) :
    SourceMachine.ValuesBound bound f.locals ∧ SourceMachine.ValuesBound bound (f.vals ++ [value]) := by
  exact ⟨bounded.1, SourceMachine.values_bound_append.mpr ⟨bounded.2,
    by simpa using bounded.1 value (List.mem_of_getElem? found)⟩⟩

theorem frame_references_local_write (f : SourceMachine.AFrame) (index : Nat) (front : List val) (value : val)
    (keep : Bool) (shape : f.vals = front ++ [value]) (bound : Nat) (bounded : SourceMachine.FrameReferencesBound bound f) :
    SourceMachine.ValuesBound bound (f.locals.set index value) ∧
      SourceMachine.ValuesBound bound (if keep then front ++ [value] else front) := by
  have values := bounded.2
  rw [shape] at values
  obtain ⟨frontBound, valueBound⟩ := SourceMachine.values_bound_append.mp values
  have kept : SourceMachine.ReferenceBound bound value := by simpa using valueBound
  refine ⟨bounded.1.set kept index, ?_⟩
  cases keep <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> assumption

theorem values_references_prefix (f : SourceMachine.AFrame) (front suffix : List val)
    (shape : f.vals = front ++ suffix) (bound : Nat) (bounded : SourceMachine.ValuesBound bound f.vals) :
    SourceMachine.ValuesBound bound front := by
  rw [shape] at bounded
  exact (SourceMachine.values_bound_append.mp bounded).1

end Itasca.Runtime.Interp
