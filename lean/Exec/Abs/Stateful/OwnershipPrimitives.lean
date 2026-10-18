import Exec.Abs.Stateful.OwnershipStore
import Exec.Abs.Stateful.Transition
namespace Exec.Abs.Ownership
open SpecExt Exec.Spec Stateful

theorem stateful_owned_advance {bounds s f rest next}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : advance s f rest = .next next) : StatefulOwned bounds next :=
  ⟨ownership_advance results frame frames step,by cases step; exact heap⟩

theorem asReference_owned {bounds value reference} (owned : ValueOwned bounds value)
    (decoded : asReference value = some reference) : ValueOwned bounds (val_ref reference) := by
  cases value <;> simp only [asReference] at decoded <;> cases decoded <;> exact owned

theorem stateful_refNull_owned {bounds s f rest next type after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : refNull s f rest type after = .next next) : StatefulOwned bounds next := by
  apply stateful_owned_advance heap results _ frames step
  refine ⟨frame.1,valuesOwned_append.mpr ⟨frame.2,?_⟩⟩
  cases type <;> simp [ValuesOwned,ValueOwned]

theorem stateful_refFunc_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (issued : ∀ address,f.module.FUNCS[index]? = some address → address < bounds.functions)
    (step : refFunc s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold refFunc at step
  split at step
  · contradiction
  next address mapped =>
    apply stateful_owned_advance heap results _ frames step
    exact ⟨frame.1,valuesOwned_append.mpr ⟨frame.2,valuesOwned_cons.mpr ⟨issued address mapped,valuesOwned_nil _⟩⟩⟩

theorem stateful_refIsNull_owned {bounds s f rest next after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : refIsNull s f rest after = .next next) : StatefulOwned bounds next := by
  unfold refIsNull at step
  split at step
  · contradiction
  next front value popped =>
    have prefixOwned := (frame.2.pop popped).1
    repeat' first | split at step | contradiction
    all_goals
      apply stateful_owned_advance heap results _ frames step
      exact ⟨frame.1,valuesOwned_append.mpr ⟨prefixOwned,by simp [ValuesOwned,ValueOwned,integerVal]⟩⟩

theorem stateful_tableGet_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : tableGet s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold tableGet at step
  split at step
  next front value address popped mapped =>
    have prefixOwned := (frame.2.pop popped).1
    split at step
    next position object decoded found =>
      split at step
      next inside =>
        apply stateful_owned_advance heap results _ frames step
        refine ⟨frame.1,valuesOwned_append.mpr ⟨prefixOwned,valuesOwned_cons.mpr ⟨?_,valuesOwned_nil _⟩⟩⟩
        exact heap.tables object (List.mem_of_getElem? found) _ (List.getElem_mem inside)
      · contradiction
    · contradiction
  · contradiction

theorem stateful_tableSet_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : tableSet s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold tableSet at step
  split at step
  next first value address popped mapped =>
    have firstOwned := frame.2.pop popped
    split at step
    next front offset reference object previous decoded found =>
      have prefixOwned := (firstOwned.1.pop previous).1
      have valueOwned := asReference_owned firstOwned.2 decoded
      repeat' first | split at step | contradiction
      all_goals
        apply stateful_owned_advance (step := step)
        · exact heap.table_write _ _ _ _ valueOwned
        · exact results
        · exact ⟨frame.1,prefixOwned⟩
        · exact frames
    · contradiction
  · contradiction

theorem stateful_tableSize_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : tableSize s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold tableSize at step
  repeat' first | split at step | contradiction
  all_goals
    apply stateful_owned_advance heap results _ frames step
    exact ⟨frame.1,valuesOwned_append.mpr ⟨frame.2,by simp [ValuesOwned,ValueOwned,integerVal]⟩⟩

theorem stateful_memorySize_owned {bounds s f rest next after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : memorySize s f rest after = .next next) : StatefulOwned bounds next := by
  unfold memorySize at step
  repeat' first | split at step | contradiction
  all_goals
    apply stateful_owned_advance heap results _ frames step
    exact ⟨frame.1,valuesOwned_append.mpr ⟨frame.2,by simp [ValuesOwned,ValueOwned,integerVal]⟩⟩

theorem stateful_elementDrop_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : elementDrop s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold elementDrop at step
  repeat' first | split at step | contradiction
  all_goals
    apply stateful_owned_advance (step := step)
    · exact heap.elem_drop f.toFrame index
    · exact results
    · exact frame
    · exact frames

theorem stateful_dataDrop_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : dataDrop s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold dataDrop at step
  repeat' first | split at step | contradiction
  all_goals
    apply stateful_owned_advance (step := step)
    · exact heap.data_drop f.toFrame index
    · exact results
    · exact frame
    · exact frames
end Exec.Abs.Ownership
