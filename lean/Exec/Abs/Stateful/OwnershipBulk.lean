import Exec.Abs.Stateful.OwnershipPrimitives
namespace Itasca.Runtime.Abs.Ownership
open SpecExt Itasca.Runtime.Spec Stateful

theorem ValuesOwned.popThree {bounds values front a b c} (owned : ValuesOwned bounds values)
    (popped : Stateful.popThree values = some (front,a,b,c)) :
    ValuesOwned bounds front ∧ ValueOwned bounds a ∧ ValueOwned bounds b ∧ ValueOwned bounds c := by
  unfold Stateful.popThree at popped
  split at popped
  · contradiction
  next first last one =>
    have h1 := owned.pop one
    split at popped
    · contradiction
    next second middle two =>
      have h2 := h1.1.pop two
      split at popped
      · contradiction
      next third start three =>
        have h3 := h2.1.pop three
        cases popped
        exact ⟨h3.1,h3.2,h2.2,h1.2⟩

theorem stateful_memoryFill_owned {bounds s f rest next after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : memoryFill s f rest after = .next next) : StatefulOwned bounds next := by
  unfold memoryFill at step
  split at step
  next front offset value size address popped mapped =>
    have prefixOwned := (frame.2.popThree popped).1
    repeat' first | split at step | contradiction
    all_goals
      apply stateful_owned_advance (step := step)
      · exact heap.memory_fill _ _ _ _
      · exact results
      · exact ⟨frame.1,prefixOwned⟩
      · exact frames
  · contradiction

theorem stateful_memoryCopy_owned {bounds s f rest next after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : memoryCopy s f rest after = .next next) : StatefulOwned bounds next := by
  unfold memoryCopy at step
  split at step
  next front offset value size address popped mapped =>
    have prefixOwned := (frame.2.popThree popped).1
    repeat' first | split at step | contradiction
    all_goals
      apply stateful_owned_advance (step := step)
      · exact heap.memory_copy _ _ _ _
      · exact results
      · exact ⟨frame.1,prefixOwned⟩
      · exact frames
  · contradiction

theorem stateful_memoryInit_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : memoryInit s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold memoryInit at step
  split at step
  next front offset value size address dataAddress popped mapped dataMapped =>
    have prefixOwned := (frame.2.popThree popped).1
    repeat' first | split at step | contradiction
    all_goals
      apply stateful_owned_advance (step := step)
      · exact heap.memory_init _ _ _ _ _
      · exact results
      · exact ⟨frame.1,prefixOwned⟩
      · exact frames
  · contradiction

theorem stateful_tableFill_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : tableFill s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold tableFill at step
  split at step
  next front offset value size address popped mapped =>
    have input := frame.2.popThree popped
    split at step
    next destination reference count object destinationEq referenceEq countEq found =>
      have valueOwned := asReference_owned input.2.2.1 referenceEq
      split at step
      next inside =>
        apply stateful_owned_advance (step := step)
        · exact heap.table_fill _ _ _ _ _ valueOwned
        · exact results
        · exact ⟨frame.1,input.1⟩
        · exact frames
      · contradiction
    · contradiction
  · contradiction

theorem stateful_tableCopy_owned {bounds s f rest next index sourceIndex after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : tableCopy s f rest index sourceIndex after = .next next) : StatefulOwned bounds next := by
  unfold tableCopy at step
  split at step
  next front offset value size address sourceAddress popped mapped sourceMapped =>
    have prefixOwned := (frame.2.popThree popped).1
    split at step
    next destination source count object sourceObject destinationEq sourceEq countEq found sourceFound =>
      split at step
      next inside =>
        apply stateful_owned_advance (step := step)
        · exact heap.table_copy _ _ _ _ _ _ _ _ _ _ mapped sourceMapped found sourceFound inside
        · exact results
        · exact ⟨frame.1,prefixOwned⟩
        · exact frames
      · contradiction
    · contradiction
  · contradiction

theorem stateful_tableInit_owned {bounds s f rest next index sourceIndex after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : tableInit s f rest index sourceIndex after = .next next) : StatefulOwned bounds next := by
  unfold tableInit at step
  split at step
  next front offset value size address sourceAddress popped mapped sourceMapped =>
    have prefixOwned := (frame.2.popThree popped).1
    split at step
    next destination source count object sourceObject destinationEq sourceEq countEq found sourceFound =>
      split at step
      next inside =>
        apply stateful_owned_advance (step := step)
        · exact heap.table_init _ _ _ _ _ _ _ _ sourceMapped sourceFound inside.1
        · exact results
        · exact ⟨frame.1,prefixOwned⟩
        · exact frames
      · contradiction
    · contradiction
  · contradiction
end Itasca.Runtime.Abs.Ownership
