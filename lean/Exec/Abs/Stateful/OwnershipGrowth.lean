import Exec.Abs.Stateful.OwnershipPrimitives
namespace Itasca.Runtime.Abs.Ownership
open SpecExt Itasca.Runtime.Spec Stateful

theorem stateful_memoryGrow_owned {bounds choice s f rest next after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : memoryGrow choice s f rest after = .next next) : StatefulOwned bounds next := by
  unfold memoryGrow at step
  split at step
  next front value address popped mapped =>
    have prefixOwned := (frame.2.pop popped).1
    repeat' first | split at step | contradiction
    all_goals try simp_all only [Option.some.injEq,Prod.mk.injEq,asReference_value]
    all_goals
      apply stateful_owned_advance (step := step)
      · exact heap.metadata rfl rfl rfl rfl
      · exact results
      · exact ⟨frame.1,valuesOwned_append.mpr ⟨prefixOwned,by simp [ValuesOwned,ValueOwned,integerVal]⟩⟩
      · exact frames
  · contradiction

theorem stateful_tableGrow_owned {bounds choice s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (front : List val) (reference : ref) (delta address : Nat) (object : tableinst)
    (values : f.vals = front ++ [val_ref reference,integerVal .I32 delta])
    (mapped : f.module.TABLES[index]? = some address) (found : s.store.TABLES[address]? = some object)
    (allowed : TableGrowthChoice object delta reference choice)
    (step : tableGrow choice s f rest index after = .next next) : StatefulOwned bounds next := by
  have input : ValuesOwned bounds front ∧ ValueOwned bounds (val_ref reference) := by
    have owned := frame.2
    rw [values] at owned
    exact ⟨(valuesOwned_append.mp owned).1,(valuesOwned_cons.mp (valuesOwned_append.mp owned).2).1⟩
  have split : f.vals = (front ++ [val_ref reference]) ++ [integerVal .I32 delta] := by
    simpa [List.append_assoc] using values
  cases allowed with
  | refused =>
    simp only [tableGrow,split,pop_append,mapped,found,asReference_value] at step
    repeat' first | split at step | contradiction
    all_goals try simp_all only [Option.some.injEq,Prod.mk.injEq,asReference_value]
    all_goals
      apply stateful_owned_advance (step := step)
      · exact heap
      · exact results
      · exact ⟨frame.1,valuesOwned_append.mpr ⟨input.1,by simp [ValuesOwned,ValueOwned,integerVal]⟩⟩
      · exact frames
  | @grown fresh grown =>
    have newHeap := heap.table_grow address object fresh delta reference (List.mem_of_getElem? found) input.2 grown
    simp only [tableGrow,split,pop_append,mapped,found,asReference_value] at step
    repeat' first | split at step | contradiction
    all_goals try simp_all only [Option.some.injEq,Prod.mk.injEq,asReference_value]
    all_goals
      apply stateful_owned_advance (step := step)
      · exact newHeap
      · exact results
      · exact ⟨frame.1,valuesOwned_append.mpr ⟨input.1,by simp [ValuesOwned,ValueOwned,integerVal]⟩⟩
      · exact frames
end Itasca.Runtime.Abs.Ownership
