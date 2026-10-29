import Itasca.Runtime.SourceMachine.Stateful.OwnershipStore
import Itasca.Runtime.SourceMachine.Stateful.Transition

/-!
Stateful ownership preservation, composing primitive updates, bulk operations and growth under retained heap ownership.
-/

/-! ## Ownership Primitives -/

section

namespace Itasca.Runtime.Abs.Ownership
open SpecExt Itasca.Runtime.Spec Stateful

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
end Itasca.Runtime.Abs.Ownership

end

/-! ## Ownership Bulk -/

section

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

end

/-! ## Ownership Growth -/

section

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

end

/-! ## Ownership -/

section

namespace Itasca.Runtime.Abs.Ownership
open SpecExt Itasca.Runtime.Spec Stateful

theorem StatefulHeapOwned.frame_function {bounds s} {f : AFrame} {instruction : instr} {after : List instr}
    (heap : StatefulHeapOwned bounds s) (typed : FrameTyped s {f with code := instruction::after} [])
    (index address : Nat) (mapped : f.module.FUNCS[index]? = some address) : address < bounds.functions := by
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands typed
  have mappedBound := (List.getElem?_eq_some_iff.mp mapped).1
  have bound : index < C.FUNCS.length := by rw [←bindings.funcs.length_eq]; exact mappedBound
  obtain ⟨fn,found,_⟩ := bindings.funcs.get mappedBound bound
  simp only [List.get_eq_getElem] at found
  have addressEq : f.module.FUNCS[index] = address := (List.getElem?_eq_some_iff.mp mapped).2
  rw [addressEq] at found
  exact Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp found).1 heap.functions

theorem evaluate_owned (bounds : Bounds) (choice : Selection) (op : Instruction)
    (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame) (after : List instr) (next : AState)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (owned : StatefulOwned bounds ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (allowed : choice.Allowed op s f)
    (step : evaluate choice op ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after = .next next) :
    StatefulOwned bounds next := by
  have frame : FrameOwned bounds f := owned.values.2 {f with code := op.source::after} (List.mem_cons_self ..)
  have frames : ∀ item ∈ rest,FrameOwned bounds item := fun item member => owned.values.2 item (by simp [member])
  cases op with
  | refNull type =>
    exact stateful_refNull_owned owned.heap owned.values.1 frame frames step
  | refIsNull =>
    exact stateful_refIsNull_owned owned.heap owned.values.1 frame frames step
  | tableGet index =>
    exact stateful_tableGet_owned owned.heap owned.values.1 frame frames step
  | tableSet index =>
    exact stateful_tableSet_owned owned.heap owned.values.1 frame frames step
  | tableSize index =>
    exact stateful_tableSize_owned owned.heap owned.values.1 frame frames step
  | tableFill index =>
    exact stateful_tableFill_owned owned.heap owned.values.1 frame frames step
  | tableCopy index source =>
    exact stateful_tableCopy_owned owned.heap owned.values.1 frame frames step
  | tableInit index source =>
    exact stateful_tableInit_owned owned.heap owned.values.1 frame frames step
  | elemDrop index =>
    exact stateful_elementDrop_owned owned.heap owned.values.1 frame frames step
  | memorySize =>
    exact stateful_memorySize_owned owned.heap owned.values.1 frame frames step
  | memoryGrow =>
    exact stateful_memoryGrow_owned owned.heap owned.values.1 frame frames step
  | memoryFill =>
    exact stateful_memoryFill_owned owned.heap owned.values.1 frame frames step
  | memoryCopy =>
    exact stateful_memoryCopy_owned owned.heap owned.values.1 frame frames step
  | memoryInit index =>
    exact stateful_memoryInit_owned owned.heap owned.values.1 frame frames step
  | dataDrop index =>
    exact stateful_dataDrop_owned owned.heap owned.values.1 frame frames step
  | refFunc index =>
    apply stateful_refFunc_owned owned.heap owned.values.1 frame frames _ step
    intro address mapped
    have active : FrameTyped s {f with code := (.refFunc index : Instruction).source::after} [] := by
      cases typed.typed.frames with | cons head _ => exact head
    exact owned.heap.frame_function active index address mapped
  | tableGrow index =>
    obtain ⟨front,reference,delta,address,object,values,mapped,found,_⟩ := tableGrow_choices s ambient f rest index after typed
    exact stateful_tableGrow_owned owned.heap owned.values.1 frame frames front reference delta address object
      values mapped found (allowed front reference delta address object values mapped found) step

theorem stateful_transition_owned (bounds : Bounds) (op : Instruction)
    (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame) (after : List instr) (next : AState)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (owned : StatefulOwned bounds ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after op (.next next)) :
    StatefulOwned bounds next := by
  obtain ⟨choice,allowed,evaluated⟩ := step
  exact evaluate_owned bounds choice op s ambient f rest after next typed owned allowed evaluated
end Itasca.Runtime.Abs.Ownership

end
