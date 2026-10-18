import Exec.Abs.Stateful.OwnershipBulk
import Exec.Abs.Stateful.OwnershipGrowth
namespace Exec.Abs.Ownership
open SpecExt Exec.Spec Stateful

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
end Exec.Abs.Ownership
