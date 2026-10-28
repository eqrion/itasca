import Itasca.Runtime.Interp.Memory.MemoryCore
import Itasca.Runtime.Interp.Memory.MemoryStoreSlots
namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt

 theorem core_store_value {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (memoryAddress : runtime.MemoryAddr)
    (object : runtime.store.MemInst M) (s : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (front : List val) (bits : Nat) (op : Abs.Memory.Store) (number : num_) (argument : memarg) (offset : U32)
    (storeEq : s.store = Store.decodeStore view code store) (moduleEq : f.module = Store.decodeInstance store inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (values : f.vals = front ++ [Abs.integerVal .I32 bits,.CONST op.type number]) (bound : bits < 2^32)
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val) :
    Abs.Core.store s f rest after op argument =
      if bits+offset.val+op.bytes ≤ (view object.buf).length then
        .next {s with store := Spec.memoryPayloadWrite (Store.decodeStore view code store) ⟨[],Store.decodeInstance store inst⟩ (bits+offset.val) (op.payload number), frames := {f with code := after, vals := front} :: rest}
      else .trap := by
  have stack : f.vals = (front ++ [Abs.integerVal .I32 bits]) ++ [.CONST op.type number] := by
    simpa only [List.append_assoc,List.singleton_append] using values
  simp only [Abs.Core.store,stack,Abs.pop_append,Abs.integerVal,Abs.integer,numtype_Inn,
    and_self,ite_true,true_and,if_pos bound,moduleEq,Store.decodeInstance,List.getElem?_map,mapped,Option.map_some,
    storeEq,Store.decodeStore,issued,offsetEq,Store.decodeMemory,Store.decodeBytes,List.length_map,
    List.map_drop,List.map_take,Abs.advance]
  simp only [Spec.memoryPayloadWrite,Abs.AFrame.toFrame,moduleEq,Store.decodeInstance]

 theorem execute_store_core_values {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (op : Abs.Memory.Store) (address value offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (s : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (front : List val) (bits : Nat) (number : num_) (argument : memarg)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (values : f.vals = front ++ [Abs.integerVal .I32 bits,.CONST op.type number])
    (slots : FrameSlots exec raw f)
    (addressSlot : address.val = Code.slots (f.locals.map Code.valueType) + Code.slots (front.map Code.valueType))
    (valueSlot : value.val = address.val+1)
    (bitsBound : bits < 2^32) (numberWf : wf_num_ op.type number)
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val) :
    runtime.interp.execute_store memory exec store raw.instance raw.base (storeOpcode op) address value offset ⦃ out =>
      MemoryMutation view store out.2 memoryAddress object ∧
      ((out.1 = .Ok () ∧ Abs.Core.store s f rest after op argument =
          .next {s with store := Store.decodeStore view code out.2, frames := {f with code := after, vals := front} :: rest} ∧
        FrameSlots exec raw {f with code := after, vals := front}) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ Abs.Core.store s f rest after op argument = .trap ∧
        Store.decodeStore view code out.2 = Store.decodeStore view code store)) ⦄ := by
  have actualValues : ValuesAt exec.slots.val raw.base.val
      ((f.locals++front) ++ [Abs.integerVal .I32 bits,.CONST op.type number]) := by
    simpa only [FrameSlots,values,List.append_assoc] using slots
  have actualAddress : address.val = Code.slots ((f.locals++front).map Code.valueType) := by
    simpa only [List.map_append,Code.slots_append] using addressSlot
  have abstract := core_store_value view code store inst memoryAddress object s f rest after front bits op number argument offset
    storeEq moduleEq mapped issued values bitsBound offsetEq
  apply WP.spec_mono (execute_store_slots memory view laws code exec store raw.instance raw.base op address value offset inst memoryAddress object
    (f.locals++front) bits number found mapped issued actualValues actualAddress valueSlot bitsBound numberWf)
  intro out effect
  refine ⟨effect.1,?_⟩
  split at effect
  · rename_i inside
    rw [if_pos inside,←effect.2.2] at abstract
    exact Or.inl ⟨effect.2.1,abstract,actualValues.locals⟩
  · rename_i outside
    rw [if_neg outside] at abstract
    exact Or.inr ⟨effect.2.1,abstract,effect.2.2⟩
end Itasca.Runtime.Interp.MemoryDescriptor
