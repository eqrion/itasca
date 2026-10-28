import Itasca.Runtime.Interp.Memory.MemoryLoadSlots
import Itasca.Runtime.Interp.Memory.MemoryDispatchBridge
import Itasca.Runtime.Abs.Core.MemoryStep
namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt

 theorem core_load_value {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (memoryAddress : runtime.MemoryAddr)
    (object : runtime.store.MemInst M) (s : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (front : List val) (bits : Nat) (op : Abs.Memory.Load) (argument : memarg) (offset : U32)
    (storeEq : s.store = Store.decodeStore view code store) (moduleEq : f.module = Store.decodeInstance store inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (values : f.vals = front ++ [Abs.integerVal .I32 bits]) (bound : bits < 2^32)
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val) :
    Abs.Core.load s f rest after op argument =
      if bits+offset.val+op.bytes ≤ (view object.buf).length then
        .next {s with frames := {f with code := after, vals := front ++ [op.value
          (Store.decodeBytes (((view object.buf).val.drop (bits+offset.val)).take op.bytes))]} :: rest}
      else .trap := by
  simp only [Abs.Core.load,values,Abs.pop_append,Abs.integerVal,Abs.integer,numtype_Inn,
    and_self,ite_true,true_and,if_pos bound,moduleEq,Store.decodeInstance,List.getElem?_map,mapped,Option.map_some,
    storeEq,Store.decodeStore,issued,offsetEq,Store.decodeMemory,Store.decodeBytes,List.length_map,
    List.map_drop,List.map_take,Abs.advance]

 theorem execute_load_core {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (op : Abs.Memory.Load) (address offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (s : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (front : List val) (bits : Nat) (argument : memarg)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (values : f.vals = front ++ [Abs.integerVal .I32 bits])
    (slots : FrameSlots exec raw f)
    (addressSlot : address.val = Code.slots (f.locals.map Code.valueType) + Code.slots (front.map Code.valueType))
    (bitsBound : bits < 2^32) (offsetEq : proj_uN_0 argument.OFFSET = offset.val) :
    runtime.interp.execute_load memory exec store raw.instance raw.base (loadOpcode op) address address offset ⦃ out =>
      (∃ nextFrame, out.1 = .Ok () ∧ Abs.Core.load s f rest after op argument = .next {s with frames := nextFrame :: rest} ∧
        FrameSlots out.2 raw nextFrame ∧ {out.2 with slots := exec.slots} = exec) ∨
      (out = (.Err (.Trap .MemoryOutOfBounds),exec) ∧ Abs.Core.load s f rest after op argument = .trap) ⦄ := by
  have actualValues : ValuesAt exec.slots.val raw.base.val ((f.locals++front) ++ [Abs.integerVal .I32 bits]) := by
    simpa only [FrameSlots,values,List.append_assoc] using slots
  have actualAddress : address.val = Code.slots ((f.locals++front).map Code.valueType) := by
    simpa only [List.map_append,Code.slots_append] using addressSlot
  have abstract := core_load_value view code store inst memoryAddress object s f rest after front bits op argument offset
    storeEq moduleEq mapped issued values bitsBound offsetEq
  apply WP.spec_mono (execute_load_slots memory view laws exec store raw.instance raw.base op address offset inst memoryAddress object
    (f.locals++front) bits found mapped issued actualValues actualAddress bitsBound)
  intro out effect
  split at effect
  · rename_i inside
    rw [if_pos inside] at abstract
    exact Or.inl ⟨_,effect.1,abstract,by simpa only [FrameSlots,List.append_assoc] using effect.2.1,effect.2.2⟩
  · rename_i outside
    rw [if_neg outside] at abstract
    exact Or.inr ⟨effect,abstract⟩
end Itasca.Runtime.Interp.MemoryDescriptor
