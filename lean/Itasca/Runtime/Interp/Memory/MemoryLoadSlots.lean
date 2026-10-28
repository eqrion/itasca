import Itasca.Runtime.Interp.Memory.MemoryValueSlots
namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std

 theorem execute_load_slots {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (instanceIndex base : Usize)
    (op : Abs.Memory.Load) (address offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (front : List val) (bits : Nat)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (values : ValuesAt exec.slots.val base.val (front ++ [Abs.integerVal .I32 bits]))
    (addressSlot : address.val = Code.slots (front.map Code.valueType))
    (bitsBound : bits < 2^32) :
    runtime.interp.execute_load memory exec store instanceIndex base (loadOpcode op) address address offset ⦃ out =>
      if bits + offset.val + op.bytes ≤ (view object.buf).length then
        out.1 = .Ok () ∧
        ValuesAt out.2.slots.val base.val (front ++ [op.value
          (Store.decodeBytes (((view object.buf).val.drop (bits+offset.val)).take op.bytes))]) ∧
        {out.2 with slots := exec.slots} = exec
      else out = (.Err (.Trap .MemoryOutOfBounds),exec) ⦄ := by
  have words : WordsAt exec.slots.val base.val (Code.encodeValues front ++ [bits]) := by
    simpa only [ValuesAt,Code.encodeValues_append,Code.encodeValues,Code.encodeValue,Abs.integerVal,
      numtype_Inn,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil] using values
  have tail := words.append_right
  obtain ⟨bound,wordEq⟩ := tail 0 (by simp)
  have addressPosition : address.val = (Code.encodeValues front).length := by simpa only [Code.encodeValues_length] using addressSlot
  have atBound : base.val + address.val < exec.slots.length := by simpa only [Nat.add_zero,←addressPosition] using bound
  let word := exec.slots.val[base.val+address.val]
  have input : exec.slots.val[base.val+address.val]? = some word := List.getElem?_eq_getElem atBound
  have actual : word.val = bits := by
    have concrete : exec.slots.val[base.val+address.val]!.val = bits := by
      simpa only [Nat.add_zero,←addressPosition,List.getElem!_cons_zero] using wordEq
    simpa only [_root_.getElem!_pos exec.slots.val (base.val+address.val) atBound] using concrete
  have castEq : (UScalar.cast .U32 word).val = bits := by scalar_tac
  apply WP.spec_mono (execute_load_effect memory view laws exec store instanceIndex base (loadOpcode op) address address offset
    inst memoryAddress object word found mapped issued input atBound)
  intro out effect
  rw [load_width,castEq] at effect
  split at effect
  · rename_i inside
    rw [if_pos inside]
    refine ⟨effect.1,?_,effect.2.2⟩
    rw [effect.2.1]
    have updated := words.append_left.set_append
      (scalarLoadedWord (loadOpcode op) (scalarLoadBytes (view object.buf).val (bits+offset.val) 0#u64 0 op.bytes))
      (by simpa only [←addressPosition] using atBound)
    rw [addressPosition]
    simpa only [ValuesAt,Code.encodeValues_append,Code.encodeValues,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,load_word_encode op _ _ inside] using updated
  · rename_i outside
    rw [if_neg outside]
    exact effect
end Itasca.Runtime.Interp.MemoryDescriptor
