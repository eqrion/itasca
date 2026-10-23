import Exec.Interp.Memory.MemoryValueSlots
namespace Exec.Interp.MemoryDescriptor
open Aeneas Aeneas.Std

 theorem execute_load_footprint {M : Type} (memory : runtime.platform.MemoryBuffer M)
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
      out.1 = .Ok () → ∃ word, base.val+address.val < exec.slots.length ∧
        SlotsEffect exec out.2 (exec.slots.val.set (base.val+address.val) word) ⦄ := by
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
  intro success
  split at effect
  · exact ⟨_,atBound,effect.2⟩
  · rw [effect] at success
    contradiction
end Exec.Interp.MemoryDescriptor
