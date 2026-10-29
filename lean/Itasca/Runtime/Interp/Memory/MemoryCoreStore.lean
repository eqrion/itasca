import Itasca.Runtime.Interp.Memory.MemoryValueSlots
import Itasca.Runtime.Interp.Relations.Readback
import Itasca.Runtime.Interp.Memory.MemoryCore

/-!
Scalar store execution from numeric input encoding through operand slots. The core correspondence uses the actual store bytes and preserves the stated memory effect.
-/

/-! ## Memory Numeric Input -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std

theorem numeric_input_word (words : List U64) (position : Nat) (ty : numtype) (value : num_)
    (wellFormed : wf_num_ ty value)
    (represented : WordsAt words position (Code.encodeValue (.CONST ty value))) :
    ∃ word, words[position]? = some word ∧ numericStoreValue ty word = value := by
  have lengthEq : (Code.encodeValue (.CONST ty value)).length = 1 := by
    rw [Code.encodeValue_length]
    cases ty <;> rfl
  obtain ⟨bits,encoded⟩ := List.length_eq_one_iff.mp lengthEq
  rw [encoded] at represented
  obtain ⟨bound,atWord⟩ := represented 0 (by simp)
  simp only [Nat.add_zero,List.getElem!_cons_zero] at bound atWord
  let word := words[position]
  have wordBits : word.val = bits := by simpa only [_root_.getElem!_pos words position bound] using atWord
  have pair : pairWords (numericMemoryType ty) (word,0#u64) = Code.encodeValue (.CONST ty value) := by
    rw [encoded,←wordBits]
    cases ty <;> rfl
  have floatBound : numericMemoryType ty = .F32 → word.val < 2^32 := by
    intro floating
    have sourceType : Code.valueType (.CONST ty value) = .F32 := by
      cases ty <;> simp_all [numericMemoryType,Code.valueType,valtype_numtype,numtype_Inn,numtype_Fnn]
    have bounded := encodeValue_f32_low (.CONST ty value) (.val_case_0 ty value wellFormed) sourceType
    simpa only [encoded,List.getElem!_cons_zero,wordBits] using bounded
  have roundtrip := Code.decode_encode (.CONST ty value) (.val_case_0 ty value wellFormed) []
  simp only [List.append_nil] at roundtrip
  have translated : sourceType (numericMemoryType ty) = Code.valueType (.CONST ty value) := by cases ty <;> rfl
  rw [←translated,←pair,decode_words_code _ _ _ floatBound] at roundtrip
  have decoded := congrArg Prod.fst (Option.some.inj roundtrip)
  rw [numericStoreValue_decodes] at decoded
  exact ⟨word,List.getElem?_eq_getElem bound,(val.CONST.inj decoded).2⟩
end Itasca.Runtime.Interp.MemoryDescriptor

end

/-! ## Memory Store Slots -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std

 theorem execute_store_slots {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (instanceIndex base : Usize)
    (op : Abs.Memory.Store) (address value offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (front : List val) (bits : Nat) (number : num_)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (values : ValuesAt exec.slots.val base.val (front ++ [Abs.integerVal .I32 bits,.CONST op.type number]))
    (addressSlot : address.val = Code.slots (front.map Code.valueType))
    (valueSlot : value.val = address.val+1)
    (bitsBound : bits < 2^32) (numberWf : wf_num_ op.type number) :
    runtime.interp.execute_store memory exec store instanceIndex base (storeOpcode op) address value offset ⦃ out =>
      MemoryMutation view store out.2 memoryAddress object ∧
      if bits+offset.val+op.bytes ≤ (view object.buf).length then
        out.1 = .Ok () ∧ Store.decodeStore view code out.2 =
          Spec.memoryPayloadWrite (Store.decodeStore view code store) ⟨[],Store.decodeInstance store inst⟩
            (bits+offset.val) (op.payload number)
      else out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ Store.decodeStore view code out.2 = Store.decodeStore view code store ⦄ := by
  have words : WordsAt exec.slots.val base.val
      ((Code.encodeValues front ++ [bits]) ++ Code.encodeValue (.CONST op.type number)) := by
    simpa only [ValuesAt,Code.encodeValues_append,Code.encodeValues,Code.encodeValue,Abs.integerVal,
      numtype_Inn,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] using values
  have addressPosition : address.val = (Code.encodeValues front).length := by simpa only [Code.encodeValues_length] using addressSlot
  have addressWords := words.append_left.append_right
  obtain ⟨bound,wordEq⟩ := addressWords 0 (by simp)
  have atBound : base.val+address.val < exec.slots.length := by simpa only [Nat.add_zero,←addressPosition] using bound
  let word := exec.slots.val[base.val+address.val]
  have input : exec.slots.val[base.val+address.val]? = some word := List.getElem?_eq_getElem atBound
  have actual : word.val = bits := by
    have concrete : exec.slots.val[base.val+address.val]!.val = bits := by
      simpa only [Nat.add_zero,←addressPosition,List.getElem!_cons_zero] using wordEq
    simpa only [_root_.getElem!_pos exec.slots.val (base.val+address.val) atBound] using concrete
  have castEq : (UScalar.cast .U32 word).val = bits := by scalar_tac
  have numericWords : WordsAt exec.slots.val (base.val+value.val) (Code.encodeValue (.CONST op.type number)) := by
    simpa only [List.length_append,List.length_singleton,←addressPosition,←valueSlot] using words.append_right
  obtain ⟨valueWord,inputValue,decoded⟩ := numeric_input_word exec.slots.val (base.val+value.val) op.type number numberWf numericWords
  have effect := execute_store_value memory view laws code exec store instanceIndex base op address value offset inst memoryAddress object word valueWord
    found mapped issued input inputValue
  simpa only [castEq,decoded] using effect
end Itasca.Runtime.Interp.MemoryDescriptor

end

/-! ## Memory Core Store -/

section

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

end
