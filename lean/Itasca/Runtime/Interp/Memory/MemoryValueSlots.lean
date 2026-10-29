import Itasca.Runtime.Interp.Memory.MemoryMutation
import Itasca.Runtime.SourceMachine.Memory.Semantics
import Itasca.Runtime.Interp.Relations.Regions

/-!
Scalar memory values represented in machine words. Descriptor-specific bounds connect decoded load values to word encoding and the destination slots.
-/

/-! ## Memory Descriptor Values -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt

 theorem load_word_value (op : Abs.Memory.Load) (bytes : List U8) (start : Nat)
    (inside : start + op.bytes ≤ bytes.length) :
    Store.decodeWords (numericMemoryType op.type)
      (scalarLoadedWord (loadOpcode op) (scalarLoadBytes bytes start 0#u64 0 op.bytes)) 0#u64 =
      op.value (Store.decodeBytes ((bytes.drop start).take op.bytes)) := by
  cases op with
  | full ty =>
    have decoded := numeric_load_word_decodes ty bytes start (by cases ty <;> exact inside)
    cases ty <;> exact decoded
  | packed ty width sign =>
    have decoded := PackedMemory.load_word_decodes (packed width) sign bytes start
      (by simpa only [packed_bytes,Abs.Memory.Load.bytes] using inside)
    cases ty <;> cases width <;> exact decoded

 theorem store_payload (op : Abs.Memory.Store) (word : U64) :
    op.payload (numericStoreValue op.type word) = Builtins.integerBytes op.bytes word.val := by
  cases op with
  | full ty =>
    have payload := numericStoreValue_bytes ty word
    cases ty <;> exact payload
  | packed ty width =>
    cases ty with
    | I32 =>
      cases width <;> simp only [Abs.Memory.Store.payload,Abs.Memory.Store.type,
        numericStoreValue,numtype_Inn,proj_num__0,Option.get!,proj_uN_0,Abs.Memory.PackedWidth.bits,
        Nat.reduceDiv,Abs.Memory.Store.bytes]
      · exact PackedMemory.store_bytes .i32x8 word
      · exact PackedMemory.store_bytes .i32x16 word
    | I64 => cases width <;> rfl

 theorem execute_store_value {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (instanceIndex base : Usize)
    (op : Abs.Memory.Store) (address value offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M) (addressWord valueWord : U64)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (input : exec.slots.val[base.val+address.val]? = some addressWord)
    (inputValue : exec.slots.val[base.val+value.val]? = some valueWord) :
    runtime.interp.execute_store memory exec store instanceIndex base (storeOpcode op) address value offset ⦃ out =>
      MemoryMutation view store out.2 memoryAddress object ∧
      if (UScalar.cast .U32 addressWord).val + offset.val + op.bytes ≤ (view object.buf).length then
        out.1 = .Ok () ∧ Store.decodeStore view code out.2 =
          Spec.memoryPayloadWrite (Store.decodeStore view code store) ⟨[],Store.decodeInstance store inst⟩
            ((UScalar.cast .U32 addressWord).val+offset.val) (op.payload (numericStoreValue op.type valueWord))
      else out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ Store.decodeStore view code out.2 = Store.decodeStore view code store ⦄ := by
  apply WP.spec_mono (execute_store_effect memory view laws exec store instanceIndex base (storeOpcode op) address value offset
    inst memoryAddress object addressWord valueWord found mapped issued input inputValue)
  intro out effect
  obtain ⟨buffer,after,effect⟩ := effect
  unfold ScalarStoreEffect at effect
  rw [store_width] at effect
  split at effect
  · rename_i inside
    obtain ⟨status,written⟩ := effect
    have lengthEq : (view buffer).length = (view object.buf).length := by
      change (view buffer).val.length = (view object.buf).val.length
      rw [written,scalarStoreBytes_length]
    refine ⟨⟨buffer,after,lengthEq⟩,?_⟩
    rw [if_pos inside]
    refine ⟨status,?_⟩
    rw [after]
    apply memory_write_decodes view code store inst ⟨[],Store.decodeInstance store inst⟩ memoryAddress object buffer
      _ _ rfl mapped issued
    · simpa only [store_payload,Builtins.integerBytes_length] using inside
    · rw [written,scalarStoreBytes_source _ _ _ _ inside,store_payload]
  · rename_i outside
    have status := congrArg Prod.fst effect
    have unchanged : view buffer = view object.buf := congrArg Prod.snd effect
    refine ⟨⟨buffer,after,by rw [unchanged]⟩,?_⟩
    rw [if_neg outside]
    refine ⟨status,?_⟩
    rw [after]
    exact memory_unchanged_decodes view code store memoryAddress object buffer issued unchanged
end Itasca.Runtime.Interp.MemoryDescriptor

end

/-! ## Memory Value Slots -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt

theorem scalar_load_bytes_bound (bytes : List U8) (start width : Nat)
    (widthBound : width ≤ 8) (inside : start+width ≤ bytes.length) :
    (scalarLoadBytes bytes start 0#u64 0 width).val < 256^width := by
  rw [scalarLoadBytes_source bytes start width widthBound inside]
  have valid : Forall wf_byte (Store.decodeBytes ((bytes.drop start).take width)) := by
    intro b member
    obtain ⟨raw,_,rfl⟩ := List.mem_map.mp member
    constructor
    scalar_tac
  have lengthEq : (Store.decodeBytes ((bytes.drop start).take width)).length = width := by
    simp only [Store.decodeBytes,List.length_map,List.length_take,List.length_drop]
    omega
  simpa only [lengthEq] using Spec.integerOfBytes_bound _ valid

theorem load_word_small (op : Abs.Memory.Load) (word : U64)
    (bounded : word.val < 256^op.bytes) :
    op.type = .I32 ∨ op.type = .F32 → (scalarLoadedWord (loadOpcode op) word).val < 2^32 := by
  intro small
  cases op with
  | full ty =>
    cases ty <;> simp only [Abs.Memory.Load.type] at small
    · change word.val < 2^32
      exact bounded
    · simp at small
    · change word.val < 2^32
      exact bounded
    · simp at small
  | packed ty width sign =>
    cases ty with
    | I64 => simp [Abs.Memory.Load.type,numtype_Inn] at small
    | I32 =>
      cases width with
      | byte =>
        cases sign with
        | U => change word.val < 2^32; norm_num [Abs.Memory.Load.bytes,Abs.Memory.PackedWidth.bits] at bounded; omega
        | S =>
          change (UScalar.cast .U64 (IScalar.hcast .U32 (IScalar.cast .I32 (UScalar.hcast .I8 word)))).val < 2^32
          scalar_tac
      | half =>
        cases sign with
        | U => change word.val < 2^32; norm_num [Abs.Memory.Load.bytes,Abs.Memory.PackedWidth.bits] at bounded; omega
        | S =>
          change (UScalar.cast .U64 (IScalar.hcast .U32 (IScalar.cast .I32 (UScalar.hcast .I16 word)))).val < 2^32
          scalar_tac

theorem numeric_word_encode (ty : numtype) (word : U64)
    (small : ty = .I32 ∨ ty = .F32 → word.val < 2^32) :
    Code.encodeValue (Store.decodeWords (numericMemoryType ty) word 0#u64) = [word.val] := by
  cases ty
  · change [word.val % 2^32] = [word.val]
    rw [Nat.mod_eq_of_lt (small (Or.inl rfl))]
  · rfl
  · change [Builtins.floatBits 32 (Builtins.floatOfBits 32 (word.val % 2^32))] = [word.val]
    have bound := small (Or.inr rfl)
    rw [Nat.mod_eq_of_lt bound,Builtins.Float.float_bits_roundtrip_32 word.val bound]
  · change [Builtins.floatBits 64 (Builtins.floatOfBits 64 word.val)] = [word.val]
    rw [Builtins.Float.float_bits_roundtrip_64 word.val (by scalar_tac)]

theorem load_word_encode (op : Abs.Memory.Load) (bytes : List U8) (start : Nat)
    (inside : start + op.bytes ≤ bytes.length) :
    Code.encodeValue (op.value (Store.decodeBytes ((bytes.drop start).take op.bytes))) =
      [(scalarLoadedWord (loadOpcode op) (scalarLoadBytes bytes start 0#u64 0 op.bytes)).val] := by
  rw [←load_word_value op bytes start inside]
  apply numeric_word_encode
  apply load_word_small
  apply scalar_load_bytes_bound bytes start op.bytes
  · cases op with
    | full ty => cases ty <;> decide
    | packed ty width sign => cases width <;> simp [Abs.Memory.Load.bytes,Abs.Memory.PackedWidth.bits]
  · exact inside
end Itasca.Runtime.Interp.MemoryDescriptor

end
