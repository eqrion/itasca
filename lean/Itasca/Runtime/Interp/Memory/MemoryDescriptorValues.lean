import Itasca.Runtime.Interp.Memory.MemoryMutation
import Itasca.Runtime.Abs.Memory.Semantics
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
