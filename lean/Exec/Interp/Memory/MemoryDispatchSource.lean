import Exec.Interp.Memory.MemoryDispatch
import Exec.Interp.Memory.MemoryDecode

namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt
open Exec.Store

/-- Full-width STORE dispatch follows one source memory transition. A rejected
access returns the precise bounds trap and preserves the decoded store. -/
theorem execute_numeric_store_source {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (instanceIndex base : Usize)
    (ty : numtype) (address value offset : U32) (inst : runtime.store.Instance)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.Memory M) (addressWord valueWord : U64)
    (ambient : frame) (argument : memarg)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (input : exec.slots.val[base.val + address.val]? = some addressWord)
    (inputValue : exec.slots.val[base.val + value.val]? = some valueWord)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (storeWf : wf_store (decodeStore view code store)) (ambientWf : wf_frame ambient)
    (operationWf : wf_admininstr (.STORE ty none argument))
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val) :
    runtime.interp.execute_store memory exec store instanceIndex base (numericStoreOpcode ty) address value offset ⦃ out =>
      (out.1 = .Ok () ∨ out.1 = .Err (.Trap .MemoryOutOfBounds)) ∧
      StepH ⟨⟨decodeStore view code store,ambient⟩,
        [Spec.Segment.i32 (UScalar.cast .U32 addressWord).val,
          .CONST ty (numericStoreValue ty valueWord),.STORE ty none argument]⟩ []
        ⟨⟨decodeStore view code out.2,ambient⟩,match out.1 with | .Ok _ => [] | .Err _ => [.TRAP]⟩ ∧
      (out.1 = .Err (.Trap .MemoryOutOfBounds) → decodeStore view code out.2 = decodeStore view code store) ⦄ := by
  have memoryEq := memory_lookup_decodes view code store inst ambient memoryAddress object moduleEq mapped issued
  have mapBound : 0 < ambient.MODULE.MEMS.length := by
    rw [moduleEq]
    simpa only [decodeInstance,List.length_map] using (List.getElem?_eq_some_iff.mp mapped).1
  have source := Spec.numeric_store_step (decodeStore view code store) ambient ty argument
    (UScalar.cast .U32 addressWord).val (numericStoreValue ty valueWord)
    storeWf ambientWf (by scalar_tac) operationWf (numericStoreValue_wf ty valueWord) mapBound
  simp only [memoryEq,decodeMemory,offsetEq,decodeBytes,List.length_map] at source
  apply WP.spec_mono (execute_store_effect memory view laws exec store instanceIndex base
    (numericStoreOpcode ty) address value offset inst memoryAddress object addressWord valueWord found mapped issued input inputValue)
  intro out effect
  obtain ⟨buffer,storeEq,bytesEffect⟩ := effect
  have width : (scalarStoreWidth (numericStoreOpcode ty)).val = Spec.scalarNumBytes ty := by cases ty <;> rfl
  unfold ScalarStoreEffect at bytesEffect
  rw [width] at bytesEffect
  by_cases fits : (UScalar.cast .U32 addressWord).val + offset.val + Spec.scalarNumBytes ty ≤ (view object.buf).val.length
  · rw [if_pos fits] at source bytesEffect
    obtain ⟨status,bytesEq⟩ := bytesEffect
    change out.1 = .Ok () at status
    have payloadBound : (UScalar.cast .U32 addressWord).val + offset.val +
        (nbytes_ ty (numericStoreValue ty valueWord)).length ≤ (view object.buf).length := by
      simpa only [numericStoreValue_bytes,Builtins.integerBytes_length] using fits
    have written : decodeBytes (view buffer).val = (decodeBytes (view object.buf).val).setSlice!
        ((UScalar.cast .U32 addressWord).val + offset.val) (nbytes_ ty (numericStoreValue ty valueWord)) := by
      rw [bytesEq,scalarStoreBytes_source _ _ _ _ fits,numericStoreValue_bytes]
    have decoded := memory_write_decodes view code store inst ambient memoryAddress object buffer
      ((UScalar.cast .U32 addressWord).val+offset.val) (nbytes_ ty (numericStoreValue ty valueWord))
      moduleEq mapped issued payloadBound written
    refine ⟨Or.inl status,?_,?_⟩
    · simpa only [status,storeEq,decoded] using source
    · simp [status]
  · rw [if_neg fits] at source bytesEffect
    have status : out.1 = .Err (.Trap .MemoryOutOfBounds) := congrArg Prod.fst bytesEffect
    have unchanged : view buffer = view object.buf := congrArg Prod.snd bytesEffect
    have decoded := memory_unchanged_decodes view code store memoryAddress object buffer issued unchanged
    refine ⟨Or.inr status,?_,?_⟩
    · simpa only [status,storeEq,decoded] using source
    · intro _
      rw [storeEq,decoded]

/-- Full-width LOAD dispatch exposes the exact source result and destination-slot
update, or the bounds trap with the complete execution state unchanged. -/
theorem execute_numeric_load_source {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (instanceIndex base : Usize)
    (ty : numtype) (dst address offset : U32) (inst : runtime.store.Instance)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.Memory M) (addressWord : U64)
    (ambient : frame) (argument : memarg)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (input : exec.slots.val[base.val + address.val]? = some addressWord)
    (capacity : base.val + dst.val < exec.slots.length)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (storeWf : wf_store (decodeStore view code store)) (ambientWf : wf_frame ambient)
    (operationWf : wf_admininstr (.LOAD ty none argument))
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val) :
    runtime.interp.execute_load memory exec store instanceIndex base (numericLoadOpcode ty) dst address offset ⦃ out =>
      (∃ word, out.1 = .Ok () ∧ SlotsEffect exec out.2 (exec.slots.val.set (base.val+dst.val) word) ∧
        StepH ⟨⟨decodeStore view code store,ambient⟩,
          [Spec.Segment.i32 (UScalar.cast .U32 addressWord).val,.LOAD ty none argument]⟩ []
          ⟨⟨decodeStore view code store,ambient⟩,[admininstr_val (decodeWords (numericMemoryType ty) word 0#u64)]⟩) ∨
      (out = (.Err (.Trap .MemoryOutOfBounds),exec) ∧
        StepH ⟨⟨decodeStore view code store,ambient⟩,
          [Spec.Segment.i32 (UScalar.cast .U32 addressWord).val,.LOAD ty none argument]⟩ []
          ⟨⟨decodeStore view code store,ambient⟩,[.TRAP]⟩) ⦄ := by
  have memoryEq := memory_lookup_decodes view code store inst ambient memoryAddress object moduleEq mapped issued
  have bytesWf : Forall wf_byte (fun_mem ⟨decodeStore view code store,ambient⟩ (.mk_uN 0)).BYTES := by
    rw [memoryEq]
    intro byte member
    obtain ⟨raw,_,rfl⟩ := List.mem_map.mp member
    constructor
    scalar_tac
  have source := Spec.numeric_load_step (decodeStore view code store) ambient ty argument
    (UScalar.cast .U32 addressWord).val storeWf ambientWf (by scalar_tac) operationWf bytesWf
  simp only [Spec.numericLoadResult,memoryEq,decodeMemory,offsetEq,decodeBytes,List.length_map] at source
  apply WP.spec_mono (execute_load_effect memory view laws exec store instanceIndex base
    (numericLoadOpcode ty) dst address offset inst memoryAddress object addressWord found mapped issued input capacity)
  intro out effect
  have width : (scalarLoadWidth (numericLoadOpcode ty)).val = Spec.scalarNumBytes ty := by cases ty <;> rfl
  have wordEq (word : U64) : scalarLoadedWord (numericLoadOpcode ty) word = word := by cases ty <;> rfl
  simp only [width,wordEq] at effect
  by_cases fits : (UScalar.cast .U32 addressWord).val + offset.val + Spec.scalarNumBytes ty ≤ (view object.buf).val.length
  · rw [if_pos fits] at source effect
    refine Or.inl ⟨_,effect.1,effect.2,?_⟩
    simpa only [numeric_load_word_decodes ty (view object.buf).val _ fits,
      admininstr_val,decodeBytes,List.map_take,List.map_drop] using source
  · rw [if_neg fits] at source effect
    exact Or.inr ⟨effect,source⟩
end Exec.Interp
