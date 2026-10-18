import Exec.Interp.Relations.PackedMemory

namespace Exec.Interp.PackedMemory
open Aeneas Aeneas.Std SpecExt

private theorem machineBytes_wf (bytes : List U8) : Forall wf_byte (Store.decodeBytes bytes) := by
  intro byte member
  obtain ⟨raw,_,rfl⟩ := List.mem_map.mp member
  constructor
  scalar_tac

theorem load_word_decodes (op : Spec.PackedMemory) (sign : sx) (bytes : List U8) (start : Nat)
    (inside : start + op.bytes ≤ bytes.length) :
    Store.decodeWords (numericMemoryType (numtype_Inn op.type))
      (scalarLoadedWord (loadOpcode op sign) (scalarLoadBytes bytes start 0#u64 0 op.bytes)) 0#u64 =
      .CONST (numtype_Inn op.type) (op.loaded sign (Store.decodeBytes ((bytes.drop start).take op.bytes))) := by
  have width : op.bytes ≤ 8 := by cases op <;> decide
  have wordEq := scalarLoadBytes_source bytes start op.bytes width inside
  have payloadWf := machineBytes_wf ((bytes.drop start).take op.bytes)
  have payloadLength : (Store.decodeBytes ((bytes.drop start).take op.bytes)).length = op.bytes := by
    simp only [Store.decodeBytes,List.length_map,List.length_take,List.length_drop]
    omega
  have bounded := Spec.integerOfBytes_bound _ payloadWf
  rw [payloadLength] at bounded
  have power : 256^op.bytes = 2^op.bits := by cases op <;> decide
  rw [power] at bounded
  rw [load_word_value op sign _ (by rw [wordEq]; exact bounded)]
  simp only [Spec.PackedMemory.loaded,inv_ibytes_,wordEq]

/-- Every packed load, signed or unsigned, returns exactly its source value or
the generated bounds trap. -/
theorem memory_load_source (op : Spec.PackedMemory) (sign : sx) (address offset : U32) (bytes : Slice U8)
    (s : store) (f : frame) (argument : memarg)
    (storeWf : wf_store s) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (op.load sign argument))
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (memoryEq : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Store.decodeBytes bytes.val) :
    runtime.interp.memory.load (loadOpcode op sign) address offset bytes ⦃ result =>
      match result with
      | .Ok word => StepH ⟨⟨s,f⟩,[Spec.Segment.i32 address.val,op.load sign argument]⟩ []
          ⟨⟨s,f⟩,[admininstr_val (Store.decodeWords (numericMemoryType (numtype_Inn op.type)) word 0#u64)]⟩
      | .Err error => error = .Trap .MemoryOutOfBounds ∧
          StepH ⟨⟨s,f⟩,[Spec.Segment.i32 address.val,op.load sign argument]⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩ ⦄ := by
  have source := op.load_step s f sign argument address.val storeWf frameWf (by scalar_tac)
    operationWf (by rw [memoryEq]; exact machineBytes_wf bytes.val)
  simp only [memoryEq,offsetEq,Store.decodeBytes,List.length_map] at source
  apply WP.spec_mono (memory_load_effect (loadOpcode op sign) address offset bytes)
  intro result effect
  unfold ScalarLoadEffect at effect
  rw [load_width] at effect
  by_cases fits : address.val + offset.val + op.bytes ≤ bytes.val.length
  · rw [if_pos fits] at source effect
    rw [effect]
    simpa only [load_word_decodes op sign bytes.val _ fits,admininstr_val,
      Store.decodeBytes,List.map_take,List.map_drop] using source
  · rw [if_neg fits] at source effect
    rw [effect]
    exact ⟨rfl,source⟩

/-- Every packed store writes the canonical low-byte source payload. Bounds
failure leaves the entire byte slice unchanged. -/
theorem memory_store_source (op : Spec.PackedMemory) (address offset : U32) (value : U64) (bytes : Slice U8)
    (s : store) (f : frame) (argument : memarg)
    (storeWf : wf_store s) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (op.store argument))
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (memoryEq : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Store.decodeBytes bytes.val)
    (mapped : 0 < f.MODULE.MEMS.length) :
    runtime.interp.memory.store (storeOpcode op) address offset value bytes ⦃ out =>
      if address.val + offset.val + op.bytes ≤ bytes.length then
        out.1 = .Ok () ∧ Store.decodeBytes out.2.val = (Store.decodeBytes bytes.val).setSlice!
          (address.val+offset.val) (Builtins.integerBytes op.bytes value.val) ∧
        StepH ⟨⟨s,f⟩,[Spec.Segment.i32 address.val,.CONST (numtype_Inn op.type)
          (numericStoreValue (numtype_Inn op.type) value),op.store argument]⟩ []
          ⟨⟨Spec.memoryPayloadWrite s f (address.val+offset.val) (Builtins.integerBytes op.bytes value.val),f⟩,[]⟩
      else out = (.Err (.Trap .MemoryOutOfBounds),bytes) ∧
        StepH ⟨⟨s,f⟩,[Spec.Segment.i32 address.val,.CONST (numtype_Inn op.type)
          (numericStoreValue (numtype_Inn op.type) value),op.store argument]⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩ ⦄ := by
  have source := op.store_step s f argument address.val
    (storeBits op value)
    storeWf frameWf (by scalar_tac) operationWf
    (by rw [←store_value op value]; exact numericStoreValue_wf _ value) mapped
  simp only [memoryEq,offsetEq,Store.decodeBytes,List.length_map,←store_value op value,store_bytes op value] at source
  apply WP.spec_mono (memory_store_effect (storeOpcode op) address offset value bytes)
  intro out effect
  unfold ScalarStoreEffect at effect
  rw [store_width] at effect
  by_cases fits : address.val + offset.val + op.bytes ≤ bytes.val.length
  · rw [if_pos fits] at source effect ⊢
    obtain ⟨status,byteEffect⟩ := effect
    refine ⟨status,?_,source⟩
    rw [byteEffect,scalarStoreBytes_source bytes.val (address.val+offset.val) value op.bytes fits]
  · rw [if_neg fits] at source effect ⊢
    exact ⟨effect,source⟩
end Exec.Interp.PackedMemory
