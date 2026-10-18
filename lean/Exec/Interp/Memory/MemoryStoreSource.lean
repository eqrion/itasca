import Exec.Interp.Memory.MemoryStoreEncoding
import Exec.Interp.Memory.MemoryLoadSource
import Exec.Spec.MemoryStore

namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt

def numericStoreOpcode : numtype → U16
  | .I32 => 54#u16
  | .I64 => 55#u16
  | .F32 => 56#u16
  | .F64 => 57#u16

def numericStoreValue (ty : numtype) (word : U64) : num_ :=
  match ty with
  | .I32 => .mk_num__0 .I32 (.mk_uN (word.val % 2^32))
  | .I64 => .mk_num__0 .I64 (.mk_uN word.val)
  | .F32 => .mk_num__1 .F32 (Builtins.floatOfBits 32 (word.val % 2^32))
  | .F64 => .mk_num__1 .F64 (Builtins.floatOfBits 64 word.val)

theorem numericStoreValue_decodes (ty : numtype) (word : U64) :
    Store.decodeWords (numericMemoryType ty) word 0#u64 = .CONST ty (numericStoreValue ty word) := by
  cases ty <;> rfl

private theorem numericStoreOpcode_width (ty : numtype) :
    (scalarStoreWidth (numericStoreOpcode ty)).val = Spec.scalarNumBytes ty := by cases ty <;> rfl

theorem numericStoreValue_wf (ty : numtype) (word : U64) : wf_num_ ty (numericStoreValue ty word) := by
  cases ty
  · apply wf_num_.num__case_0 .I32 .I32 _ (by decide) _ rfl
    constructor
    have bound := Nat.mod_lt word.val (by norm_num : 0 < 2^32)
    norm_num [size,valtype_Inn,proj_uN_0]
    omega
  · apply wf_num_.num__case_0 .I64 .I64 _ (by decide) _ rfl
    constructor
    norm_num [size,valtype_Inn,proj_uN_0]
    scalar_tac
  · apply wf_num_.num__case_1 .F32 .F32 _ _ rfl
    exact Builtins.Float.floatOfBits_wf_32 _ (Nat.mod_lt _ (by norm_num))
  · apply wf_num_.num__case_1 .F64 .F64 _ _ rfl
    apply Builtins.Float.floatOfBits_wf_64
    scalar_tac

theorem numericStoreValue_bytes (ty : numtype) (word : U64) :
    nbytes_ ty (numericStoreValue ty word) = Builtins.integerBytes (Spec.scalarNumBytes ty) word.val := by
  cases ty
  · simpa [nbytes_,numericStoreValue,ibytes_,proj_uN_0,Spec.scalarNumBytes] using Spec.integerBytes_mod 4 word.val
  · rfl
  · have bits := Builtins.Float.float_bits_roundtrip_32 (word.val % 2^32) (Nat.mod_lt _ (by norm_num))
    change Builtins.integerBytes 4 (Builtins.floatBits 32 (Builtins.floatOfBits 32 (word.val % 2^32))) = _
    rw [bits]
    exact Spec.integerBytes_mod 4 word.val
  · have bits := Builtins.Float.float_bits_roundtrip_64 word.val (by scalar_tac)
    simp [nbytes_,numericStoreValue,fbytes_,bits,Spec.scalarNumBytes]

/-- The complete full-width scalar store produces exactly the specification
byte payload and source store transition; failed writes leave every byte intact. -/
theorem memory_numeric_store_source (ty : numtype) (address offset : U32) (value : U64) (bytes : Slice U8)
    (s : store) (f : frame) (argument : memarg)
    (storeWf : wf_store s) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (.STORE ty none argument))
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (memoryEq : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Store.decodeBytes bytes.val)
    (mapped : 0 < f.MODULE.MEMS.length) :
    runtime.interp.memory.store (numericStoreOpcode ty) address offset value bytes ⦃ out =>
      if address.val + offset.val + Spec.scalarNumBytes ty ≤ bytes.length then
        out.1 = .Ok () ∧ Store.decodeBytes out.2.val =
          (Store.decodeBytes bytes.val).setSlice! (address.val+offset.val) (nbytes_ ty (numericStoreValue ty value)) ∧
        StepH ⟨⟨s,f⟩,[Spec.Segment.i32 address.val,.CONST ty (numericStoreValue ty value),.STORE ty none argument]⟩ []
          ⟨⟨Spec.memoryPayloadWrite s f (address.val+offset.val) (nbytes_ ty (numericStoreValue ty value)),f⟩,[]⟩
      else out = (.Err (.Trap .MemoryOutOfBounds),bytes) ∧
        StepH ⟨⟨s,f⟩,[Spec.Segment.i32 address.val,.CONST ty (numericStoreValue ty value),.STORE ty none argument]⟩ []
          ⟨⟨s,f⟩,[.TRAP]⟩ ⦄ := by
  have source := Spec.numeric_store_step s f ty argument address.val (numericStoreValue ty value)
    storeWf frameWf (by scalar_tac) operationWf (numericStoreValue_wf ty value) mapped
  simp only [memoryEq,offsetEq,Store.decodeBytes,List.length_map] at source
  apply WP.spec_mono (memory_store_effect (numericStoreOpcode ty) address offset value bytes)
  intro out effect
  unfold ScalarStoreEffect at effect
  rw [numericStoreOpcode_width] at effect
  by_cases fits : address.val + offset.val + Spec.scalarNumBytes ty ≤ bytes.val.length
  · rw [if_pos fits] at source effect ⊢
    obtain ⟨status,byteEffect⟩ := effect
    refine ⟨status,?_,source⟩
    rw [byteEffect,scalarStoreBytes_source bytes.val (address.val+offset.val) value (Spec.scalarNumBytes ty) fits,
      numericStoreValue_bytes]
  · rw [if_neg fits] at source effect ⊢
    exact ⟨effect,source⟩
end Exec.Interp
