import Itasca.Runtime.Spec.MemoryFillSource
import Itasca.Runtime.Spec.PackedMemory
namespace Itasca.Runtime.Spec.Segment
open SpecExt

def loadByte : admininstr := PackedMemory.load .i32x8 .U zeroMemarg

theorem loadByte_wf : wf_admininstr loadByte := by
  apply wf_admininstr.admininstr_case_56
  · simp only [Option.toList_some,Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact .loadop__case_0 _ .I32 _ (.loadop_Inn_case_0 .I32 (.mk_sz 8) .U (by constructor; decide) (by decide)) rfl
  · exact zeroMemarg_wf

theorem memory_load_byte_step (s : store) (f : frame) (position : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hp : position < 2^32)
    (bytesWf : Forall wf_byte (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES)
    (inside : position < (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length) :
    StepH ⟨⟨s,f⟩,[i32 position,loadByte]⟩ []
      ⟨⟨s,f⟩,[i32 (proj_byte_0 (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES[position]!)]⟩ := by
  have step := PackedMemory.load_step s f .i32x8 .U zeroMemarg position hs hf hp loadByte_wf bytesWf
  have first : ((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.drop position).take 1 =
      [(fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES[position]!] := by
    rw [List.take_one_drop_eq_of_lt_length inside]
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem inside]
  have valueBound := byte_bound ((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES[position]!) (bytesWf _ (by simp [inside]))
  simpa [loadByte,PackedMemory.load,PackedMemory.loaded,PackedMemory.bytes,PackedMemory.bits,PackedMemory.type,
    numtype_Inn,zeroMemarg,proj_uN_0,first,show position+1 ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length from by omega,
    inv_ibytes_,extend__,sizenn,Builtins.integerOfBytes,proj_byte_0,Nat.mod_eq_of_lt (show proj_byte_0 (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES[position]! < 2^32 from by omega),i32] using step

/-- The source copy expansion reads before it writes, even when the source
and destination designate the same memory. -/
theorem memory_copy_byte_steps (s : store) (f : frame) (destination source : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32)
    (mapped : 0 < f.MODULE.MEMS.length)
    (bytesWf : Forall wf_byte (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES)
    (inside : source < (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length)
    (destinationInside : destination < (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length) :
    StepsH ⟨⟨s,f⟩,[i32 destination,i32 source,loadByte,storeByte]⟩ []
      ⟨⟨memoryWrite s f destination (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES[source]!,f⟩,[]⟩ := by
  have byteWf := bytesWf ((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES[source]!) (by simp [inside])
  have loaded := stepH_instrs (memory_load_byte_step s f source hs hf hi bytesWf inside)
    [.CONST .I32 (.mk_num__0 .I32 (.mk_uN destination))] [storeByte]
    (by simpa [Forall] using wf_val.val_case_0 _ _ ((by cases i32_wf destination hd; assumption)))
    (by simpa [Forall] using storeByte_wf)
  have stored := memory_write_step s f destination _ hs hf hd byteWf mapped destinationInside
  exact stepsH_trans (stepsH_single (by simpa [instrContext,vals,admininstr_val,i32] using loaded)) (stepsH_single stored)
end Itasca.Runtime.Spec.Segment
