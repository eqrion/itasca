import Exec.Spec.MemoryByteCopy
namespace Itasca.Runtime.Spec.Segment
open SpecExt

theorem memory_copy_trap (s : store) (f : frame) (destination source count : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32) (hn : count < 2^32)
    (outside : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length < source+count ∨
      (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length < destination+count) :
    StepH ⟨⟨s,f⟩,operands destination source count ++ [.MEMORY_COPY]⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩ := by
  have input := init_config_wf s f destination source count .MEMORY_COPY hs hf hd hi hn .admininstr_case_65
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_make hs hf (by simp [Forall]; exact .admininstr_case_73))
  exact Step_read.memory_copy_trap ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN destination)) (.mk_num__0 .I32 (.mk_uN source)) count
    (by simp [proj_num__0]) (by simp [proj_num__0]) outside input .admininstr_case_73 (index_wf _ (by decide))

theorem memory_copy_zero (s : store) (f : frame) (destination source : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32)
    (inside : source ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length ∧ destination ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length) :
    StepH ⟨⟨s,f⟩,operands destination source 0 ++ [.MEMORY_COPY]⟩ [] ⟨⟨s,f⟩,[]⟩ := by
  have input := init_config_wf s f destination source 0 .MEMORY_COPY hs hf hd hi (by decide) .admininstr_case_65
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_make hs hf (by simp [Forall]))
  exact Step_read.memory_copy_zero ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN destination)) (.mk_num__0 .I32 (.mk_uN source)) 0
    (by simp [proj_num__0]) (by simp [proj_num__0]) (by simpa [proj_num__0,proj_uN_0] using inside) rfl input

theorem memory_copy_forward_expand (s : store) (f : frame) (destination source count : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32) (hn : count+1 < 2^32)
    (inside : source+(count+1) ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length ∧ destination+(count+1) ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length)
    (direction : destination ≤ source) :
    StepH ⟨⟨s,f⟩,operands destination source (count+1) ++ [.MEMORY_COPY]⟩ []
      ⟨⟨s,f⟩,[i32 destination,i32 source,loadByte,storeByte] ++
        (operands (next32 destination) (next32 source) count ++ [.MEMORY_COPY])⟩ := by
  have input := init_config_wf s f destination source (count+1) .MEMORY_COPY hs hf hd hi hn .admininstr_case_65
  have output : wf_config ⟨⟨s,f⟩,[i32 destination,i32 source,loadByte,storeByte] ++
        (operands (next32 destination) (next32 source) count ++ [.MEMORY_COPY])⟩ := by
    apply wf_config_make hs hf
    simp only [operands,List.cons_append,List.nil_append,Forall,List.mem_cons,List.not_mem_nil,
      false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨i32_wf _ hd,i32_wf _ hi,loadByte_wf,storeByte_wf,i32_wf _ (next32_bound _),
      i32_wf _ (next32_bound _),i32_wf _ (by omega),.admininstr_case_65⟩
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  have read := Step_read.memory_copy_le ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN destination)) (.mk_num__0 .I32 (.mk_uN source))
    (count+1) (.mk_uN (next32 source)) (.mk_uN (next32 destination)) zeroMemarg
    (by simp [proj_num__0]) (next32_add source) (by simp [proj_num__0]) (next32_add destination)
    (.fun_memarg0_case_0 zeroMemarg_wf) (Nat.succ_ne_zero count) inside direction input
    (i32_wf _ hd) (i32_wf _ hi) loadByte_wf storeByte_wf (i32_wf _ (next32_bound _)) (i32_wf _ (next32_bound _))
    (by simpa [i32] using i32_wf count (by omega)) .admininstr_case_65
  simpa [operands,i32,loadByte,storeByte,PackedMemory.load,PackedMemory.type,PackedMemory.bits,numtype_Inn] using read

theorem memory_copy_backward_expand (s : store) (f : frame) (destination source count : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32) (hn : count+1 < 2^32)
    (inside : source+(count+1) ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length ∧ destination+(count+1) ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length)
    (memoryBound : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length ≤ 2^32)
    (direction : source < destination) :
    StepH ⟨⟨s,f⟩,operands destination source (count+1) ++ [.MEMORY_COPY]⟩ []
      ⟨⟨s,f⟩,[i32 (destination+count),i32 (source+count),loadByte,storeByte] ++
        (operands destination source count ++ [.MEMORY_COPY])⟩ := by
  have endEq (n : Nat) : ((n : Int)+(count+1)).toNat-1 = n+count := by omega
  have hd' : destination+count < 2^32 := by omega
  have hi' : source+count < 2^32 := by omega
  have input := init_config_wf s f destination source (count+1) .MEMORY_COPY hs hf hd hi hn .admininstr_case_65
  have output : wf_config ⟨⟨s,f⟩,[i32 (destination+count),i32 (source+count),loadByte,storeByte] ++
        (operands destination source count ++ [.MEMORY_COPY])⟩ := by
    apply wf_config_make hs hf
    simp only [operands,List.cons_append,List.nil_append,Forall,List.mem_cons,List.not_mem_nil,
      false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨i32_wf _ hd',i32_wf _ hi',loadByte_wf,storeByte_wf,i32_wf _ hd,i32_wf _ hi,
      i32_wf _ (by omega),.admininstr_case_65⟩
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  have read := Step_read.memory_copy_gt ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN destination)) (.mk_num__0 .I32 (.mk_uN source))
    (count+1) zeroMemarg (by simp [proj_num__0]) (by simp [proj_num__0]) (.fun_memarg0_case_0 zeroMemarg_wf)
    direction (Nat.succ_ne_zero count) inside input
    (by simpa [proj_num__0,proj_uN_0,i32,endEq] using i32_wf _ hd')
    (by simpa [proj_num__0,proj_uN_0,i32,endEq] using i32_wf _ hi')
    loadByte_wf storeByte_wf (i32_wf _ hd) (i32_wf _ hi)
    (by simpa [i32] using i32_wf count (by omega)) .admininstr_case_65
  simpa [operands,i32,loadByte,storeByte,PackedMemory.load,PackedMemory.type,PackedMemory.bits,numtype_Inn,proj_num__0,proj_uN_0,endEq] using read
end Itasca.Runtime.Spec.Segment
