import Exec.Spec.MemoryInitSource
namespace Itasca.Runtime.Spec.Segment
open SpecExt

def fillByte (value : Nat) : byte := .mk_byte (value % 256)
theorem fillByte_wf (value : Nat) : wf_byte (fillByte value) := by
  change wf_byte (.mk_byte (value % 256))
  constructor
  have := Nat.mod_lt value (by decide : 0 < 256)
  omega

theorem fill_byte_encoding (value : Nat) : ibytes_ 8 (wrap__ 32 8 (.mk_uN value)) = [fillByte value] := by
  norm_num [ibytes_,wrap__,proj_uN_0,SpecExt.Builtins.integerBytes,fillByte]

theorem memory_write_i32_step (s : store) (f : frame) (position value : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hp : position < 2^32) (hv : value < 2^32)
    (mapped : 0 < f.MODULE.MEMS.length)
    (inside : position < (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length) :
    StepH ⟨⟨s,f⟩,[i32 position,i32 value,storeByte]⟩ []
      ⟨⟨memoryWrite s f position (fillByte value),f⟩,[]⟩ := by
  have fresh := memoryWrite_wf s f position (fillByte value) hs (fillByte_wf value)
  apply StepH.step
  apply Step.store_pack_val _ _ .I32 _ 8 zeroMemarg [fillByte value] _
  · simp [proj_num__0]
  · have write := fun_with_mem.fun_with_mem_case_0 s f (.mk_uN 0) position 1 [fillByte value] mapped (by omega)
      (by simpa only [splice_singleton_eq_set,memoryWrite,proj_uN_0] using wf_state.state_case_0 _ _ fresh hf) (.state_case_0 _ _ hs hf)
    norm_num [proj_num__0,proj_uN_0,zeroMemarg,rat_to_nat,splice_singleton_eq_set,memoryWrite] at write ⊢
    exact write
  · simp [size,valtype_Inn]
  · simp [proj_num__0]
  · exact (fill_byte_encoding value).symm
  · apply wf_config_make hs hf
    simp only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨i32_wf _ hp,i32_wf _ hv,storeByte_wf⟩
  · exact wf_config_make fresh hf (by simp [Forall])

theorem memory_fill_trap (s : store) (f : frame) (destination value count : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hv : value < 2^32) (hn : count < 2^32)
    (outside : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length < destination+count) :
    StepH ⟨⟨s,f⟩,operands destination value count ++ [.MEMORY_FILL]⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩ := by
  have input := init_config_wf s f destination value count .MEMORY_FILL hs hf hd hv hn .admininstr_case_64
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_make hs hf (by simp [Forall]; exact .admininstr_case_73))
  exact Step_read.memory_fill_trap ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN destination))
    (.CONST .I32 (.mk_num__0 .I32 (.mk_uN value))) count
    (by simp [proj_num__0]) outside input .admininstr_case_73 (index_wf _ (by decide))

theorem memory_fill_zero (s : store) (f : frame) (destination value : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hv : value < 2^32)
    (inside : destination ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length) :
    StepH ⟨⟨s,f⟩,operands destination value 0 ++ [.MEMORY_FILL]⟩ [] ⟨⟨s,f⟩,[]⟩ := by
  have input := init_config_wf s f destination value 0 .MEMORY_FILL hs hf hd hv (by decide) .admininstr_case_64
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_make hs hf (by simp [Forall]))
  exact Step_read.memory_fill_zero ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN destination))
    (.CONST .I32 (.mk_num__0 .I32 (.mk_uN value))) 0
    (by simp [proj_num__0]) (by simpa [proj_num__0,proj_uN_0] using inside) rfl input

theorem memory_fill_expand (s : store) (f : frame) (destination value count : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hv : value < 2^32) (hn : count+1 < 2^32)
    (inside : destination+(count+1) ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length) :
    StepH ⟨⟨s,f⟩,operands destination value (count+1) ++ [.MEMORY_FILL]⟩ []
      ⟨⟨s,f⟩,[i32 destination,i32 value,storeByte] ++
        (operands (next32 destination) value count ++ [.MEMORY_FILL])⟩ := by
  have input := init_config_wf s f destination value (count+1) .MEMORY_FILL hs hf hd hv hn .admininstr_case_64
  have output : wf_config ⟨⟨s,f⟩,[i32 destination,i32 value,storeByte] ++
        (operands (next32 destination) value count ++ [.MEMORY_FILL])⟩ := by
    apply wf_config_make hs hf
    simp only [operands,List.cons_append,List.nil_append,Forall,List.mem_cons,List.not_mem_nil,
      false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨i32_wf _ hd,i32_wf _ hv,storeByte_wf,i32_wf _ (next32_bound _),i32_wf _ hv,
      i32_wf _ (by omega),.admininstr_case_64⟩
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  have read := Step_read.memory_fill_succ ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN destination))
    (.CONST .I32 (.mk_num__0 .I32 (.mk_uN value))) (count+1) (.mk_uN (next32 destination)) zeroMemarg
    (by simp [proj_num__0]) (next32_add destination) (.fun_memarg0_case_0 zeroMemarg_wf)
    (Nat.succ_ne_zero count) inside input (i32_wf _ hd) storeByte_wf (i32_wf _ (next32_bound _))
    (by simpa [i32] using i32_wf count (by omega)) .admininstr_case_64
  simpa [operands,i32,storeByte,admininstr_val] using read

def memoryFill (s : store) (f : frame) (destination value : Nat) : Nat → store
  | 0 => s
  | count+1 => memoryFill (memoryWrite s f destination (fillByte value)) f (next32 destination) value count

theorem memory_fill_steps (s : store) (f : frame) (destination value count : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hv : value < 2^32) (hn : count < 2^32)
    (mapped : 0 < f.MODULE.MEMS.length) (address : f.MODULE.MEMS[0]! < s.MEMS.length)
    (inside : destination+count ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length) :
    StepsH ⟨⟨s,f⟩,operands destination value count ++ [.MEMORY_FILL]⟩ []
      ⟨⟨memoryFill s f destination value count,f⟩,[]⟩ := by
  induction count generalizing s destination with
  | zero => exact stepsH_single (memory_fill_zero s f destination value hs hf hd hv (by simpa using inside))
  | succ count ih =>
    let fresh := memoryWrite s f destination (fillByte value)
    have hw := memoryWrite_wf s f destination (fillByte value) hs (fillByte_wf value)
    have lengthEq := memoryWrite_mem_length s f destination (fillByte value) address
    have afterWf := (wf_config_parts (init_config_wf fresh f (next32 destination) value count _ hw hf (next32_bound _) hv
      (by omega) .admininstr_case_64)).2
    have first := memory_fill_expand s f destination value count hs hf hd hv hn inside
    have second := stepH_instrs (memory_write_i32_step s f destination value hs hf hd hv mapped (by omega)) []
      (operands (next32 destination) value count ++ [.MEMORY_FILL]) (by simp [Forall]) afterWf
    have rest := ih fresh (next32 destination) hw (next32_bound _) (by omega)
      (by simpa [fresh,memoryWrite] using address)
      (by rw [show (fun_mem ⟨fresh,f⟩ (.mk_uN 0)).BYTES.length =
            (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length from lengthEq]
          have := next32_le destination
          omega)
    have combined := stepsH_trans (stepsH_single first) (stepsH_trans (stepsH_single second) rest)
    simpa only [instrContext,vals,List.map_nil,List.nil_append,List.append_nil,memoryFill,fresh] using combined
end Itasca.Runtime.Spec.Segment
