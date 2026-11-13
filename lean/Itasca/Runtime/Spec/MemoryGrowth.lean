import Itasca.Runtime.Spec.FloatPromote
import Itasca.Runtime.Spec.FloatTrunc
import Itasca.Runtime.Spec.SegmentInitCases

/-!
Sections, each formerly its own module: MemoryFill, MemoryByteCopy, MemoryCopy, CopyPlain, TableCopy, TableGrowth, MemoryGrowth.
-/

/-! ## MemoryFill -/

section

/-!
Source semantics of `memory.fill`. Connect the generated recursive rules to the bounded interval update used by runtime correspondence proofs.
-/

/-! ## Memory Fill Source -/

section

namespace Itasca.Runtime.Spec.Segment
open SpecExt

def fillByte (value : Nat) : byte := .mk_byte (value % 256)
theorem fill_byte_wf (value : Nat) : wf_byte (fillByte value) := by
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
  have fresh := memory_write_wf s f position (fillByte value) hs (fill_byte_wf value)
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
    exact ⟨i32_wf _ hp,i32_wf _ hv,store_byte_wf⟩
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
    exact ⟨i32_wf _ hd,i32_wf _ hv,store_byte_wf,i32_wf _ (next32_bound _),i32_wf _ hv,
      i32_wf _ (by omega),.admininstr_case_64⟩
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  have read := Step_read.memory_fill_succ ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN destination))
    (.CONST .I32 (.mk_num__0 .I32 (.mk_uN value))) (count+1) (.mk_uN (next32 destination)) zeroMemarg
    (by simp [proj_num__0]) (next32_add destination) (.fun_memarg0_case_0 zero_memarg_wf)
    (Nat.succ_ne_zero count) inside input (i32_wf _ hd) store_byte_wf (i32_wf _ (next32_bound _))
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
  | zero => exact steps_h_single (memory_fill_zero s f destination value hs hf hd hv (by simpa using inside))
  | succ count ih =>
    let fresh := memoryWrite s f destination (fillByte value)
    have hw := memory_write_wf s f destination (fillByte value) hs (fill_byte_wf value)
    have lengthEq := memory_write_mem_length s f destination (fillByte value) address
    have afterWf := (wf_config_parts (init_config_wf fresh f (next32 destination) value count _ hw hf (next32_bound _) hv
      (by omega) .admininstr_case_64)).2
    have first := memory_fill_expand s f destination value count hs hf hd hv hn inside
    have second := step_h_instrs (memory_write_i32_step s f destination value hs hf hd hv mapped (by omega)) []
      (operands (next32 destination) value count ++ [.MEMORY_FILL]) (by simp [Forall]) afterWf
    have rest := ih fresh (next32 destination) hw (next32_bound _) (by omega)
      (by simpa [fresh,memoryWrite] using address)
      (by rw [show (fun_mem ⟨fresh,f⟩ (.mk_uN 0)).BYTES.length =
            (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length from lengthEq]
          have := next32_le destination
          omega)
    have combined := steps_h_trans (steps_h_single first) (steps_h_trans (steps_h_single second) rest)
    simpa only [instrContext,vals,List.map_nil,List.nil_append,List.append_nil,memoryFill,fresh] using combined
end Itasca.Runtime.Spec.Segment

end

/-! ## Memory Fill Algebra -/

section

namespace Itasca.Runtime.Spec.Segment
open SpecExt

theorem memory_fill_eq (s : store) (f : frame) (destination value count : Nat)
    (address : f.MODULE.MEMS[0]! < s.MEMS.length)
    (memoryBound : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length ≤ 2^32)
    (inside : destination+count ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length) :
    memoryFill s f destination value count =
      {s with MEMS := s.MEMS.modify f.MODULE.MEMS[0]! (fun memory =>
        {memory with BYTES := fillInto memory.BYTES destination (fillByte value) count})} := by
  induction count generalizing s destination with
  | zero =>
    simp only [memoryFill,fillInto]
    have identity : (fun memory : meminst => {memory with BYTES := memory.BYTES}) = id := by funext memory; cases memory; rfl
    rw [identity,List.modify_id]
  | succ count ih =>
    by_cases done : count=0
    · subst count
      simp only [memoryFill,fillInto,memoryWrite]
    · have dstBound : destination+1 < 2^32 := by omega
      have dstNext : next32 destination = destination+1 := Nat.mod_eq_of_lt dstBound
      have lengthEq := memory_write_mem_length s f destination (fillByte value) address
      rw [memoryFill,dstNext,ih (memoryWrite s f destination (fillByte value)) (destination+1)
        (by simpa [memoryWrite] using address)
        (by simpa only [lengthEq] using memoryBound) (by rw [lengthEq]; omega)]
      simp only [memoryWrite,List.modify_modify_eq,Function.comp_def,fillInto]
end Itasca.Runtime.Spec.Segment

end

end

/-! ## MemoryByteCopy -/

section

namespace Itasca.Runtime.Spec.Segment
open SpecExt

def loadByte : admininstr := PackedMemory.load .i32x8 .U zeroMemarg

theorem load_byte_wf : wf_admininstr loadByte := by
  apply wf_admininstr.admininstr_case_56
  · simp only [Option.toList_some,Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact .loadop__case_0 _ .I32 _ (.loadop_Inn_case_0 .I32 (.mk_sz 8) .U (by constructor; decide) (by decide)) rfl
  · exact zero_memarg_wf

theorem memory_load_byte_step (s : store) (f : frame) (position : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hp : position < 2^32)
    (bytesWf : Forall wf_byte (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES)
    (inside : position < (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length) :
    StepH ⟨⟨s,f⟩,[i32 position,loadByte]⟩ []
      ⟨⟨s,f⟩,[i32 (proj_byte_0 (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES[position]!)]⟩ := by
  have step := PackedMemory.load_step s f .i32x8 .U zeroMemarg position hs hf hp load_byte_wf bytesWf
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
  have loaded := step_h_instrs (memory_load_byte_step s f source hs hf hi bytesWf inside)
    [.CONST .I32 (.mk_num__0 .I32 (.mk_uN destination))] [storeByte]
    (by simpa [Forall] using wf_val.val_case_0 _ _ ((by cases i32_wf destination hd; assumption)))
    (by simpa [Forall] using store_byte_wf)
  have stored := memory_write_step s f destination _ hs hf hd byteWf mapped destinationInside
  exact steps_h_trans (steps_h_single (by simpa [instrContext,vals,admininstr_val,i32] using loaded)) (steps_h_single stored)
end Itasca.Runtime.Spec.Segment

end

/-! ## MemoryCopy -/

section

/-!
Source semantics of `memory.copy`. Connect the generated recursive rules to the bounded interval update used by runtime correspondence proofs.
-/

/-! ## Memory Copy Source -/

section

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
    exact ⟨i32_wf _ hd,i32_wf _ hi,load_byte_wf,store_byte_wf,i32_wf _ (next32_bound _),
      i32_wf _ (next32_bound _),i32_wf _ (by omega),.admininstr_case_65⟩
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  have read := Step_read.memory_copy_le ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN destination)) (.mk_num__0 .I32 (.mk_uN source))
    (count+1) (.mk_uN (next32 source)) (.mk_uN (next32 destination)) zeroMemarg
    (by simp [proj_num__0]) (next32_add source) (by simp [proj_num__0]) (next32_add destination)
    (.fun_memarg0_case_0 zero_memarg_wf) (Nat.succ_ne_zero count) inside direction input
    (i32_wf _ hd) (i32_wf _ hi) load_byte_wf store_byte_wf (i32_wf _ (next32_bound _)) (i32_wf _ (next32_bound _))
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
    exact ⟨i32_wf _ hd',i32_wf _ hi',load_byte_wf,store_byte_wf,i32_wf _ hd,i32_wf _ hi,
      i32_wf _ (by omega),.admininstr_case_65⟩
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  have read := Step_read.memory_copy_gt ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN destination)) (.mk_num__0 .I32 (.mk_uN source))
    (count+1) zeroMemarg (by simp [proj_num__0]) (by simp [proj_num__0]) (.fun_memarg0_case_0 zero_memarg_wf)
    direction (Nat.succ_ne_zero count) inside input
    (by simpa [proj_num__0,proj_uN_0,i32,endEq] using i32_wf _ hd')
    (by simpa [proj_num__0,proj_uN_0,i32,endEq] using i32_wf _ hi')
    load_byte_wf store_byte_wf (i32_wf _ hd) (i32_wf _ hi)
    (by simpa [i32] using i32_wf count (by omega)) .admininstr_case_65
  simpa [operands,i32,loadByte,storeByte,PackedMemory.load,PackedMemory.type,PackedMemory.bits,numtype_Inn,proj_num__0,proj_uN_0,endEq] using read
end Itasca.Runtime.Spec.Segment

end

/-! ## Memory Copy Run -/

section

namespace Itasca.Runtime.Spec.Segment
open SpecExt

theorem memory_bytes_wf (s : store) (f : frame) (wellFormed : wf_store s)
    (address : f.MODULE.MEMS[0]! < s.MEMS.length) : Forall wf_byte (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES := by
  have memories : Forall wf_meminst s.MEMS := by cases wellFormed; assumption
  have memory := memories (s.MEMS[f.MODULE.MEMS[0]!]!) (by simpa only [getElem!_pos s.MEMS (f.MODULE.MEMS[0]!) address] using List.getElem_mem address)
  simp only [fun_mem,proj_uN_0]
  generalize same : s.MEMS[f.MODULE.MEMS[0]!]! = m at memory ⊢
  cases memory
  assumption

def memoryCopyForward (s : store) (f : frame) (destination source : Nat) : Nat → store
  | 0 => s
  | count+1 => memoryCopyForward
      (memoryWrite s f destination (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES[source]!) f
      (next32 destination) (next32 source) count

def memoryCopyBackward (s : store) (f : frame) (destination source : Nat) : Nat → store
  | 0 => s
  | count+1 => memoryCopyBackward
      (memoryWrite s f (destination+count) (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES[source+count]!) f destination source count

theorem memory_copy_forward_steps (s : store) (f : frame) (destination source count : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32) (hn : count < 2^32)
    (mapped : 0 < f.MODULE.MEMS.length) (address : f.MODULE.MEMS[0]! < s.MEMS.length)
    (memoryBound : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length ≤ 2^32)
    (inside : source+count ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length ∧ destination+count ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length)
    (direction : destination ≤ source ∨ count=0) :
    StepsH ⟨⟨s,f⟩,operands destination source count ++ [.MEMORY_COPY]⟩ []
      ⟨⟨memoryCopyForward s f destination source count,f⟩,[]⟩ := by
  induction count generalizing s destination source with
  | zero => exact steps_h_single (memory_copy_zero s f destination source hs hf hd hi (by simpa using inside))
  | succ count ih =>
    have order : destination ≤ source := by omega
    have bytesWf := memory_bytes_wf s f hs address
    have srcInside : source < (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length := by omega
    let value := (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES[source]!
    have valueWf : wf_byte value := bytesWf _ (by simp [value,srcInside])
    let fresh := memoryWrite s f destination value
    have hw := memory_write_wf s f destination value hs valueWf
    have lengthEq := memory_write_mem_length s f destination value address
    have afterWf := (wf_config_parts (init_config_wf fresh f (next32 destination) (next32 source) count _ hw hf
      (next32_bound _) (next32_bound _) (by omega) .admininstr_case_65)).2
    have first := memory_copy_forward_expand s f destination source count hs hf hd hi hn inside order
    have second := steps_h_instrs (memory_copy_byte_steps s f destination source hs hf hd hi mapped bytesWf srcInside (by have := inside.2; omega)) []
      (operands (next32 destination) (next32 source) count ++ [.MEMORY_COPY]) (by simp [Forall]) afterWf
    have nextDirection : next32 destination ≤ next32 source ∨ count=0 := by
      by_cases done : count=0
      · exact Or.inr done
      · have dstBelow : destination+1 < 2^32 := by omega
        have srcBelow : source+1 < 2^32 := by omega
        simp only [next32,Nat.mod_eq_of_lt dstBelow,Nat.mod_eq_of_lt srcBelow]
        exact Or.inl (by omega)
    have rest := ih fresh (next32 destination) (next32 source) hw (next32_bound _) (next32_bound _) (by omega)
      (by simpa [fresh,memoryWrite] using address) (by simpa only [fresh,lengthEq] using memoryBound)
      (by rw [show (fun_mem ⟨fresh,f⟩ (.mk_uN 0)).BYTES.length = (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length from lengthEq]
          have := next32_le destination; have := next32_le source; omega) nextDirection
    have combined := steps_h_trans (steps_h_single first) (steps_h_trans second rest)
    simpa only [instrContext,vals,List.map_nil,List.nil_append,List.append_nil,memoryCopyForward,value,fresh] using combined

theorem memory_copy_backward_steps (s : store) (f : frame) (destination source count : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32) (hn : count < 2^32)
    (mapped : 0 < f.MODULE.MEMS.length) (address : f.MODULE.MEMS[0]! < s.MEMS.length)
    (memoryBound : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length ≤ 2^32)
    (inside : source+count ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length ∧ destination+count ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length)
    (direction : source < destination ∨ count=0) :
    StepsH ⟨⟨s,f⟩,operands destination source count ++ [.MEMORY_COPY]⟩ []
      ⟨⟨memoryCopyBackward s f destination source count,f⟩,[]⟩ := by
  induction count generalizing s with
  | zero => exact steps_h_single (memory_copy_zero s f destination source hs hf hd hi (by simpa using inside))
  | succ count ih =>
    have order : source < destination := by omega
    have bytesWf := memory_bytes_wf s f hs address
    have srcInside : source+count < (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length := by omega
    let value := (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES[source+count]!
    have valueWf : wf_byte value := bytesWf _ (by simp [value,srcInside])
    let fresh := memoryWrite s f (destination+count) value
    have hw := memory_write_wf s f (destination+count) value hs valueWf
    have lengthEq := memory_write_mem_length s f (destination+count) value address
    have afterWf := (wf_config_parts (init_config_wf fresh f destination source count _ hw hf hd hi
      (by omega) .admininstr_case_65)).2
    have first := memory_copy_backward_expand s f destination source count hs hf hd hi hn inside memoryBound order
    have second := steps_h_instrs (memory_copy_byte_steps s f (destination+count) (source+count) hs hf (by omega) (by omega)
      mapped bytesWf srcInside (by have := inside.2; omega)) [] (operands destination source count ++ [.MEMORY_COPY]) (by simp [Forall]) afterWf
    have rest := ih fresh hw (by omega) (by simpa [fresh,memoryWrite] using address)
      (by simpa only [fresh,lengthEq] using memoryBound)
      (by rw [show (fun_mem ⟨fresh,f⟩ (.mk_uN 0)).BYTES.length = (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length from lengthEq]; omega)
      (Or.inl order)
    have combined := steps_h_trans (steps_h_single first) (steps_h_trans second rest)
    simpa only [instrContext,vals,List.map_nil,List.nil_append,List.append_nil,memoryCopyBackward,value,fresh] using combined
end Itasca.Runtime.Spec.Segment

end

/-! ## Memory Copy Algebra -/

section

namespace Itasca.Runtime.Spec.Segment
open SpecExt

def withBytes (memory : meminst) (bytes : List byte) : meminst := {memory with BYTES := bytes}

theorem memory_copy_forward_words (s : store) (f : frame) (destination source count : Nat)
    (address : f.MODULE.MEMS[0]! < s.MEMS.length) :
    memoryCopyForward s f destination source count =
      {s with MEMS := s.MEMS.set (f.MODULE.MEMS[0]!) (withBytes (s.MEMS[f.MODULE.MEMS[0]!]!) (copyForward (s.MEMS[f.MODULE.MEMS[0]!]!).BYTES destination source count))} := by
  induction count generalizing s destination source with
  | zero =>
    simp only [memoryCopyForward,copyForward]
    have identity : withBytes (s.MEMS[f.MODULE.MEMS[0]!]!) (s.MEMS[f.MODULE.MEMS[0]!]!).BYTES = s.MEMS[f.MODULE.MEMS[0]!]! := by cases s.MEMS[f.MODULE.MEMS[0]!]!; rfl
    rw [identity]
    simp only [getElem!_pos s.MEMS (f.MODULE.MEMS[0]!) address,List.set_getElem_self]
  | succ count ih =>
    rw [memoryCopyForward,ih (memoryWrite s f destination (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES[source]!)
      (next32 destination) (next32 source) (by simpa [memoryWrite] using address)]
    simp only [memoryWrite,fun_mem,proj_uN_0,List.modify_eq_set,copyForward,withBytes]
    generalize same : f.MODULE.MEMS[0]! = a at address ⊢
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem address,List.set_set,address]

theorem memory_copy_backward_words (s : store) (f : frame) (destination source count : Nat)
    (address : f.MODULE.MEMS[0]! < s.MEMS.length) :
    memoryCopyBackward s f destination source count =
      {s with MEMS := s.MEMS.set (f.MODULE.MEMS[0]!) (withBytes (s.MEMS[f.MODULE.MEMS[0]!]!) (copyBackward (s.MEMS[f.MODULE.MEMS[0]!]!).BYTES destination source count))} := by
  induction count generalizing s with
  | zero =>
    simp only [memoryCopyBackward,copyBackward]
    have identity : withBytes (s.MEMS[f.MODULE.MEMS[0]!]!) (s.MEMS[f.MODULE.MEMS[0]!]!).BYTES = s.MEMS[f.MODULE.MEMS[0]!]! := by cases s.MEMS[f.MODULE.MEMS[0]!]!; rfl
    rw [identity]
    simp only [getElem!_pos s.MEMS (f.MODULE.MEMS[0]!) address,List.set_getElem_self]
  | succ count ih =>
    rw [memoryCopyBackward,ih (memoryWrite s f (destination+count) (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES[source+count]!)
      (by simpa [memoryWrite] using address)]
    simp only [memoryWrite,fun_mem,proj_uN_0,List.modify_eq_set,copyBackward,withBytes]
    generalize same : f.MODULE.MEMS[0]! = a at address ⊢
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem address,List.set_set,address]
end Itasca.Runtime.Spec.Segment

end

/-! ## Memory Copy Snapshot -/

section

namespace Itasca.Runtime.Spec.Segment
open SpecExt

def memoryCopy (s : store) (f : frame) (destination source count : Nat) : store :=
  {s with MEMS := s.MEMS.set (f.MODULE.MEMS[0]!) (withBytes (s.MEMS[f.MODULE.MEMS[0]!]!) ((s.MEMS[f.MODULE.MEMS[0]!]!).BYTES.setSlice! destination ((s.MEMS[f.MODULE.MEMS[0]!]!).BYTES.slice source (source+count))))}

theorem memory_copy_steps (s : store) (f : frame) (destination source count : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32) (hn : count < 2^32)
    (mapped : 0 < f.MODULE.MEMS.length) (address : f.MODULE.MEMS[0]! < s.MEMS.length)
    (memoryBound : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length ≤ 2^32)
    (inside : source+count ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length ∧ destination+count ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length) :
    StepsH ⟨⟨s,f⟩,operands destination source count ++ [.MEMORY_COPY]⟩ []
      ⟨⟨memoryCopy s f destination source count,f⟩,[]⟩ := by
  by_cases direction : destination ≤ source
  · have run := memory_copy_forward_steps s f destination source count hs hf hd hi hn mapped address memoryBound inside (Or.inl direction)
    have snapshot := copy_forward_snapshot (s.MEMS[f.MODULE.MEMS[0]!]!).BYTES
      (s.MEMS[f.MODULE.MEMS[0]!]!).BYTES destination source 0 count count
      (CopyPrefix.initial _ _ _) (by omega) direction inside.1 inside.2 memoryBound
    simp only [Nat.add_zero] at snapshot
    rw [memory_copy_forward_words _ _ _ _ _ address,snapshot] at run
    exact run
  · have run := memory_copy_backward_steps s f destination source count hs hf hd hi hn mapped address memoryBound inside (Or.inl (by omega))
    have snapshot := copy_backward_snapshot (s.MEMS[f.MODULE.MEMS[0]!]!).BYTES
      (s.MEMS[f.MODULE.MEMS[0]!]!).BYTES destination source count count
      (CopySuffix.initial _ _ _ _) (by omega) (by omega) inside.1 inside.2
    rw [memory_copy_backward_words _ _ _ _ _ address,snapshot] at run
    exact run
end Itasca.Runtime.Spec.Segment

end

end

/-! ## CopyPlain -/

section

namespace Itasca.Runtime.Spec.Segment

def copyForwardPlain {T : Type} [Inhabited T] (words : List T) (dst src : Nat) : Nat → List T
  | 0 => words
  | n+1 => copyForwardPlain (words.set dst words[src]!) (dst+1) (src+1) n

theorem copy_forward_plain_snapshot {T : Type} [Inhabited T] (before current : List T) (dst src index remaining count : Nat)
    (state : CopyPrefix before current dst src index) (progress : index+remaining=count)
    (direction : dst ≤ src) (sourceBound : src+count ≤ before.length) (targetBound : dst+count ≤ before.length) :
    copyForwardPlain current (dst+index) (src+index) remaining = before.setSlice! dst (before.slice src (src+count)) := by
  induction remaining generalizing current index with
  | zero =>
    have last : index=count := by omega
    exact (last ▸ state).complete sourceBound targetBound
  | succ remaining ih =>
    have fresh := state.write direction (by omega) (by omega)
    simpa only [copyForwardPlain,Nat.add_assoc] using ih _ (index+1) fresh (by omega)

def copyBackwardFrom {T : Type} [Inhabited T] (words source : List T) (dst src : Nat) : Nat → List T
  | 0 => words
  | n+1 => copyBackwardFrom (words.set (dst+n) source[src+n]!) source dst src n

@[simp] theorem copy_backward_from_length {T : Type} [Inhabited T] (words source : List T) (dst src count : Nat) :
    (copyBackwardFrom words source dst src count).length = words.length := by
  induction count generalizing words with
  | zero => rfl
  | succ n ih => simp only [copyBackwardFrom,ih,List.length_set]

theorem copy_backward_from_effect {T : Type} [Inhabited T] (before source : List T) (dst src count : Nat)
    (sourceBound : src+count ≤ source.length) (targetBound : dst+count ≤ before.length) :
    (∀ j, j < count → (copyBackwardFrom before source dst src count)[dst+j]? = source[src+j]?) ∧
    (∀ j, j < dst ∨ dst+count ≤ j → (copyBackwardFrom before source dst src count)[j]? = before[j]?) := by
  induction count generalizing before with
  | zero => simp [copyBackwardFrom]
  | succ n ih =>
    obtain ⟨copied,outside⟩ := ih (before.set (dst+n) source[src+n]!) (by omega) (by simp; omega)
    constructor
    · intro j bound
      by_cases last : j=n
      · subst j
        have old := outside (dst+n) (Or.inr (by omega))
        have sourceInside : src+n < source.length := by omega
        have targetInside : dst+n < before.length := by omega
        simpa [copyBackwardFrom,sourceInside,targetInside] using old
      · simpa only [copyBackwardFrom] using copied j (by omega)
    · intro j bound
      have old := outside j (by omega)
      have distinct : dst+n ≠ j := by omega
      simpa only [copyBackwardFrom,List.getElem?_set,distinct,if_false] using old

theorem copy_backward_from_snapshot {T : Type} [Inhabited T] (before source : List T) (dst src count : Nat)
    (sourceBound : src+count ≤ source.length) (targetBound : dst+count ≤ before.length) :
    copyBackwardFrom before source dst src count = before.setSlice! dst (source.slice src (src+count)) := by
  have sliceLength : (source.slice src (src+count)).length = count := by rw [List.slice_length]; omega
  obtain ⟨copied,outside⟩ := copy_backward_from_effect before source dst src count sourceBound targetBound
  apply List.ext_getElem?
  intro index
  by_cases first : index < dst
  · rw [List.setSlice!_getElem?_prefix _ _ _ _ first]
    exact outside index (Or.inl first)
  · by_cases last : dst+count ≤ index
    · rw [List.setSlice!_getElem?_suffix _ _ _ _ (by omega)]
      exact outside index (Or.inr last)
    · rw [List.setSlice!_getElem?_middle _ _ _ _ (by omega),List.getElem?_slice _ _ _ _ (by omega)]
      have equal : dst+(index-dst)=index := by omega
      simpa only [equal] using copied (index-dst) (by omega)
end Itasca.Runtime.Spec.Segment

end

/-! ## TableCopy -/

section

/-!
Source semantics of table.copy, including reference typing, recursive runs and snapshot updates. Used to relate overlapping runtime copies to source reduction.
-/

/-! ## Table Copy Source -/

section

namespace Itasca.Runtime.Spec.Segment
open SpecExt

theorem table_copy_trap (s : store) (f : frame) (destination source count targetTable sourceTable : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32) (hn : count < 2^32) (ht : targetTable < 2^32) (hy : sourceTable < 2^32)
    (outside : (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS.length < source+count ∨
      (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS.length < destination+count) :
    StepH ⟨⟨s,f⟩,operands destination source count ++ [(.TABLE_COPY (.mk_uN targetTable) (.mk_uN sourceTable))]⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩ := by
  have input := init_config_wf s f destination source count (.TABLE_COPY (.mk_uN targetTable) (.mk_uN sourceTable)) hs hf (by omega) (by omega) hn (.admininstr_case_53 _ _ (index_wf _ ht) (index_wf _ hy))
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_make hs hf (by simp [Forall]; exact .admininstr_case_73))
  exact Step_read.table_copy_trap ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN destination)) (.mk_num__0 .I32 (.mk_uN source)) count (.mk_uN targetTable) (.mk_uN sourceTable)
    (by simp [proj_num__0]) (by simp [proj_num__0]) outside input .admininstr_case_73

theorem table_copy_zero (s : store) (f : frame) (destination source targetTable sourceTable : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32) (ht : targetTable < 2^32) (hy : sourceTable < 2^32)
    (inside : source ≤ (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS.length ∧ destination ≤ (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS.length) :
    StepH ⟨⟨s,f⟩,operands destination source 0 ++ [(.TABLE_COPY (.mk_uN targetTable) (.mk_uN sourceTable))]⟩ [] ⟨⟨s,f⟩,[]⟩ := by
  have input := init_config_wf s f destination source 0 (.TABLE_COPY (.mk_uN targetTable) (.mk_uN sourceTable)) hs hf hd hi (by decide) (.admininstr_case_53 _ _ (index_wf _ ht) (index_wf _ hy))
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_make hs hf (by simp [Forall]))
  exact Step_read.table_copy_zero ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN destination)) (.mk_num__0 .I32 (.mk_uN source)) 0 (.mk_uN targetTable) (.mk_uN sourceTable)
    (by simp [proj_num__0]) (by simp [proj_num__0]) (by simpa [proj_num__0,proj_uN_0] using inside) rfl input

theorem table_copy_forward_expand (s : store) (f : frame) (destination source count targetTable sourceTable : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination+1 < 2^32) (hi : source+1 < 2^32) (hn : count+1 < 2^32) (ht : targetTable < 2^32) (hy : sourceTable < 2^32)
    (inside : source+(count+1) ≤ (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS.length ∧ destination+(count+1) ≤ (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS.length)
    (direction : destination ≤ source) :
    StepH ⟨⟨s,f⟩,operands destination source (count+1) ++ [(.TABLE_COPY (.mk_uN targetTable) (.mk_uN sourceTable))]⟩ []
      ⟨⟨s,f⟩,[i32 destination,i32 source,.TABLE_GET (.mk_uN sourceTable),.TABLE_SET (.mk_uN targetTable)] ++
        (operands (destination+1) (source+1) count ++ [(.TABLE_COPY (.mk_uN targetTable) (.mk_uN sourceTable))])⟩ := by
  have input := init_config_wf s f destination source (count+1) (.TABLE_COPY (.mk_uN targetTable) (.mk_uN sourceTable)) hs hf (by omega) (by omega) hn (.admininstr_case_53 _ _ (index_wf _ ht) (index_wf _ hy))
  have output : wf_config ⟨⟨s,f⟩,[i32 destination,i32 source,.TABLE_GET (.mk_uN sourceTable),.TABLE_SET (.mk_uN targetTable)] ++
        (operands (destination+1) (source+1) count ++ [(.TABLE_COPY (.mk_uN targetTable) (.mk_uN sourceTable))])⟩ := by
    apply wf_config_make hs hf
    simp only [operands,List.cons_append,List.nil_append,Forall,List.mem_cons,List.not_mem_nil,
      false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨i32_wf _ (by omega),i32_wf _ (by omega),(.admininstr_case_48 _ (index_wf _ hy)),(.admininstr_case_49 _ (index_wf _ ht)),i32_wf _ (by omega),
      i32_wf _ (by omega),i32_wf _ (by omega),(.admininstr_case_53 _ _ (index_wf _ ht) (index_wf _ hy))⟩
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  have read := Step_read.table_copy_le ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN destination)) (.mk_num__0 .I32 (.mk_uN source))
    (count+1) (.mk_uN targetTable) (.mk_uN sourceTable)
    (by simp [proj_num__0]) (by simp [proj_num__0]) (Nat.succ_ne_zero count) inside direction input
    (i32_wf _ (by omega)) (i32_wf _ (by omega)) (.admininstr_case_48 _ (index_wf _ hy)) (.admininstr_case_49 _ (index_wf _ ht)) (by simpa [proj_num__0,proj_uN_0,i32] using i32_wf _ hd) (by simpa [proj_num__0,proj_uN_0,i32] using i32_wf _ hi)
    (by simpa [i32] using i32_wf count (by omega)) (.admininstr_case_53 _ _ (index_wf _ ht) (index_wf _ hy))
  simpa [operands,i32,proj_num__0,proj_uN_0] using read

theorem table_copy_backward_expand (s : store) (f : frame) (destination source count targetTable sourceTable : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32) (hn : count+1 < 2^32) (ht : targetTable < 2^32) (hy : sourceTable < 2^32)
    (inside : source+(count+1) ≤ (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS.length ∧ destination+(count+1) ≤ (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS.length)
    (tableBounds : (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS.length < 2^32 ∧ (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS.length < 2^32)
    (direction : source < destination) :
    StepH ⟨⟨s,f⟩,operands destination source (count+1) ++ [(.TABLE_COPY (.mk_uN targetTable) (.mk_uN sourceTable))]⟩ []
      ⟨⟨s,f⟩,[i32 (destination+count),i32 (source+count),.TABLE_GET (.mk_uN sourceTable),.TABLE_SET (.mk_uN targetTable)] ++
        (operands destination source count ++ [(.TABLE_COPY (.mk_uN targetTable) (.mk_uN sourceTable))])⟩ := by
  have endEq (n : Nat) : ((n : Int)+(count+1)).toNat-1 = n+count := by omega
  have hd' : destination+count < 2^32 := by omega
  have hi' : source+count < 2^32 := by omega
  have input := init_config_wf s f destination source (count+1) (.TABLE_COPY (.mk_uN targetTable) (.mk_uN sourceTable)) hs hf (by omega) (by omega) hn (.admininstr_case_53 _ _ (index_wf _ ht) (index_wf _ hy))
  have output : wf_config ⟨⟨s,f⟩,[i32 (destination+count),i32 (source+count),.TABLE_GET (.mk_uN sourceTable),.TABLE_SET (.mk_uN targetTable)] ++
        (operands destination source count ++ [(.TABLE_COPY (.mk_uN targetTable) (.mk_uN sourceTable))])⟩ := by
    apply wf_config_make hs hf
    simp only [operands,List.cons_append,List.nil_append,Forall,List.mem_cons,List.not_mem_nil,
      false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨i32_wf _ hd',i32_wf _ hi',(.admininstr_case_48 _ (index_wf _ hy)),(.admininstr_case_49 _ (index_wf _ ht)),i32_wf _ (by omega),i32_wf _ (by omega),
      i32_wf _ (by omega),(.admininstr_case_53 _ _ (index_wf _ ht) (index_wf _ hy))⟩
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  have read := Step_read.table_copy_gt ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN destination)) (.mk_num__0 .I32 (.mk_uN source))
    (count+1) (.mk_uN targetTable) (.mk_uN sourceTable) (by simp [proj_num__0]) (by simp [proj_num__0])
    direction (Nat.succ_ne_zero count) inside input
    (by simpa [proj_num__0,proj_uN_0,i32,endEq] using i32_wf _ hd')
    (by simpa [proj_num__0,proj_uN_0,i32,endEq] using i32_wf _ hi')
    (.admininstr_case_48 _ (index_wf _ hy)) (.admininstr_case_49 _ (index_wf _ ht)) (i32_wf _ (by omega)) (i32_wf _ (by omega))
    (by simpa [i32] using i32_wf count (by omega)) (.admininstr_case_53 _ _ (index_wf _ ht) (index_wf _ hy))
  simpa [operands,i32,proj_num__0,proj_uN_0,proj_num__0,proj_uN_0,endEq] using read
end Itasca.Runtime.Spec.Segment

end

/-! ## Table Reference Copy -/

section

namespace Itasca.Runtime.Spec.Segment
open SpecExt

theorem table_copy_reference_steps (s : store) (f : frame) (destination source targetTable sourceTable : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32)
    (ht : targetTable < 2^32) (hy : sourceTable < 2^32)
    (mapped : targetTable < f.MODULE.TABLES.length)
    (sourceInside : source < (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS.length)
    (targetInside : destination < (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS.length) :
    StepsH ⟨⟨s,f⟩,[i32 destination,i32 source,.TABLE_GET (.mk_uN sourceTable),.TABLE_SET (.mk_uN targetTable)]⟩ []
      ⟨⟨tableWrite s f targetTable destination (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS[source]!,f⟩,[]⟩ := by
  have loaded := step_h_instrs (table_get_step s f sourceTable source hs hf hy hi)
    [.CONST .I32 (.mk_num__0 .I32 (.mk_uN destination))] [.TABLE_SET (.mk_uN targetTable)]
    (by simpa [Forall] using wf_val.val_case_0 _ _ ((by cases i32_wf destination hd; assumption)))
    (by simpa [Forall] using wf_admininstr.admininstr_case_49 _ (index_wf _ ht))
  have stored := table_write_step s f targetTable destination (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS[source]! hs hf hd ht mapped targetInside
  exact steps_h_trans (steps_h_single (by simpa [instrContext,vals,admininstr_val,i32,sourceInside] using loaded)) (steps_h_single stored)

theorem table_write_other_length (s : store) (f : frame) (index other position : Nat) (value : ref)
    (address : f.MODULE.TABLES[other]! < s.TABLES.length) :
    (fun_table ⟨tableWrite s f index position value,f⟩ (.mk_uN other)).REFS.length =
      (fun_table ⟨s,f⟩ (.mk_uN other)).REFS.length := by
  simp only [fun_table,tableWrite,proj_uN_0]
  generalize same : f.MODULE.TABLES[index]! = a
  generalize otherEq : f.MODULE.TABLES[other]! = b at address ⊢
  by_cases equal : a=b
  · subst a
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem address,equal]
  · simp [List.getElem!_eq_getElem?_getD,List.getElem?_modify,equal]
end Itasca.Runtime.Spec.Segment

end

/-! ## Table Copy Run -/

section

namespace Itasca.Runtime.Spec.Segment
open SpecExt

def tableCopyForward (s : store) (f : frame) (targetTable sourceTable destination source : Nat) : Nat → store
  | 0 => s
  | count+1 => tableCopyForward
      (tableWrite s f targetTable destination (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS[source]!) f targetTable sourceTable
      (destination+1) (source+1) count

def tableCopyBackward (s : store) (f : frame) (targetTable sourceTable destination source : Nat) : Nat → store
  | 0 => s
  | count+1 => tableCopyBackward
      (tableWrite s f targetTable (destination+count) (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS[source+count]!) f targetTable sourceTable destination source count

theorem table_copy_forward_steps (s : store) (f : frame) (destination source count targetTable sourceTable : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32) (hn : count < 2^32) (ht : targetTable < 2^32) (hy : sourceTable < 2^32)
    (mapped : targetTable < f.MODULE.TABLES.length) (address : f.MODULE.TABLES[targetTable]! < s.TABLES.length)
    (sourceAddress : f.MODULE.TABLES[sourceTable]! < s.TABLES.length)
    (tableBounds : (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS.length < 2^32 ∧ (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS.length < 2^32)
    (inside : source+count ≤ (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS.length ∧ destination+count ≤ (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS.length)
    (direction : destination ≤ source ∨ count=0) :
    StepsH ⟨⟨s,f⟩,operands destination source count ++ [(.TABLE_COPY (.mk_uN targetTable) (.mk_uN sourceTable))]⟩ []
      ⟨⟨tableCopyForward s f targetTable sourceTable destination source count,f⟩,[]⟩ := by
  induction count generalizing s destination source with
  | zero => exact steps_h_single (table_copy_zero s f destination source targetTable sourceTable hs hf hd hi ht hy (by simpa using inside))
  | succ count ih =>
    have order : destination ≤ source := by omega
    have srcInside : source < (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS.length := by omega
    let value := (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS[source]!
    let fresh := tableWrite s f targetTable destination value
    have hw := table_write_wf s f targetTable destination value hs
    have lengthEq := table_write_table_length s f targetTable destination value address
    have sourceLengthEq := table_write_other_length s f targetTable sourceTable destination value sourceAddress
    have afterWf := (wf_config_parts (init_config_wf fresh f (destination+1) (source+1) count _ hw hf
      (by omega) (by omega) (by omega) (.admininstr_case_53 _ _ (index_wf _ ht) (index_wf _ hy)))).2
    have first := table_copy_forward_expand s f destination source count targetTable sourceTable hs hf (by omega) (by omega) hn ht hy inside order
    have second := steps_h_instrs (table_copy_reference_steps s f destination source targetTable sourceTable hs hf hd hi ht hy mapped srcInside (by omega)) []
      (operands (destination+1) (source+1) count ++ [(.TABLE_COPY (.mk_uN targetTable) (.mk_uN sourceTable))]) (by simp [Forall]) afterWf
    have rest := ih fresh (destination+1) (source+1) hw (by omega) (by omega) (by omega)
      (by simpa [fresh,tableWrite] using address) (by simpa [fresh,tableWrite] using sourceAddress)
      (by simpa only [fresh,lengthEq,sourceLengthEq] using tableBounds)
      (by rw [show (fun_table ⟨fresh,f⟩ (.mk_uN sourceTable)).REFS.length = (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS.length from sourceLengthEq,
              show (fun_table ⟨fresh,f⟩ (.mk_uN targetTable)).REFS.length = (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS.length from lengthEq]; omega)
      (Or.inl (by omega))
    have combined := steps_h_trans (steps_h_single first) (steps_h_trans second rest)
    simpa only [instrContext,vals,List.map_nil,List.nil_append,List.append_nil,tableCopyForward,value,fresh] using combined

theorem table_copy_backward_steps (s : store) (f : frame) (destination source count targetTable sourceTable : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32) (hn : count < 2^32) (ht : targetTable < 2^32) (hy : sourceTable < 2^32)
    (mapped : targetTable < f.MODULE.TABLES.length) (address : f.MODULE.TABLES[targetTable]! < s.TABLES.length)
    (sourceAddress : f.MODULE.TABLES[sourceTable]! < s.TABLES.length)
    (tableBounds : (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS.length < 2^32 ∧ (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS.length < 2^32)
    (inside : source+count ≤ (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS.length ∧ destination+count ≤ (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS.length)
    (direction : source < destination ∨ count=0) :
    StepsH ⟨⟨s,f⟩,operands destination source count ++ [(.TABLE_COPY (.mk_uN targetTable) (.mk_uN sourceTable))]⟩ []
      ⟨⟨tableCopyBackward s f targetTable sourceTable destination source count,f⟩,[]⟩ := by
  induction count generalizing s with
  | zero => exact steps_h_single (table_copy_zero s f destination source targetTable sourceTable hs hf hd hi ht hy (by simpa using inside))
  | succ count ih =>
    have order : source < destination := by omega
    have srcInside : source+count < (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS.length := by omega
    let value := (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS[source+count]!
    let fresh := tableWrite s f targetTable (destination+count) value
    have hw := table_write_wf s f targetTable (destination+count) value hs
    have lengthEq := table_write_table_length s f targetTable (destination+count) value address
    have sourceLengthEq := table_write_other_length s f targetTable sourceTable (destination+count) value sourceAddress
    have afterWf := (wf_config_parts (init_config_wf fresh f destination source count _ hw hf hd hi
      (by omega) (.admininstr_case_53 _ _ (index_wf _ ht) (index_wf _ hy)))).2
    have first := table_copy_backward_expand s f destination source count targetTable sourceTable hs hf hd hi hn ht hy inside tableBounds order
    have second := steps_h_instrs (table_copy_reference_steps s f (destination+count) (source+count) targetTable sourceTable hs hf (by omega) (by omega) ht hy mapped srcInside (by omega)) [] (operands destination source count ++ [(.TABLE_COPY (.mk_uN targetTable) (.mk_uN sourceTable))]) (by simp [Forall]) afterWf
    have rest := ih fresh hw (by omega) (by simpa [fresh,tableWrite] using address)
      (by simpa [fresh,tableWrite] using sourceAddress)
      (by simpa only [fresh,lengthEq,sourceLengthEq] using tableBounds)
      (by rw [show (fun_table ⟨fresh,f⟩ (.mk_uN sourceTable)).REFS.length = (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS.length from sourceLengthEq,
              show (fun_table ⟨fresh,f⟩ (.mk_uN targetTable)).REFS.length = (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS.length from lengthEq]; omega)
      (Or.inl order)
    have combined := steps_h_trans (steps_h_single first) (steps_h_trans second rest)
    simpa only [instrContext,vals,List.map_nil,List.nil_append,List.append_nil,tableCopyBackward,value,fresh] using combined
end Itasca.Runtime.Spec.Segment

end

/-! ## Table Copy Algebra -/

section

namespace Itasca.Runtime.Spec.Segment
open SpecExt

def withRefs (table : tableinst) (refs : List ref) : tableinst := {table with REFS := refs}

theorem table_copy_forward_same_words (s : store) (f : frame) (targetTable sourceTable destination source count : Nat)
    (address : f.MODULE.TABLES[targetTable]! < s.TABLES.length)
    (sourceAddress : f.MODULE.TABLES[sourceTable]! < s.TABLES.length)
    (aliasEq : f.MODULE.TABLES[targetTable]! = f.MODULE.TABLES[sourceTable]!) :
    tableCopyForward s f targetTable sourceTable destination source count =
      {s with TABLES := s.TABLES.set (f.MODULE.TABLES[targetTable]!) (withRefs (s.TABLES[f.MODULE.TABLES[targetTable]!]!) (copyForwardPlain (s.TABLES[f.MODULE.TABLES[targetTable]!]!).REFS destination source count))} := by
  induction count generalizing s destination source with
  | zero =>
    simp only [tableCopyForward,copyForwardPlain]
    have identity : withRefs (s.TABLES[f.MODULE.TABLES[targetTable]!]!) (s.TABLES[f.MODULE.TABLES[targetTable]!]!).REFS = s.TABLES[f.MODULE.TABLES[targetTable]!]! := by cases s.TABLES[f.MODULE.TABLES[targetTable]!]!; rfl
    rw [identity]
    simp only [getElem!_pos s.TABLES (f.MODULE.TABLES[targetTable]!) address,List.set_getElem_self]
  | succ count ih =>
    rw [tableCopyForward,ih (tableWrite s f targetTable destination (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS[source]!) (destination+1) (source+1)
      (by simpa [tableWrite] using address) (by simpa [tableWrite] using sourceAddress)]
    simp only [tableWrite,fun_table,proj_uN_0,List.modify_eq_set,copyForwardPlain,withRefs]
    rw [aliasEq] at address ⊢
    generalize same : f.MODULE.TABLES[sourceTable]! = a at address sourceAddress ⊢
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem address,List.set_set,address]

theorem table_copy_forward_distinct_words (s : store) (f : frame) (targetTable sourceTable destination source count : Nat)
    (address : f.MODULE.TABLES[targetTable]! < s.TABLES.length)
    (sourceAddress : f.MODULE.TABLES[sourceTable]! < s.TABLES.length)
    (aliasEq : f.MODULE.TABLES[targetTable]! ≠ f.MODULE.TABLES[sourceTable]!) :
    tableCopyForward s f targetTable sourceTable destination source count =
      {s with TABLES := s.TABLES.set (f.MODULE.TABLES[targetTable]!) (withRefs (s.TABLES[f.MODULE.TABLES[targetTable]!]!) (copyInto (s.TABLES[f.MODULE.TABLES[targetTable]!]!).REFS (s.TABLES[f.MODULE.TABLES[sourceTable]!]!).REFS destination source count))} := by
  induction count generalizing s destination source with
  | zero =>
    simp only [tableCopyForward,copyInto]
    have identity : withRefs (s.TABLES[f.MODULE.TABLES[targetTable]!]!) (s.TABLES[f.MODULE.TABLES[targetTable]!]!).REFS = s.TABLES[f.MODULE.TABLES[targetTable]!]! := by cases s.TABLES[f.MODULE.TABLES[targetTable]!]!; rfl
    rw [identity]
    simp only [getElem!_pos s.TABLES (f.MODULE.TABLES[targetTable]!) address,List.set_getElem_self]
  | succ count ih =>
    rw [tableCopyForward,ih (tableWrite s f targetTable destination (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS[source]!) (destination+1) (source+1)
      (by simpa [tableWrite] using address) (by simpa [tableWrite] using sourceAddress)]
    simp only [tableWrite,fun_table,proj_uN_0,List.modify_eq_set,copyInto,withRefs]
    generalize targetEq : f.MODULE.TABLES[targetTable]! = a at address aliasEq ⊢
    generalize sourceEq : f.MODULE.TABLES[sourceTable]! = b at sourceAddress aliasEq ⊢
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem address,List.getElem?_eq_getElem sourceAddress,List.set_set,address,aliasEq]

theorem table_copy_backward_same_words (s : store) (f : frame) (targetTable sourceTable destination source count : Nat)
    (address : f.MODULE.TABLES[targetTable]! < s.TABLES.length)
    (sourceAddress : f.MODULE.TABLES[sourceTable]! < s.TABLES.length)
    (aliasEq : f.MODULE.TABLES[targetTable]! = f.MODULE.TABLES[sourceTable]!) :
    tableCopyBackward s f targetTable sourceTable destination source count =
      {s with TABLES := s.TABLES.set (f.MODULE.TABLES[targetTable]!) (withRefs (s.TABLES[f.MODULE.TABLES[targetTable]!]!) (copyBackward (s.TABLES[f.MODULE.TABLES[targetTable]!]!).REFS destination source count))} := by
  induction count generalizing s with
  | zero =>
    simp only [tableCopyBackward,copyBackward]
    have identity : withRefs (s.TABLES[f.MODULE.TABLES[targetTable]!]!) (s.TABLES[f.MODULE.TABLES[targetTable]!]!).REFS = s.TABLES[f.MODULE.TABLES[targetTable]!]! := by cases s.TABLES[f.MODULE.TABLES[targetTable]!]!; rfl
    rw [identity]
    simp only [getElem!_pos s.TABLES (f.MODULE.TABLES[targetTable]!) address,List.set_getElem_self]
  | succ count ih =>
    rw [tableCopyBackward,ih (tableWrite s f targetTable (destination+count) (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS[(source+count)]!)
      (by simpa [tableWrite] using address) (by simpa [tableWrite] using sourceAddress)]
    simp only [tableWrite,fun_table,proj_uN_0,List.modify_eq_set,copyBackward,withRefs]
    rw [aliasEq] at address ⊢
    generalize same : f.MODULE.TABLES[sourceTable]! = a at address sourceAddress ⊢
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem address,List.set_set,address]

theorem table_copy_backward_distinct_words (s : store) (f : frame) (targetTable sourceTable destination source count : Nat)
    (address : f.MODULE.TABLES[targetTable]! < s.TABLES.length)
    (sourceAddress : f.MODULE.TABLES[sourceTable]! < s.TABLES.length)
    (aliasEq : f.MODULE.TABLES[targetTable]! ≠ f.MODULE.TABLES[sourceTable]!) :
    tableCopyBackward s f targetTable sourceTable destination source count =
      {s with TABLES := s.TABLES.set (f.MODULE.TABLES[targetTable]!) (withRefs (s.TABLES[f.MODULE.TABLES[targetTable]!]!) (copyBackwardFrom (s.TABLES[f.MODULE.TABLES[targetTable]!]!).REFS (s.TABLES[f.MODULE.TABLES[sourceTable]!]!).REFS destination source count))} := by
  induction count generalizing s with
  | zero =>
    simp only [tableCopyBackward,copyBackwardFrom]
    have identity : withRefs (s.TABLES[f.MODULE.TABLES[targetTable]!]!) (s.TABLES[f.MODULE.TABLES[targetTable]!]!).REFS = s.TABLES[f.MODULE.TABLES[targetTable]!]! := by cases s.TABLES[f.MODULE.TABLES[targetTable]!]!; rfl
    rw [identity]
    simp only [getElem!_pos s.TABLES (f.MODULE.TABLES[targetTable]!) address,List.set_getElem_self]
  | succ count ih =>
    rw [tableCopyBackward,ih (tableWrite s f targetTable (destination+count) (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS[(source+count)]!)
      (by simpa [tableWrite] using address) (by simpa [tableWrite] using sourceAddress)]
    simp only [tableWrite,fun_table,proj_uN_0,List.modify_eq_set,copyBackwardFrom,withRefs]
    generalize targetEq : f.MODULE.TABLES[targetTable]! = a at address aliasEq ⊢
    generalize sourceEq : f.MODULE.TABLES[sourceTable]! = b at sourceAddress aliasEq ⊢
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem address,List.getElem?_eq_getElem sourceAddress,List.set_set,address,aliasEq]

end Itasca.Runtime.Spec.Segment

end

/-! ## Table Copy Snapshot -/

section

namespace Itasca.Runtime.Spec.Segment
open SpecExt

def tableCopy (s : store) (f : frame) (targetTable sourceTable destination source count : Nat) : store :=
  {s with TABLES := s.TABLES.set (f.MODULE.TABLES[targetTable]!) (withRefs (s.TABLES[f.MODULE.TABLES[targetTable]!]!) ((s.TABLES[f.MODULE.TABLES[targetTable]!]!).REFS.setSlice! destination ((s.TABLES[f.MODULE.TABLES[sourceTable]!]!).REFS.slice source (source+count))))}

theorem table_copy_steps (s : store) (f : frame) (destination source count targetTable sourceTable : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32) (hn : count < 2^32)
    (ht : targetTable < 2^32) (hy : sourceTable < 2^32)
    (mapped : targetTable < f.MODULE.TABLES.length) (address : f.MODULE.TABLES[targetTable]! < s.TABLES.length)
    (sourceAddress : f.MODULE.TABLES[sourceTable]! < s.TABLES.length)
    (tableBounds : (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS.length < 2^32 ∧ (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS.length < 2^32)
    (inside : source+count ≤ (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS.length ∧ destination+count ≤ (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS.length) :
    StepsH ⟨⟨s,f⟩,operands destination source count ++ [.TABLE_COPY (.mk_uN targetTable) (.mk_uN sourceTable)]⟩ []
      ⟨⟨tableCopy s f targetTable sourceTable destination source count,f⟩,[]⟩ := by
  by_cases direction : destination ≤ source
  · have run := table_copy_forward_steps s f destination source count targetTable sourceTable hs hf hd hi hn ht hy mapped address sourceAddress tableBounds inside (Or.inl direction)
    by_cases same : f.MODULE.TABLES[targetTable]! = f.MODULE.TABLES[sourceTable]!
    · rw [table_copy_forward_same_words _ _ _ _ _ _ _ address sourceAddress same] at run
      have sameSource : (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS = (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS := by simp only [fun_table,proj_uN_0,same]
      have snapshot := copy_forward_plain_snapshot (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS
        (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS destination source 0 count count
        (CopyPrefix.initial _ _ _) (by omega) direction (by simpa only [sameSource] using inside.1) inside.2
      simp only [Nat.add_zero,fun_table,proj_uN_0] at snapshot
      rw [snapshot] at run
      simpa only [tableCopy,same] using run
    · simp only [fun_table,proj_uN_0] at inside
      rw [table_copy_forward_distinct_words _ _ _ _ _ _ _ address sourceAddress same,
        copy_into_eq_set_slice _ _ _ _ _ inside.1 inside.2] at run
      exact run
  · have run := table_copy_backward_steps s f destination source count targetTable sourceTable hs hf hd hi hn ht hy mapped address sourceAddress tableBounds inside (Or.inl (by omega))
    by_cases same : f.MODULE.TABLES[targetTable]! = f.MODULE.TABLES[sourceTable]!
    · rw [table_copy_backward_same_words _ _ _ _ _ _ _ address sourceAddress same] at run
      have sameSource : (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS = (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS := by simp only [fun_table,proj_uN_0,same]
      have snapshot := copy_backward_snapshot (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS
        (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS destination source count count
        (CopySuffix.initial _ _ _ _) (by omega) (by omega) (by simpa only [sameSource] using inside.1) inside.2
      simp only [fun_table,proj_uN_0] at snapshot
      rw [snapshot] at run
      simpa only [tableCopy,same] using run
    · simp only [fun_table,proj_uN_0] at inside
      rw [table_copy_backward_distinct_words _ _ _ _ _ _ _ address sourceAddress same,
        copy_backward_from_snapshot _ _ _ _ _ inside.1 inside.2] at run
      exact run
end Itasca.Runtime.Spec.Segment

end

end

/-! ## TableGrowth -/

section

namespace Itasca.Runtime.Spec
open SpecExt

/-- A refused table growth returns the WebAssembly unsigned failure sentinel. -/
theorem table_grow_fail_step (s : store) (f : frame) (index delta : Nat) (value : ref)
    (hs : wf_store s) (hf : wf_frame f) (hx : index < 2^32) (hd : delta < 2^32) :
    StepH ⟨⟨s,f⟩,[admininstr_ref value,Segment.i32 delta,.TABLE_GROW (.mk_uN index)]⟩ []
      ⟨⟨s,f⟩,[Segment.i32 (2^32-1)]⟩ := by
  apply StepH.step
  apply Step.table_grow_fail
  · simpa using (fun_inv_signed_.fun_inv_signed__case_1 32 (-1) (by decide))
  · apply wf_config_make hs hf
    simp only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨Segment.ref_wf _,Segment.i32_wf _ hd,.admininstr_case_51 _ (Segment.index_wf _ hx)⟩
  · apply wf_config_make hs hf
    simpa [Forall,Segment.i32] using Segment.i32_wf 4294967295 (by decide)

/-- A successful source table growth replaces the complete table instance and
returns its original length. -/
theorem table_grow_success_step (s : store) (f : frame) (index delta : Nat) (value : ref)
    (next : tableinst)
    (hs : wf_store s) (hf : wf_frame f) (hx : index < 2^32) (hd : delta < 2^32)
    (mapped : index < f.MODULE.TABLES.length)
    (bounded : (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length < 2^32)
    (grown : fun_growtable (fun_table ⟨s,f⟩ (.mk_uN index)) delta value (some next))
    (fresh : wf_store {s with TABLES := s.TABLES.modify f.MODULE.TABLES[index]! (fun _ => next)}) :
    StepH ⟨⟨s,f⟩,[admininstr_ref value,Segment.i32 delta,.TABLE_GROW (.mk_uN index)]⟩ []
      ⟨⟨{s with TABLES := s.TABLES.modify f.MODULE.TABLES[index]! (fun _ => next)},f⟩,
        [Segment.i32 (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length]⟩ := by
  apply StepH.step
  apply Step.table_grow_succeed _ _ _ _ next (some next)
  · exact grown
  · exact fun_with_tableinst.fun_with_tableinst_case_0 s f (.mk_uN index) next mapped (.state_case_0 _ _ fresh hf)
  · simp
  · rfl
  · apply wf_config_make hs hf
    simp only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨Segment.ref_wf _,Segment.i32_wf _ hd,.admininstr_case_51 _ (Segment.index_wf _ hx)⟩
  · apply wf_config_make fresh hf
    simpa [Forall,Segment.i32] using Segment.i32_wf _ bounded
end Itasca.Runtime.Spec

end

/-! ## MemoryGrowth -/

section

namespace Itasca.Runtime.Spec
open SpecExt

theorem memory_grow_fail_step (s : store) (f : frame) (delta : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : delta < 2^32) :
    StepH ⟨⟨s,f⟩,[Segment.i32 delta,.MEMORY_GROW]⟩ []
      ⟨⟨s,f⟩,[Segment.i32 (2^32-1)]⟩ := by
  apply StepH.step
  apply Step.memory_grow_fail
  · simpa using (fun_inv_signed_.fun_inv_signed__case_1 32 (-1) (by decide))
  · apply wf_config_make hs hf
    simp only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨Segment.i32_wf _ hd,.admininstr_case_63⟩
  · apply wf_config_make hs hf
    simpa [Forall,Segment.i32] using Segment.i32_wf 4294967295 (by decide)

theorem memory_pages_nat (length : Nat) :
    rat_to_nat ((length : Rat) / (64 * Ki : Rat)) = length / 65536 := by
  simp only [Ki]
  norm_num
  exact truncz_nat_div length 65536

theorem memory_grow_success_step (s : store) (f : frame) (delta : Nat) (next : meminst)
    (hs : wf_store s) (hf : wf_frame f) (hd : delta < 2^32)
    (mapped : 0 < f.MODULE.MEMS.length)
    (bounded : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length / 65536 < 2^32)
    (grown : fun_growmemory (fun_mem ⟨s,f⟩ (.mk_uN 0)) delta (some next))
    (fresh : wf_store {s with MEMS := s.MEMS.modify f.MODULE.MEMS[0]! (fun _ => next)}) :
    StepH ⟨⟨s,f⟩,[Segment.i32 delta,.MEMORY_GROW]⟩ []
      ⟨⟨{s with MEMS := s.MEMS.modify f.MODULE.MEMS[0]! (fun _ => next)},f⟩,
        [Segment.i32 ((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length / 65536)]⟩ := by
  have pages := memory_pages_nat (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length
  rw [← pages]
  apply StepH.step
  apply Step.memory_grow_succeed _ _ next (some next)
  · exact grown
  · exact fun_with_meminst.fun_with_meminst_case_0 s f (.mk_uN 0) next mapped (.state_case_0 _ _ fresh hf)
  · simp
  · rfl
  · apply wf_config_make hs hf
    simp only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨Segment.i32_wf _ hd,.admininstr_case_63⟩
  · apply wf_config_make fresh hf
    simpa only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp,pages,Segment.i32]
      using Segment.i32_wf _ bounded
  · exact Segment.index_wf 0 (by decide)
end Itasca.Runtime.Spec

end
