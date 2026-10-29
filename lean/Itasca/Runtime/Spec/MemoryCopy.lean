import Itasca.Runtime.Spec.MemoryByteCopy
import Itasca.Runtime.Spec.CopySnapshot

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
  | zero => exact stepsH_single (memory_copy_zero s f destination source hs hf hd hi (by simpa using inside))
  | succ count ih =>
    have order : destination ≤ source := by omega
    have bytesWf := memory_bytes_wf s f hs address
    have srcInside : source < (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length := by omega
    let value := (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES[source]!
    have valueWf : wf_byte value := bytesWf _ (by simp [value,srcInside])
    let fresh := memoryWrite s f destination value
    have hw := memoryWrite_wf s f destination value hs valueWf
    have lengthEq := memoryWrite_mem_length s f destination value address
    have afterWf := (wf_config_parts (init_config_wf fresh f (next32 destination) (next32 source) count _ hw hf
      (next32_bound _) (next32_bound _) (by omega) .admininstr_case_65)).2
    have first := memory_copy_forward_expand s f destination source count hs hf hd hi hn inside order
    have second := stepsH_instrs (memory_copy_byte_steps s f destination source hs hf hd hi mapped bytesWf srcInside (by have := inside.2; omega)) []
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
    have combined := stepsH_trans (stepsH_single first) (stepsH_trans second rest)
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
  | zero => exact stepsH_single (memory_copy_zero s f destination source hs hf hd hi (by simpa using inside))
  | succ count ih =>
    have order : source < destination := by omega
    have bytesWf := memory_bytes_wf s f hs address
    have srcInside : source+count < (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length := by omega
    let value := (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES[source+count]!
    have valueWf : wf_byte value := bytesWf _ (by simp [value,srcInside])
    let fresh := memoryWrite s f (destination+count) value
    have hw := memoryWrite_wf s f (destination+count) value hs valueWf
    have lengthEq := memoryWrite_mem_length s f (destination+count) value address
    have afterWf := (wf_config_parts (init_config_wf fresh f destination source count _ hw hf hd hi
      (by omega) .admininstr_case_65)).2
    have first := memory_copy_backward_expand s f destination source count hs hf hd hi hn inside memoryBound order
    have second := stepsH_instrs (memory_copy_byte_steps s f (destination+count) (source+count) hs hf (by omega) (by omega)
      mapped bytesWf srcInside (by have := inside.2; omega)) [] (operands destination source count ++ [.MEMORY_COPY]) (by simp [Forall]) afterWf
    have rest := ih fresh hw (by omega) (by simpa [fresh,memoryWrite] using address)
      (by simpa only [fresh,lengthEq] using memoryBound)
      (by rw [show (fun_mem ⟨fresh,f⟩ (.mk_uN 0)).BYTES.length = (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length from lengthEq]; omega)
      (Or.inl order)
    have combined := stepsH_trans (stepsH_single first) (stepsH_trans second rest)
    simpa only [instrContext,vals,List.map_nil,List.nil_append,List.append_nil,memoryCopyBackward,value,fresh] using combined
end Itasca.Runtime.Spec.Segment

end

/-! ## Memory Copy Algebra -/

section

namespace Itasca.Runtime.Spec.Segment
open SpecExt

def withBytes (memory : meminst) (bytes : List byte) : meminst := {memory with BYTES := bytes}

theorem memoryCopyForward_words (s : store) (f : frame) (destination source count : Nat)
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

theorem memoryCopyBackward_words (s : store) (f : frame) (destination source count : Nat)
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
    have snapshot := copyForward_snapshot (s.MEMS[f.MODULE.MEMS[0]!]!).BYTES
      (s.MEMS[f.MODULE.MEMS[0]!]!).BYTES destination source 0 count count
      (CopyPrefix.initial _ _ _) (by omega) direction inside.1 inside.2 memoryBound
    simp only [Nat.add_zero] at snapshot
    rw [memoryCopyForward_words _ _ _ _ _ address,snapshot] at run
    exact run
  · have run := memory_copy_backward_steps s f destination source count hs hf hd hi hn mapped address memoryBound inside (Or.inl (by omega))
    have snapshot := copyBackward_snapshot (s.MEMS[f.MODULE.MEMS[0]!]!).BYTES
      (s.MEMS[f.MODULE.MEMS[0]!]!).BYTES destination source count count
      (CopySuffix.initial _ _ _ _) (by omega) (by omega) inside.1 inside.2
    rw [memoryCopyBackward_words _ _ _ _ _ address,snapshot] at run
    exact run
end Itasca.Runtime.Spec.Segment

end
