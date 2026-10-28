import Itasca.Runtime.Spec.MemoryCopySource
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
