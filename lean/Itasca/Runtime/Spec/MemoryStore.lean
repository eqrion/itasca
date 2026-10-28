import Itasca.Runtime.Spec.ByteEncoding
import Itasca.Runtime.Spec.TableInitSource
import Itasca.Runtime.Spec.SegmentCopySlice

namespace Itasca.Runtime.Spec
open SpecExt

def memoryPayloadWrite (s : store) (f : frame) (start : Nat) (payload : List byte) : store :=
  {s with MEMS := s.MEMS.modify f.MODULE.MEMS[0]! (fun memory =>
    {memory with BYTES := splice memory.BYTES payload start})}

theorem splice_setSlice {T : Type} (bytes payload : List T) (start : Nat)
    (inside : start + payload.length ≤ bytes.length) :
    splice bytes payload start = bytes.setSlice! start payload := by
  have first : Nat.min start bytes.length = start := Nat.min_eq_left (by omega)
  simp only [splice,first,List.setSlice!]

theorem memoryPayloadWrite_wf (s : store) (f : frame) (start : Nat) (payload : List byte)
    (storeWf : wf_store s) (payloadWf : Forall wf_byte payload) :
    wf_store (memoryPayloadWrite s f start payload) := by
  cases s with | MKstore funcs globals tables memories elements datas =>
  cases storeWf with | store_case_ _ _ _ _ _ _ hf hg ht hm hd =>
  apply wf_store.store_case_ _ _ _ _ _ _ hf hg ht _ hd
  apply Segment.forall_modify _ _ _ _ hm
  intro memory valid
  cases memory with | MKmeminst ty bytes =>
  cases valid with | meminst_case_ _ _ typeWf bytesWf =>
  constructor
  · exact typeWf
  · unfold splice
    intro byte member
    rcases List.mem_append.mp member with initial | final
    · rcases List.mem_append.mp initial with original | fresh
      · exact bytesWf byte (List.mem_of_mem_take original)
      · exact payloadWf byte (List.mem_of_mem_take fresh)
    · exact bytesWf byte (List.mem_of_mem_drop final)

theorem integerBytes_wf (count value : Nat) :
    Forall wf_byte (Builtins.integerBytes count value) := by
  induction count generalizing value with
  | zero => simp [Builtins.integerBytes,Forall]
  | succ count ih =>
    intro byte member
    simp only [Builtins.integerBytes,List.mem_cons] at member
    rcases member with rfl | member
    · constructor
      have bound := Nat.mod_lt value (by decide : 0 < 256)
      omega
    · exact ih (value/256) byte member

theorem integerBytes_mod (count value : Nat) :
    Builtins.integerBytes count (value % 256^count) = Builtins.integerBytes count value := by
  have roundtrip := integerBytes_ofBytes (Builtins.integerBytes count value) (integerBytes_wf count value)
  simpa only [Builtins.integerBytes_length,Builtins.integerOfBytes_integerBytes] using roundtrip

theorem numericBytes_payload_wf (ty : numtype) (value : num_) : Forall wf_byte (nbytes_ ty value) := by
  cases ty <;> cases value <;> simp only [nbytes_,ibytes_,fbytes_] <;>
    first | exact integerBytes_wf _ _ | simp [Forall]

private theorem numeric_size_present (ty : numtype) : size (valtype_numtype ty) ≠ none := by
  cases ty <;> decide

private theorem numeric_byte_count (ty : numtype) :
    rat_to_nat ((Option.get! (size (valtype_numtype ty)) : Rat) / 8) = scalarNumBytes ty := by
  cases ty <;> norm_num [size,valtype_numtype,rat_to_nat,scalarNumBytes] <;> rfl

/-- Full-width numeric stores perform precisely the generated payload update or
bounds trap. The output store's well-formedness is derived from the input. -/
theorem numeric_store_step (s : store) (f : frame) (ty : numtype) (argument : memarg) (address : Nat) (value : num_)
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.STORE ty none argument)) (valueWf : wf_num_ ty value)
    (mapped : 0 < f.MODULE.MEMS.length) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,.CONST ty value,.STORE ty none argument]⟩ []
      (if address + proj_uN_0 argument.OFFSET + scalarNumBytes ty ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length then
        ⟨⟨memoryPayloadWrite s f (address + proj_uN_0 argument.OFFSET) (nbytes_ ty value),f⟩,[]⟩
      else ⟨⟨s,f⟩,[.TRAP]⟩) := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr [Segment.i32 address,.CONST ty value,.STORE ty none argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact .admininstr_case_13 _ _ valueWf
    · exact operationWf)
  split
  · rename_i inside
    have updatedWf := memoryPayloadWrite_wf s f (address+proj_uN_0 argument.OFFSET) (nbytes_ ty value)
      storeWf (numericBytes_payload_wf ty value)
    apply StepH.step
    apply Step.store_num_val _ _ _ _ _ (nbytes_ ty value)
    · simp [proj_num__0]
    · exact numeric_size_present ty
    · exact .fun_with_mem_case_0 s f (.mk_uN 0) _ _ _ mapped
        (by simpa only [numeric_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using inside)
        (.state_case_0 _ _ updatedWf frameWf) (.state_case_0 _ _ storeWf frameWf)
    · rfl
    · exact input
    · exact wf_config_make updatedWf frameWf (forall_nil _)
  · rename_i outside
    apply StepH.step
    apply Step.store_num_trap
    · simp [proj_num__0]
    · exact numeric_size_present ty
    · simpa only [numeric_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using Nat.lt_of_not_ge outside
    · exact input
    · exact wf_config_trap storeWf frameWf
    · exact Segment.index_wf 0 (by norm_num)
end Itasca.Runtime.Spec
