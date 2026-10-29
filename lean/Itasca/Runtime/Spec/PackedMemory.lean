import Itasca.Runtime.Spec.MemoryStore
import Itasca.Runtime.Spec.MemoryLoad
import Itasca.Runtime.Spec.IntegerExtend

namespace Itasca.Runtime.Spec
open SpecExt

/-- The five legal scalar packed widths; signedness is a separate load choice. -/
inductive PackedMemory where
  | i32x8 | i32x16 | i64x8 | i64x16 | i64x32

namespace PackedMemory

def type : PackedMemory → Inn
  | .i32x8 | .i32x16 => .I32
  | _ => .I64

def bits : PackedMemory → Nat
  | .i32x8 | .i64x8 => 8
  | .i32x16 | .i64x16 => 16
  | .i64x32 => 32

def bytes (op : PackedMemory) : Nat := op.bits / 8

def load (op : PackedMemory) (sign : sx) (argument : memarg) : admininstr :=
  .LOAD (numtype_Inn op.type) (some (.mk_loadop__0 op.type (.mk_loadop_Inn (.mk_sz op.bits) sign))) argument

def store (op : PackedMemory) (argument : memarg) : admininstr :=
  .STORE (numtype_Inn op.type) (some (.mk_sz op.bits)) argument

def loaded (op : PackedMemory) (sign : sx) (payload : List byte) : num_ :=
  .mk_num__0 op.type (extend__ op.bits (sizenn (numtype_Inn op.type)) sign (inv_ibytes_ op.bits payload))

def stored (op : PackedMemory) (value : Nat) : List byte := Builtins.integerBytes op.bytes value

theorem byte_count (op : PackedMemory) : rat_to_nat ((op.bits : Rat) / 8) = op.bytes := by
  cases op <;> norm_num [bits,bytes,rat_to_nat] <;> rfl

theorem size_eq (op : PackedMemory) : (size (valtype_Inn op.type)).get! = sizenn (numtype_Inn op.type) := by
  cases op <;> rfl

theorem size_present (op : PackedMemory) : size (valtype_Inn op.type) ≠ none := by cases op <;> decide

theorem stored_wrap (op : PackedMemory) (value : Nat) :
    ibytes_ op.bits (wrap__ (sizenn (numtype_Inn op.type)) op.bits (.mk_uN value)) = op.stored value := by
  cases op <;> exact integer_bytes_mod _ _

theorem loaded_wf (op : PackedMemory) (sign : sx) (payload : List byte)
    (valid : Forall wf_byte payload) (lengthEq : payload.length = op.bytes) :
    wf_num_ (numtype_Inn op.type) (op.loaded sign payload) := by
  have bound := integer_of_bytes_bound payload valid
  rw [lengthEq] at bound
  cases sign
  · unfold loaded extend__ inv_ibytes_
    apply unsigned_num_wf
    cases op <;> norm_num [bytes,bits,type,numtype_Inn,sizenn,size,valtype_numtype] at * <;> omega
  · let input : BitVec op.bits := BitVec.ofNat op.bits (Builtins.integerOfBytes payload)
    have inputEq : input.toNat = Builtins.integerOfBytes payload := by
      apply Nat.mod_eq_of_lt
      cases op <;> norm_num [bytes,bits] at * <;> omega
    have extension := extend_signed_bitvec op.bits (sizenn (numtype_Inn op.type)) input
    rw [inputEq] at extension
    unfold loaded inv_ibytes_
    rw [extension]
    exact unsigned_num_wf _ _ (input.signExtend (sizenn (numtype_Inn op.type))).isLt

/-- Packed source loads consume exactly their encoded byte width, then perform
canonical sign or zero extension. -/
theorem load_step (s : _root_.store) (f : frame) (op : PackedMemory) (sign : sx) (argument : memarg) (address : Nat)
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (op.load sign argument))
    (bytesWf : Forall wf_byte (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,op.load sign argument]⟩ []
      ⟨⟨s,f⟩,if address + proj_uN_0 argument.OFFSET + op.bytes ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length then
        [.CONST (numtype_Inn op.type) (op.loaded sign
          (((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.drop (address+proj_uN_0 argument.OFFSET)).take op.bytes))]
        else [.TRAP]⟩ := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr [Segment.i32 address,op.load sign argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact operationWf)
  split
  · rename_i fits
    let payload := ((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.drop (address+proj_uN_0 argument.OFFSET)).take op.bytes
    have payloadWf : Forall wf_byte payload := by
      intro byte member
      exact bytesWf byte (List.mem_of_mem_drop (List.mem_of_mem_take member))
    have payloadLength : payload.length = op.bytes := by
      simp only [payload,List.length_take,List.length_drop]
      omega
    have valueWf := op.loaded_wf sign payload payloadWf payloadLength
    have output := wf_config_make storeWf frameWf (show Forall wf_admininstr [.CONST (numtype_Inn op.type) (op.loaded sign payload)] from by
      simpa [Forall] using wf_admininstr.admininstr_case_13 _ _ valueWf)
    apply StepH.step
    apply Step.read _ _ _ ?_ input output
    unfold load loaded
    rw [←op.size_eq]
    apply Step_read.load_pack_val _ _ _ _ _ _ (inv_ibytes_ op.bits payload)
    · exact op.size_present
    · simp [proj_num__0]
    · have encoded := integer_bytes_of_bytes payload payloadWf
      rw [payloadLength] at encoded
      simpa only [ibytes_,inv_ibytes_,proj_uN_0,proj_num__0,byte_count,Option.get!_some,bytes,payload] using encoded
    · have bounded := integer_of_bytes_bound payload payloadWf
      rw [payloadLength] at bounded
      change Builtins.integerOfBytes payload < 2^op.bits
      cases op <;> norm_num [bytes,bits] at bounded ⊢ <;> exact bounded
    · exact input
    · simpa only [size_eq,loaded] using wf_admininstr.admininstr_case_13 _ _ valueWf
    · exact Segment.index_wf 0 (by norm_num)
  · rename_i outside
    apply StepH.step
    apply Step.read _ _ _ ?_ input (wf_config_trap storeWf frameWf)
    apply Step_read.load_pack_trap
    · simp [proj_num__0]
    · simpa only [byte_count,proj_num__0,proj_uN_0,Option.get!_some] using Nat.lt_of_not_ge outside
    · exact input
    · exact .admininstr_case_73
    · exact Segment.index_wf 0 (by norm_num)

/-- Packed stores use the low bytes of the source integer, preserving the
well-formed source store and returning the generated bounds trap when needed. -/
theorem store_step (s : _root_.store) (f : frame) (op : PackedMemory) (argument : memarg)
    (address value : Nat) (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (op.store argument))
    (valueWf : wf_num_ (numtype_Inn op.type) (.mk_num__0 op.type (.mk_uN value)))
    (mapped : 0 < f.MODULE.MEMS.length) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,.CONST (numtype_Inn op.type) (.mk_num__0 op.type (.mk_uN value)),op.store argument]⟩ []
      (if address + proj_uN_0 argument.OFFSET + op.bytes ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length then
        ⟨⟨memoryPayloadWrite s f (address+proj_uN_0 argument.OFFSET) (op.stored value),f⟩,[]⟩
      else ⟨⟨s,f⟩,[.TRAP]⟩) := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [Segment.i32 address,.CONST (numtype_Inn op.type) (.mk_num__0 op.type (.mk_uN value)),op.store argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact .admininstr_case_13 _ _ valueWf
    · exact operationWf)
  split
  · rename_i inside
    have updatedWf := memory_payload_write_wf s f (address+proj_uN_0 argument.OFFSET) (op.stored value)
      storeWf (integer_bytes_wf op.bytes value)
    apply StepH.step
    apply Step.store_pack_val _ _ _ _ _ _ (op.stored value)
    · simp [proj_num__0]
    · exact .fun_with_mem_case_0 s f (.mk_uN 0) _ _ _ mapped
        (by simpa only [byte_count,proj_num__0,proj_uN_0,Option.get!_some] using inside)
        (.state_case_0 _ _ updatedWf frameWf) (.state_case_0 _ _ storeWf frameWf)
    · exact op.size_present
    · simp [proj_num__0]
    · simp only [proj_num__0,Option.get!_some,size_eq,stored_wrap]
    · exact input
    · exact wf_config_make updatedWf frameWf (forall_nil _)
  · rename_i outside
    apply StepH.step
    apply Step.store_pack_trap
    · simp [proj_num__0]
    · simpa only [byte_count,proj_num__0,proj_uN_0,Option.get!_some] using Nat.lt_of_not_ge outside
    · exact input
    · exact wf_config_trap storeWf frameWf
    · exact Segment.index_wf 0 (by norm_num)
end PackedMemory
end Itasca.Runtime.Spec
