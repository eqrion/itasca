import Itasca.Runtime.Spec.FloatTrunc
import Itasca.Runtime.Spec.SegmentInitCases
import Itasca.Runtime.Spec.Integer
import Mathlib.Tactic
import «wasm2.0»

/-!
Sections, each formerly its own module: MemoryStore, PackedMemory, TableAccess, MemorySize, CopyInterval, MemoryInit, CopySnapshot, TableFill, FillSlice, References, ReferenceFunction, TableWriteBounds, FloatPromote.
-/

/-! ## MemoryStore -/

section

namespace Itasca.Runtime.Spec
open SpecExt

def memoryPayloadWrite (s : store) (f : frame) (start : Nat) (payload : List byte) : store :=
  {s with MEMS := s.MEMS.modify f.MODULE.MEMS[0]! (fun memory =>
    {memory with BYTES := splice memory.BYTES payload start})}

theorem splice_set_slice {T : Type} (bytes payload : List T) (start : Nat)
    (inside : start + payload.length ≤ bytes.length) :
    splice bytes payload start = bytes.setSlice! start payload := by
  have first : Nat.min start bytes.length = start := Nat.min_eq_left (by omega)
  simp only [splice,first,List.setSlice!]

theorem memory_payload_write_wf (s : store) (f : frame) (start : Nat) (payload : List byte)
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

theorem integer_bytes_wf (count value : Nat) :
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

theorem integer_bytes_mod (count value : Nat) :
    Builtins.integerBytes count (value % 256^count) = Builtins.integerBytes count value := by
  have roundtrip := integer_bytes_of_bytes (Builtins.integerBytes count value) (integer_bytes_wf count value)
  simpa only [Builtins.integerBytes_length,Builtins.integerOfBytes_integerBytes] using roundtrip

theorem numeric_bytes_payload_wf (ty : numtype) (value : num_) : Forall wf_byte (nbytes_ ty value) := by
  cases ty <;> cases value <;> simp only [nbytes_,ibytes_,fbytes_] <;>
    first | exact integer_bytes_wf _ _ | simp [Forall]

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
    have updatedWf := memory_payload_write_wf s f (address+proj_uN_0 argument.OFFSET) (nbytes_ ty value)
      storeWf (numeric_bytes_payload_wf ty value)
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

end

/-! ## PackedMemory -/

section

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

end

/-! ## TableAccess -/

section

namespace Itasca.Runtime.Spec
open SpecExt

/-- Source table reads return the selected reference or the exact bounds trap. -/
theorem table_get_step (s : store) (f : frame) (index position : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hx : index < 2^32) (hp : position < 2^32) :
    StepH ⟨⟨s,f⟩,[Segment.i32 position,.TABLE_GET (.mk_uN index)]⟩ []
      ⟨⟨s,f⟩,if position < (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length then
        [admininstr_ref (fun_table ⟨s,f⟩ (.mk_uN index)).REFS[position]!] else [.TRAP]⟩ := by
  have input : wf_config ⟨⟨s,f⟩,[Segment.i32 position,.TABLE_GET (.mk_uN index)]⟩ := by
    apply wf_config_make hs hf
    simp only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨Segment.i32_wf _ hp,.admininstr_case_48 _ (Segment.index_wf _ hx)⟩
  split
  · rename_i inside
    refine StepH.step (Step.read _ _ _ ?_ input ?_)
    · exact Step_read.table_get_val ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN position)) (.mk_uN index) inside
        (by simp [proj_num__0]) input
    · apply wf_config_make hs hf
      simpa [Forall] using Segment.ref_wf (fun_table ⟨s,f⟩ (.mk_uN index)).REFS[position]!
  · rename_i outside
    refine StepH.step (Step.read _ _ _ ?_ input ?_)
    · exact Step_read.table_get_trap ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN position)) (.mk_uN index)
        (by simp [proj_num__0]) (by simpa [proj_num__0,proj_uN_0] using Nat.le_of_not_gt outside) input (.admininstr_case_73)
    · apply wf_config_make hs hf
      simpa [Forall] using wf_admininstr.admininstr_case_73

/-- Table size returns the exact unsigned element count. -/
theorem table_size_step (s : store) (f : frame) (index : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hx : index < 2^32)
    (bounded : (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length < 2^32) :
    StepH ⟨⟨s,f⟩,[.TABLE_SIZE (.mk_uN index)]⟩ []
      ⟨⟨s,f⟩,[Segment.i32 (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length]⟩ := by
  have input : wf_config ⟨⟨s,f⟩,[.TABLE_SIZE (.mk_uN index)]⟩ :=
    wf_config_make hs hf (by simpa [Forall] using wf_admininstr.admininstr_case_50 _ (Segment.index_wf _ hx))
  have output := Segment.i32_wf (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length bounded
  exact StepH.step (Step.read _ _ _
    (Step_read.table_size ⟨s,f⟩ (.mk_uN index) _ rfl input output) input
    (wf_config_make hs hf (by simpa [Forall] using output)))
end Itasca.Runtime.Spec

end

/-! ## MemorySize -/

section

namespace Itasca.Runtime.Spec
open SpecExt

/-- Memory size returns the exact page count of the source memory. -/
theorem memory_size_step (s : store) (f : frame)
    (hs : wf_store s) (hf : wf_frame f)
    (aligned : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length % 65536 = 0)
    (bounded : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length / 65536 < 2^32) :
    StepH ⟨⟨s,f⟩,[.MEMORY_SIZE]⟩ []
      ⟨⟨s,f⟩,[Segment.i32 ((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length / 65536)]⟩ := by
  have input : wf_config ⟨⟨s,f⟩,[.MEMORY_SIZE]⟩ :=
    wf_config_make hs hf (by simpa [Forall] using wf_admininstr.admininstr_case_62)
  have output := Segment.i32_wf ((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length / 65536) bounded
  refine StepH.step (Step.read _ _ _ ?_ input (wf_config_make hs hf (by simpa [Forall] using output)))
  apply Step_read.memory_size
  · simp only [Ki,Nat.mul_assoc]
    norm_num
    exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero aligned)
  · exact input
  · exact output
  · exact Segment.index_wf 0 (by decide)
end Itasca.Runtime.Spec

end

/-! ## CopyInterval -/

section

namespace Itasca.Runtime.Spec.Segment

/-- A left-to-right in-place copy has written exactly its completed prefix.
Reads from the remaining source interval still refer to the original list. -/
structure CopyPrefix {T : Type} (before current : List T) (dst src copied : Nat) : Prop where
  length : current.length = before.length
  written : ∀ j, j < copied → current[dst+j]? = before[src+j]?
  outside : ∀ j, j < dst ∨ dst+copied ≤ j → current[j]? = before[j]?

theorem CopyPrefix.initial {T : Type} (before : List T) (dst src : Nat) : CopyPrefix before before dst src 0 := by
  exact ⟨rfl,by intros; omega,by intros; rfl⟩

theorem CopyPrefix.source {T : Type} [Inhabited T] {before current : List T} {dst src copied : Nat}
    (state : CopyPrefix before current dst src copied) (direction : dst ≤ src) :
    current[src+copied]! = before[src+copied]! := by
  simp only [List.getElem!_eq_getElem?_getD,state.outside (src+copied) (Or.inr (by omega))]

theorem CopyPrefix.write {T : Type} [Inhabited T] {before current : List T} {dst src copied : Nat}
    (state : CopyPrefix before current dst src copied) (direction : dst ≤ src)
    (sourceBound : src+copied < before.length) (targetBound : dst+copied < before.length) :
    CopyPrefix before (current.set (dst+copied) current[src+copied]!) dst src (copied+1) := by
  refine ⟨by simp [state.length],?_,?_⟩
  · intro j bound
    by_cases last : j=copied
    · subst j
      rw [state.source direction]
      simp [List.getElem?_set,state.length,targetBound,List.getElem!_eq_getElem?_getD,
        List.getElem?_eq_getElem sourceBound]
    · have distinct : dst+copied ≠ dst+j := by omega
      simp only [List.getElem?_set,distinct,if_false]
      exact state.written j (by omega)
  · intro j bound
    have distinct : dst+copied ≠ j := by omega
    simp only [List.getElem?_set,distinct,if_false]
    exact state.outside j (by omega)

theorem CopyPrefix.complete {T : Type} {before current : List T} {dst src count : Nat}
    (state : CopyPrefix before current dst src count) (sourceBound : src+count ≤ before.length)
    (targetBound : dst+count ≤ before.length) :
    current = before.setSlice! dst (before.slice src (src+count)) := by
  have sliceLength : (before.slice src (src+count)).length = count := by rw [List.slice_length]; omega
  apply List.ext_getElem?
  intro index
  by_cases first : index < dst
  · rw [List.setSlice!_getElem?_prefix _ _ _ _ first]
    exact state.outside index (Or.inl first)
  · by_cases last : dst+count ≤ index
    · rw [List.setSlice!_getElem?_suffix _ _ _ _ (by omega)]
      exact state.outside index (Or.inr last)
    · rw [List.setSlice!_getElem?_middle _ _ _ _ (by omega),List.getElem?_slice _ _ _ _ (by omega)]
      have same : dst+(index-dst)=index := by omega
      simpa only [same] using state.written (index-dst) (by omega)

/-- A right-to-left in-place copy has written exactly its completed suffix. -/
structure CopySuffix {T : Type} (before current : List T) (dst src remaining count : Nat) : Prop where
  length : current.length = before.length
  written : ∀ j, remaining ≤ j → j < count → current[dst+j]? = before[src+j]?
  outside : ∀ j, j < dst+remaining ∨ dst+count ≤ j → current[j]? = before[j]?

theorem CopySuffix.initial {T : Type} (before : List T) (dst src count : Nat) : CopySuffix before before dst src count count := by
  exact ⟨rfl,by intros; omega,by intros; rfl⟩

theorem CopySuffix.source {T : Type} [Inhabited T] {before current : List T} {dst src remaining count : Nat}
    (state : CopySuffix before current dst src remaining count) (direction : src ≤ dst) (positive : 0 < remaining) :
    current[src+(remaining-1)]! = before[src+(remaining-1)]! := by
  simp only [List.getElem!_eq_getElem?_getD,state.outside (src+(remaining-1)) (Or.inl (by omega))]

theorem CopySuffix.write {T : Type} [Inhabited T] {before current : List T} {dst src remaining count : Nat}
    (state : CopySuffix before current dst src remaining count) (direction : src ≤ dst)
    (positive : 0 < remaining) (bounded : remaining ≤ count)
    (sourceBound : src+remaining ≤ before.length) (targetBound : dst+remaining ≤ before.length) :
    CopySuffix before (current.set (dst+(remaining-1)) current[src+(remaining-1)]!) dst src (remaining-1) count := by
  refine ⟨by simp [state.length],?_,?_⟩
  · intro j lower upper
    by_cases last : j=remaining-1
    · subst j
      have srcInside : src+(remaining-1) < before.length := by omega
      have dstInside : dst+(remaining-1) < before.length := by omega
      rw [state.source direction positive]
      simp [List.getElem?_set,state.length,dstInside,List.getElem!_eq_getElem?_getD,
        List.getElem?_eq_getElem srcInside]
    · have distinct : dst+(remaining-1) ≠ dst+j := by omega
      simp only [List.getElem?_set,distinct,if_false]
      exact state.written j (by omega) upper
  · intro j outside
    have distinct : dst+(remaining-1) ≠ j := by omega
    simp only [List.getElem?_set,distinct,if_false]
    exact state.outside j (by omega)

theorem CopySuffix.complete {T : Type} {before current : List T} {dst src count : Nat}
    (state : CopySuffix before current dst src 0 count) (sourceBound : src+count ≤ before.length)
    (targetBound : dst+count ≤ before.length) :
    current = before.setSlice! dst (before.slice src (src+count)) := by
  apply CopyPrefix.complete (count:=count) (src:=src) (dst:=dst) (before:=before) (current:=current) _ sourceBound targetBound
  exact ⟨state.length,fun j bound => state.written j (by omega) bound,by simpa using state.outside⟩
end Itasca.Runtime.Spec.Segment

end

/-! ## MemoryInit -/

section

/-!
Source semantics of `memory.init`. Connect the generated recursive rules to the bounded interval update used by runtime correspondence proofs.
-/

/-! ## Memory Init Source -/

section

namespace Itasca.Runtime.Spec.Segment
open SpecExt

def zeroMemarg : memarg := ⟨.mk_uN 0,.mk_uN 0⟩
def storeByte : admininstr := .STORE .I32 (some (.mk_sz 8)) zeroMemarg

theorem zero_memarg_wf : wf_memarg zeroMemarg := by
  constructor <;> exact index_wf 0 (by norm_num)

theorem store_byte_wf : wf_admininstr storeByte := by
  apply wf_admininstr.admininstr_case_57 (some .I32)
  · simp only [Option.toList_some,Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    constructor
    decide
  · exact zero_memarg_wf
  · simp
  · norm_num [Forall₂,numtype_Inn,proj_sz_0,sizenn,size,valtype_numtype]

theorem byte_bound (value : byte) (hw : wf_byte value) : proj_byte_0 value < 256 := by
  cases value
  cases hw
  simp only [proj_byte_0]
  omega

theorem byte_store_encoding (value : byte) (hw : wf_byte value) :
    ibytes_ 8 (wrap__ 32 8 (.mk_uN (proj_byte_0 value))) = [value] := by
  have bound := byte_bound value hw
  cases value
  simp only [ibytes_,wrap__,proj_uN_0,proj_byte_0] at *
  norm_num [SpecExt.Builtins.integerBytes,Nat.mod_eq_of_lt bound]

theorem splice_singleton_eq_set {T : Type} (values : List T) (position : Nat) (value : T) :
    splice values [value] position = values.set position value := by
  rw [List.set_eq_take_append_cons_drop]
  by_cases inside : position < values.length
  · have minPos : Min.min position values.length = position := Nat.min_eq_left (by omega)
    have minLen : Min.min 1 (values.length-position) = 1 := Nat.min_eq_left (by omega)
    simp [splice,minPos,minLen,inside]
  · have minPos : Min.min position values.length = values.length := Nat.min_eq_right (by omega)
    simp [splice,minPos,inside]

def memoryWrite (s : store) (f : frame) (position : Nat) (value : byte) : store :=
  {s with MEMS := s.MEMS.modify f.MODULE.MEMS[0]! (fun memory =>
    {memory with BYTES := memory.BYTES.set position value})}

theorem memory_write_wf (s : store) (f : frame) (position : Nat) (value : byte)
    (hs : wf_store s) (hb : wf_byte value) : wf_store (memoryWrite s f position value) := by
  cases s with | MKstore funcs globals tables mems elems datas =>
  cases hs with | store_case_ _ _ _ _ _ _ hfn hg ht hm hd =>
  apply wf_store.store_case_ _ _ _ _ _ _ hfn hg ht _ hd
  apply forall_modify _ _ _ _ hm
  intro memory hw
  cases memory
  cases hw with | meminst_case_ _ _ htype hbytes =>
  constructor
  · exact htype
  · intro b member
    rcases List.mem_or_eq_of_mem_set member with old | changed
    · exact hbytes b old
    · subst b; exact hb

theorem memory_write_step (s : store) (f : frame) (position : Nat) (value : byte)
    (hs : wf_store s) (hf : wf_frame f) (hp : position < 2^32) (hb : wf_byte value)
    (mapped : 0 < f.MODULE.MEMS.length)
    (inside : position < (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length) :
    StepH ⟨⟨s,f⟩,[i32 position,i32 (proj_byte_0 value),storeByte]⟩ []
      ⟨⟨memoryWrite s f position value,f⟩,[]⟩ := by
  have fresh := memory_write_wf s f position value hs hb
  apply StepH.step
  apply Step.store_pack_val _ _ .I32 _ 8 zeroMemarg [value] _
  · simp [proj_num__0]
  · have write := fun_with_mem.fun_with_mem_case_0 s f (.mk_uN 0) position 1 [value] mapped (by omega)
      (by simpa only [splice_singleton_eq_set,memoryWrite,proj_uN_0] using wf_state.state_case_0 _ _ fresh hf) (.state_case_0 _ _ hs hf)
    norm_num [proj_num__0,proj_uN_0,zeroMemarg,rat_to_nat,splice_singleton_eq_set,memoryWrite] at write ⊢
    exact write
  · simp [size,valtype_Inn]
  · simp [proj_num__0]
  · exact (byte_store_encoding value hb).symm
  · apply wf_config_make hs hf
    simp only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨i32_wf _ hp,i32_wf _ (by have := byte_bound value hb; omega),store_byte_wf⟩
  · exact wf_config_make fresh hf (by simp [Forall])

def next32 (value : Nat) : Nat := (value+1) % 2^32

theorem next32_bound (value : Nat) : next32 value < 2^32 := Nat.mod_lt _ (by norm_num)
theorem next32_le (value : Nat) : next32 value ≤ value+1 := Nat.mod_le _ _

theorem next32_add (value : Nat) : fun_iadd_ 32 (.mk_uN value) (.mk_uN 1) (.mk_uN (next32 value)) :=
  .fun_iadd__case_0 _ _ _ (index_wf _ (next32_bound value))

theorem memory_init_expand (s : store) (f : frame) (destination source count dataIndex : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32)
    (hn : count+1 < 2^32) (he : dataIndex < 2^32)
    (bytesWf : Forall wf_byte (fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES)
    (inside : source+(count+1) ≤ (fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES.length ∧
      destination+(count+1) ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length) :
    StepH ⟨⟨s,f⟩,operands destination source (count+1) ++ [.MEMORY_INIT (.mk_uN dataIndex)]⟩ []
      ⟨⟨s,f⟩,[i32 destination,i32 (proj_byte_0 ((fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES[source]!)),storeByte] ++
        (operands (next32 destination) (next32 source) count ++ [.MEMORY_INIT (.mk_uN dataIndex)])⟩ := by
  have memoryWf : wf_admininstr (.MEMORY_INIT (.mk_uN dataIndex)) := .admininstr_case_66 _ (index_wf _ he)
  have srcInside : source < (fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES.length := by omega
  have byteWf : wf_byte ((fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES[source]!) := bytesWf _ (by simp [srcInside])
  have valueWf := i32_wf (proj_byte_0 ((fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES[source]!))
    (by have := byte_bound _ byteWf; omega)
  have input := init_config_wf s f destination source (count+1) _ hs hf hd hi hn memoryWf
  have output : wf_config ⟨⟨s,f⟩,[i32 destination,i32 (proj_byte_0 ((fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES[source]!)),storeByte] ++
        (operands (next32 destination) (next32 source) count ++ [.MEMORY_INIT (.mk_uN dataIndex)])⟩ := by
    apply wf_config_make hs hf
    simp only [operands,List.cons_append,List.nil_append,Forall,List.mem_cons,
      List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨i32_wf _ hd,valueWf,store_byte_wf,i32_wf _ (next32_bound _),i32_wf _ (next32_bound _),i32_wf _ (by omega),memoryWf⟩
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  have read := Step_read.memory_init_succ ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN destination))
    (.mk_num__0 .I32 (.mk_uN source)) (count+1) (.mk_uN dataIndex)
    (.mk_uN (next32 source)) (.mk_uN (next32 destination)) zeroMemarg srcInside
    (by simp [proj_num__0]) (next32_add source) (by simp [proj_num__0]) (next32_add destination)
    (.fun_memarg0_case_0 zero_memarg_wf) (Nat.succ_ne_zero count) inside input
    (i32_wf _ hd) valueWf store_byte_wf (i32_wf _ (next32_bound _)) (i32_wf _ (next32_bound _))
    (by simpa [i32] using i32_wf count (by omega)) memoryWf
  simpa [operands,i32,storeByte,proj_num__0,proj_uN_0] using read

def memoryInit (s : store) (f : frame) (dataIndex destination source : Nat) : Nat → store
  | 0 => s
  | count+1 => memoryInit
      (memoryWrite s f destination ((fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES[source]!))
      f dataIndex (next32 destination) (next32 source) count

theorem memory_write_mem_length (s : store) (f : frame) (position : Nat) (value : byte)
    (address : f.MODULE.MEMS[0]! < s.MEMS.length) :
    (fun_mem ⟨memoryWrite s f position value,f⟩ (.mk_uN 0)).BYTES.length =
      (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length := by
  simp only [fun_mem,memoryWrite,proj_uN_0]
  generalize f.MODULE.MEMS[0]! = a at address ⊢
  simp [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem address]

theorem memory_init_steps (s : store) (f : frame) (destination source count dataIndex : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32)
    (hn : count < 2^32) (he : dataIndex < 2^32)
    (mapped : 0 < f.MODULE.MEMS.length)
    (address : f.MODULE.MEMS[0]! < s.MEMS.length)
    (bytesWf : Forall wf_byte (fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES)
    (inside : source+count ≤ (fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES.length ∧
      destination+count ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length) :
    StepsH ⟨⟨s,f⟩,operands destination source count ++ [.MEMORY_INIT (.mk_uN dataIndex)]⟩ []
      ⟨⟨memoryInit s f dataIndex destination source count,f⟩,[]⟩ := by
  induction count generalizing s destination source with
  | zero => exact steps_h_single (memory_init_zero s f destination source dataIndex hs hf hd hi he inside)
  | succ count ih =>
    let value := (fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES[source]!
    have srcInside : source < (fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES.length := by omega
    have valueWf : wf_byte value := bytesWf _ (by simp [value,srcInside])
    let fresh := memoryWrite s f destination value
    have hw := memory_write_wf s f destination value hs valueWf
    have lengthEq := memory_write_mem_length s f destination value address
    have afterWf := (wf_config_parts (init_config_wf fresh f (next32 destination) (next32 source) count _ hw hf (next32_bound _) (next32_bound _)
      (by omega) (.admininstr_case_66 _ (index_wf _ he)))).2
    have first := memory_init_expand s f destination source count dataIndex hs hf hd hi hn he bytesWf inside
    have second := step_h_instrs (memory_write_step s f destination value hs hf hd valueWf mapped (by have := inside.2; omega)) []
      (operands (next32 destination) (next32 source) count ++ [.MEMORY_INIT (.mk_uN dataIndex)])
      (by simp [Forall]) afterWf
    have rest := ih fresh (next32 destination) (next32 source) hw (next32_bound _) (next32_bound _) (by omega)
      (by simpa [fresh,memoryWrite] using address) bytesWf
      (by rw [show (fun_mem ⟨fresh,f⟩ (.mk_uN 0)).BYTES.length =
            (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length from lengthEq]
          change next32 source+count ≤ (fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES.length ∧ _
          have := next32_le source
          have := next32_le destination
          omega)
    have combined := steps_h_trans (steps_h_single first) (steps_h_trans (steps_h_single second) rest)
    simpa only [instrContext,vals,List.map_nil,List.nil_append,List.append_nil,memoryInit,value,fresh] using combined

end Itasca.Runtime.Spec.Segment

end

/-! ## Memory Init Algebra -/

section

namespace Itasca.Runtime.Spec.Segment
open SpecExt

theorem memory_init_eq (s : store) (f : frame) (dataIndex destination source count : Nat)
    (address : f.MODULE.MEMS[0]! < s.MEMS.length)
    (memoryBound : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length ≤ 2^32)
    (dataBound : (fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES.length ≤ 2^32)
    (inside : source+count ≤ (fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES.length ∧
      destination+count ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length) :
    memoryInit s f dataIndex destination source count =
      {s with MEMS := s.MEMS.modify f.MODULE.MEMS[0]! (fun memory =>
        {memory with BYTES := copyInto memory.BYTES (fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES destination source count})} := by
  induction count generalizing s destination source with
  | zero =>
    simp only [memoryInit,copyInto]
    have identity : (fun memory : meminst => {memory with BYTES := memory.BYTES}) = id := by funext memory; cases memory; rfl
    rw [identity,List.modify_id]
  | succ count ih =>
    by_cases done : count = 0
    · subst count
      simp only [memoryInit,copyInto,memoryWrite,fun_data,proj_uN_0]
    · have dstBound : destination+1 < 2^32 := by omega
      have srcBound : source+1 < 2^32 := by omega
      have dstNext : next32 destination = destination+1 := Nat.mod_eq_of_lt dstBound
      have srcNext : next32 source = source+1 := Nat.mod_eq_of_lt srcBound
      have lengthEq := memory_write_mem_length s f destination
        ((fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES[source]!) address
      rw [memoryInit,dstNext,srcNext,ih (memoryWrite s f destination ((fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES[source]!)) (destination+1) (source+1)
        (by simpa [memoryWrite] using address)
        (by simpa only [lengthEq] using memoryBound) dataBound
        (by rw [lengthEq]; change source+1+count ≤ (fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES.length ∧ _; omega)]
      simp only [memoryWrite,fun_data,proj_uN_0,List.modify_modify_eq,Function.comp_def,copyInto]

end Itasca.Runtime.Spec.Segment

end

end

/-! ## CopySnapshot -/

section

namespace Itasca.Runtime.Spec.Segment

def copyForward {T : Type} [Inhabited T] (words : List T) (dst src : Nat) : Nat → List T
  | 0 => words
  | count+1 => copyForward (words.set dst words[src]!) (next32 dst) (next32 src) count

def copyBackward {T : Type} [Inhabited T] (words : List T) (dst src : Nat) : Nat → List T
  | 0 => words
  | count+1 => copyBackward (words.set (dst+count) words[src+count]!) dst src count

theorem copy_forward_snapshot {T : Type} [Inhabited T] (before current : List T) (dst src index remaining count : Nat)
    (state : CopyPrefix before current dst src index) (progress : index+remaining=count)
    (direction : dst ≤ src) (sourceBound : src+count ≤ before.length) (targetBound : dst+count ≤ before.length)
    (lengthBound : before.length ≤ 2^32) :
    copyForward current (dst+index) (src+index) remaining = before.setSlice! dst (before.slice src (src+count)) := by
  induction remaining generalizing current index with
  | zero =>
    have last : index=count := by omega
    exact (last ▸ state).complete sourceBound targetBound
  | succ remaining ih =>
    have srcInside : src+index < before.length := by omega
    have dstInside : dst+index < before.length := by omega
    have fresh := state.write direction srcInside dstInside
    by_cases done : remaining=0
    · subst remaining
      simp only [copyForward]
      have last : index+1=count := by omega
      exact (last ▸ fresh).complete sourceBound targetBound
    · have dstNext : next32 (dst+index) = dst+(index+1) := by
        unfold next32
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      have srcNext : next32 (src+index) = src+(index+1) := by
        unfold next32
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      rw [copyForward,dstNext,srcNext]
      exact ih _ (index+1) fresh (by omega)

theorem copy_backward_snapshot {T : Type} [Inhabited T] (before current : List T) (dst src remaining count : Nat)
    (state : CopySuffix before current dst src remaining count) (progress : remaining≤count)
    (direction : src ≤ dst) (sourceBound : src+count ≤ before.length) (targetBound : dst+count ≤ before.length) :
    copyBackward current dst src remaining = before.setSlice! dst (before.slice src (src+count)) := by
  induction remaining generalizing current with
  | zero => exact state.complete sourceBound targetBound
  | succ remaining ih =>
    have fresh := state.write direction (by omega) progress (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at fresh
    rw [copyBackward]
    exact ih _ fresh (by omega)
end Itasca.Runtime.Spec.Segment

end

/-! ## TableFill -/

section

/-!
Source semantics of `table.fill`. Connect the generated recursive rules to the bounded interval update used by runtime correspondence proofs.
-/

/-! ## Table Fill Source -/

section

namespace Itasca.Runtime.Spec.Segment
open SpecExt

def fillOperands (destination : Nat) (value : ref) (count : Nat) : List admininstr :=
  [i32 destination,admininstr_ref value,i32 count]

theorem fill_config_wf (s : store) (f : frame) (destination count tableIndex : Nat) (value : ref)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hn : count < 2^32) (ht : tableIndex < 2^32) :
    wf_config ⟨⟨s,f⟩,fillOperands destination value count ++ [.TABLE_FILL (.mk_uN tableIndex)]⟩ := by
  apply wf_config_make hs hf
  simp only [fillOperands,List.cons_append,List.nil_append,Forall,List.mem_cons,List.not_mem_nil,
    false_implies,forall_const,and_true,forall_eq_or_imp]
  exact ⟨i32_wf _ hd,ref_wf _,i32_wf _ hn,.admininstr_case_52 _ (index_wf _ ht)⟩

theorem table_fill_trap (s : store) (f : frame) (destination count tableIndex : Nat) (value : ref)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hn : count < 2^32) (ht : tableIndex < 2^32)
    (outside : (fun_table ⟨s,f⟩ (.mk_uN tableIndex)).REFS.length < destination+count) :
    StepH ⟨⟨s,f⟩,fillOperands destination value count ++ [.TABLE_FILL (.mk_uN tableIndex)]⟩ []
      ⟨⟨s,f⟩,[.TRAP]⟩ := by
  have reference : admininstr_val (val_ref value) = admininstr_ref value := by cases value <;> rfl
  have input := fill_config_wf s f destination count tableIndex value hs hf hd hn ht
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_make hs hf (by simp [Forall]; exact .admininstr_case_73))
  have read := Step_read.table_fill_trap ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN destination)) (val_ref value) count (.mk_uN tableIndex)
    (by simp [proj_num__0]) (by simpa only [proj_num__0,proj_uN_0,Option.get!] using outside)
    (by simpa only [fillOperands,i32,List.cons_append,List.nil_append,reference] using input) .admininstr_case_73
  simpa only [fillOperands,i32,List.cons_append,List.nil_append,reference] using read

theorem table_fill_zero (s : store) (f : frame) (destination tableIndex : Nat) (value : ref)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (ht : tableIndex < 2^32)
    (inside : destination ≤ (fun_table ⟨s,f⟩ (.mk_uN tableIndex)).REFS.length) :
    StepH ⟨⟨s,f⟩,fillOperands destination value 0 ++ [.TABLE_FILL (.mk_uN tableIndex)]⟩ [] ⟨⟨s,f⟩,[]⟩ := by
  have reference : admininstr_val (val_ref value) = admininstr_ref value := by cases value <;> rfl
  have input := fill_config_wf s f destination 0 tableIndex value hs hf hd (by decide) ht
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_make hs hf (by simp [Forall]))
  have read := Step_read.table_fill_zero ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN destination)) (val_ref value) 0 (.mk_uN tableIndex)
    (by simp [proj_num__0]) (by simpa only [proj_num__0,proj_uN_0,Option.get!,Nat.add_zero] using inside) rfl
    (by simpa only [fillOperands,i32,List.cons_append,List.nil_append,reference] using input)
  simpa only [fillOperands,i32,List.cons_append,List.nil_append,reference] using read

theorem table_fill_expand (s : store) (f : frame) (destination count tableIndex : Nat) (value : ref)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination+1 < 2^32) (hn : count+1 < 2^32) (ht : tableIndex < 2^32)
    (inside : destination+(count+1) ≤ (fun_table ⟨s,f⟩ (.mk_uN tableIndex)).REFS.length) :
    StepH ⟨⟨s,f⟩,fillOperands destination value (count+1) ++ [.TABLE_FILL (.mk_uN tableIndex)]⟩ []
      ⟨⟨s,f⟩,[i32 destination,admininstr_ref value,.TABLE_SET (.mk_uN tableIndex)] ++
        (fillOperands (destination+1) value count ++ [.TABLE_FILL (.mk_uN tableIndex)])⟩ := by
  have reference : admininstr_val (val_ref value) = admininstr_ref value := by cases value <;> rfl
  have input := fill_config_wf s f destination (count+1) tableIndex value hs hf (by omega) hn ht
  have output : wf_config ⟨⟨s,f⟩,[i32 destination,admininstr_ref value,.TABLE_SET (.mk_uN tableIndex)] ++
        (fillOperands (destination+1) value count ++ [.TABLE_FILL (.mk_uN tableIndex)])⟩ := by
    apply wf_config_make hs hf
    simp only [fillOperands,List.cons_append,List.nil_append,Forall,List.mem_cons,List.not_mem_nil,
      false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨i32_wf _ (by omega),ref_wf _,.admininstr_case_49 _ (index_wf _ ht),i32_wf _ hd,ref_wf _,
      i32_wf _ (by omega),.admininstr_case_52 _ (index_wf _ ht)⟩
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  have read := Step_read.table_fill_succ ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN destination)) (val_ref value) (count+1) (.mk_uN tableIndex)
    (by simp [proj_num__0]) (Nat.succ_ne_zero count) (by simpa only [proj_num__0,proj_uN_0,Option.get!] using inside)
    (by simpa only [fillOperands,i32,List.cons_append,List.nil_append,reference] using input)
    (i32_wf _ (by omega)) (.admininstr_case_49 _ (index_wf _ ht)) (i32_wf _ hd)
    (by simpa [i32] using i32_wf count (by omega)) (.admininstr_case_52 _ (index_wf _ ht))
  simpa [fillOperands,i32,reference,proj_num__0,proj_uN_0] using read
def tableFill (s : store) (f : frame) (index destination : Nat) (value : ref) : Nat → store
  | 0 => s
  | count+1 => tableFill (tableWrite s f index destination value) f index (destination+1) value count

/-- Finite generated reduction of table.fill performs one table.set per
requested element and then the zero-length rule. -/
theorem table_fill_steps (s : store) (f : frame) (destination count tableIndex : Nat) (value : ref)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hn : count < 2^32) (ht : tableIndex < 2^32)
    (mapped : tableIndex < f.MODULE.TABLES.length)
    (address : f.MODULE.TABLES[tableIndex]! < s.TABLES.length)
    (tableBound : (fun_table ⟨s,f⟩ (.mk_uN tableIndex)).REFS.length < 2^32)
    (inside : destination+count ≤ (fun_table ⟨s,f⟩ (.mk_uN tableIndex)).REFS.length) :
    StepsH ⟨⟨s,f⟩,fillOperands destination value count ++ [.TABLE_FILL (.mk_uN tableIndex)]⟩ []
      ⟨⟨tableFill s f tableIndex destination value count,f⟩,[]⟩ := by
  induction count generalizing s destination with
  | zero => exact steps_h_single (table_fill_zero s f destination tableIndex value hs hf hd ht (by simpa using inside))
  | succ count ih =>
    have hd' : destination+1 < 2^32 := by omega
    let fresh := tableWrite s f tableIndex destination value
    have hw := table_write_wf s f tableIndex destination value hs
    have lengthEq := table_write_table_length s f tableIndex destination value address
    have afterWf := (wf_config_parts (fill_config_wf fresh f (destination+1) count tableIndex value hw hf hd' (by omega) ht)).2
    have first := table_fill_expand s f destination count tableIndex value hs hf hd' hn ht inside
    have second := step_h_instrs (table_write_step s f tableIndex destination value hs hf hd ht mapped (by omega)) []
      (fillOperands (destination+1) value count ++ [.TABLE_FILL (.mk_uN tableIndex)]) (by simp [Forall]) afterWf
    have rest := ih fresh (destination+1) hw hd' (by omega)
      (by simpa [fresh,tableWrite] using address)
      (by simpa only [fresh,lengthEq] using tableBound)
      (by rw [show (fun_table ⟨fresh,f⟩ (.mk_uN tableIndex)).REFS.length =
            (fun_table ⟨s,f⟩ (.mk_uN tableIndex)).REFS.length from lengthEq]; omega)
    have combined := steps_h_trans (steps_h_single first) (steps_h_trans (steps_h_single second) rest)
    simpa only [instrContext,vals,List.map_nil,List.nil_append,List.append_nil,tableFill,fresh] using combined
end Itasca.Runtime.Spec.Segment

end

/-! ## Table Fill Algebra -/

section

namespace Itasca.Runtime.Spec.Segment
open SpecExt

def fillInto {T : Type} (before : List T) (destination : Nat) (value : T) : Nat → List T
  | 0 => before
  | count+1 => fillInto (before.set destination value) (destination+1) value count

theorem fill_into_map {T U : Type} (decode : T → U) (before : List T) (destination count : Nat) (value : T) :
    (fillInto before destination value count).map decode =
      fillInto (before.map decode) destination (decode value) count := by
  induction count generalizing before destination with
  | zero => rfl
  | succ count ih => simp only [fillInto,ih,List.map_set]

theorem table_fill_eq (s : store) (f : frame) (tableIndex destination count : Nat) (value : ref) :
    tableFill s f tableIndex destination value count =
      {s with TABLES := s.TABLES.modify f.MODULE.TABLES[tableIndex]! (fun table =>
        {table with REFS := fillInto table.REFS destination value count})} := by
  induction count generalizing s destination with
  | zero =>
    simp only [tableFill,fillInto]
    have identity : (fun table : tableinst => {table with REFS := table.REFS}) = id := by funext table; cases table; rfl
    rw [identity,List.modify_id]
  | succ count ih =>
    rw [tableFill,ih]
    simp only [tableWrite,List.modify_modify_eq,Function.comp_def,fillInto]
    congr 1
    congr 1
    funext table
    simp only [List.modify_eq_set]
end Itasca.Runtime.Spec.Segment

end

end

/-! ## FillSlice -/

section

namespace Itasca.Runtime.Spec.Segment

theorem fill_into_effect {T : Type} (before : List T) (dst count : Nat) (value : T)
    (targetBound : dst+count ≤ before.length) :
    (∀ j, j < count → (fillInto before dst value count)[dst+j]? = some value) ∧
    (∀ j, j < dst ∨ dst+count ≤ j → (fillInto before dst value count)[j]? = before[j]?) := by
  induction count generalizing before dst with
  | zero => simp [fillInto]
  | succ count ih =>
    obtain ⟨filled,outside⟩ := ih (before.set dst value) (dst+1)
      (by simpa using (show dst+1+count ≤ before.length by omega))
    constructor
    · intro j bound
      cases j with
      | zero =>
        have first := outside dst (Or.inl (by omega))
        have targetInside : dst < before.length := by omega
        simpa [fillInto,targetInside] using first
      | succ j =>
        have previous := filled j (by omega)
        simpa only [fillInto,Nat.add_assoc,Nat.add_comm 1 j] using previous
    · intro j bound
      have tailOutside := outside j (by omega)
      have distinct : dst ≠ j := by omega
      simpa only [fillInto,List.getElem?_set,distinct,if_false] using tailOutside

theorem fill_into_eq_set_slice {T : Type} (before : List T) (dst count : Nat) (value : T)
    (targetBound : dst+count ≤ before.length) :
    fillInto before dst value count = before.setSlice! dst (List.replicate count value) := by
  obtain ⟨filled,outside⟩ := fill_into_effect before dst count value targetBound
  apply List.ext_getElem?
  intro index
  by_cases first : index < dst
  · rw [List.setSlice!_getElem?_prefix _ _ _ _ first]
    exact outside index (Or.inl first)
  · by_cases last : dst+count ≤ index
    · rw [List.setSlice!_getElem?_suffix _ _ _ _ (by simp; omega)]
      exact outside index (Or.inr last)
    · rw [List.setSlice!_getElem?_middle _ _ _ _ (by simp; omega)]
      have equal : dst+(index-dst) = index := by omega
      simpa only [equal,List.getElem?_replicate,show index-dst<count from by omega,if_true] using filled (index-dst) (by omega)
end Itasca.Runtime.Spec.Segment

end

/-! ## References -/

section

namespace Itasca.Runtime.Spec
open SpecExt

def referenceIsNull : ref → Nat
  | .REF_NULL _ => 1
  | _ => 0

/-- Nullness follows the generated positive and negative pure reduction
rules, including the negative rule's exclusion premise. -/
theorem ref_is_null_pure (value : ref) :
    Step_pure [admininstr_ref value,.REF_IS_NULL] [Segment.i32 (referenceIsNull value)] := by
  cases value with
  | REF_NULL ty =>
    exact .ref_is_null_true _ ty rfl .admininstr_case_42 (Segment.i32_wf 1 (by decide))
  | REF_FUNC_ADDR address =>
    apply Step_pure.ref_is_null_false _ _ .admininstr_case_42 (Segment.i32_wf 0 (by decide))
    intro excluded
    generalize equation : [admininstr_ref (ref.REF_FUNC_ADDR address),admininstr.REF_IS_NULL] = instructions at excluded
    cases excluded with
    | ref_is_null_true_0 value ty equality opcode result => subst value; simp [admininstr_ref] at equation
  | REF_HOST_ADDR address =>
    apply Step_pure.ref_is_null_false _ _ .admininstr_case_42 (Segment.i32_wf 0 (by decide))
    intro excluded
    generalize equation : [admininstr_ref (ref.REF_HOST_ADDR address),admininstr.REF_IS_NULL] = instructions at excluded
    cases excluded with
    | ref_is_null_true_0 value ty equality opcode result => subst value; simp [admininstr_ref] at equation

theorem ref_is_null_step (s : store) (f : frame) (value : ref)
    (hs : wf_store s) (hf : wf_frame f) :
    StepH ⟨⟨s,f⟩,[admininstr_ref value,.REF_IS_NULL]⟩ []
      ⟨⟨s,f⟩,[Segment.i32 (referenceIsNull value)]⟩ := by
  refine StepH.step (Step.pure _ _ _ (ref_is_null_pure value) ?_ ?_)
  · apply wf_config_make hs hf
    simp only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨Segment.ref_wf value,.admininstr_case_42⟩
  · apply wf_config_make hs hf
    have bound : referenceIsNull value < 2^32 := by cases value <;> simp [referenceIsNull]
    simpa [Forall] using Segment.i32_wf _ bound
end Itasca.Runtime.Spec

end

/-! ## ReferenceFunction -/

section

namespace Itasca.Runtime.Spec
open SpecExt

/-- Source REF_FUNC resolves the function address in the current instance. -/
theorem ref_func_step (s : store) (f : frame) (index address : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hx : index < 2^32)
    (mapped : f.MODULE.FUNCS[index]? = some address) :
    StepH ⟨⟨s,f⟩,[.REF_FUNC (.mk_uN index)]⟩ []
      ⟨⟨s,f⟩,[.REF_FUNC_ADDR address]⟩ := by
  have input : wf_config ⟨⟨s,f⟩,[.REF_FUNC (.mk_uN index)]⟩ :=
    wf_config_make hs hf (by simpa [Forall] using wf_admininstr.admininstr_case_41 _ (Segment.index_wf _ hx))
  have output := wf_admininstr.admininstr_case_68 address
  have lookup : (fun_funcaddr ⟨s,f⟩)[index]! = address := by
    simp [fun_funcaddr,List.getElem!_eq_getElem?_getD,mapped]
  refine StepH.step (Step.read _ _ _ ?_ input (wf_config_make hs hf (by simpa [Forall] using output)))
  have step := Step_read.ref_func ⟨s,f⟩ (.mk_uN index)
    (by simpa [fun_funcaddr,proj_uN_0] using (List.getElem?_eq_some_iff.mp mapped).1) input
    (wf_admininstr.admininstr_case_68 _)
  simpa only [proj_uN_0,lookup] using step
end Itasca.Runtime.Spec

end

/-! ## TableWriteBounds -/

section

namespace Itasca.Runtime.Spec
open SpecExt

/-- The source table write reports its bounds trap before changing the store. -/
theorem table_set_trap_step (s : store) (f : frame) (index position : Nat) (value : ref)
    (hs : wf_store s) (hf : wf_frame f) (hx : index < 2^32) (hp : position < 2^32)
    (outside : (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length ≤ position) :
    StepH ⟨⟨s,f⟩,[Segment.i32 position,admininstr_ref value,.TABLE_SET (.mk_uN index)]⟩ []
      ⟨⟨s,f⟩,[.TRAP]⟩ := by
  apply StepH.step
  apply Step.table_set_trap
  · simp [proj_num__0]
  · exact outside
  · apply wf_config_make hs hf
    simp only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨Segment.i32_wf _ hp,Segment.ref_wf _,.admininstr_case_49 _ (Segment.index_wf _ hx)⟩
  · exact wf_config_make hs hf (by simpa [Forall] using wf_admininstr.admininstr_case_73)
end Itasca.Runtime.Spec

end

/-! ## FloatPromote -/

section

namespace Itasca.Runtime.Spec
open SpecExt SpecExt.Builtins.Float

theorem float_promote_relation (value : fN) :
    fun_cvtop__ .F32 .F64 (.mk_cvtop___3 .F32 .F64 .PROMOTE) (.mk_num__1 .F32 value)
      (some ((promote__ 32 64 value).map (num_.mk_num__1 .F64))) := by
  apply fun_cvtop__.fun_cvtop___case_22
  exact float_results_wf .F64 _ (float_demote_wf 32 64 (by omega) value)
end Itasca.Runtime.Spec

end
