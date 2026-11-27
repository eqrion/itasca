import Itasca.Runtime.Spec.TypingAndNumericOperations
import Mathlib.Tactic
import WebAssembly.Builtins.IntegerRepresentation
import WebAssembly.Builtins.Float.Representation
import WebAssembly.Builtins.Float.Comparison
import Aeneas.Data.List.List
import WebAssembly
import Itasca.Runtime.SourceMachine.Simulation
import Mathlib.Data.List.Forall2
import Itasca.Runtime.Spec.Simd.LaneOperations
import WebAssembly.Host

open WebAssembly

/-!
Proofs for Runtime / Spec.

This module collects ScalarOperations, PrimitiveOperations, ExecutionSupport.
Each section documents its contracts and consumers.
-/

/-! ## ScalarOperations -/

section

/-!
# Scalar Operations

Scalar numeric, memory and table operations satisfy their pinned specification rules.
-/

/-! ## TableInit -/

section

/-!
Source semantics of `table.init`. Connect the generated recursive rules to the bounded interval update used by runtime correspondence proofs.
-/

/-! ## Table Init Source -/

section

namespace Itasca.Spec.Segment
open WebAssembly

def tableWrite (s : store) (f : frame) (index position : Nat) (value : ref) : store :=
  {s with TABLES := s.TABLES.modify f.MODULE.TABLES[index]! (fun table =>
    {table with REFS := table.REFS.modify position (fun _ => value)})}

theorem forall_modify {T : Type} (p : T → Prop) (xs : List T) (index : Nat) (f : T → T)
    (all : Forall p xs) (preserve : ∀ x, p x → p (f x)) : Forall p (xs.modify index f) := by
  induction xs generalizing index with
  | nil => simp [Forall]
  | cons x xs ih =>
    have hx : p x := all x (by simp)
    have ht : Forall p xs := fun y hy => all y (by simp [hy])
    cases index with
    | zero =>
      change Forall p (f x :: xs)
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact preserve x hx
      · exact ht y hy
    | succ n =>
      change Forall p (x :: xs.modify n f)
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact ih n ht y hy

theorem table_write_wf (s : store) (f : frame) (index position : Nat) (value : ref)
    (hs : wf_store s) : wf_store (tableWrite s f index position value) := by
  cases s with | MKstore funcs globals tables mems elems datas =>
  cases hs with | store_case_ _ _ _ _ _ _ hfn hg ht hm hd =>
  apply wf_store.store_case_ _ _ _ _ _ _ hfn hg _ hm hd
  apply forall_modify _ _ _ _ ht
  intro table hw
  cases table
  cases hw
  constructor
  assumption

theorem ref_wf (value : ref) : wf_admininstr (admininstr_ref value) := by
  cases value <;> simp only [admininstr_ref] <;> constructor

theorem table_write_step (s : store) (f : frame) (index position : Nat) (value : ref)
    (hs : wf_store s) (hf : wf_frame f) (hp : position < 2^32) (hx : index < 2^32)
    (mapped : index < f.MODULE.TABLES.length)
    (inside : position < (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length) :
    StepH ⟨⟨s,f⟩,[i32 position,admininstr_ref value,.TABLE_SET (.mk_uN index)]⟩ []
      ⟨⟨tableWrite s f index position value,f⟩,[]⟩ := by
  have fresh := table_write_wf s f index position value hs
  apply StepH.step
  apply Step.table_set_val
  · simp [proj_num__0]
  · apply fun_with_table.fun_with_table_case_0
    · exact mapped
    · exact inside
    · exact .state_case_0 _ _ fresh hf
    · exact .state_case_0 _ _ hs hf
  · exact inside
  · apply wf_config_make hs hf
    simp only [Forall, List.mem_cons, List.not_mem_nil, false_implies, forall_const, and_true, forall_eq_or_imp]
    exact ⟨i32_wf _ hp, ref_wf _, .admininstr_case_49 _ (index_wf _ hx)⟩
  · exact wf_config_make fresh hf (by simp [Forall])

theorem table_init_expand (s : store) (f : frame) (destination source count tableIndex elementIndex : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination+1 < 2^32) (hi : source+1 < 2^32)
    (hn : count+1 < 2^32) (ht : tableIndex < 2^32) (he : elementIndex < 2^32)
    (inside : source+(count+1) ≤ (fun_elem ⟨s,f⟩ (.mk_uN elementIndex)).REFS.length ∧
      destination+(count+1) ≤ (fun_table ⟨s,f⟩ (.mk_uN tableIndex)).REFS.length) :
    StepH ⟨⟨s,f⟩,operands destination source (count+1) ++ [.TABLE_INIT (.mk_uN tableIndex) (.mk_uN elementIndex)]⟩ []
      ⟨⟨s,f⟩,[i32 destination,admininstr_ref ((fun_elem ⟨s,f⟩ (.mk_uN elementIndex)).REFS[source]!),.TABLE_SET (.mk_uN tableIndex)] ++
        (operands (destination+1) (source+1) count ++ [.TABLE_INIT (.mk_uN tableIndex) (.mk_uN elementIndex)])⟩ := by
  have tableWf : wf_admininstr (.TABLE_INIT (.mk_uN tableIndex) (.mk_uN elementIndex)) :=
    .admininstr_case_54 _ _ (index_wf _ ht) (index_wf _ he)
  have setWf : wf_admininstr (.TABLE_SET (.mk_uN tableIndex)) := .admininstr_case_49 _ (index_wf _ ht)
  have input := init_config_wf s f destination source (count+1) _ hs hf (by omega) (by omega) hn tableWf
  have output : wf_config ⟨⟨s,f⟩,[i32 destination,admininstr_ref ((fun_elem ⟨s,f⟩ (.mk_uN elementIndex)).REFS[source]!),.TABLE_SET (.mk_uN tableIndex)] ++
        (operands (destination+1) (source+1) count ++ [.TABLE_INIT (.mk_uN tableIndex) (.mk_uN elementIndex)])⟩ := by
    apply wf_config_make hs hf
    simp only [operands, List.cons_append, List.nil_append, Forall, List.mem_cons,
      List.not_mem_nil, false_implies, forall_const, and_true, forall_eq_or_imp]
    exact ⟨i32_wf _ (by omega),ref_wf _,setWf,i32_wf _ hd,i32_wf _ hi,i32_wf _ (by omega),tableWf⟩
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  have read := Step_read.table_init_succ ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN destination))
    (.mk_num__0 .I32 (.mk_uN source)) (count+1) (.mk_uN tableIndex) (.mk_uN elementIndex)
    (by simpa [proj_num__0,proj_uN_0] using (show source < (fun_elem ⟨s,f⟩ (.mk_uN elementIndex)).REFS.length by omega))
    (by simp [proj_num__0]) (by simp [proj_num__0]) (Nat.succ_ne_zero count) inside input
    (i32_wf _ (by omega)) setWf (i32_wf _ hd) (i32_wf _ hi)
    (by simpa [i32] using i32_wf count (by omega)) tableWf
  simpa [operands,i32,proj_num__0,proj_uN_0] using read

def tableInit (s : store) (f : frame) (tableIndex elementIndex destination source : Nat) : Nat → store
  | 0 => s
  | count+1 => tableInit
      (tableWrite s f tableIndex destination ((fun_elem ⟨s,f⟩ (.mk_uN elementIndex)).REFS[source]!))
      f tableIndex elementIndex (destination+1) (source+1) count

theorem table_write_table_length (s : store) (f : frame) (index position : Nat) (value : ref)
    (address : f.MODULE.TABLES[index]! < s.TABLES.length) :
    (fun_table ⟨tableWrite s f index position value,f⟩ (.mk_uN index)).REFS.length =
      (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length := by
  simp only [fun_table,tableWrite,proj_uN_0]
  generalize f.MODULE.TABLES[index]! = a at address ⊢
  simp [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem address]

theorem table_init_steps (s : store) (f : frame) (destination source count tableIndex elementIndex : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32)
    (hn : count < 2^32) (ht : tableIndex < 2^32) (he : elementIndex < 2^32)
    (mapped : tableIndex < f.MODULE.TABLES.length)
    (address : f.MODULE.TABLES[tableIndex]! < s.TABLES.length)
    (tableBound : (fun_table ⟨s,f⟩ (.mk_uN tableIndex)).REFS.length < 2^32)
    (elementBound : (fun_elem ⟨s,f⟩ (.mk_uN elementIndex)).REFS.length < 2^32)
    (inside : source+count ≤ (fun_elem ⟨s,f⟩ (.mk_uN elementIndex)).REFS.length ∧
      destination+count ≤ (fun_table ⟨s,f⟩ (.mk_uN tableIndex)).REFS.length) :
    StepsH ⟨⟨s,f⟩,operands destination source count ++ [.TABLE_INIT (.mk_uN tableIndex) (.mk_uN elementIndex)]⟩ []
      ⟨⟨tableInit s f tableIndex elementIndex destination source count,f⟩,[]⟩ := by
  induction count generalizing s destination source with
  | zero => exact steps_h_single (table_init_zero s f destination source tableIndex elementIndex hs hf hd hi ht he inside)
  | succ count ih =>
    have hd' : destination+1 < 2^32 := by omega
    have hi' : source+1 < 2^32 := by omega
    let value := (fun_elem ⟨s,f⟩ (.mk_uN elementIndex)).REFS[source]!
    let fresh := tableWrite s f tableIndex destination value
    have hw := table_write_wf s f tableIndex destination value hs
    have lengthEq := table_write_table_length s f tableIndex destination value address
    have afterWf := (wf_config_parts (init_config_wf fresh f (destination+1) (source+1) count _ hw hf hd' hi'
      (by omega) (.admininstr_case_54 _ _ (index_wf _ ht) (index_wf _ he)))).2
    have first := table_init_expand s f destination source count tableIndex elementIndex hs hf hd' hi' hn ht he inside
    have second := step_h_instrs (table_write_step s f tableIndex destination value hs hf hd ht mapped (by omega)) []
      (operands (destination+1) (source+1) count ++ [.TABLE_INIT (.mk_uN tableIndex) (.mk_uN elementIndex)])
      (by simp [Forall]) afterWf
    have rest := ih fresh (destination+1) (source+1) hw hd' hi' (by omega)
      (by simpa [fresh,tableWrite] using address)
      (by simpa only [fresh,lengthEq] using tableBound) elementBound
      (by rw [show (fun_table ⟨fresh,f⟩ (.mk_uN tableIndex)).REFS.length =
            (fun_table ⟨s,f⟩ (.mk_uN tableIndex)).REFS.length from lengthEq]
          simpa only [fresh,tableWrite,fun_elem,Nat.add_assoc,Nat.add_comm 1 count] using inside)
    have combined := steps_h_trans (steps_h_single first) (steps_h_trans (steps_h_single second) rest)
    simpa only [instrContext,vals,List.map_nil,List.nil_append,List.append_nil,tableInit,value,fresh] using combined

end Itasca.Spec.Segment

end

/-! ## Table Init Algebra -/

section

namespace Itasca.Spec.Segment
open WebAssembly

theorem table_init_eq (s : store) (f : frame) (tableIndex elementIndex destination source count : Nat) :
    tableInit s f tableIndex elementIndex destination source count =
      {s with TABLES := s.TABLES.modify f.MODULE.TABLES[tableIndex]! (fun table => {table with REFS := copyInto table.REFS (fun_elem ⟨s,f⟩ (.mk_uN elementIndex)).REFS destination source count})} := by
  induction count generalizing s destination source with
  | zero =>
    simp only [tableInit,copyInto]
    have identity : (fun table : tableinst => {table with REFS := table.REFS}) = id := by funext table; cases table; rfl
    rw [identity,List.modify_id]
  | succ count ih =>
    rw [tableInit,ih]
    simp only [tableWrite,fun_elem,proj_uN_0,List.modify_modify_eq,Function.comp_def,copyInto]
    congr 1
    congr 1
    funext table
    simp only [List.modify_eq_set]

end Itasca.Spec.Segment

end

end

/-! ## Globals -/

section

namespace Itasca.Spec
open WebAssembly

/-- Source global writes change a single value, retaining its declared type. -/
def globalWrite (s : store) (f : frame) (index : Nat) (value : val) : store :=
  {s with GLOBALS := s.GLOBALS.modify f.MODULE.GLOBALS[index]! (fun global => {global with VALUE := value})}

theorem global_write_wf (s : store) (f : frame) (index : Nat) (value : val)
    (hs : wf_store s) (hv : wf_val value) : wf_store (globalWrite s f index value) := by
  cases s with | MKstore funcs globals tables mems elems datas =>
  cases hs with | store_case_ _ _ _ _ _ _ hfn hg ht hm hd =>
  apply wf_store.store_case_ _ _ _ _ _ _ hfn _ ht hm hd
  apply Segment.forall_modify _ _ _ _ hg
  intro global _
  exact .globalinst_case_ _ _ hv

/-- The generated global-read rule resolves the exact instance/global lookup;
well-formedness of the selected value follows from the input store. -/
theorem global_get_step (s : store) (f : frame) (index address : Nat) (global : globalinst)
    (hs : wf_store s) (hf : wf_frame f) (hx : index < 2^32)
    (mapped : f.MODULE.GLOBALS[index]? = some address)
    (found : s.GLOBALS[address]? = some global) :
    StepH ⟨⟨s,f⟩,[.GLOBAL_GET (.mk_uN index)]⟩ []
      ⟨⟨s,f⟩,vals [global.VALUE]⟩ := by
  have hg : wf_globalinst global := by
    cases hs
    apply_assumption
    exact List.mem_of_getElem? found
  have hv : wf_val global.VALUE := by cases hg; assumption
  have input := wf_config_make hs hf (show Forall wf_admininstr [.GLOBAL_GET (.mk_uN index)] from by
    simpa [Forall] using wf_admininstr.admininstr_case_46 _ (Segment.index_wf index hx))
  have output := wf_config_vals hs hf (show Forall wf_val [global.VALUE] from by simpa [Forall] using hv)
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  simpa [fun_global, proj_uN_0, List.getElem!_eq_getElem?_getD, mapped, found, vals] using
    Step_read.global_get ⟨s,f⟩ (.mk_uN index) input

/-- The generated global-write rule, including source well-formedness of the
updated store. Mutability and value typing belong to instruction typing. -/
theorem global_set_step (s : store) (f : frame) (index : Nat) (value : val)
    (hs : wf_store s) (hf : wf_frame f) (hx : index < 2^32)
    (hv : wf_val value) (mapped : index < f.MODULE.GLOBALS.length) :
    StepH ⟨⟨s,f⟩,[admininstr_val value,.GLOBAL_SET (.mk_uN index)]⟩ []
      ⟨⟨globalWrite s f index value,f⟩,[]⟩ := by
  have outputWf := global_write_wf s f index value hs hv
  apply StepH.step
  apply Step.global_set
  · exact .fun_with_global_case_0 s f (.mk_uN index) value mapped
      (.state_case_0 _ _ outputWf hf)
  · apply wf_config_make hs hf
    intro instruction member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact wf_admininstr_val hv
    · exact .admininstr_case_47 _ (Segment.index_wf index hx)
  · exact wf_config_make outputWf hf (forall_nil _)
end Itasca.Spec

end

/-! ## ByteEncoding -/

section

namespace Itasca.Spec
open WebAssembly.Builtins

private theorem byte_value_bound (value : byte) (hw : wf_byte value) : proj_byte_0 value < 256 := by
  cases value
  cases hw
  simp only [proj_byte_0]
  omega

/-- Well-formed little-endian bytes fit their represented width. -/
theorem integer_of_bytes_bound (bytes : List byte) (valid : Forall wf_byte bytes) :
    integerOfBytes bytes < 256^bytes.length := by
  induction bytes with
  | nil => simp [integerOfBytes]
  | cons byte bytes ih =>
    have head := byte_value_bound byte (valid byte (by simp))
    have tail := ih (fun b member => valid b (by simp [member]))
    cases byte
    simp only [integerOfBytes, List.length_cons, Nat.pow_succ, proj_byte_0] at *
    omega

/-- Decoding and encoding an arbitrary well-formed byte string is exact,
including leading zero bytes. -/
theorem integer_bytes_of_bytes (bytes : List byte) (valid : Forall wf_byte bytes) :
    integerBytes bytes.length (integerOfBytes bytes) = bytes := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
    have head := byte_value_bound byte (valid byte (by simp))
    have tail := ih (fun b member => valid b (by simp [member]))
    cases byte with | mk_byte bits =>
    simp only [integerOfBytes, List.length_cons, integerBytes, proj_byte_0] at *
    have low : (bits + 256 * integerOfBytes bytes) % 256 = bits := by omega
    have high : (bits + 256 * integerOfBytes bytes) / 256 = integerOfBytes bytes := by omega
    rw [low,high,tail]

def scalarNumBytes : numtype → Nat
  | .I32 | .F32 => 4
  | .I64 | .F64 => 8

/-- The source numeric decoder and encoder are inverse for exactly sized byte
payloads, including every IEEE float bit pattern. -/
theorem numeric_bytes_roundtrip (ty : numtype) (bytes : List byte)
    (valid : Forall wf_byte bytes) (sized : bytes.length = scalarNumBytes ty) :
    nbytes_ ty (inv_nbytes_ ty bytes) = bytes := by
  have bounded := integer_of_bytes_bound bytes valid
  have roundtrip := integer_bytes_of_bytes bytes valid
  cases ty <;> simp only [scalarNumBytes] at sized
  · simpa [nbytes_,inv_nbytes_,ibytes_,inv_ibytes_,proj_uN_0,sized] using roundtrip
  · simpa [nbytes_,inv_nbytes_,ibytes_,inv_ibytes_,proj_uN_0,sized] using roundtrip
  · have bits : integerOfBytes bytes < 2^32 := by rw [sized] at bounded; norm_num at bounded ⊢; exact bounded
    simpa [nbytes_,inv_nbytes_,fbytes_,inv_fbytes_,Float.float_bits_roundtrip_32 _ bits,sized] using roundtrip
  · have bits : integerOfBytes bytes < 2^64 := by rw [sized] at bounded; norm_num at bounded ⊢; exact bounded
    simpa [nbytes_,inv_nbytes_,fbytes_,inv_fbytes_,Float.float_bits_roundtrip_64 _ bits,sized] using roundtrip
theorem numeric_bytes_wf (ty : numtype) (bytes : List byte)
    (valid : Forall wf_byte bytes) (sized : bytes.length = scalarNumBytes ty) :
    wf_num_ ty (inv_nbytes_ ty bytes) := by
  have bounded := integer_of_bytes_bound bytes valid
  cases ty <;> simp only [scalarNumBytes] at sized
  · apply wf_num_.num__case_0 .I32 .I32 _ (by decide) _ rfl
    apply wf_uN.uN_case_0
    rw [sized] at bounded
    norm_num [size,valtype_Inn,inv_ibytes_,proj_uN_0] at bounded ⊢
    omega
  · apply wf_num_.num__case_0 .I64 .I64 _ (by decide) _ rfl
    apply wf_uN.uN_case_0
    rw [sized] at bounded
    norm_num [size,valtype_Inn,inv_ibytes_,proj_uN_0] at bounded ⊢
    omega
  · apply wf_num_.num__case_1 .F32 .F32 _ _ rfl
    apply Float.float_of_bits_wf_32
    rw [sized] at bounded
    simpa using bounded
  · apply wf_num_.num__case_1 .F64 .F64 _ _ rfl
    apply Float.float_of_bits_wf_64
    rw [sized] at bounded
    simpa using bounded
end Itasca.Spec

end

/-! ## MemoryLoad -/

section

namespace Itasca.Spec
open WebAssembly

def numericLoadResult (ty : numtype) (bytes : List byte) (start : Nat) : List admininstr :=
  if start + scalarNumBytes ty ≤ bytes.length then
    [.CONST ty (inv_nbytes_ ty ((bytes.drop start).take (scalarNumBytes ty)))]
  else [.TRAP]

private theorem numeric_size_present (ty : numtype) : size (valtype_numtype ty) ≠ none := by
  cases ty <;> decide

private theorem numeric_byte_count (ty : numtype) :
    rat_to_nat ((Option.get! (size (valtype_numtype ty)) : Rat) / 8) = scalarNumBytes ty := by
  cases ty <;> norm_num [size,valtype_numtype,rat_to_nat,scalarNumBytes] <;> rfl

/-- A source numeric load returns the canonical little-endian decoding or takes
the generated bounds-trap rule. Both outcomes preserve the source store. -/
theorem numeric_load_step (s : store) (f : frame) (ty : numtype) (argument : memarg) (address : Nat)
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.LOAD ty none argument))
    (bytesWf : Forall wf_byte (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,.LOAD ty none argument]⟩ []
      ⟨⟨s,f⟩,numericLoadResult ty (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES
        (address + proj_uN_0 argument.OFFSET)⟩ := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr [Segment.i32 address,.LOAD ty none argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact operationWf)
  unfold numericLoadResult
  split
  · rename_i fits
    let bytes := (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES
    let start := address + proj_uN_0 argument.OFFSET
    have payloadWf : Forall wf_byte ((bytes.drop start).take (scalarNumBytes ty)) := by
      intro byte member
      exact bytesWf byte (List.mem_of_mem_drop (List.mem_of_mem_take member))
    have payloadLength : ((bytes.drop start).take (scalarNumBytes ty)).length = scalarNumBytes ty := by
      simp only [List.length_take,List.length_drop]
      dsimp only [bytes,start]
      omega
    have valueWf := numeric_bytes_wf ty _ payloadWf payloadLength
    have output := wf_config_make storeWf frameWf (show Forall wf_admininstr [.CONST ty (inv_nbytes_ ty ((bytes.drop start).take (scalarNumBytes ty)))] from by
      simpa [Forall] using wf_admininstr.admininstr_case_13 _ _ valueWf)
    apply StepH.step
    apply Step.read _ _ _ ?_ input output
    apply Step_read.load_num_val
    · simp [proj_num__0]
    · exact numeric_size_present ty
    · simpa only [numeric_byte_count,proj_num__0,proj_uN_0,Option.get!_some,bytes,start] using
        numeric_bytes_roundtrip ty _ payloadWf payloadLength
    · exact input
    · exact .admininstr_case_13 _ _ valueWf
    · exact Segment.index_wf 0 (by norm_num)
  · rename_i outside
    apply StepH.step
    apply Step.read _ _ _ ?_ input (wf_config_trap storeWf frameWf)
    apply Step_read.load_num_trap
    · simp [proj_num__0]
    · exact numeric_size_present ty
    · simpa only [numeric_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using Nat.lt_of_not_ge outside
    · exact input
    · exact .admininstr_case_73
    · exact Segment.index_wf 0 (by norm_num)
end Itasca.Spec

end

/-! ## SegmentCopySlice -/

section

namespace Itasca.Spec.Segment

/-- The sequential source writes copy the selected interval and preserve every
position outside it. The source list is independent of the destination. -/
theorem copy_into_effect {T : Type} [Inhabited T] (before source : List T) (dst src count : Nat)
    (sourceBound : src + count ≤ source.length) (targetBound : dst + count ≤ before.length) :
    (∀ j, j < count → (copyInto before source dst src count)[dst + j]? = source[src + j]?) ∧
    (∀ j, j < dst ∨ dst + count ≤ j → (copyInto before source dst src count)[j]? = before[j]?) := by
  induction count generalizing before dst src with
  | zero => simp [copyInto]
  | succ count ih =>
    obtain ⟨copied, outside⟩ := ih (before.set dst source[src]!) (dst+1) (src+1)
      (by omega) (by simpa using (show dst+1+count ≤ before.length by omega))
    constructor
    · intro j bound
      cases j with
      | zero =>
        have first := outside dst (Or.inl (by omega))
        have sourceInside : src < source.length := by omega
        have targetInside : dst < before.length := by omega
        simpa [copyInto, sourceInside, targetInside] using first
      | succ j =>
        have previous := copied j (by omega)
        simpa only [copyInto, Nat.add_assoc, Nat.add_comm 1 j] using previous
    · intro j bound
      have tailOutside := outside j (by omega)
      have distinct : dst ≠ j := by omega
      simpa only [copyInto, List.getElem?_set, distinct, if_false] using tailOutside

/-- Source byte-at-a-time initialization equals the slice replacement used by
the extracted memory-buffer operation. -/
theorem copy_into_eq_set_slice {T : Type} [Inhabited T] (before source : List T) (dst src count : Nat)
    (sourceBound : src + count ≤ source.length) (targetBound : dst + count ≤ before.length) :
    copyInto before source dst src count = before.setSlice! dst (source.slice src (src+count)) := by
  have sliceLength : (source.slice src (src+count)).length = count := by
    rw [List.slice_length]
    omega
  obtain ⟨copied, outside⟩ := copy_into_effect before source dst src count sourceBound targetBound
  apply List.ext_getElem?
  intro index
  by_cases first : index < dst
  · rw [List.setSlice!_getElem?_prefix _ _ _ _ first]
    exact outside index (Or.inl first)
  · by_cases last : dst+count ≤ index
    · rw [List.setSlice!_getElem?_suffix _ _ _ _ (by omega)]
      exact outside index (Or.inr last)
    · rw [List.setSlice!_getElem?_middle _ _ _ _ (by omega),
        List.getElem?_slice _ _ _ _ (by omega)]
      have equal : dst + (index-dst) = index := by omega
      simpa only [equal] using copied (index-dst) (by omega)
end Itasca.Spec.Segment

end

/-! ## SegmentDrops -/

section

namespace Itasca.Spec
open WebAssembly

def droppedDataStore (s : store) (f : frame) (index : Nat) : store :=
  {s with DATAS := s.DATAS.modify f.MODULE.DATAS[index]! (fun data => {data with BYTES := []})}

def droppedElementStore (s : store) (f : frame) (index : Nat) : store :=
  {s with ELEMS := s.ELEMS.modify f.MODULE.ELEMS[index]! (fun element => {element with REFS := []})}

theorem data_drop_step (s : store) (f : frame) (index : Nat)
    (old : wf_store s) (ambient : wf_frame f) (encoded : index < 2^32)
    (mapped : index < f.MODULE.DATAS.length) (fresh : wf_store (droppedDataStore s f index)) :
    StepH ⟨⟨s,f⟩,[.DATA_DROP (.mk_uN index)]⟩ [] ⟨⟨droppedDataStore s f index,f⟩,[]⟩ := by
  have update : fun_with_data ⟨s,f⟩ (.mk_uN index) [] ⟨droppedDataStore s f index,f⟩ :=
    .fun_with_data_case_0 s f (.mk_uN index) [] mapped (.state_case_0 _ _ fresh ambient)
  apply StepH.step
  apply Step.data_drop _ _ _ update
  · apply wf_config_make old ambient
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    exact .admininstr_case_67 _ (wf_uN.uN_case_0 32 index (by norm_num; omega))
  · exact wf_config_make fresh ambient (by simp [Forall])

theorem element_drop_step (s : store) (f : frame) (index : Nat)
    (old : wf_store s) (ambient : wf_frame f) (encoded : index < 2^32)
    (mapped : index < f.MODULE.ELEMS.length) (fresh : wf_store (droppedElementStore s f index)) :
    StepH ⟨⟨s,f⟩,[.ELEM_DROP (.mk_uN index)]⟩ [] ⟨⟨droppedElementStore s f index,f⟩,[]⟩ := by
  have update : fun_with_elem ⟨s,f⟩ (.mk_uN index) [] ⟨droppedElementStore s f index,f⟩ :=
    .fun_with_elem_case_0 s f (.mk_uN index) [] mapped (.state_case_0 _ _ fresh ambient)
  apply StepH.step
  apply Step.elem_drop _ _ _ update
  · apply wf_config_make old ambient
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    exact .admininstr_case_55 _ (wf_uN.uN_case_0 32 index (by norm_num; omega))
  · exact wf_config_make fresh ambient (by simp [Forall])

end Itasca.Spec

end

/-! ## IntegerDeterminism -/

section

namespace Itasca.Spec

theorem signed_deterministic {width bits : Nat} {left right : Int}
    (first : fun_signed_ width bits left) (second : fun_signed_ width bits right) : left = right := by
  cases first <;> cases second <;> first | rfl | omega

theorem inv_signed_deterministic {width : Nat} {bits : Int} {left right : Nat}
    (first : fun_inv_signed_ width bits left) (second : fun_inv_signed_ width bits right) : left = right := by
  cases first <;> cases second <;> first | rfl | omega

theorem idiv_deterministic {width : Nat} {sign : sx} {a b : uN} {left right : Option uN}
    (first : fun_idiv_ width sign a b left) (second : fun_idiv_ width sign a b right) : left = right := by
  cases first <;> cases second
  all_goals first | rfl | simp_all only [proj_uN_0, ne_eq, not_true_eq_false]
  all_goals grind only [signed_deterministic, inv_signed_deterministic]

theorem irem_deterministic {width : Nat} {sign : sx} {a b : uN} {left right : Option uN}
    (first : fun_irem_ width sign a b left) (second : fun_irem_ width sign a b right) : left = right := by
  cases first <;> cases second
  all_goals first | rfl | simp_all only [proj_uN_0, ne_eq, not_true_eq_false]
  all_goals grind only [signed_deterministic, inv_signed_deterministic]
theorem integer_binop_deterministic {ty : Inn} {op : binop_Inn} {a b : uN}
    {left right : List num_}
    (first : fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty op) (.mk_num__0 ty a) (.mk_num__0 ty b) (some left))
    (second : fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty op) (.mk_num__0 ty a) (.mk_num__0 ty b) (some right)) : left = right := by
  cases ty <;> cases first <;> cases second
  all_goals first | rfl | skip
  all_goals try casesm* fun_iadd_ .., fun_isub_ .., fun_imul_ ..
  all_goals first | rfl | grind only [idiv_deterministic, irem_deterministic]
theorem integer_unop_deterministic {ty : Inn} {op : unop_Inn} {a : uN}
    {left right : List num_}
    (first : fun_unop_ (numtype_Inn ty) (.mk_unop__0 ty op) (.mk_num__0 ty a) (some left))
    (second : fun_unop_ (numtype_Inn ty) (.mk_unop__0 ty op) (.mk_num__0 ty a) (some right)) : left = right := by
  cases ty <;> cases first <;> cases second <;> rfl

theorem integer_relop_deterministic {ty : Inn} {op : relop_Inn} {a b : uN}
    {left right : num_}
    (first : fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty op) (.mk_num__0 ty a) (.mk_num__0 ty b) (some left))
    (second : fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty op) (.mk_num__0 ty a) (.mk_num__0 ty b) (some right)) : left = right := by
  cases ty <;> cases first <;> cases second
  all_goals try casesm* fun_ieq_ .., fun_ine_ .., fun_ilt_ .., fun_igt_ .., fun_ile_ .., fun_ige_ ..
  all_goals first | rfl | grind only [signed_deterministic]

theorem integer_cvtop_deterministic {source target : Inn} {op : cvtop__Inn_1_Inn_2} {a : uN}
    {left right : List num_}
    (first : fun_cvtop__ (numtype_Inn source) (numtype_Inn target) (.mk_cvtop___0 source target op) (.mk_num__0 source a) (some left))
    (second : fun_cvtop__ (numtype_Inn source) (numtype_Inn target) (.mk_cvtop___0 source target op) (.mk_num__0 source a) (some right)) : left = right := by
  cases source <;> cases target <;> cases first <;> cases second <;> rfl
end Itasca.Spec

end

/-! ## FloatPure -/

section

namespace Itasca.Spec
open WebAssembly

/-- A concrete member of a permitted float result list takes one generated step. -/
theorem float_unary_pure (ty : Fnn) (op : unop_Fnn) (a result : fN)
    (allowed : List fN)
    (relation : fun_unop_ (numtype_Fnn ty) (.mk_unop__1 ty op) (.mk_num__1 ty a)
      (some (allowed.map (num_.mk_num__1 ty))))
    (chosen : result ∈ allowed)
    (inputWf : wf_fN (sizenn (numtype_Fnn ty)) a)
    (resultWf : wf_fN (sizenn (numtype_Fnn ty)) result) :
    Step_pure [.CONST (numtype_Fnn ty) (.mk_num__1 ty a),
      .UNOP (numtype_Fnn ty) (.mk_unop__1 ty op)]
      [.CONST (numtype_Fnn ty) (.mk_num__1 ty result)] := by
  apply Step_pure.unop_val _ _ _ _ _ relation
  · simpa using List.length_pos_of_mem chosen
  · simp
  · simp only [Option.get!_some, List.contains_iff_mem]
    exact List.mem_map.mpr ⟨result, chosen, rfl⟩
  · exact wf_admininstr_val (.val_case_0 _ _ (float_num_wf ty a inputWf))
  · exact wf_admininstr_instr (.instr_case_14 _ _ (.unop__case_1 _ _ _ rfl))
  · exact wf_admininstr_val (.val_case_0 _ _ (float_num_wf ty result resultWf))

/-- Float binary operators retain the source specification's permitted choices. -/
theorem float_binary_pure (ty : Fnn) (op : binop_Fnn) (a b result : fN)
    (allowed : List fN)
    (relation : fun_binop_ (numtype_Fnn ty) (.mk_binop__1 ty op)
      (.mk_num__1 ty a) (.mk_num__1 ty b) (some (allowed.map (num_.mk_num__1 ty))))
    (chosen : result ∈ allowed)
    (inputWf : wf_fN (sizenn (numtype_Fnn ty)) a)
    (secondWf : wf_fN (sizenn (numtype_Fnn ty)) b)
    (resultWf : wf_fN (sizenn (numtype_Fnn ty)) result) :
    Step_pure [.CONST (numtype_Fnn ty) (.mk_num__1 ty a),
      .CONST (numtype_Fnn ty) (.mk_num__1 ty b),
      .BINOP (numtype_Fnn ty) (.mk_binop__1 ty op)]
      [.CONST (numtype_Fnn ty) (.mk_num__1 ty result)] := by
  apply Step_pure.binop_val _ _ _ _ _ _ relation
  · simpa using List.length_pos_of_mem chosen
  · simp
  · simp only [Option.get!_some, List.contains_iff_mem]
    exact List.mem_map.mpr ⟨result, chosen, rfl⟩
  · exact wf_admininstr_val (.val_case_0 _ _ (float_num_wf ty a inputWf))
  · exact wf_admininstr_val (.val_case_0 _ _ (float_num_wf ty b secondWf))
  · exact wf_admininstr_instr (.instr_case_15 _ _ (.binop__case_1 _ _ _ rfl))
  · exact wf_admininstr_val (.val_case_0 _ _ (float_num_wf ty result resultWf))
end Itasca.Spec

end

/-! ## FloatComparison -/

section

namespace Itasca.Spec
open WebAssembly

/-- A checked floating comparison reduces to its exact i32 Boolean result. -/
theorem float_comparison_pure (ty : Fnn) (op : relop_Fnn) (a b : fN) (value : Nat)
    (relation : fun_relop_ (numtype_Fnn ty) (.mk_relop__1 ty op)
      (.mk_num__1 ty a) (.mk_num__1 ty b) (some (.mk_num__0 .I32 (.mk_uN value))))
    (ha : wf_fN (sizenn (numtype_Fnn ty)) a) (hb : wf_fN (sizenn (numtype_Fnn ty)) b)
    (bound : value < 2 ^ 32) :
    Step_pure [.CONST (numtype_Fnn ty) (.mk_num__1 ty a),
      .CONST (numtype_Fnn ty) (.mk_num__1 ty b),
      .RELOP (numtype_Fnn ty) (.mk_relop__1 ty op)]
      [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value))] := by
  have wf := unsigned_num_wf .I32 value bound
  apply Step_pure.relop _ _ _ _ _ _ relation
  · simp
  · rfl
  · exact wf
  · exact wf_admininstr_val (.val_case_0 _ _ (float_num_wf ty a ha))
  · exact wf_admininstr_val (.val_case_0 _ _ (float_num_wf ty b hb))
  · exact wf_admininstr_instr (.instr_case_17 _ _ (.relop__case_1 _ _ _ rfl))
  · exact wf_admininstr_val (.val_case_0 _ _ wf)

end Itasca.Spec

end

/-! ## FloatMinMax -/

section

namespace Itasca.Spec
open WebAssembly WebAssembly.Builtins WebAssembly.Builtins.Float

theorem float_min_wf (width : Nat) (hw : width = 32 ∨ width = 64) (a b : fN)
    (ha : wf_fN width a) (hb : wf_fN width b) :
    Forall (wf_fN width) (fmin_ width a b) := by
  unfold fmin_
  split_ifs
  · exact nans_wf width hw _
  · exact singleton_wf (with_sign_wf (zero_wf width) _)
  · exact singleton_wf ha
  · exact singleton_wf hb

theorem float_max_wf (width : Nat) (hw : width = 32 ∨ width = 64) (a b : fN)
    (ha : wf_fN width a) (hb : wf_fN width b) :
    Forall (wf_fN width) (fmax_ width a b) := by
  unfold fmax_
  split_ifs
  · exact nans_wf width hw _
  · exact singleton_wf (with_sign_wf (zero_wf width) _)
  · exact singleton_wf hb
  · exact singleton_wf ha

theorem float_f32_min_relation (a b : fN) (ha : wf_fN 32 a) (hb : wf_fN 32 b) :
    fun_binop_ .F32 (.mk_binop__1 .F32 .MIN) (.mk_num__1 .F32 a) (.mk_num__1 .F32 b)
      (some ((fmin_ 32 a b).map (num_.mk_num__1 .F32))) := by
  apply fun_binop_.fun_binop__case_32
  · exact float_min_wf 32 (by omega) a b ha hb
  · exact float_results_wf .F32 _ (float_min_wf 32 (by omega) a b ha hb)

theorem float_f32_max_relation (a b : fN) (ha : wf_fN 32 a) (hb : wf_fN 32 b) :
    fun_binop_ .F32 (.mk_binop__1 .F32 .MAX) (.mk_num__1 .F32 a) (.mk_num__1 .F32 b)
      (some ((fmax_ 32 a b).map (num_.mk_num__1 .F32))) := by
  apply fun_binop_.fun_binop__case_34
  · exact float_max_wf 32 (by omega) a b ha hb
  · exact float_results_wf .F32 _ (float_max_wf 32 (by omega) a b ha hb)

theorem float_f64_min_relation (a b : fN) (ha : wf_fN 64 a) (hb : wf_fN 64 b) :
    fun_binop_ .F64 (.mk_binop__1 .F64 .MIN) (.mk_num__1 .F64 a) (.mk_num__1 .F64 b)
      (some ((fmin_ 64 a b).map (num_.mk_num__1 .F64))) := by
  apply fun_binop_.fun_binop__case_33
  · exact float_min_wf 64 (by omega) a b ha hb
  · exact float_results_wf .F64 _ (float_min_wf 64 (by omega) a b ha hb)

theorem float_f64_max_relation (a b : fN) (ha : wf_fN 64 a) (hb : wf_fN 64 b) :
    fun_binop_ .F64 (.mk_binop__1 .F64 .MAX) (.mk_num__1 .F64 a) (.mk_num__1 .F64 b)
      (some ((fmax_ 64 a b).map (num_.mk_num__1 .F64))) := by
  apply fun_binop_.fun_binop__case_35
  · exact float_max_wf 64 (by omega) a b ha hb
  · exact float_results_wf .F64 _ (float_max_wf 64 (by omega) a b ha hb)

end Itasca.Spec

end

/-! ## FloatConvert -/

section

namespace Itasca.Spec
open WebAssembly WebAssembly.Builtins WebAssembly.Builtins.Float

/-- Integer conversion uses the concrete rational rounding definition. -/
theorem float_convert_relation (source : Inn) (target : Fnn) (sign : sx) (bits : Nat) :
    fun_cvtop__ (numtype_Inn source) (numtype_Fnn target)
      (.mk_cvtop___1 source target (.CONVERT sign)) (.mk_num__0 source (.mk_uN bits))
      (some [.mk_num__1 target (convert__ (sizenn (numtype_Inn source))
        (sizenn (numtype_Fnn target)) sign (.mk_uN bits))]) := by
  have wf : wf_num_ (numtype_Fnn target) (.mk_num__1 target
      (convert__ (sizenn (numtype_Inn source)) (sizenn (numtype_Fnn target)) sign (.mk_uN bits))) := by
    apply float_num_wf
    unfold convert__
    exact round_wf _ (by cases target <;> decide) _ _
  cases source <;> cases target
  · exact .fun_cvtop___case_16 sign _ wf
  · exact .fun_cvtop___case_18 sign _ wf
  · exact .fun_cvtop___case_17 sign _ wf
  · exact .fun_cvtop___case_19 sign _ wf

/-- The generic generated conversion step, preserving all permitted results. -/
theorem numeric_conversion_pure (source target : numtype) (op : cvtop__) (input result : num_)
    (allowed : List num_) (relation : fun_cvtop__ source target op input (some allowed))
    (chosen : result ∈ allowed) (inputWf : wf_num_ source input)
    (resultWf : wf_num_ target result) (opWf : wf_cvtop__ source target op) (different : target ≠ source) :
    Step_pure [.CONST source input, .CVTOP target source op] [.CONST target result] := by
  apply Step_pure.cvtop_val _ _ _ _ _ _ relation
  · simpa using List.length_pos_of_mem chosen
  · simp
  · simpa using chosen
  · exact wf_admininstr_val (.val_case_0 _ _ inputWf)
  · exact wf_admininstr_instr (.instr_case_18 _ _ _ opWf different)
  · exact wf_admininstr_val (.val_case_0 _ _ resultWf)
end Itasca.Spec
namespace Itasca.Spec
open WebAssembly WebAssembly.Builtins WebAssembly.Builtins.Float

theorem float_special_wf (target : Nat) (value : fN)
    (special : isInf value || isZero value) : wf_fN target value := by
  have choice : magnitude value = .INF ∨ magnitude value = .SUBNORM 0 := by
    simpa only [isInf, isZero, Bool.or_eq_true, beq_iff_eq] using special
  cases value <;> simp only [magnitude] at choice
  all_goals rcases choice with rfl | rfl
  all_goals first
    | exact .fN_case_0 _ _ (.fNmag_case_2 _)
    | exact .fN_case_1 _ _ (.fNmag_case_2 _)
    | exact .fN_case_0 _ _ (zero_wf target)
    | exact .fN_case_1 _ _ (zero_wf target)

theorem float_demote_wf (source target : Nat) (width : target = 32 ∨ target = 64)
    (value : fN) : Forall (wf_fN target) (demote__ source target value) := by
  unfold demote__
  split_ifs with hn hc hs
  · exact canonical_nans_wf target width
  · exact arithmetic_nans_wf target width
  · exact singleton_wf (float_special_wf target value hs)
  · exact singleton_wf (round_wf target width _ _)

theorem float_demote_relation (value : fN) :
    fun_cvtop__ .F64 .F32 (.mk_cvtop___3 .F64 .F32 .DEMOTE) (.mk_num__1 .F64 value)
      (some ((demote__ 64 32 value).map (num_.mk_num__1 .F32))) := by
  apply fun_cvtop__.fun_cvtop___case_25
  exact float_results_wf .F32 _ (float_demote_wf 64 32 (by omega) value)

theorem float_convert_pure (source : Inn) (target : Fnn) (sign : sx) (bits : Nat)
    (bound : bits < 2 ^ sizenn (numtype_Inn source)) (result : fN)
    (chosen : result ∈ [convert__ (sizenn (numtype_Inn source)) (sizenn (numtype_Fnn target)) sign (.mk_uN bits)]) :
    Step_pure [.CONST (numtype_Inn source) (.mk_num__0 source (.mk_uN bits)),
      .CVTOP (numtype_Fnn target) (numtype_Inn source) (.mk_cvtop___1 source target (.CONVERT sign))]
      [.CONST (numtype_Fnn target) (.mk_num__1 target result)] := by
  simp only [List.mem_singleton] at chosen
  subst result
  apply numeric_conversion_pure _ _ _ _ _ _ (float_convert_relation source target sign bits)
  · simp
  · exact unsigned_num_wf source bits bound
  · apply float_num_wf
    exact round_wf _ (by cases target <;> decide) _ _
  · exact .cvtop___case_1 _ _ _ _ _ (.cvtop__Inn_1_Fnn_2_case_0 _ _ _) rfl rfl
  · cases source <;> cases target <;> decide
end Itasca.Spec

end

/-! ## FloatReinterpret -/

section

namespace Itasca.Spec
open WebAssembly WebAssembly.Builtins WebAssembly.Builtins.Float

theorem f32_reinterpret_i32_pure (bits : Nat) (bound : bits < 2 ^ 32) :
    Step_pure [.CONST .I32 (.mk_num__0 .I32 (.mk_uN bits)), .CVTOP .F32 .I32 (.mk_cvtop___1 .I32 .F32 .REINTERPRET)]
      [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 bits))] := by
  have iw := unsigned_num_wf .I32 bits bound
  have fw := float_num_wf .F32 _ (float_of_bits_wf 32 (by omega) bits)
  have relation : fun_cvtop__ .I32 .F32 (.mk_cvtop___1 .I32 .F32 .REINTERPRET) (.mk_num__0 .I32 (.mk_uN bits))
      (some [(.mk_num__1 .F32 (floatOfBits 32 bits))]) := by
    exact .fun_cvtop___case_28 _ (by decide) (by decide) (by decide) iw
  apply numeric_conversion_pure _ _ _ _ _ _ relation
  · simp
  · exact iw
  · exact fw
  · exact .cvtop___case_1 _ _ _ _ _ (.cvtop__Inn_1_Fnn_2_case_1 _ _ (by decide)) rfl rfl
  · decide

theorem i32_reinterpret_f32_pure (bits : Nat) (bound : bits < 2 ^ 32) :
    Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 bits)), .CVTOP .I32 .F32 (.mk_cvtop___2 .F32 .I32 .REINTERPRET)]
      [.CONST .I32 (.mk_num__0 .I32 (.mk_uN bits))] := by
  have iw := unsigned_num_wf .I32 bits bound
  have fw := float_num_wf .F32 _ (float_of_bits_wf 32 (by omega) bits)
  have relation : fun_cvtop__ .F32 .I32 (.mk_cvtop___2 .F32 .I32 .REINTERPRET) (.mk_num__1 .F32 (floatOfBits 32 bits))
      (some [(.mk_num__0 .I32 (.mk_uN bits))]) := by
    have same := float_bits_roundtrip_32 bits bound
    simpa only [reinterpret__, numtype_Fnn, numtype_Inn, same] using
      fun_cvtop__.fun_cvtop___case_32 _ (by decide) (by decide) (by decide) fw
  apply numeric_conversion_pure _ _ _ _ _ _ relation
  · simp
  · exact fw
  · exact iw
  · exact .cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_2 _ _ (by decide)) rfl rfl
  · decide

theorem f64_reinterpret_i64_pure (bits : Nat) (bound : bits < 2 ^ 64) :
    Step_pure [.CONST .I64 (.mk_num__0 .I64 (.mk_uN bits)), .CVTOP .F64 .I64 (.mk_cvtop___1 .I64 .F64 .REINTERPRET)]
      [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 bits))] := by
  have iw := unsigned_num_wf .I64 bits bound
  have fw := float_num_wf .F64 _ (float_of_bits_wf 64 (by omega) bits)
  have relation : fun_cvtop__ .I64 .F64 (.mk_cvtop___1 .I64 .F64 .REINTERPRET) (.mk_num__0 .I64 (.mk_uN bits))
      (some [(.mk_num__1 .F64 (floatOfBits 64 bits))]) := by
    exact .fun_cvtop___case_31 _ (by decide) (by decide) (by decide) iw
  apply numeric_conversion_pure _ _ _ _ _ _ relation
  · simp
  · exact iw
  · exact fw
  · exact .cvtop___case_1 _ _ _ _ _ (.cvtop__Inn_1_Fnn_2_case_1 _ _ (by decide)) rfl rfl
  · decide

theorem i64_reinterpret_f64_pure (bits : Nat) (bound : bits < 2 ^ 64) :
    Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 bits)), .CVTOP .I64 .F64 (.mk_cvtop___2 .F64 .I64 .REINTERPRET)]
      [.CONST .I64 (.mk_num__0 .I64 (.mk_uN bits))] := by
  have iw := unsigned_num_wf .I64 bits bound
  have fw := float_num_wf .F64 _ (float_of_bits_wf 64 (by omega) bits)
  have relation : fun_cvtop__ .F64 .I64 (.mk_cvtop___2 .F64 .I64 .REINTERPRET) (.mk_num__1 .F64 (floatOfBits 64 bits))
      (some [(.mk_num__0 .I64 (.mk_uN bits))]) := by
    have same := float_bits_roundtrip_64 bits bound
    simpa only [reinterpret__, numtype_Fnn, numtype_Inn, same] using
      fun_cvtop__.fun_cvtop___case_35 _ (by decide) (by decide) (by decide) fw
  apply numeric_conversion_pure _ _ _ _ _ _ relation
  · simp
  · exact fw
  · exact iw
  · exact .cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_2 _ _ (by decide)) rfl rfl
  · decide

end Itasca.Spec

end

/-! ## FloatSigns -/

section

namespace Itasca.Spec
open WebAssembly WebAssembly.Builtins.Float

theorem float_abs_wf (width : Nat) (a : fN) (ha : wf_fN width a) :
    Forall (wf_fN width) (fabs_ width a) := by
  apply singleton_wf
  exact .fN_case_0 _ _ (magnitude_wf ha)

theorem float_neg_wf (width : Nat) (a : fN) (ha : wf_fN width a) :
    Forall (wf_fN width) (fneg_ width a) := by
  exact singleton_wf (with_sign_wf (magnitude_wf ha) _)

theorem float_copysign_wf (width : Nat) (a b : fN) (ha : wf_fN width a) :
    Forall (wf_fN width) (fcopysign_ width a b) := by
  exact singleton_wf (with_sign_wf (magnitude_wf ha) _)

theorem float_f32_abs_relation (a : fN) (ha : wf_fN 32 a) :
    fun_unop_ .F32 (.mk_unop__1 .F32 .ABS) (.mk_num__1 .F32 a)
      (some ((fabs_ 32 a).map (num_.mk_num__1 .F32))) := by
  apply fun_unop_.fun_unop__case_8
  exact float_results_wf .F32 _ (float_abs_wf 32 a ha)

theorem float_f32_neg_relation (a : fN) (ha : wf_fN 32 a) :
    fun_unop_ .F32 (.mk_unop__1 .F32 .NEG) (.mk_num__1 .F32 a)
      (some ((fneg_ 32 a).map (num_.mk_num__1 .F32))) := by
  apply fun_unop_.fun_unop__case_10
  exact float_results_wf .F32 _ (float_neg_wf 32 a ha)

theorem float_f32_copysign_relation (a b : fN) (ha : wf_fN 32 a) :
    fun_binop_ .F32 (.mk_binop__1 .F32 .COPYSIGN) (.mk_num__1 .F32 a) (.mk_num__1 .F32 b)
      (some ((fcopysign_ 32 a b).map (num_.mk_num__1 .F32))) := by
  apply fun_binop_.fun_binop__case_36
  · exact float_copysign_wf 32 a b ha
  · exact float_results_wf .F32 _ (float_copysign_wf 32 a b ha)

theorem float_f64_abs_relation (a : fN) (ha : wf_fN 64 a) :
    fun_unop_ .F64 (.mk_unop__1 .F64 .ABS) (.mk_num__1 .F64 a)
      (some ((fabs_ 64 a).map (num_.mk_num__1 .F64))) := by
  apply fun_unop_.fun_unop__case_9
  exact float_results_wf .F64 _ (float_abs_wf 64 a ha)

theorem float_f64_neg_relation (a : fN) (ha : wf_fN 64 a) :
    fun_unop_ .F64 (.mk_unop__1 .F64 .NEG) (.mk_num__1 .F64 a)
      (some ((fneg_ 64 a).map (num_.mk_num__1 .F64))) := by
  apply fun_unop_.fun_unop__case_11
  exact float_results_wf .F64 _ (float_neg_wf 64 a ha)

theorem float_f64_copysign_relation (a b : fN) (ha : wf_fN 64 a) :
    fun_binop_ .F64 (.mk_binop__1 .F64 .COPYSIGN) (.mk_num__1 .F64 a) (.mk_num__1 .F64 b)
      (some ((fcopysign_ 64 a b).map (num_.mk_num__1 .F64))) := by
  apply fun_binop_.fun_binop__case_37
  · exact float_copysign_wf 64 a b ha
  · exact float_results_wf .F64 _ (float_copysign_wf 64 a b ha)
end Itasca.Spec

end

/-! ## FloatTrunc -/

section

namespace Itasca.Spec
open WebAssembly WebAssembly.Builtins WebAssembly.Builtins.Float

theorem encode_signed_num_wf (target : Inn) (value : Int) :
    wf_num_ (numtype_Inn target) (.mk_num__0 target (encodeSigned (sizenn (numtype_Inn target)) value)) := by
  have bound := (BitVec.ofInt (sizenn (numtype_Inn target)) value).isLt
  apply unsigned_num_wf
  simpa [encodeSigned, BitVec.toNat_ofInt] using bound

theorem saturate_num_wf (target : Inn) (sign : sx) (value : Int) :
    wf_num_ (numtype_Inn target) (.mk_num__0 target (saturate (sizenn (numtype_Inn target)) sign value)) := by
  cases sign with
  | S =>
    unfold saturate
    exact encode_signed_num_wf target _
  | U =>
    unfold saturate
    apply unsigned_num_wf
    have positive : (0:Int) < 2^(sizenn (numtype_Inn target)) := by positivity
    have upper : max 0 (min value ((2:Int)^(sizenn (numtype_Inn target))-1)) < 2^(sizenn (numtype_Inn target)) := by omega
    have nonnegative : (0:Int) ≤ max 0 (min value ((2:Int)^(sizenn (numtype_Inn target))-1)) := by omega
    rw [Int.toNat_lt nonnegative]
    exact_mod_cast upper

theorem float_trunc_results_wf (source : Nat) (target : Inn) (sign : sx) (value : fN) :
    Forall (fun result => wf_num_ (numtype_Inn target) (.mk_num__0 target result))
      (trunc__ source (sizenn (numtype_Inn target)) sign value).toList := by
  unfold trunc__
  split
  · simp [Forall]
  · split <;> simp [Forall, encode_signed_num_wf]

theorem float_trunc_sat_results_wf (source : Nat) (target : Inn) (sign : sx) (value : fN) :
    Forall (fun result => wf_num_ (numtype_Inn target) (.mk_num__0 target result))
      (trunc_sat__ source (sizenn (numtype_Inn target)) sign value).toList := by
  unfold trunc_sat__
  split
  · simp only [Option.toList_some, Forall, List.mem_singleton, forall_eq]
    exact unsigned_num_wf target 0 (by positivity)
  · split <;> simp [Forall, saturate_num_wf]

theorem option_list_map (f : α → β) (value : Option α) :
    list_ β (OMap f value) = value.toList.map f := by cases value <;> rfl

theorem float_trunc_relation (source : Fnn) (target : Inn) (sign : sx) (value : fN) :
    fun_cvtop__ (numtype_Fnn source) (numtype_Inn target)
      (.mk_cvtop___2 source target (.TRUNC sign)) (.mk_num__1 source value)
      (some ((trunc__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign value).toList.map (num_.mk_num__0 target))) := by
  have wf := float_trunc_results_wf (sizenn (numtype_Fnn source)) target sign value
  cases source <;> cases target
  · simpa only [option_list_map, sizenn, sizenn1, sizenn2, numtype_Inn, numtype_Fnn, valtype_numtype, size, Option.get!] using fun_cvtop__.fun_cvtop___case_8 sign value wf
  · simpa only [option_list_map, sizenn, sizenn1, sizenn2, numtype_Inn, numtype_Fnn, valtype_numtype, size, Option.get!] using fun_cvtop__.fun_cvtop___case_10 sign value wf
  · simpa only [option_list_map, sizenn, sizenn1, sizenn2, numtype_Inn, numtype_Fnn, valtype_numtype, size, Option.get!] using fun_cvtop__.fun_cvtop___case_9 sign value wf
  · simpa only [option_list_map, sizenn, sizenn1, sizenn2, numtype_Inn, numtype_Fnn, valtype_numtype, size, Option.get!] using fun_cvtop__.fun_cvtop___case_11 sign value wf

theorem float_trunc_sat_relation (source : Fnn) (target : Inn) (sign : sx) (value : fN) :
    fun_cvtop__ (numtype_Fnn source) (numtype_Inn target)
      (.mk_cvtop___2 source target (.TRUNC_SAT sign)) (.mk_num__1 source value)
      (some ((trunc_sat__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign value).toList.map (num_.mk_num__0 target))) := by
  have wf := float_trunc_sat_results_wf (sizenn (numtype_Fnn source)) target sign value
  cases source <;> cases target
  · simpa only [option_list_map, sizenn, sizenn1, sizenn2, numtype_Inn, numtype_Fnn, valtype_numtype, size, Option.get!] using fun_cvtop__.fun_cvtop___case_12 sign value wf
  · simpa only [option_list_map, sizenn, sizenn1, sizenn2, numtype_Inn, numtype_Fnn, valtype_numtype, size, Option.get!] using fun_cvtop__.fun_cvtop___case_14 sign value wf
  · simpa only [option_list_map, sizenn, sizenn1, sizenn2, numtype_Inn, numtype_Fnn, valtype_numtype, size, Option.get!] using fun_cvtop__.fun_cvtop___case_13 sign value wf
  · simpa only [option_list_map, sizenn, sizenn1, sizenn2, numtype_Inn, numtype_Fnn, valtype_numtype, size, Option.get!] using fun_cvtop__.fun_cvtop___case_15 sign value wf

theorem float_truncation_pure (source : Fnn) (target : Inn) (sign : sx) (saturating : Bool)
    (value : fN) (expected : Option iN)
    (conversion : (if saturating then trunc_sat__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign value
      else trunc__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign value) = expected)
    (inputWf : wf_fN (sizenn (numtype_Fnn source)) value) :
    Step_pure [.CONST (numtype_Fnn source) (.mk_num__1 source value),
      .CVTOP (numtype_Inn target) (numtype_Fnn source)
        (.mk_cvtop___2 source target (if saturating then .TRUNC_SAT sign else .TRUNC sign))]
      (match expected with
       | some result => [.CONST (numtype_Inn target) (.mk_num__0 target result)]
       | none => [.TRAP]) := by
  have relation : fun_cvtop__ (numtype_Fnn source) (numtype_Inn target)
      (.mk_cvtop___2 source target (if saturating then .TRUNC_SAT sign else .TRUNC sign))
      (.mk_num__1 source value) (some (expected.toList.map (num_.mk_num__0 target))) := by
    rw [← conversion]
    cases saturating
    · exact float_trunc_relation source target sign value
    · exact float_trunc_sat_relation source target sign value
  have resultsWf : Forall (fun result => wf_num_ (numtype_Inn target) (.mk_num__0 target result)) expected.toList := by
    rw [← conversion]
    cases saturating
    · exact float_trunc_results_wf _ target sign value
    · exact float_trunc_sat_results_wf _ target sign value
  have opWf : wf_cvtop__ (numtype_Fnn source) (numtype_Inn target)
      (.mk_cvtop___2 source target (if saturating then .TRUNC_SAT sign else .TRUNC sign)) := by
    apply wf_cvtop__.cvtop___case_2
    · cases saturating
      · exact .cvtop__Fnn_1_Inn_2_case_0 _ _ _
      · exact .cvtop__Fnn_1_Inn_2_case_1 _ _ _
    · rfl
    · rfl
  have input : wf_num_ (numtype_Fnn source) (.mk_num__1 source value) := float_num_wf source value inputWf
  have different : numtype_Inn target ≠ numtype_Fnn source := by cases source <;> cases target <;> decide
  cases expected with
  | none =>
    apply Step_pure.cvtop_trap _ _ _ _ _ relation
    · simp
    · rfl
    · exact wf_admininstr_val (.val_case_0 _ _ input)
    · exact wf_admininstr_instr (.instr_case_18 _ _ _ opWf different)
    · exact .admininstr_case_73
  | some result =>
    apply numeric_conversion_pure _ _ _ _ _ _ relation
    · simp
    · exact input
    · exact resultsWf result (by simp)
    · exact opWf
    · exact different
end Itasca.Spec

end

end

/-! ## PrimitiveOperations -/

section

/-!
# Primitive source operation laws

Scalar memory representations, table/reference operations and initialization/copy effects
are related to source judgments. Exact floating-point promotion supplies a shared operand-
level source fact.
-/

/-! ## MemoryStore -/

section

namespace Itasca.Spec
open WebAssembly

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
  simpa only [Builtins.integer_bytes_length,Builtins.integer_of_bytes_integer_bytes] using roundtrip

theorem numeric_bytes_payload_wf (ty : numtype) (value : num_) : Forall wf_byte (nbytes_ ty value) := by
  cases ty <;> cases value <;> simp only [nbytes_,ibytes_,fbytes_] <;>
    first | exact integer_bytes_wf _ _ | simp [Forall]

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
end Itasca.Spec

end

/-! ## PackedMemory -/

section

namespace Itasca.Spec
open WebAssembly

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
theorem load_step (s : WebAssembly.store) (f : frame) (op : PackedMemory) (sign : sx) (argument : memarg) (address : Nat)
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
theorem store_step (s : WebAssembly.store) (f : frame) (op : PackedMemory) (argument : memarg)
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
end Itasca.Spec

end

/-! ## TableAccess -/

section

namespace Itasca.Spec
open WebAssembly

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
end Itasca.Spec

end

/-! ## MemorySize -/

section

namespace Itasca.Spec
open WebAssembly

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
end Itasca.Spec

end

/-! ## CopyInterval -/

section

namespace Itasca.Spec.Segment

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
end Itasca.Spec.Segment

end

/-! ## MemoryInit -/

section

/-!
Source semantics of `memory.init`. Connect the generated recursive rules to the bounded interval update used by runtime correspondence proofs.
-/

/-! ## Memory Init Source -/

section

namespace Itasca.Spec.Segment
open WebAssembly

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
  norm_num [WebAssembly.Builtins.integerBytes,Nat.mod_eq_of_lt bound]

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

end Itasca.Spec.Segment

end

/-! ## Memory Init Algebra -/

section

namespace Itasca.Spec.Segment
open WebAssembly

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

end Itasca.Spec.Segment

end

end

/-! ## CopySnapshot -/

section

namespace Itasca.Spec.Segment

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
end Itasca.Spec.Segment

end

/-! ## TableFill -/

section

/-!
Source semantics of `table.fill`. Connect the generated recursive rules to the bounded interval update used by runtime correspondence proofs.
-/

/-! ## Table Fill Source -/

section

namespace Itasca.Spec.Segment
open WebAssembly

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
end Itasca.Spec.Segment

end

/-! ## Table Fill Algebra -/

section

namespace Itasca.Spec.Segment
open WebAssembly

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
end Itasca.Spec.Segment

end

end

/-! ## FillSlice -/

section

namespace Itasca.Spec.Segment

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
end Itasca.Spec.Segment

end

/-! ## References -/

section

namespace Itasca.Spec
open WebAssembly

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
end Itasca.Spec

end

/-! ## ReferenceFunction -/

section

namespace Itasca.Spec
open WebAssembly

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
end Itasca.Spec

end

/-! ## TableWriteBounds -/

section

namespace Itasca.Spec
open WebAssembly

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
end Itasca.Spec

end

/-! ## FloatPromote -/

section

namespace Itasca.Spec
open WebAssembly WebAssembly.Builtins.Float

theorem float_promote_relation (value : fN) :
    fun_cvtop__ .F32 .F64 (.mk_cvtop___3 .F32 .F64 .PROMOTE) (.mk_num__1 .F32 value)
      (some ((promote__ 32 64 value).map (num_.mk_num__1 .F64))) := by
  apply fun_cvtop__.fun_cvtop___case_22
  exact float_results_wf .F64 _ (float_demote_wf 32 64 (by omega) value)
end Itasca.Spec

end

end

/-! ## ExecutionSupport -/

section

/-!
# Source execution support

Generated membership/typing facts, source allocation and instantiation, host calls and
eventful divergence support joined execution constructions. Shared segment-program and
copying algebra stays independent of extracted runtime execution.
-/

/-! ## IndirectCallSource -/

section

namespace Itasca.Spec
open WebAssembly

/-- The generated indirect-call rule resolves exactly a function reference
whose signature matches the module type selected by the instruction. -/
def IndirectTarget (s : store) (f : frame) (table type position address : Nat) : Prop :=
  (fun_table ⟨s,f⟩ (.mk_uN table)).REFS[position]? = some (.REF_FUNC_ADDR address) ∧
    ∃ function,s.FUNCS[address]?=some function ∧ fun_type ⟨s,f⟩ (.mk_uN type)=function.TYPE

theorem call_indirect_resolve (s : store) (f : frame) (table type position address : Nat)
    (hs : wf_store s) (hf : wf_frame f) (ht : table<2^32) (hy : type<2^32) (hp : position<2^32)
    (target : IndirectTarget s f table type position address) :
    StepH ⟨⟨s,f⟩,[Segment.i32 position,.CALL_INDIRECT (.mk_uN table) (.mk_uN type)]⟩ []
      ⟨⟨s,f⟩,[.CALL_ADDR address]⟩ := by
  have input : wf_config ⟨⟨s,f⟩,[Segment.i32 position,.CALL_INDIRECT (.mk_uN table) (.mk_uN type)]⟩ := by
    apply wf_config_make hs hf
    simp only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨Segment.i32_wf _ hp,.admininstr_case_11 _ _ (Segment.index_wf _ ht) (Segment.index_wf _ hy)⟩
  obtain ⟨inside,reference⟩ := List.getElem?_eq_some_iff.mp target.1
  obtain ⟨function,lookup,signature⟩ := target.2
  obtain ⟨issued,actual⟩ := List.getElem?_eq_some_iff.mp lookup
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_make hs hf (by simpa [Forall] using wf_admininstr.admininstr_case_70 address))
  apply Step_read.call_indirect_call ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN position)) (.mk_uN table) (.mk_uN type) address
  · exact inside
  · simp [proj_num__0]
  · simpa only [proj_num__0,proj_uN_0,Option.get!,getElem!_pos (fun_table ⟨s,f⟩ (.mk_uN table)).REFS position inside] using reference
  · exact issued
  · simpa only [fun_funcinst,getElem!_pos s.FUNCS address issued,actual] using signature
  · exact input
  · exact .admininstr_case_70 _

theorem call_indirect_trap (s : store) (f : frame) (table type position : Nat)
    (hs : wf_store s) (hf : wf_frame f) (ht : table<2^32) (hy : type<2^32) (hp : position<2^32)
    (missing : ¬∃address,IndirectTarget s f table type position address) :
    StepH ⟨⟨s,f⟩,[Segment.i32 position,.CALL_INDIRECT (.mk_uN table) (.mk_uN type)]⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩ := by
  have input : wf_config ⟨⟨s,f⟩,[Segment.i32 position,.CALL_INDIRECT (.mk_uN table) (.mk_uN type)]⟩ := by
    apply wf_config_make hs hf
    simp only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨Segment.i32_wf _ hp,.admininstr_case_11 _ _ (Segment.index_wf _ ht) (Segment.index_wf _ hy)⟩
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_make hs hf (by simpa [Forall] using wf_admininstr.admininstr_case_73))
  apply Step_read.call_indirect_trap ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN position)) (.mk_uN table) (.mk_uN type) ?_ input .admininstr_case_73
  intro prior
  cases prior with
  | call_indirect_call_0 _ _ _ _ address inside numeric reference issued signature _ _ =>
    have inside' : position < (fun_table ⟨s,f⟩ (.mk_uN table)).REFS.length := inside
    have issued' : address < s.FUNCS.length := issued
    apply missing
    refine ⟨address,List.getElem?_eq_some_iff.mpr ⟨inside',?_⟩,s.FUNCS[address],List.getElem?_eq_getElem issued',?_⟩
    · simpa only [proj_num__0,proj_uN_0,Option.get!,getElem!_pos (fun_table ⟨s,f⟩ (.mk_uN table)).REFS position inside'] using reference
    · simpa only [fun_funcinst,getElem!_pos s.FUNCS address issued'] using signature
end Itasca.Spec

end

/-! ## Invocation -/

section

namespace Itasca.Spec
open WebAssembly

theorem invocation_config {s : store} {address : funcaddr} {args : List val} {initial : config}
    (invoked : fun_invoke s address args initial) :
    initial = ⟨⟨s, invocationFrame⟩, vals args ++ [.CALL_ADDR address]⟩ := by
  cases invoked
  simp_all [invocationFrame, vals, Map]

theorem invocation_frame_wf {s : store} {address : funcaddr} {args : List val} {initial : config}
    (invoked : fun_invoke s address args initial) : wf_frame invocationFrame := by
  cases invoked
  assumption
end Itasca.Spec

end

/-! ## Allocation -/

section

namespace Itasca.Spec
open WebAssembly

def allocationFunctionIndex : func → Nat
  | .FUNC (.mk_uN index) _ _ => index

def allocationFunction (inst : moduleinst) (source : func) : funcinst :=
  ⟨inst.TYPES[allocationFunctionIndex source]!, inst, funccode_func source⟩

def allocationTable : tabletype → tableinst
  | .mk_tabletype (.mk_limits (.mk_uN minimum) maximum) ty =>
    ⟨.mk_tabletype (.mk_limits (.mk_uN minimum) maximum) ty, List.replicate minimum (.REF_NULL ty)⟩

def allocationMemory : memtype → meminst
  | .PAGE (.mk_limits (.mk_uN minimum) maximum) =>
    ⟨.PAGE (.mk_limits (.mk_uN minimum) maximum), List.replicate (minimum * (64 * Ki)) (.mk_byte 0)⟩

theorem allocation_function_wf (inst : moduleinst) (source : func)
    (instanceWf : wf_moduleinst inst) (sourceWf : wf_func source) : wf_funcinst (allocationFunction inst source) := by
  cases sourceWf with
  | func_case_0 index locals body indexWf bodyWf =>
    exact .funcinst_case_ _ _ _ instanceWf (.funccode_case_0 _ _ _ indexWf bodyWf)

theorem allocate_function (s : store) (inst : moduleinst) (source : func)
    (instanceWf : wf_moduleinst inst) (sourceWf : wf_func source)
    (bound : allocationFunctionIndex source < inst.TYPES.length) :
    fun_allocfunc s inst source ({s with FUNCS := s.FUNCS ++ [allocationFunction inst source]}, s.FUNCS.length) := by
  have allocatedWf := allocation_function_wf inst source instanceWf sourceWf
  cases source with
  | FUNC index locals body =>
    exact .fun_allocfunc_case_0 s inst _ _ index locals body bound rfl rfl allocatedWf allocatedWf sourceWf

theorem allocate_global (s : store) (value : globalinst) (wf : wf_globalinst value) :
    fun_allocglobal s value.TYPE value.VALUE ({s with GLOBALS := s.GLOBALS ++ [value]}, s.GLOBALS.length) := by
  exact .fun_allocglobal_case_0 s value.TYPE value.VALUE value (by cases value; rfl) wf (by simpa using wf)

theorem allocate_table (s : store) (ty : tabletype) (wf : wf_tabletype ty) :
    fun_alloctable s ty ({s with TABLES := s.TABLES ++ [allocationTable ty]}, s.TABLES.length) := by
  cases ty with | mk_tabletype limits refType =>
    cases limits with | mk_limits minimum maximum =>
      cases minimum with | mk_uN minimum =>
        exact .fun_alloctable_case_0 s _ maximum refType _ rfl (.tableinst_case_ _ _ wf) (.tableinst_case_ _ _ wf)

theorem allocate_memory (s : store) (ty : memtype) (wf : wf_memtype ty) :
    fun_allocmem s ty ({s with MEMS := s.MEMS ++ [allocationMemory ty]}, s.MEMS.length) := by
  cases ty with | PAGE limits =>
    cases limits with | mk_limits minimum maximum =>
      cases minimum with | mk_uN minimum =>
        have bytes : Forall wf_byte (List.replicate (minimum * (64 * Ki)) (.mk_byte 0)) := by
          intro value member
          have same : value = .mk_byte 0 := (List.mem_replicate.mp member).2
          rw [same]; constructor; norm_num
        exact .fun_allocmem_case_0 s _ maximum _ rfl (.meminst_case_ _ _ wf bytes) (.meminst_case_ _ _ wf bytes)

theorem allocate_element (s : store) (element : eleminst) :
    fun_allocelem s element.TYPE element.REFS ({s with ELEMS := s.ELEMS ++ [element]}, s.ELEMS.length) := by
  exact .fun_allocelem_case_0 s element.TYPE element.REFS element (by cases element; rfl)

theorem allocate_data (s : store) (data : datainst) (wf : wf_datainst data) :
    fun_allocdata s data.BYTES ({s with DATAS := s.DATAS ++ [data]}, s.DATAS.length) := by
  exact .fun_allocdata_case_0 s data.BYTES data (by cases data; rfl) wf (by simpa using wf)

/-- Allocating a list appends its instances and issues precisely the consecutive
addresses starting at the old vector length. -/
theorem allocate_functions (s : store) (inst : moduleinst) (sources : List func)
    (instanceWf : wf_moduleinst inst) (sourceWf : Forall wf_func sources)
    (bounds : ∀ source ∈ sources, allocationFunctionIndex source < inst.TYPES.length) :
    fun_allocfuncs s inst sources
      ({s with FUNCS := s.FUNCS ++ sources.map (allocationFunction inst)}, List.range' s.FUNCS.length sources.length) := by
  induction sources generalizing s with
  | nil => simpa using fun_allocfuncs.fun_allocfuncs_case_0 s inst
  | cons source sources ih =>
    have one := allocate_function s inst source instanceWf (sourceWf source (by simp)) (bounds source (by simp))
    have rest := ih {s with FUNCS := s.FUNCS ++ [allocationFunction inst source]}
      (fun f hf => sourceWf f (by simp [hf])) (fun f hf => bounds f (by simp [hf]))
    simpa only [List.map_cons, List.length_cons, List.range'_succ, List.length_append,
      List.length_singleton, List.length_nil, Nat.zero_add, List.append_assoc, List.singleton_append] using
      fun_allocfuncs.fun_allocfuncs_case_1 s inst source sources _ _ _ _ _ _ rest one rfl rfl

theorem allocate_globals (s : store) (values : List globalinst)
    (wf : Forall wf_globalinst values) :
    fun_allocglobals s (values.map globalinst.TYPE) (values.map globalinst.VALUE)
      ({s with GLOBALS := s.GLOBALS ++ values}, List.range' s.GLOBALS.length values.length) := by
  induction values generalizing s with
  | nil => simpa using fun_allocglobals.fun_allocglobals_case_0 s
  | cons value values ih =>
    have one := allocate_global s value (wf value (by simp))
    have rest := ih {s with GLOBALS := s.GLOBALS ++ [value]}
      (fun value member => wf value (by simp [member]))
    simpa only [List.map_cons, List.length_cons, List.range'_succ, List.length_append,
      List.length_singleton, List.length_nil, Nat.zero_add, List.append_assoc, List.singleton_append] using
      fun_allocglobals.fun_allocglobals_case_1 s value.TYPE (values.map globalinst.TYPE) value.VALUE (values.map globalinst.VALUE) _ _ _ _ _ _ rest one rfl rfl

theorem allocate_tables (s : store) (values : List tabletype)
    (wf : Forall wf_tabletype values) :
    fun_alloctables s (values)
      ({s with TABLES := s.TABLES ++ values.map allocationTable}, List.range' s.TABLES.length values.length) := by
  induction values generalizing s with
  | nil => simpa using fun_alloctables.fun_alloctables_case_0 s
  | cons value values ih =>
    have one := allocate_table s value (wf value (by simp))
    have rest := ih {s with TABLES := s.TABLES ++ [allocationTable value]}
      (fun value member => wf value (by simp [member]))
    simpa only [List.map_cons, List.length_cons, List.range'_succ, List.length_append,
      List.length_singleton, List.length_nil, Nat.zero_add, List.append_assoc, List.singleton_append] using
      fun_alloctables.fun_alloctables_case_1 s value values _ _ _ _ _ _ rest one rfl rfl

theorem allocate_memories (s : store) (values : List memtype)
    (wf : Forall wf_memtype values) :
    fun_allocmems s (values)
      ({s with MEMS := s.MEMS ++ values.map allocationMemory}, List.range' s.MEMS.length values.length) := by
  induction values generalizing s with
  | nil => simpa using fun_allocmems.fun_allocmems_case_0 s
  | cons value values ih =>
    have one := allocate_memory s value (wf value (by simp))
    have rest := ih {s with MEMS := s.MEMS ++ [allocationMemory value]}
      (fun value member => wf value (by simp [member]))
    simpa only [List.map_cons, List.length_cons, List.range'_succ, List.length_append,
      List.length_singleton, List.length_nil, Nat.zero_add, List.append_assoc, List.singleton_append] using
      fun_allocmems.fun_allocmems_case_1 s value values _ _ _ _ _ _ rest one rfl rfl

theorem allocate_elements (s : store) (values : List eleminst) :
    fun_allocelems s (values.map eleminst.TYPE) (values.map eleminst.REFS)
      ({s with ELEMS := s.ELEMS ++ values}, List.range' s.ELEMS.length values.length) := by
  induction values generalizing s with
  | nil => simpa using fun_allocelems.fun_allocelems_case_0 s
  | cons value values ih =>
    have one := allocate_element s value
    have rest := ih {s with ELEMS := s.ELEMS ++ [value]}
    simpa only [List.map_cons, List.length_cons, List.range'_succ, List.length_append,
      List.length_singleton, List.length_nil, Nat.zero_add, List.append_assoc, List.singleton_append] using
      fun_allocelems.fun_allocelems_case_1 s value.TYPE (values.map eleminst.TYPE) value.REFS (values.map eleminst.REFS) _ _ _ _ _ _ rest one rfl rfl

theorem allocate_datas (s : store) (values : List datainst)
    (wf : Forall wf_datainst values) :
    fun_allocdatas s (values.map datainst.BYTES)
      ({s with DATAS := s.DATAS ++ values}, List.range' s.DATAS.length values.length) := by
  induction values generalizing s with
  | nil => simpa using fun_allocdatas.fun_allocdatas_case_0 s
  | cons value values ih =>
    have one := allocate_data s value (wf value (by simp))
    have rest := ih {s with DATAS := s.DATAS ++ [value]}
      (fun value member => wf value (by simp [member]))
    simpa only [List.map_cons, List.length_cons, List.range'_succ, List.length_append,
      List.length_singleton, List.length_nil, Nat.zero_add, List.append_assoc, List.singleton_append] using
      fun_allocdatas.fun_allocdatas_case_1 s value.BYTES (values.map datainst.BYTES) _ _ _ _ _ _ rest one rfl rfl

end Itasca.Spec

end

/-! ## SegmentPrograms -/

section

namespace Itasca.Spec.Segment

def elementSize : elem → Nat
  | .ELEM _ expressions _ => expressions.length

def dataSize : data → Nat
  | .DATA bytes _ => bytes.length

def singleMemoryData : data → Prop
  | .DATA _ (.ACTIVE memory _) => memory = .mk_uN 0
  | .DATA _ .PASSIVE => True

private theorem const_wf (bits : Nat) (bound : bits < 2^32) :
    wf_instr (.CONST .I32 (.mk_num__0 .I32 (.mk_uN bits))) :=
  .instr_case_13 _ _ (.num__case_0 .I32 .I32 _ (by decide) (index_wf bits bound) rfl)

theorem element_program (segment : elem) (index : idx)
    (valid : wf_elem segment) (bounded : elementSize segment < 2^32)
    (indexWf : wf_uN 32 index) :
    fun_runelem segment index (elementProgram segment index) ∧
      Forall wf_instr (elementProgram segment index) := by
  cases valid with
  | elem_case_0 ty expressions mode exprWf modeWf =>
    cases modeWf with
    | elemmode_case_1 => exact ⟨.fun_runelem_case_0 _ _ _, by simp [elementProgram,Forall]⟩
    | elemmode_case_2 =>
      have drop := wf_instr.instr_case_55 index indexWf
      exact ⟨.fun_runelem_case_1 _ _ _ drop, by simpa [elementProgram,Forall] using drop⟩
    | elemmode_case_0 table offset tableWf offsetWf =>
      have zero := const_wf 0 (by decide)
      have count := const_wf expressions.length bounded
      have init := wf_instr.instr_case_54 table index tableWf indexWf
      have drop := wf_instr.instr_case_55 index indexWf
      refine ⟨.fun_runelem_case_2 _ _ _ _ _ _ rfl zero count init drop, ?_⟩
      apply forall_append offsetWf
      simpa [Forall] using And.intro zero (And.intro count (And.intro init drop))

theorem data_program (segment : data) (index : idx)
    (valid : wf_data segment) (bounded : dataSize segment < 2^32)
    (single : singleMemoryData segment) (indexWf : wf_uN 32 index) :
    fun_rundata segment index (some (dataProgram segment index)) ∧
      Forall wf_instr (dataProgram segment index) := by
  cases valid with
  | data_case_0 bytes mode bytesWf modeWf =>
    cases modeWf with
    | datamode_case_1 => exact ⟨.fun_rundata_case_0 _ _, by simp [dataProgram,Forall]⟩
    | datamode_case_0 memory offset memoryWf offsetWf =>
      change memory = .mk_uN 0 at single
      subst memory
      have zero := const_wf 0 (by decide)
      have count := const_wf bytes.length bounded
      have init := wf_instr.instr_case_66 index indexWf
      have drop := wf_instr.instr_case_67 index indexWf
      refine ⟨.fun_rundata_case_1 _ _ _ _ rfl zero count init drop, ?_⟩
      apply forall_append offsetWf
      simpa [Forall] using And.intro zero (And.intro count (And.intro init drop))

theorem element_programs (segments : List elem) (countBound : segments.length ≤ 2^32)
    (valid : ∀ segment ∈ segments, wf_elem segment ∧ elementSize segment < 2^32) :
    List.Forall₂ (fun index program => fun_runelem segments[index]! (.mk_uN index) program)
      (List.range segments.length) (elementPrograms segments) ∧
    Forall (fun program => Forall wf_instr program) (elementPrograms segments) := by
  have one : ∀ index ∈ List.range segments.length,
      fun_runelem segments[index]! (.mk_uN index) (elementProgram segments[index]! (.mk_uN index)) ∧
      Forall wf_instr (elementProgram segments[index]! (.mk_uN index)) := by
    intro index member
    have bound := List.mem_range.mp member
    have present : segments[index]! ∈ segments := by
      simpa only [getElem!_pos segments index bound] using List.getElem_mem bound
    exact element_program _ _ (valid _ present).1 (valid _ present).2 (index_wf _ (by omega))
  constructor
  · apply List.forall₂_map_right_iff.mpr
    exact List.forall₂_same.mpr (fun index member => (one index member).1)
  · intro program member
    obtain ⟨index, present, rfl⟩ := List.mem_map.mp member
    exact (one index present).2

theorem data_programs (segments : List data) (countBound : segments.length ≤ 2^32)
    (valid : ∀ segment ∈ segments, wf_data segment ∧ dataSize segment < 2^32 ∧ singleMemoryData segment) :
    List.Forall₂ (fun index program => fun_rundata segments[index]! (.mk_uN index) (some program))
      (List.range segments.length) (dataPrograms segments) ∧
    Forall (fun program => Forall wf_instr program) (dataPrograms segments) := by
  have one : ∀ index ∈ List.range segments.length,
      fun_rundata segments[index]! (.mk_uN index) (some (dataProgram segments[index]! (.mk_uN index))) ∧
      Forall wf_instr (dataProgram segments[index]! (.mk_uN index)) := by
    intro index member
    have bound := List.mem_range.mp member
    have present : segments[index]! ∈ segments := by
      simpa only [getElem!_pos segments index bound] using List.getElem_mem bound
    exact data_program _ _ (valid _ present).1 (valid _ present).2.1
      (valid _ present).2.2 (index_wf _ (by omega))
  constructor
  · apply List.forall₂_map_right_iff.mpr
    exact List.forall₂_same.mpr (fun index member => (one index member).1)
  · intro program member
    obtain ⟨index, present, rfl⟩ := List.mem_map.mp member
    exact (one index present).2

private theorem admin_programs_wf (programs : List (List instr))
    (valid : Forall (fun program => Forall wf_instr program) programs) :
    Forall wf_admininstr (programs.flatten.map admininstr_instr) := by
  intro instruction member
  obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨program, programPresent, present⟩ := List.mem_flatten.mp present
  exact wf_admininstr_instr (valid program programPresent source present)

/-- The generated instantiation result is syntactically well formed once its
allocated store, module frame, source segment programs, and start index are. -/
theorem initialization_config_wf (s : store) (inst : moduleinst)
    (elements datas : List (List instr)) (start : Option idx)
    (storeWf : wf_store s) (instanceWf : wf_moduleinst inst)
    (elementWf : Forall (fun program => Forall wf_instr program) elements)
    (dataWf : Forall (fun program => Forall wf_instr program) datas)
    (startWf : Forall (wf_uN 32) start.toList) :
    wf_config ⟨⟨s, ⟨[], inst⟩⟩,
      elements.flatten.map admininstr_instr ++
        (datas.flatten.map admininstr_instr ++ (start.map admininstr.CALL).toList)⟩ := by
  apply wf_config_make storeWf (.frame_case_ _ _ (by simp [Forall]) instanceWf)
  apply forall_append (admin_programs_wf elements elementWf)
  apply forall_append (admin_programs_wf datas dataWf)
  cases start with
  | none => simp [Forall]
  | some index =>
    have indexWf : wf_uN 32 index := by simpa [Forall] using startWf
    simpa [Forall] using wf_admininstr.admininstr_case_10 index indexWf
end Itasca.Spec.Segment

end

/-! ## Instantiation -/

section

namespace Itasca.Spec
open WebAssembly

private theorem concat_flatten {A : Type} (programs : List (List A)) : concat_ A programs = programs.flatten := by
  induction programs with
  | nil => rfl
  | cons head tail ih => simp only [concat_, List.flatten_cons, ih]

private theorem wf_concat (programs : List (List instr))
    (wf : Forall (fun program => Forall wf_instr program) programs) :
    Forall wf_instr (concat_ instr programs) := by
  rw [concat_flatten]
  intro instruction member
  obtain ⟨program, present, member⟩ := List.mem_flatten.mp member
  exact wf program present instruction member

private theorem get_some_programs (indices : List Nat) (programs : List (List instr))
    (lengths : indices.length = programs.length) :
    (indices.map (fun _ (program : Option (List instr)) => Option.get! program)).ap
      (programs.map some) = programs := by
  induction indices generalizing programs with
  | nil => cases programs <;> simp_all [WebAssembly.List.ap]
  | cons index rest ih =>
    cases programs with
    | nil => simp at lengths
    | cons program programs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at lengths
      simpa only [List.map_cons, WebAssembly.List.ap, List.zipWith_cons_cons, Option.get!_some] using
        congrArg (program :: ·) (ih programs lengths)

/-- A compact constructor for the generated instantiation judgment. Repeated
allocation and segment premises in the generated rule are discharged from one
source derivation each; partial data programs are all present. -/
theorem instantiate_source
    (s after : store) (source : module) (externals : List externaddr)
    (types : List functype) (imports : List «import») (functions : List func)
    (globals : List global) (tables : List table) (memories : List mem)
    (elements : List elem) (datas : List data) (startIndex : Option idx) (exports : List «export»)
    (globalExprs : List expr) (globalTypes : List globaltype)
    (elementModes : List elemmode) (elementExprs : List (List expr)) (elementTypes : List reftype)
    (values : List val) (references : List (List ref))
    (importedFunctions : List funcaddr) (importedGlobals : List globaladdr)
    (inst : moduleinst) (elementPrograms dataPrograms : List (List instr))
    (sourceEq : source = .MODULE (types.map type.TYPE) imports functions globals tables memories
      elements datas (startIndex.map start.START) exports)
    (globalsEq : globals = Map₂ (fun expression ty => global.GLOBAL ty expression) globalExprs globalTypes)
    (elementsEq : elements = Map₃ (fun mode expressions ty => elem.ELEM ty expressions mode)
      elementModes elementExprs elementTypes)
    (importFunctions : fun_funcs externals importedFunctions)
    (importGlobals : fun_globals externals importedGlobals)
    (initialModule : moduleinst)
    (initialEq : initialModule = ⟨types,
      importedFunctions ++ (List.range functions.length).map (fun index => s.FUNCS.length + index),
      importedGlobals, [], [], [], [], []⟩)
    (globalCounts : globalExprs.length = values.length)
    (globalEval : Forall₂ (fun expression value => Eval_expr ⟨s, ⟨[], initialModule⟩⟩ expression
      ⟨s, ⟨[], initialModule⟩⟩ [value]) globalExprs values)
    (elementCounts : elementExprs.length = references.length)
    (elementValueCounts : Forall₂ (fun expressions values => expressions.length = values.length) elementExprs references)
    (elementEval : Forall₂ (fun expressions values => Forall₂ (fun expression value =>
      Eval_expr ⟨s, ⟨[], initialModule⟩⟩ expression ⟨s, ⟨[], initialModule⟩⟩ [val_ref value])
      expressions values) elementExprs references)
    (allocated : fun_allocmodule s source externals values references (after, inst))
    (runElements : List.Forall₂ (fun index program => fun_runelem elements[index]! (.mk_uN index) program)
      (List.range elements.length) elementPrograms)
    (runDatas : List.Forall₂ (fun index program => fun_rundata datas[index]! (.mk_uN index) (some program))
      (List.range datas.length) dataPrograms)
    (valuesWf : Forall wf_val values) (afterWf : wf_store after) (instWf : wf_moduleinst inst)
    (elementsWf : Forall (fun program => Forall wf_instr program) elementPrograms)
    (datasWf : Forall (fun program => Forall wf_instr program) dataPrograms)
    (configWf : wf_config ⟨⟨after, ⟨[], inst⟩⟩,
      elementPrograms.flatten.map admininstr_instr ++
      (dataPrograms.flatten.map admininstr_instr ++ (startIndex.map admininstr.CALL).toList)⟩)
    (sourceWf : wf_module source)
    (globalTypeCounts : globalExprs.length = globalTypes.length)
    (globalWf : Forall₂ (fun expression ty => wf_global (.GLOBAL ty expression)) globalExprs globalTypes)
    (elementModeCounts : elementModes.length = elementExprs.length)
    (elementTypeCounts : elementModes.length = elementTypes.length)
    (elementWf : Forall₃ (fun mode expressions ty => wf_elem (.ELEM ty expressions mode))
      elementModes elementExprs elementTypes)
    (startWf : Forall (fun index => wf_start (.START index)) startIndex.toList)
    (initialWf : wf_moduleinst initialModule) (storeWf : wf_store s)
    (elementBound : elements.length ≤ 2^32) (dataBound : datas.length ≤ 2^32) :
    fun_instantiate s source externals ⟨⟨after, ⟨[], inst⟩⟩,
      elementPrograms.flatten.map admininstr_instr ++
      (dataPrograms.flatten.map admininstr_instr ++ (startIndex.map admininstr.CALL).toList)⟩ := by
  have eb : Forall (fun index => index < elements.length) (List.range elements.length) := by
    intro index member; exact List.mem_range.mp member
  have db : Forall (fun index => index < datas.length) (List.range datas.length) := by
    intro index member; exact List.mem_range.mp member
  have elementRun : Forall₂ (fun index program => fun_runelem elements[index]! (.mk_uN index) program)
      (List.range elements.length) elementPrograms := fun _ member => List.forall₂_zip runElements member
  have dataRun : Forall₂ (fun index program => fun_rundata datas[index]! (.mk_uN index) program)
      (List.range datas.length) (dataPrograms.map some) := by
    exact fun _ member => List.forall₂_zip (List.forall₂_map_right_iff.mpr runDatas) member
  have flattened := get_some_programs (List.range datas.length) dataPrograms runDatas.length_eq
  have defined : Forall₂ (fun (_ : Nat) (program : Option (List instr)) => program ≠ none)
      (List.range datas.length) (dataPrograms.map some) := by
    intro pair member
    have present := List.of_mem_zip member |>.2
    obtain ⟨program, _, equal⟩ := List.mem_map.mp present
    simp [← equal]
  have initialFrame : wf_frame ⟨[], initialModule⟩ := .frame_case_ _ _ (by simp [Forall]) initialWf
  have finalFrame : wf_frame ⟨[], inst⟩ := .frame_case_ _ _ (by simp [Forall]) instWf
  have elementAll : Forall wf_instr (concat_ instr elementPrograms) := by
    exact wf_concat elementPrograms elementsWf
  have dataAll : Forall wf_instr (concat_ instr dataPrograms) := by
    exact wf_concat dataPrograms datasWf
  refine fun_instantiate.fun_instantiate_case_0 s source externals ⟨[], inst⟩ startIndex types globalExprs
    globalTypes elementModes elementExprs elementTypes initialModule ⟨[], initialModule⟩ values references
    0 0 (types.map type.TYPE) imports functions globals tables memories elements datas (startIndex.map start.START)
    exports functions.length elements.length datas.length ⟨s, ⟨[], initialModule⟩⟩ after inst
    elementPrograms.flatten dataPrograms.flatten importedGlobals importedFunctions
    (dataPrograms.map some) (dataPrograms.map some) elementPrograms elementPrograms
    (after, inst) (after, inst) (dataPrograms.map some) elementPrograms (after, inst)
    importedGlobals importedFunctions
    importGlobals importFunctions db dataRun db dataRun eb elementRun eb elementRun allocated allocated
    db dataRun eb elementRun allocated importGlobals importFunctions sourceEq.symm rfl globalsEq elementsEq rfl
    rfl rfl rfl initialEq rfl rfl globalCounts globalEval elementCounts elementValueCounts elementEval rfl rfl
    ?_ defined ?_ valuesWf afterWf instWf elementAll ?_ ?_ ?_ ?_ ?_ globalTypeCounts globalWf
    elementModeCounts elementTypeCounts elementWf startWf ?_ initialFrame (.state_case_0 _ _ storeWf initialFrame)
    finalFrame ?_ ?_
  · exact (concat_flatten elementPrograms).symm
  · simpa only [flattened] using (concat_flatten dataPrograms).symm
  · intro pair member
    exact elementsWf pair.2 ((List.of_mem_zip member).2)
  · simpa only [flattened] using dataAll
  · intro pair member
    obtain ⟨program, present, equal⟩ := List.mem_map.mp ((List.of_mem_zip member).2)
    simpa only [← equal, Option.get!_some] using datasWf program present
  · simpa only [Map, OMap] using configWf
  · simpa only [← sourceEq] using sourceWf
  · simpa only [initialEq] using initialWf
  · intro index member
    constructor
    have bound := (List.mem_range.mp member).trans_le elementBound
    norm_num at *
    omega
  · intro index member
    constructor
    have bound := (List.mem_range.mp member).trans_le dataBound
    norm_num at *
    omega
end Itasca.Spec

end

/-! ## AllocationModule -/

section

namespace Itasca.Spec
open WebAssembly

def allocationStore (s : store) (inst : moduleinst) (functions : List func)
    (globals : List globalinst) (tables : List tabletype) (memories : List memtype)
    (elements : List eleminst) (datas : List datainst) : store :=
  ⟨s.FUNCS ++ functions.map (allocationFunction inst), s.GLOBALS ++ globals,
    s.TABLES ++ tables.map allocationTable, s.MEMS ++ memories.map allocationMemory,
    s.ELEMS ++ elements, s.DATAS ++ datas⟩

private theorem store_parts {s : store} (wf : wf_store s) :
    Forall wf_funcinst s.FUNCS ∧ Forall wf_globalinst s.GLOBALS ∧ Forall wf_tableinst s.TABLES ∧
      Forall wf_meminst s.MEMS ∧ Forall wf_datainst s.DATAS := by
  cases wf; exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption⟩

/-- Concrete list allocation proves the generated whole-module allocator.
The only retained allocation-side evidence is syntax, index bounds, the exact
published module layout, and the independently checked export resolutions. -/
theorem allocate_module (s : store) (source : module) (externals : List externaddr)
    (inst : moduleinst) (types : List functype) (imports : List «import») (functions : List func)
    (globals : List globalinst) (tables : List tabletype) (memories : List memtype)
    (elements : List eleminst) (datas : List datainst)
    (globalExpressions : List expr) (elementExpressions : List (List expr))
    (elementModes : List elemmode) (dataModes : List datamode) (start : Option start)
    (exports : List «export») (exportInstances : List exportinst)
    (importedFunctions importedGlobals importedTables importedMemories : List Nat)
    (sourceEq : source = .MODULE (types.map type.TYPE) imports functions
      (Map₂ (fun expression ty => global.GLOBAL ty expression) globalExpressions (globals.map globalinst.TYPE))
      (tables.map table.TABLE) (memories.map mem.MEMORY)
      (Map₃ (fun mode expressions ty => elem.ELEM ty expressions mode)
        elementModes elementExpressions (elements.map eleminst.TYPE))
      (Map₂ data.DATA (datas.map datainst.BYTES) dataModes) start exports)
    (layout : inst = ⟨types,
      importedFunctions ++ List.range' s.FUNCS.length functions.length,
      importedGlobals ++ List.range' s.GLOBALS.length globals.length,
      importedTables ++ List.range' s.TABLES.length tables.length,
      importedMemories ++ List.range' s.MEMS.length memories.length,
      List.range' s.ELEMS.length elements.length, List.range' s.DATAS.length datas.length, exportInstances⟩)
    (importFunctions : fun_funcs externals importedFunctions)
    (importGlobals : fun_globals externals importedGlobals)
    (importTables : fun_tables externals importedTables)
    (importMemories : fun_mems externals importedMemories)
    (resolvedExports : List.Forall₂ (fun ex allocated => fun_instexport inst.FUNCS inst.GLOBALS inst.TABLES inst.MEMS ex allocated)
      exports exportInstances)
    (storeWf : wf_store s) (sourceWf : wf_module source) (instanceWf : wf_moduleinst inst)
    (functionsWf : Forall wf_func functions)
    (functionBounds : ∀ function ∈ functions, allocationFunctionIndex function < inst.TYPES.length)
    (globalsWf : Forall wf_globalinst globals) (tablesWf : Forall wf_tabletype tables)
    (memoriesWf : Forall wf_memtype memories) (datasWf : Forall wf_datainst datas) :
    fun_allocmodule s source externals (globals.map globalinst.VALUE) (elements.map eleminst.REFS)
      (allocationStore s inst functions globals tables memories elements datas, inst) := by
  let s1 := {s with FUNCS := s.FUNCS ++ functions.map (allocationFunction inst)}
  let s2 := {s1 with GLOBALS := s.GLOBALS ++ globals}
  let s3 := {s2 with TABLES := s.TABLES ++ tables.map allocationTable}
  let s4 := {s3 with MEMS := s.MEMS ++ memories.map allocationMemory}
  let s5 := {s4 with ELEMS := s.ELEMS ++ elements}
  let s6 := allocationStore s inst functions globals tables memories elements datas
  have f := allocate_functions s inst functions instanceWf functionsWf functionBounds
  have g := allocate_globals s1 globals globalsWf
  have t := allocate_tables s2 tables tablesWf
  have m := allocate_memories s3 memories memoriesWf
  have e := allocate_elements s4 elements
  have d := allocate_datas s5 datas datasWf
  obtain ⟨oldFunctions, oldGlobals, oldTables, oldMemories, oldDatas⟩ := store_parts storeWf
  have newFunctions : Forall wf_funcinst (functions.map (allocationFunction inst)) := by
    intro value member
    obtain ⟨function, present, rfl⟩ := List.mem_map.mp member
    exact allocation_function_wf inst function instanceWf (functionsWf function present)
  have newTables : Forall wf_tableinst (tables.map allocationTable) := by
    intro value member
    obtain ⟨ty, present, rfl⟩ := List.mem_map.mp member
    cases ty with | mk_tabletype limits rt =>
      cases limits with | mk_limits minimum maximum =>
        cases minimum
        exact .tableinst_case_ _ _ (tablesWf _ present)
  have newMemories : Forall wf_meminst (memories.map allocationMemory) := by
    intro value member
    obtain ⟨ty, present, rfl⟩ := List.mem_map.mp member
    cases ty with | PAGE limits =>
      cases limits with | mk_limits minimum maximum =>
        cases minimum
        constructor
        · exact memoriesWf _ present
        · intro value member
          have same := (List.mem_replicate.mp member).2
          rw [same]; constructor; norm_num
  have wf1 : wf_store s1 := .store_case_ _ _ _ _ _ _ (forall_append oldFunctions newFunctions) oldGlobals oldTables oldMemories oldDatas
  have wf2 : wf_store s2 := .store_case_ _ _ _ _ _ _ (forall_append oldFunctions newFunctions) (forall_append oldGlobals globalsWf) oldTables oldMemories oldDatas
  have wf3 : wf_store s3 := .store_case_ _ _ _ _ _ _ (forall_append oldFunctions newFunctions) (forall_append oldGlobals globalsWf) (forall_append oldTables newTables) oldMemories oldDatas
  have wf4 : wf_store s4 := .store_case_ _ _ _ _ _ _ (forall_append oldFunctions newFunctions) (forall_append oldGlobals globalsWf) (forall_append oldTables newTables) (forall_append oldMemories newMemories) oldDatas
  have wf5 : wf_store s5 := .store_case_ _ _ _ _ _ _ (forall_append oldFunctions newFunctions) (forall_append oldGlobals globalsWf) (forall_append oldTables newTables) (forall_append oldMemories newMemories) oldDatas
  have wf6 : wf_store s6 := .store_case_ _ _ _ _ _ _ (forall_append oldFunctions newFunctions) (forall_append oldGlobals globalsWf) (forall_append oldTables newTables) (forall_append oldMemories newMemories) (forall_append oldDatas datasWf)
  have exportsResolved : Forall₂ (fun allocated ex => fun_instexport
      (importedFunctions ++ List.range' s.FUNCS.length functions.length)
      (importedGlobals ++ List.range' s.GLOBALS.length globals.length)
      (importedTables ++ List.range' s.TABLES.length tables.length)
      (importedMemories ++ List.range' s.MEMS.length memories.length) ex allocated) exportInstances exports := by
    intro pair member
    have proof := List.forall₂_zip resolvedExports.flip member
    simpa only [layout] using proof
  refine fun_allocmodule.fun_allocmodule_case_0 s source externals (globals.map globalinst.VALUE)
    (elements.map eleminst.REFS) s6 inst types imports functions.length functions globals.length
    globalExpressions (globals.map globalinst.TYPE) tables.length tables memories.length memories
    elements.length elementModes elementExpressions (elements.map eleminst.TYPE) datas.length
    (datas.map datainst.BYTES) dataModes start exports s1 s2 s3 s4 s5
    importedFunctions importedGlobals importedTables importedMemories
    (List.range' s.FUNCS.length functions.length) (List.range' s.GLOBALS.length globals.length)
    (List.range' s.TABLES.length tables.length) (List.range' s.MEMS.length memories.length)
    (List.range' s.ELEMS.length elements.length) (List.range' s.DATAS.length datas.length)
    exportInstances _ _ _ _ _ _ exportInstances importedMemories importedTables importedGlobals importedFunctions
    d e m t g f resolvedExports.length_eq.symm exportsResolved importMemories importTables importGlobals importFunctions
    sourceEq rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ rfl layout rfl rfl rfl rfl rfl rfl
    wf6 instanceWf wf1 wf2 wf3 wf4 wf5 ?_ ?_
  all_goals first
    | exact List.range'_eq_map_range
    | simpa only [← sourceEq, Map] using sourceWf
    | simpa only [← layout] using instanceWf
end Itasca.Spec

end

/-! ## SplitCopy -/

section

namespace Itasca.Spec.Segment

/-- A write in the left half of a split buffer reconstructs the corresponding
write in the original buffer. -/
theorem set_slice_split_left {T : Type} (before payload : List T) (split start : Nat)
    (splitBound : split ≤ before.length) (inside : start+payload.length ≤ split) :
    (before.take split).setSlice! start payload ++ before.drop split = before.setSlice! start payload := by
  have leftRoom : payload.length ≤ (before.take split).length-start := by simp only [List.length_take]; omega
  have wholeRoom : payload.length ≤ before.length-start := by omega
  simp only [List.setSlice!,Nat.min_eq_left leftRoom,Nat.min_eq_left wholeRoom,List.take_length]
  rw [List.take_take, Nat.min_eq_left (by omega : start ≤ split)]
  rw [List.drop_take]
  have combine := List.take_append_drop (split-(start+payload.length)) (before.drop (start+payload.length))
  rw [List.drop_drop] at combine
  have total : start+payload.length+(split-(start+payload.length))=split := by omega
  rw [total] at combine
  simpa only [List.append_assoc] using congrArg (fun rest => before.take start ++ payload ++ rest) combine

/-- A write starting at the right half reconstructs its original-buffer write. -/
theorem set_slice_split_right {T : Type} (before payload : List T) (split : Nat)
    (inside : split+payload.length ≤ before.length) :
    before.take split ++ (before.drop split).setSlice! 0 payload = before.setSlice! split payload := by
  have room : payload.length ≤ before.length-split := by omega
  simp [List.setSlice!,room,List.drop_drop,Nat.min_eq_left room,List.append_assoc]
end Itasca.Spec.Segment

end

/-! ## PureWf -/

section

namespace Itasca.Spec
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem pure_output_wf {before after : List admininstr} (step : Step_pure before after) :
    Forall wf_admininstr after := by
  cases step
  all_goals simp_all only [Forall,List.mem_cons,List.not_mem_nil,false_implies,implies_true,forall_eq_or_imp,true_and]
  all_goals try { solve | simp_all [wf_admininstr_val] }
  all_goals cases_type wf_admininstr
  all_goals simp_all [Forall,List.mem_append]
  all_goals simp only [Map,List.mem_map] at *
  all_goals aesop (add safe apply wf_admininstr_instr)

theorem val_wf_of_admin {value : val} (h : wf_admininstr (admininstr_val value)) :
    wf_val value := by
  cases value <;> cases h <;> constructor <;> assumption

theorem pure_singleton_wf {before : List admininstr} {value : val}
    (step : Step_pure before [admininstr_val value]) : wf_val value := by
  exact val_wf_of_admin (pure_output_wf step _ (by simp))

theorem pure_i32_bound {before : List admininstr} {n : Nat}
    (step : Step_pure before [admininstr_val (.CONST .I32 (.mk_num__0 .I32 (.mk_uN n)))]) :
    n < 2^32 := by
  have h := pure_singleton_wf step
  cases h
  cases_type wf_num_
  cases_type wf_uN
  norm_num [size,valtype_Inn] at *
  omega
end Itasca.Spec

end

/-! ## EventfulInfinite -/

section

namespace Itasca.Spec
open WebAssembly

theorem InfiniteSourceWithEvents.prepend {initial next : config} {events : List HostEvent}
    (infinite : InfiniteSourceWithEvents next) (steps : StepsH initial events next) :
    InfiniteSourceWithEvents initial := by
  obtain ⟨states,trace,first,edges⟩ := infinite
  obtain ⟨prefixCount,prefixSteps⟩ := steps_h_count steps
  refine ⟨(fun n => match n with | 0 => initial | n+1 => states (n+1)),
    (fun n => match n with | 0 => events ++ trace 0 | n+1 => trace (n+1)),rfl,?_⟩
  intro n
  cases n with
  | zero =>
    obtain ⟨count,positive,edge⟩ := edges 0
    rw [first] at edge
    exact ⟨prefixCount+count,by omega,by simpa using prefixSteps.trans edge⟩
  | succ n => exact edges (n+1)

/-- Conditional simulation plumbing: total concrete successors and strict
administrative decrease yield a positive source chunk with a real finite
concrete history. No fixed bound on future host-published code is assumed. -/
theorem positive_history_of_decreasing_stutter {S : Type}
    (next : S → List HostEvent → S → Prop) (decode : S → config) (potential : S → Nat)
    (successor : ∀ s, ∃ events after, next s events after)
    (simulation : ∀ s events after, next s events after →
      (decode s = decode after ∧ events = [] ∧ potential after < potential s) ∨
      ∃ count, 0 < count ∧ StepsHN count (decode s) events (decode after))
    (initial : S) :
    ∃ after events dispatches count, 0 < dispatches ∧
      Iterations next dispatches initial events after ∧ 0 < count ∧
      StepsHN count (decode initial) events (decode after) := by
  have bounded : ∀ budget s, potential s ≤ budget →
      ∃ after events dispatches count, 0 < dispatches ∧
        Iterations next dispatches s events after ∧ 0 < count ∧
        StepsHN count (decode s) events (decode after) := by
    intro budget
    induction budget with
    | zero =>
      intro s bound
      obtain ⟨events,after,edge⟩ := successor s
      rcases simulation s events after edge with ⟨same,empty,decrease⟩ | ⟨count,positive,steps⟩
      · omega
      · exact ⟨after,events,1,count,by omega,by simpa using Iterations.cons edge (.refl after),positive,steps⟩
    | succ budget ih =>
      intro s bound
      obtain ⟨events,after,edge⟩ := successor s
      rcases simulation s events after edge with ⟨same,rfl,decrease⟩ | ⟨count,positive,steps⟩
      · obtain ⟨last,trace,dispatches,count,nonempty,history,positive,steps⟩ := ih after (by omega)
        exact ⟨last,trace,dispatches+1,count,by omega,by simpa using Iterations.cons edge history,
          positive,by simpa only [same] using steps⟩
      · exact ⟨after,events,1,count,by omega,by simpa using Iterations.cons edge (.refl after),positive,steps⟩
  exact bounded (potential initial) initial (Nat.le_refl _)

/-- The infinite source chunks are backed by consecutive histories of `next`.
A runtime application must establish `successor` and `simulation` from its
actual loop; this lemma alone makes no claim about interpreter execution. -/
theorem infinite_histories_of_decreasing_stutter {S : Type}
    (next : S → List HostEvent → S → Prop) (decode : S → config) (potential : S → Nat)
    (successor : ∀ s, ∃ events after, next s events after)
    (simulation : ∀ s events after, next s events after →
      (decode s = decode after ∧ events = [] ∧ potential after < potential s) ∨
      ∃ count, 0 < count ∧ StepsHN count (decode s) events (decode after))
    (initial : S) :
    ∃ states : Nat → S, ∃ events : Nat → List HostEvent,
      states 0 = initial ∧ ∀ n, ∃ dispatches count, 0 < dispatches ∧
        Iterations next dispatches (states n) (events n) (states (n+1)) ∧
        0 < count ∧ StepsHN count (decode (states n)) (events n) (decode (states (n+1))) := by
  classical
  have advance := positive_history_of_decreasing_stutter next decode potential successor simulation
  let stateAfter (s : S) : S := Classical.choose (advance s)
  let traceAfter (s : S) : List HostEvent := Classical.choose (Classical.choose_spec (advance s))
  let states : Nat → S := fun n => Nat.rec initial (fun _ previous => stateAfter previous) n
  refine ⟨states,fun n => traceAfter (states n),rfl,?_⟩
  intro n
  exact Classical.choose_spec (Classical.choose_spec (advance (states n)))

theorem infinite_source_of_decreasing_stutter {S : Type}
    (next : S → List HostEvent → S → Prop) (decode : S → config) (potential : S → Nat)
    (successor : ∀ s, ∃ events after, next s events after)
    (simulation : ∀ s events after, next s events after →
      (decode s = decode after ∧ events = [] ∧ potential after < potential s) ∨
      ∃ count, 0 < count ∧ StepsHN count (decode s) events (decode after))
    (initial : S) : InfiniteSourceWithEvents (decode initial) := by
  obtain ⟨states,events,first,edges⟩ :=
    infinite_histories_of_decreasing_stutter next decode potential successor simulation initial
  refine ⟨fun n => decode (states n),events,congrArg decode first,?_⟩
  intro n
  obtain ⟨dispatches,count,nonempty,history,positive,steps⟩ := edges n
  exact ⟨count,positive,steps⟩
end Itasca.Spec

end

/-! ## HostCall -/

section

namespace Itasca.Spec
open WebAssembly

/-- Typed source arguments make a host-call redex well formed. -/
theorem host_call_wf {s : store} {f : frame} {fa : funcaddr}
    {params : List valtype} {args : List val}
    (source : wf_store s) (ambient : wf_frame f) (typed : ResultsTyped s params args) :
    wf_config ⟨⟨s, f⟩, vals args ++ [.CALL_ADDR fa]⟩ := by
  apply wf_config_make source ambient
  apply forall_append (wf_vals (results_typed_wf typed))
  intro instruction member
  have same := List.mem_singleton.mp member
  subst instruction
  exact .admininstr_case_70 fa

/-- A host result that passed the concrete type check supplies the independent
host extension's result-typing premise and records the returned source values. -/
theorem host_return_step {s s' : store} {f : frame} {fa : funcaddr} {id : Nat}
    {params results : List valtype} {args returned : List val}
    (host : HostFunction s fa id params results)
    (arguments : ResultsTyped s params args) (extension : Extend_store s s')
    (sourceTyped : Store_ok s')
    (typed : ResultsTyped s' results returned) (ambient : wf_frame f) :
    StepH ⟨⟨s, f⟩, vals args ++ [.CALL_ADDR fa]⟩ [.call fa args (some returned)]
      ⟨⟨s', f⟩, vals returned⟩ := by
  have stores := extend_store_wf extension
  exact .host_return host arguments extension sourceTyped typed
    (host_call_wf stores.1 ambient arguments)
    (wf_config_vals stores.2 ambient (results_typed_wf typed))

/-- Explicit host traps and rejected host results share the same atomic source
trap transition, including all callback store effects. -/
theorem host_trap_step {s s' : store} {f : frame} {fa : funcaddr} {id : Nat}
    {params results : List valtype} {args : List val}
    (host : HostFunction s fa id params results)
    (arguments : ResultsTyped s params args) (extension : Extend_store s s')
    (sourceTyped : Store_ok s')
    (ambient : wf_frame f) :
    StepH ⟨⟨s, f⟩, vals args ++ [.CALL_ADDR fa]⟩ [.call fa args none]
      ⟨⟨s', f⟩, [.TRAP]⟩ := by
  have stores := extend_store_wf extension
  exact .host_trap host arguments extension sourceTyped (host_call_wf stores.1 ambient arguments)
    (wf_config_trap stores.2 ambient)
end Itasca.Spec

end

/-! ## Depth -/

section

/-!
Administrative frame depth, excluding the ambient frame. Source invocation resource arguments use this nesting measure independently of runtime slots.
-/

namespace Itasca.Spec

@[simp] theorem instrs_depth_nil : instrsDepth [] = 0 := rfl

@[simp] theorem instrs_depth_append (xs ys : List admininstr) :
    instrsDepth (xs ++ ys) = max (instrsDepth xs) (instrsDepth ys) := by
  induction xs with
  | nil => simp [instrsDepth]
  | cons ai rest ih => simp [instrsDepth, ih, Nat.max_assoc]

@[simp] theorem instrs_depth_singleton (ai : admininstr) :
    instrsDepth [ai] = instrDepth ai := by simp [instrsDepth]

end Itasca.Spec

end

end
