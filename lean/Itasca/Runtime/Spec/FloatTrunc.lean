import Itasca.Runtime.Spec.SegmentInitCases
import Itasca.Runtime.Spec.Integer
import Mathlib.Tactic
import SpecExt.Builtins.Examples
import SpecExt.Builtins.Float.Sign
import SpecExt.Builtins.Float.MinMax
import Aeneas.Data.List.List

/-!
Sections, each formerly its own module: TableInit, Globals, ByteEncoding, MemoryLoad, SegmentCopySlice, SegmentDrops, IntegerDeterminism, FloatPure, FloatComparison, FloatMinMax, FloatConvert, FloatReinterpret, FloatSigns, FloatTrunc.
-/

/-! ## TableInit -/

section

/-!
Source semantics of `table.init`. Connect the generated recursive rules to the bounded interval update used by runtime correspondence proofs.
-/

/-! ## Table Init Source -/

section

namespace Itasca.Runtime.Spec.Segment
open SpecExt

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

end Itasca.Runtime.Spec.Segment

end

/-! ## Table Init Algebra -/

section

namespace Itasca.Runtime.Spec.Segment
open SpecExt

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

end Itasca.Runtime.Spec.Segment

end

end

/-! ## Globals -/

section

namespace Itasca.Runtime.Spec
open SpecExt

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
end Itasca.Runtime.Spec

end

/-! ## ByteEncoding -/

section

namespace Itasca.Runtime.Spec
open SpecExt.Builtins

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
    apply Float.floatOfBits_wf_32
    rw [sized] at bounded
    simpa using bounded
  · apply wf_num_.num__case_1 .F64 .F64 _ _ rfl
    apply Float.floatOfBits_wf_64
    rw [sized] at bounded
    simpa using bounded
end Itasca.Runtime.Spec

end

/-! ## MemoryLoad -/

section

namespace Itasca.Runtime.Spec
open SpecExt

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
end Itasca.Runtime.Spec

end

/-! ## SegmentCopySlice -/

section

namespace Itasca.Runtime.Spec.Segment

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
end Itasca.Runtime.Spec.Segment

end

/-! ## SegmentDrops -/

section

namespace Itasca.Runtime.Spec
open SpecExt

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

end Itasca.Runtime.Spec

end

/-! ## IntegerDeterminism -/

section

namespace Itasca.Runtime.Spec

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
end Itasca.Runtime.Spec

end

/-! ## FloatPure -/

section

namespace Itasca.Runtime.Spec
open SpecExt

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
end Itasca.Runtime.Spec

end

/-! ## FloatComparison -/

section

namespace Itasca.Runtime.Spec
open SpecExt

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

end Itasca.Runtime.Spec

end

/-! ## FloatMinMax -/

section

namespace Itasca.Runtime.Spec
open SpecExt SpecExt.Builtins SpecExt.Builtins.Float

theorem float_min_wf (width : Nat) (hw : width = 32 ∨ width = 64) (a b : fN)
    (ha : wf_fN width a) (hb : wf_fN width b) :
    Forall (wf_fN width) (fmin_ width a b) := by
  unfold fmin_
  split_ifs
  · exact nans_wf width hw _
  · exact singleton_wf (withSign_wf (zero_wf width) _)
  · exact singleton_wf ha
  · exact singleton_wf hb

theorem float_max_wf (width : Nat) (hw : width = 32 ∨ width = 64) (a b : fN)
    (ha : wf_fN width a) (hb : wf_fN width b) :
    Forall (wf_fN width) (fmax_ width a b) := by
  unfold fmax_
  split_ifs
  · exact nans_wf width hw _
  · exact singleton_wf (withSign_wf (zero_wf width) _)
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

end Itasca.Runtime.Spec

end

/-! ## FloatConvert -/

section

namespace Itasca.Runtime.Spec
open SpecExt SpecExt.Builtins SpecExt.Builtins.Float

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
end Itasca.Runtime.Spec
namespace Itasca.Runtime.Spec
open SpecExt SpecExt.Builtins SpecExt.Builtins.Float

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
  · exact canonicalNaNs_wf target width
  · exact arithmeticNaNs_wf target width
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
end Itasca.Runtime.Spec

end

/-! ## FloatReinterpret -/

section

namespace Itasca.Runtime.Spec
open SpecExt SpecExt.Builtins SpecExt.Builtins.Float

theorem f32_reinterpret_i32_pure (bits : Nat) (bound : bits < 2 ^ 32) :
    Step_pure [.CONST .I32 (.mk_num__0 .I32 (.mk_uN bits)), .CVTOP .F32 .I32 (.mk_cvtop___1 .I32 .F32 .REINTERPRET)]
      [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 bits))] := by
  have iw := unsigned_num_wf .I32 bits bound
  have fw := float_num_wf .F32 _ (floatOfBits_wf 32 (by omega) bits)
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
  have fw := float_num_wf .F32 _ (floatOfBits_wf 32 (by omega) bits)
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
  have fw := float_num_wf .F64 _ (floatOfBits_wf 64 (by omega) bits)
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
  have fw := float_num_wf .F64 _ (floatOfBits_wf 64 (by omega) bits)
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

end Itasca.Runtime.Spec

end

/-! ## FloatSigns -/

section

namespace Itasca.Runtime.Spec
open SpecExt SpecExt.Builtins.Float

theorem float_abs_wf (width : Nat) (a : fN) (ha : wf_fN width a) :
    Forall (wf_fN width) (fabs_ width a) := by
  apply singleton_wf
  exact .fN_case_0 _ _ (magnitude_wf ha)

theorem float_neg_wf (width : Nat) (a : fN) (ha : wf_fN width a) :
    Forall (wf_fN width) (fneg_ width a) := by
  exact singleton_wf (withSign_wf (magnitude_wf ha) _)

theorem float_copysign_wf (width : Nat) (a b : fN) (ha : wf_fN width a) :
    Forall (wf_fN width) (fcopysign_ width a b) := by
  exact singleton_wf (withSign_wf (magnitude_wf ha) _)

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
end Itasca.Runtime.Spec

end

/-! ## FloatTrunc -/

section

namespace Itasca.Runtime.Spec
open SpecExt SpecExt.Builtins SpecExt.Builtins.Float

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
end Itasca.Runtime.Spec

end
