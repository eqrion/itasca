import Itasca.Runtime.Spec.TableInit
import Itasca.Runtime.Spec.Wf
import Mathlib.Tactic
import SpecExt.Builtins.Bytes
import Itasca.Runtime.Spec.SegmentCopy

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
