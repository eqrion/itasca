import Itasca.Runtime.Spec.SegmentInitCases
import Itasca.Runtime.Spec.Context
import Mathlib.Tactic

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

theorem tableWrite_wf (s : store) (f : frame) (index position : Nat) (value : ref)
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
  have fresh := tableWrite_wf s f index position value hs
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

theorem tableWrite_table_length (s : store) (f : frame) (index position : Nat) (value : ref)
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
  | zero => exact stepsH_single (table_init_zero s f destination source tableIndex elementIndex hs hf hd hi ht he inside)
  | succ count ih =>
    have hd' : destination+1 < 2^32 := by omega
    have hi' : source+1 < 2^32 := by omega
    let value := (fun_elem ⟨s,f⟩ (.mk_uN elementIndex)).REFS[source]!
    let fresh := tableWrite s f tableIndex destination value
    have hw := tableWrite_wf s f tableIndex destination value hs
    have lengthEq := tableWrite_table_length s f tableIndex destination value address
    have afterWf := (wf_config_parts (init_config_wf fresh f (destination+1) (source+1) count _ hw hf hd' hi'
      (by omega) (.admininstr_case_54 _ _ (index_wf _ ht) (index_wf _ he)))).2
    have first := table_init_expand s f destination source count tableIndex elementIndex hs hf hd' hi' hn ht he inside
    have second := stepH_instrs (table_write_step s f tableIndex destination value hs hf hd ht mapped (by omega)) []
      (operands (destination+1) (source+1) count ++ [.TABLE_INIT (.mk_uN tableIndex) (.mk_uN elementIndex)])
      (by simp [Forall]) afterWf
    have rest := ih fresh (destination+1) (source+1) hw hd' hi' (by omega)
      (by simpa [fresh,tableWrite] using address)
      (by simpa only [fresh,lengthEq] using tableBound) elementBound
      (by rw [show (fun_table ⟨fresh,f⟩ (.mk_uN tableIndex)).REFS.length =
            (fun_table ⟨s,f⟩ (.mk_uN tableIndex)).REFS.length from lengthEq]
          simpa only [fresh,tableWrite,fun_elem,Nat.add_assoc,Nat.add_comm 1 count] using inside)
    have combined := stepsH_trans (stepsH_single first) (stepsH_trans (stepsH_single second) rest)
    simpa only [instrContext,vals,List.map_nil,List.nil_append,List.append_nil,tableInit,value,fresh] using combined

end Itasca.Runtime.Spec.Segment
