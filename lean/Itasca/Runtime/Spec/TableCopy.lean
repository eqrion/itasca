import Itasca.Runtime.Spec.TableFill
import Itasca.Runtime.Spec.TableAccess
import Itasca.Runtime.Spec.CopyPlain

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
