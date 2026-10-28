import Itasca.Runtime.Spec.TableFillSource
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
