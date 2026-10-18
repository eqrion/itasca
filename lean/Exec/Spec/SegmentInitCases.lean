import Exec.Spec.Wf
import Mathlib.Tactic

namespace Exec.Spec.Segment
open SpecExt

def i32 (bits : Nat) : admininstr := .CONST .I32 (.mk_num__0 .I32 (.mk_uN bits))
def operands (destination source count : Nat) : List admininstr := [i32 destination, i32 source, i32 count]

theorem index_wf (bits : Nat) (bound : bits < 2^32) : wf_uN 32 (.mk_uN bits) :=
  .uN_case_0 _ _ (by norm_num; omega)

theorem i32_wf (bits : Nat) (bound : bits < 2^32) : wf_admininstr (i32 bits) := by
  apply wf_admininstr.admininstr_case_13
  exact .num__case_0 .I32 .I32 _ (by decide) (index_wf bits bound) rfl

theorem init_config_wf (s : store) (f : frame) (destination source count : Nat) (instruction : admininstr)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32) (hn : count < 2^32)
    (hw : wf_admininstr instruction) : wf_config ⟨⟨s,f⟩,operands destination source count ++ [instruction]⟩ := by
  apply wf_config_make hs hf
  simpa only [operands, Forall, List.mem_cons, List.mem_singleton, List.cons_append, List.nil_append,
    forall_eq_or_imp, forall_eq, List.not_mem_nil, false_implies, forall_const, and_true] using And.intro (i32_wf destination hd) (And.intro (i32_wf source hi) (And.intro (i32_wf count hn) hw))

theorem table_init_trap (s : store) (f : frame) (destination source count tableIndex elementIndex : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32) (hn : count < 2^32)
    (ht : tableIndex < 2^32) (he : elementIndex < 2^32)
    (outside : source + count > (fun_elem ⟨s,f⟩ (.mk_uN elementIndex)).REFS.length ∨
      destination + count > (fun_table ⟨s,f⟩ (.mk_uN tableIndex)).REFS.length) :
    StepH ⟨⟨s,f⟩,operands destination source count ++ [.TABLE_INIT (.mk_uN tableIndex) (.mk_uN elementIndex)]⟩ []
      ⟨⟨s,f⟩,[.TRAP]⟩ := by
  have input := init_config_wf s f destination source count _ hs hf hd hi hn
    (.admininstr_case_54 _ _ (index_wf tableIndex ht) (index_wf elementIndex he))
  have output : wf_config ⟨⟨s,f⟩,[.TRAP]⟩ := wf_config_make hs hf (by simp [Forall]; exact .admininstr_case_73)
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  apply Step_read.table_init_trap
  · simp [proj_num__0]
  · simp [proj_num__0]
  · simpa only [proj_num__0, Option.get!, proj_uN_0] using outside
  · exact input
  · exact .admininstr_case_73

theorem table_init_zero (s : store) (f : frame) (destination source tableIndex elementIndex : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32)
    (ht : tableIndex < 2^32) (he : elementIndex < 2^32)
    (inside : source ≤ (fun_elem ⟨s,f⟩ (.mk_uN elementIndex)).REFS.length ∧
      destination ≤ (fun_table ⟨s,f⟩ (.mk_uN tableIndex)).REFS.length) :
    StepH ⟨⟨s,f⟩,operands destination source 0 ++ [.TABLE_INIT (.mk_uN tableIndex) (.mk_uN elementIndex)]⟩ []
      ⟨⟨s,f⟩,[]⟩ := by
  have input := init_config_wf s f destination source 0 _ hs hf hd hi (by norm_num)
    (.admininstr_case_54 _ _ (index_wf tableIndex ht) (index_wf elementIndex he))
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_make hs hf (by simp [Forall]))
  apply Step_read.table_init_zero
  · simp [proj_num__0]
  · simp [proj_num__0]
  · simpa only [proj_num__0, Option.get!, proj_uN_0, Nat.add_zero] using inside
  · rfl
  · exact input


theorem memory_init_trap (s : store) (f : frame) (destination source count dataIndex : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32) (hn : count < 2^32)
    (he : dataIndex < 2^32)
    (outside : source + count > (fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES.length ∨
      destination + count > (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length) :
    StepH ⟨⟨s,f⟩,operands destination source count ++ [.MEMORY_INIT (.mk_uN dataIndex)]⟩ []
      ⟨⟨s,f⟩,[.TRAP]⟩ := by
  have input := init_config_wf s f destination source count _ hs hf hd hi hn
    (.admininstr_case_66 _ (index_wf dataIndex he))
  have output : wf_config ⟨⟨s,f⟩,[.TRAP]⟩ := wf_config_make hs hf (by simp [Forall]; exact .admininstr_case_73)
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  apply Step_read.memory_init_trap
  · simp [proj_num__0]
  · simp [proj_num__0]
  · simpa only [proj_num__0, Option.get!, proj_uN_0] using outside
  · exact input
  · exact .admininstr_case_73

  · exact index_wf 0 (by norm_num)

theorem memory_init_zero (s : store) (f : frame) (destination source dataIndex : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32)
    (he : dataIndex < 2^32)
    (inside : source ≤ (fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES.length ∧
      destination ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length) :
    StepH ⟨⟨s,f⟩,operands destination source 0 ++ [.MEMORY_INIT (.mk_uN dataIndex)]⟩ []
      ⟨⟨s,f⟩,[]⟩ := by
  have input := init_config_wf s f destination source 0 _ hs hf hd hi (by norm_num)
    (.admininstr_case_66 _ (index_wf dataIndex he))
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_make hs hf (by simp [Forall]))
  apply Step_read.memory_init_zero
  · simp [proj_num__0]
  · simp [proj_num__0]
  · simpa only [proj_num__0, Option.get!, proj_uN_0, Nat.add_zero] using inside
  · rfl
  · exact input


end Exec.Spec.Segment
