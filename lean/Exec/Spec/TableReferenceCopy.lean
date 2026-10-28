import Exec.Spec.TableCopySource
import Exec.Spec.TableAccess
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
  have loaded := stepH_instrs (table_get_step s f sourceTable source hs hf hy hi)
    [.CONST .I32 (.mk_num__0 .I32 (.mk_uN destination))] [.TABLE_SET (.mk_uN targetTable)]
    (by simpa [Forall] using wf_val.val_case_0 _ _ ((by cases i32_wf destination hd; assumption)))
    (by simpa [Forall] using wf_admininstr.admininstr_case_49 _ (index_wf _ ht))
  have stored := table_write_step s f targetTable destination (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS[source]! hs hf hd ht mapped targetInside
  exact stepsH_trans (stepsH_single (by simpa [instrContext,vals,admininstr_val,i32,sourceInside] using loaded)) (stepsH_single stored)

theorem tableWrite_other_length (s : store) (f : frame) (index other position : Nat) (value : ref)
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
