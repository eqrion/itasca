import Exec.Spec.TableReferenceCopy
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
  | zero => exact stepsH_single (table_copy_zero s f destination source targetTable sourceTable hs hf hd hi ht hy (by simpa using inside))
  | succ count ih =>
    have order : destination ≤ source := by omega
    have srcInside : source < (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS.length := by omega
    let value := (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS[source]!
    let fresh := tableWrite s f targetTable destination value
    have hw := tableWrite_wf s f targetTable destination value hs
    have lengthEq := tableWrite_table_length s f targetTable destination value address
    have sourceLengthEq := tableWrite_other_length s f targetTable sourceTable destination value sourceAddress
    have afterWf := (wf_config_parts (init_config_wf fresh f (destination+1) (source+1) count _ hw hf
      (by omega) (by omega) (by omega) (.admininstr_case_53 _ _ (index_wf _ ht) (index_wf _ hy)))).2
    have first := table_copy_forward_expand s f destination source count targetTable sourceTable hs hf (by omega) (by omega) hn ht hy inside order
    have second := stepsH_instrs (table_copy_reference_steps s f destination source targetTable sourceTable hs hf hd hi ht hy mapped srcInside (by omega)) []
      (operands (destination+1) (source+1) count ++ [(.TABLE_COPY (.mk_uN targetTable) (.mk_uN sourceTable))]) (by simp [Forall]) afterWf
    have rest := ih fresh (destination+1) (source+1) hw (by omega) (by omega) (by omega)
      (by simpa [fresh,tableWrite] using address) (by simpa [fresh,tableWrite] using sourceAddress)
      (by simpa only [fresh,lengthEq,sourceLengthEq] using tableBounds)
      (by rw [show (fun_table ⟨fresh,f⟩ (.mk_uN sourceTable)).REFS.length = (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS.length from sourceLengthEq,
              show (fun_table ⟨fresh,f⟩ (.mk_uN targetTable)).REFS.length = (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS.length from lengthEq]; omega)
      (Or.inl (by omega))
    have combined := stepsH_trans (stepsH_single first) (stepsH_trans second rest)
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
  | zero => exact stepsH_single (table_copy_zero s f destination source targetTable sourceTable hs hf hd hi ht hy (by simpa using inside))
  | succ count ih =>
    have order : source < destination := by omega
    have srcInside : source+count < (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS.length := by omega
    let value := (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS[source+count]!
    let fresh := tableWrite s f targetTable (destination+count) value
    have hw := tableWrite_wf s f targetTable (destination+count) value hs
    have lengthEq := tableWrite_table_length s f targetTable (destination+count) value address
    have sourceLengthEq := tableWrite_other_length s f targetTable sourceTable (destination+count) value sourceAddress
    have afterWf := (wf_config_parts (init_config_wf fresh f destination source count _ hw hf hd hi
      (by omega) (.admininstr_case_53 _ _ (index_wf _ ht) (index_wf _ hy)))).2
    have first := table_copy_backward_expand s f destination source count targetTable sourceTable hs hf hd hi hn ht hy inside tableBounds order
    have second := stepsH_instrs (table_copy_reference_steps s f (destination+count) (source+count) targetTable sourceTable hs hf (by omega) (by omega) ht hy mapped srcInside (by omega)) [] (operands destination source count ++ [(.TABLE_COPY (.mk_uN targetTable) (.mk_uN sourceTable))]) (by simp [Forall]) afterWf
    have rest := ih fresh hw (by omega) (by simpa [fresh,tableWrite] using address)
      (by simpa [fresh,tableWrite] using sourceAddress)
      (by simpa only [fresh,lengthEq,sourceLengthEq] using tableBounds)
      (by rw [show (fun_table ⟨fresh,f⟩ (.mk_uN sourceTable)).REFS.length = (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS.length from sourceLengthEq,
              show (fun_table ⟨fresh,f⟩ (.mk_uN targetTable)).REFS.length = (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS.length from lengthEq]; omega)
      (Or.inl order)
    have combined := stepsH_trans (stepsH_single first) (stepsH_trans second rest)
    simpa only [instrContext,vals,List.map_nil,List.nil_append,List.append_nil,tableCopyBackward,value,fresh] using combined
end Itasca.Runtime.Spec.Segment
