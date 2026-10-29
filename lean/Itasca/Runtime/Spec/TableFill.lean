import Itasca.Runtime.Spec.TableInit

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
