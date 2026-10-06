import Itasca.ModuleIndexSpaces

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

theorem refFunc_wf (idx : U32) : wf_instr (.REF_FUNC (.mk_uN idx.val)) :=
  .instr_case_41 _ (EnvTranslation.index_wf idx)

theorem refFunc_const (C : context) (hC : wf_context C) (idx : U32)
    (hi : idx.val < C.FUNCS.length) :
    Expr_ok_const C [.REF_FUNC (.mk_uN idx.val)] .FUNCREF := by
  have hw := refFunc_wf idx
  have hws : Forall wf_instr [instr.REF_FUNC (.mk_uN idx.val)] := by simpa [Forall] using hw
  have ht : Instr_ok C (.REF_FUNC (.mk_uN idx.val)) (.mk_functype (.mk_list []) (.mk_list [.FUNCREF])) :=
    .ref_func C _ C.FUNCS[idx.val]! hi rfl hC hw
  exact .mk_Expr_ok_const C _ _
    (.mk_Expr_ok C _ _ (.instr C _ [] _ ht hC hw) hC hws)
    (.mk_Expr_const C _ (by simpa [Forall] using Instr_const.ref_func C _ hC hw) hC hws)
    hC hws

theorem element_wf (entry : ModuleBinary.Element) : wf_elem (element entry) := by
  constructor
  · simp only [Forall, List.mem_map]
    rintro _ ⟨idx, _, rfl⟩
    simpa [Forall] using refFunc_wf idx
  · exact .elemmode_case_0 _ _ (EnvTranslation.index_wf entry.tableIdx)
      (ModuleConstants.expression_wf entry.offset)

theorem element_typed {env : module.Env} (hv : ModuleEnv.Valid env)
    (entry : module.Element) (he : entry ∈ env.elements.val) :
    Elem_ok (initializerContext env) (element (ModuleEnv.rawElement entry)) .FUNCREF := by
  obtain ⟨hi, hoffset, hfuncs⟩ := hv.elements entry he
  let C := initializerContext env
  have hC : wf_context C := initializerContext_wf env
  dsimp only [element, ModuleEnv.rawElement]
  apply Elem_ok.mk_Elem_ok C .FUNCREF _ _
  · simp only [Forall, List.mem_map]
    rintro _ ⟨idx, hidx, rfl⟩
    exact refFunc_const C hC idx (by simpa [C, initializerContext, moduleContext] using hfuncs idx hidx)
  · apply Elemmode_ok.active C _ _ .FUNCREF
      (EnvTranslation.limitsType env.table_types.val[entry.table_idx.val].limits)
    · simpa [C, initializerContext, moduleContext, proj_uN_0] using hi
    · simp only [C, initializerContext, moduleContext, proj_uN_0]
      rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map]
      rfl
    · exact hoffset.expr_ok_const C hC rfl
    · exact hC
    · exact .elemmode_case_0 _ _ (EnvTranslation.index_wf entry.table_idx)
        (ModuleConstants.expression_wf entry.offset)
    · exact EnvTranslation.tableType_wf _
  · exact hC
  · exact element_wf (ModuleEnv.rawElement entry)

theorem table_typed {env tables memories} (hc : ModuleEnv.Cache env tables memories)
    (hv : ModuleEnv.Valid env) (tt : types.TableType) (ht : tt ∈ tables)
    (C : context) (hC : wf_context C) :
    Table_ok C (table tt) (EnvTranslation.tableType tt) := by
  have hm : tt ∈ env.table_types.val := by rw [hc.tables]; exact List.mem_append_right _ ht
  exact .mk_Table_ok C _ (ModuleTranslation.tableType_valid tt (hv.tables tt hm)) hC
    (.table_case_0 _ (EnvTranslation.tableType_wf tt))

theorem memory_typed {env tables memories} (hc : ModuleEnv.Cache env tables memories)
    (hv : ModuleEnv.Valid env) (mt : types.MemType) (ht : mt ∈ memories)
    (C : context) (hC : wf_context C) :
    Mem_ok C (memory mt) (EnvTranslation.memType mt) := by
  have hm : mt ∈ env.mem_types.val := by rw [hc.memories]; exact List.mem_append_right _ ht
  exact .mk_Mem_ok C _ (ModuleTranslation.memType_valid mt (hv.memories mt hm)) hC
    (.mem_case_0 _ (EnvTranslation.memType_wf mt))

end Itasca.ModuleElaboration
