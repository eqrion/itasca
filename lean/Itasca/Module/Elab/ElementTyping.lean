import Itasca.Module.Elab.IndexSpaces
import Itasca.Module.Elab.SegmentTyping

/-!
# Element, table and memory typing

Generated typing judgments (`Elem_ok`, `Table_ok`, `Mem_ok`) for the elements, tables and
memories of a valid cached environment, in the initializer context, and the `ref.func` constant
expression used by function reference initializers.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

/-- `ref.func` of a 32-bit index is a well-formed instruction. -/
theorem refFunc_wf (idx : U32) : wf_instr (.REF_FUNC (.mk_uN idx.val)) :=
  .instr_case_41 _ (EnvTranslation.index_wf idx)

/-- `ref.func idx` is a constant `funcref` expression when `idx` is a function index of `C`. -/
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

/-- An elaborated element segment is well formed. -/
theorem element_wf (entry : ModuleBinary.Element) : wf_elem (element entry) := by
  constructor
  · simp only [Forall, List.mem_map]
    rintro _ ⟨init, _, rfl⟩
    exact ModuleConstants.expression_wf init
  · exact ModuleSegments.elementMode_wf entry.mode

/-- Each element segment of a valid environment is typed in the initializer context. -/
theorem element_typed {env : module.Env} {profile : ValidationProfile} (hv : ModuleEnv.Valid env profile)
    (entry : module.Element) (he : entry ∈ env.elements.val) :
    Elem_ok (initializerContext env) (element (ModuleEnv.rawElement entry))
      (Translate.referenceType entry.elem) := by
  exact (hv.elements entry he).typed (initializerContext env) (initializerContext_wf env)
    rfl rfl rfl

/-- Each defined table of a valid cached environment is typed in any well-formed context. -/
theorem table_typed {env tables memories} (hc : ModuleEnv.Cache env tables memories)
    {profile : ValidationProfile} (hv : ModuleEnv.Valid env profile) (tt : types.TableType) (ht : tt ∈ tables)
    (C : context) (hC : wf_context C) :
    Table_ok C (table tt) (EnvTranslation.tableType tt) := by
  have hm : tt ∈ env.table_types.val := by rw [hc.tables]; exact List.mem_append_right _ ht
  exact .mk_Table_ok C _ (ModuleTranslation.tableType_valid tt (hv.tables tt hm)) hC
    (.table_case_0 _ (EnvTranslation.tableType_wf tt))

/-- Each defined memory of a valid cached environment is typed in any well-formed context. -/
theorem memory_typed {env tables memories} (hc : ModuleEnv.Cache env tables memories)
    {profile : ValidationProfile} (hv : ModuleEnv.Valid env profile) (mt : types.MemType) (ht : mt ∈ memories)
    (C : context) (hC : wf_context C) :
    Mem_ok C (memory mt) (EnvTranslation.memType mt) := by
  have hm : mt ∈ env.mem_types.val := by rw [hc.memories]; exact List.mem_append_right _ ht
  exact .mk_Mem_ok C _ (ModuleTranslation.memType_valid mt (hv.memories mt hm)) hC
    (.mem_case_0 _ (EnvTranslation.memType_wf mt))

end Itasca.ModuleElaboration
