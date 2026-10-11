import Itasca.Module.ModuleSegmentSyntax
import Itasca.Module.ModuleConstantTyping

open Aeneas Aeneas.Std

namespace Itasca.ModuleSegments

/-- Every mode uses the element type actually recorded in metadata. Initializer
references are checked in the complete function space. -/
theorem elementValid.typed {env : module.Env} {entry : module.Element}
    (h : elementValid env entry) (C : context) (hC : wf_context C)
    (hglobals : ModuleConstants.GlobalContext env C)
    (hfunctions : ModuleConstants.FunctionContext env C)
    (htables : C.TABLES = env.table_types.val.map EnvTranslation.tableType) :
    Elem_ok C
      (.ELEM (Translate.referenceType entry.elem)
        (entry.init.val.map ModuleConstants.expression) (elementMode entry.mode))
      (Translate.referenceType entry.elem) := by
  obtain ⟨hmode, hinits⟩ := h
  apply Elem_ok.mk_Elem_ok C (Translate.referenceType entry.elem) _ _
  · simp only [Forall, List.mem_map]
    rintro _ ⟨init, hinit, rfl⟩
    have ht := (hinits init hinit).expr_ok_const C hC hglobals hfunctions
    have hty : Translate.valueType (ModuleConstants.referenceValueType entry.elem) =
        valtype_reftype (Translate.referenceType entry.elem) := by cases entry.elem <;> rfl
    exact hty ▸ ht
  · cases hm : entry.mode with
    | Passive => exact .passive C _ hC .elemmode_case_1
    | Declarative => exact .declare C _ hC .elemmode_case_2
    | Active idx offset =>
      simp only [hm] at hmode
      obtain ⟨hi, htype, hoffset⟩ := hmode
      have ht : EnvTranslation.tableType env.table_types.val[idx.val] =
          .mk_tabletype (EnvTranslation.limitsType env.table_types.val[idx.val].limits)
            (Translate.referenceType entry.elem) := by
        simp only [EnvTranslation.tableType, htype]
      apply Elemmode_ok.active C _ _ (Translate.referenceType entry.elem)
        (EnvTranslation.limitsType env.table_types.val[idx.val].limits)
      · simpa [htables, proj_uN_0] using hi
      · simp only [htables, proj_uN_0]
        rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map]
        exact ht
      · exact hoffset.expr_ok_const C hC hglobals hfunctions
      · exact hC
      · exact .elemmode_case_0 _ _ (EnvTranslation.index_wf idx)
          (ModuleConstants.expression_wf offset)
      · exact ht ▸ EnvTranslation.tableType_wf _
  · exact hC
  · constructor
    · simp only [Forall, List.mem_map]
      rintro _ ⟨init, _, rfl⟩
      exact ModuleConstants.expression_wf init
    · exact elementMode_wf entry.mode

end Itasca.ModuleSegments
