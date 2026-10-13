import Itasca.Module.Elab.SegmentSyntax
import Itasca.Module.Const.Typing

/-!
# Segment typing

`ModuleSegments.elementValid.typed` and `ModuleData.Valid.typed` show valid element and data
segments have the generated judgments `Elem_ok` and `Data_ok` in any well-formed context that
agrees with the environment on the relevant index spaces.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleSegments

/-- A valid element segment is typed with the element type recorded in its metadata, in every mode.
Initializer references are checked in the complete function space. -/
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

open Aeneas Aeneas.Std

namespace Itasca.ModuleData

/-- A valid data segment is typed. Both profiles allow at most one memory, and passive segments
need no memory. -/
theorem Valid.typed {env : module.Env} {segment : module.Data} (h : Valid env segment)
    (hmems : env.mem_types.val.length ≤ 1) (C : context) (hC : wf_context C)
    (hglobals : ModuleConstants.GlobalContext env C)
    (hfunctions : ModuleConstants.FunctionContext env C)
    (hmem : C.MEMS = env.mem_types.val.map EnvTranslation.memType) :
    Data_ok C (translate (raw segment)) := by
  apply Data_ok.mk_Data_ok C _ _ _ hC (translate_wf (raw segment))
  cases hm : segment.mode with
  | Passive => simpa [raw, hm, ModuleSegments.dataMode] using Datamode_ok.passive C hC .datamode_case_1
  | Active idx offset =>
    obtain ⟨hi, ho⟩ := (show idx.val < env.mem_types.val.length ∧
      ModuleConstants.Valid env offset .I32 from by simpa [Valid, hm] using h)
    have hzero : idx.val = 0 := by omega
    have hpositive : 0 < env.mem_types.val.length := by omega
    let mt := env.mem_types.val[0]
    have hmt : C.MEMS[0]! = EnvTranslation.memType mt := by
      rw [hmem, getElem!_pos _ _ (by simpa using hpositive), List.getElem_map]
    simp only [raw, hm, ModuleSegments.dataMode, hzero]
    apply Datamode_ok.active C _ (EnvTranslation.memType mt)
    · simpa [hmem] using hpositive
    · exact hmt
    · exact ho.expr_ok_const C hC hglobals hfunctions
    · exact hC
    · exact EnvTranslation.memType_wf mt
    · exact .datamode_case_0 _ _ (EnvTranslation.index_wf 0#u32)
        (ModuleConstants.expression_wf offset)

end Itasca.ModuleData
