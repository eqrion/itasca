import Itasca.Module.Definitions
import Itasca.Results.Definitions.Validation
import Itasca.Module.Const.Parser

open WebAssembly

/-! ## SegmentSyntax -/

section

/-!
# Segment syntax

`Module.Segments.elementValid` and `Module.Data.Valid` state when element and data segments are valid
against an environment, independently of binary decoding and the generated judgment. The
`elementMode`, `dataMode` and `Module.Data.translate` functions map segments to SpecTec syntax, and
the `_wf` lemmas show the results are well formed.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Segments

/-- The translated element mode is well formed. -/
theorem element_mode_wf (mode : metadata.ElementMode) : wf_elemmode (elementMode mode) := by
  cases mode with
  | Active idx offset =>
      exact .elemmode_case_0 _ _ (Translation.Environment.index_wf idx)
        (Module.Constants.expression_wf offset)
  | Passive => exact .elemmode_case_1
  | Declarative => exact .elemmode_case_2

/-- The translated data mode is well formed. -/
theorem data_mode_wf (mode : metadata.DataMode) : wf_datamode (dataMode mode) := by
  cases mode with
  | Active idx offset =>
      exact .datamode_case_0 _ _ (Translation.Environment.index_wf idx)
        (Module.Constants.expression_wf offset)
  | Passive => exact .datamode_case_1

end Itasca.Module.Segments

namespace Itasca.Module.Data

/-- The data segment is valid against `env`. An active segment names a memory in range and has a
valid `i32` offset. -/
def Valid (env : metadata.CodeMetadata) (segment : metadata.Data) : Prop :=
  match segment.mode with
  | .Active idx offset => idx.val < env.memories.val.length ∧ Module.Constants.Valid env offset .I32
  | .Passive => True

/-- A translated data segment is well formed. -/
theorem translate_wf (segment : Binary.Data) : wf_data (translate segment) := by
  constructor
  · simp only [Forall, List.mem_map]
    rintro _ ⟨b, _, rfl⟩
    constructor
    have h := b.hmax
    norm_num at h ⊢
    omega
  · exact Module.Segments.data_mode_wf segment.mode

end Itasca.Module.Data

end

/-! ## SegmentTyping -/

section

/-!
# Segment typing

`Module.Segments.elementValid.typed` and `Module.Data.Valid.typed` show valid element and data
segments have the generated judgments `Elem_ok` and `Data_ok` in any well-formed context that
agrees with the environment on the relevant index spaces.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Segments

/-- A valid element segment is typed with the element type recorded in its metadata, in every mode.
Initializer references are checked in the complete function space. -/
theorem elementValid.typed {env : metadata.CodeMetadata} {entry : metadata.Element}
    (h : elementValid env entry) (C : context) (hC : wf_context C)
    (hglobals : Module.Constants.GlobalContext env C)
    (hfunctions : Module.Constants.FunctionContext env C)
    (htables : C.TABLES = env.tables.val.map (fun d => Translation.Environment.tableType d.ty)) :
    Elem_ok C
      (.ELEM (Translation.referenceType entry.elem)
        ((Module.Environment.rawElement entry).init.map Module.Constants.expression) (elementMode entry.mode))
      (Translation.referenceType entry.elem) := by
  obtain ⟨hmode, hinits⟩ := h
  apply Elem_ok.mk_Elem_ok C (Translation.referenceType entry.elem) _ _
  · simp only [Forall, List.mem_map]
    rintro _ ⟨init, hinit, rfl⟩
    have ht := (hinits init hinit).expr_ok_const C hC hglobals hfunctions
    have hty : Translation.valueType (Module.Constants.referenceValueType entry.elem) =
        valtype_reftype (Translation.referenceType entry.elem) := by cases entry.elem <;> rfl
    exact hty ▸ ht
  · cases hm : entry.mode with
    | Passive => exact .passive C _ hC .elemmode_case_1
    | Declarative => exact .declare C _ hC .elemmode_case_2
    | Active idx offset =>
      simp only [hm] at hmode
      obtain ⟨hi, htype, hoffset⟩ := hmode
      have ht : Translation.Environment.tableType env.tables.val[idx.val].ty =
          .mk_tabletype (Translation.Environment.limitsType env.tables.val[idx.val].ty.limits)
            (Translation.referenceType entry.elem) := by
        simp only [Translation.Environment.tableType, htype]
      apply Elemmode_ok.active C _ _ (Translation.referenceType entry.elem)
        (Translation.Environment.limitsType env.tables.val[idx.val].ty.limits)
      · simpa [htables, proj_uN_0] using hi
      · simp only [htables, proj_uN_0]
        rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map]
        exact ht
      · exact hoffset.expr_ok_const C hC hglobals hfunctions
      · exact hC
      · exact .elemmode_case_0 _ _ (Translation.Environment.index_wf idx)
          (Module.Constants.expression_wf offset)
      · exact ht ▸ Translation.Environment.table_type_wf _
  · exact hC
  · constructor
    · simp only [Forall, List.mem_map]
      rintro _ ⟨init, _, rfl⟩
      exact Module.Constants.expression_wf init
    · exact element_mode_wf entry.mode

end Itasca.Module.Segments

open Aeneas Aeneas.Std

namespace Itasca.Module.Data

/-- A valid data segment is typed. The implementation allows at most one memory;
passive segments need none. -/
theorem Valid.typed {env : metadata.CodeMetadata} {segment : metadata.Data} (h : Valid env segment)
    (hmems : env.memories.val.length ≤ 1) (C : context) (hC : wf_context C)
    (hglobals : Module.Constants.GlobalContext env C)
    (hfunctions : Module.Constants.FunctionContext env C)
    (hmem : C.MEMS = env.memories.val.map (fun d => Translation.Environment.memType d.ty)) :
    Data_ok C (translate (raw segment)) := by
  apply Data_ok.mk_Data_ok C _ _ _ hC (translate_wf (raw segment))
  cases hm : segment.mode with
  | Passive => simpa [raw, hm, Module.Segments.dataMode] using Datamode_ok.passive C hC .datamode_case_1
  | Active idx offset =>
    obtain ⟨hi, ho⟩ := (show idx.val < env.memories.val.length ∧
      Module.Constants.Valid env offset .I32 from by simpa [Valid, hm] using h)
    have hzero : idx.val = 0 := by omega
    have hpositive : 0 < env.memories.val.length := by omega
    let mt := env.memories.val[0].ty
    have hmt : C.MEMS[0]! = Translation.Environment.memType mt := by
      rw [hmem, getElem!_pos _ _ (by simpa using hpositive), List.getElem_map]
    simp only [raw, hm, Module.Segments.dataMode, hzero]
    apply Datamode_ok.active C _ (Translation.Environment.memType mt)
    · simpa [hmem] using hpositive
    · exact hmt
    · exact ho.expr_ok_const C hC hglobals hfunctions
    · exact hC
    · exact Translation.Environment.mem_type_wf mt
    · exact .datamode_case_0 _ _ (Translation.Environment.index_wf 0#u32)
        (Module.Constants.expression_wf offset)

end Itasca.Module.Data

end
