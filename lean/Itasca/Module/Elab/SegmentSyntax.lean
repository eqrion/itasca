import Itasca.Module.Const.Syntax

/-!
# Segment syntax

`ModuleSegments.elementValid` and `ModuleData.Valid` state when element and data segments are valid
against an environment, independently of binary decoding and the generated judgment. The
`elementMode`, `dataMode` and `ModuleData.translate` functions map segments to SpecTec syntax, and
the `_wf` lemmas show the results are well formed.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleSegments

/-- The element segment is valid against `env`. An active segment names a table of its element type
with a valid `i32` offset, and every initializer is a valid constant of the element type. Validity
describes index spaces and initializer types independently of binary decoding and the generated
module judgment. -/
def elementValid (env : module.Env) (entry : module.Element) : Prop :=
  (match entry.mode with
    | .Active idx offset => ∃ hi : idx.val < env.table_types.val.length,
        env.table_types.val[idx.val].elem = entry.elem ∧ ModuleConstants.Valid env offset .I32
    | .Passive | .Declarative => True) ∧
  ∀ init ∈ entry.init.val,
    ModuleConstants.Valid env init (ModuleConstants.referenceValueType entry.elem)

/-- The SpecTec element mode of an element segment mode. -/
def elementMode : module.ElementMode → elemmode
  | .Active idx offset => .ACTIVE (.mk_uN idx.val) (ModuleConstants.expression offset)
  | .Passive => .PASSIVE
  | .Declarative => .DECLARE

/-- The SpecTec data mode of a data segment mode. -/
def dataMode : module.DataMode → datamode
  | .Active idx offset => .ACTIVE (.mk_uN idx.val) (ModuleConstants.expression offset)
  | .Passive => .PASSIVE

/-- The translated element mode is well formed. -/
theorem elementMode_wf (mode : module.ElementMode) : wf_elemmode (elementMode mode) := by
  cases mode with
  | Active idx offset =>
      exact .elemmode_case_0 _ _ (EnvTranslation.index_wf idx)
        (ModuleConstants.expression_wf offset)
  | Passive => exact .elemmode_case_1
  | Declarative => exact .elemmode_case_2

/-- The translated data mode is well formed. -/
theorem dataMode_wf (mode : module.DataMode) : wf_datamode (dataMode mode) := by
  cases mode with
  | Active idx offset =>
      exact .datamode_case_0 _ _ (EnvTranslation.index_wf idx)
        (ModuleConstants.expression_wf offset)
  | Passive => exact .datamode_case_1

end Itasca.ModuleSegments

namespace Itasca.ModuleData

/-- The independent grammar's data segment corresponding to an extracted data segment. -/
def raw (segment : module.Data) : ModuleBinary.Data := ⟨segment.mode, segment.init.val⟩

/-- The data segment is valid against `env`. An active segment names a memory in range and has a
valid `i32` offset. -/
def Valid (env : module.Env) (segment : module.Data) : Prop :=
  match segment.mode with
  | .Active idx offset => idx.val < env.mem_types.val.length ∧ ModuleConstants.Valid env offset .I32
  | .Passive => True

/-- The SpecTec data segment of a raw data segment. -/
def translate (segment : ModuleBinary.Data) : _root_.data :=
  .DATA (segment.init.map (fun b => .mk_byte b.val)) (ModuleSegments.dataMode segment.mode)

/-- A translated data segment is well formed. -/
theorem translate_wf (segment : ModuleBinary.Data) : wf_data (translate segment) := by
  constructor
  · simp only [Forall, List.mem_map]
    rintro _ ⟨b, _, rfl⟩
    constructor
    have h := b.hmax
    norm_num at h ⊢
    omega
  · exact ModuleSegments.dataMode_wf segment.mode

end Itasca.ModuleData
