import Itasca.Module.ModuleConstantSyntax

open Aeneas Aeneas.Std

namespace Itasca.ModuleSegments

/-- Segment validity describes index spaces and initializer types independently
of binary decoding and the generated module judgment. -/
def elementValid (env : module.Env) (entry : module.Element) : Prop :=
  (match entry.mode with
    | .Active idx offset => ∃ hi : idx.val < env.table_types.val.length,
        env.table_types.val[idx.val].elem = entry.elem ∧ ModuleConstants.Valid env offset .I32
    | .Passive | .Declarative => True) ∧
  ∀ init ∈ entry.init.val,
    ModuleConstants.Valid env init (ModuleConstants.referenceValueType entry.elem)

def elementMode : module.ElementMode → elemmode
  | .Active idx offset => .ACTIVE (.mk_uN idx.val) (ModuleConstants.expression offset)
  | .Passive => .PASSIVE
  | .Declarative => .DECLARE

def dataMode : module.DataMode → datamode
  | .Active idx offset => .ACTIVE (.mk_uN idx.val) (ModuleConstants.expression offset)
  | .Passive => .PASSIVE

theorem elementMode_wf (mode : module.ElementMode) : wf_elemmode (elementMode mode) := by
  cases mode with
  | Active idx offset =>
      exact .elemmode_case_0 _ _ (EnvTranslation.index_wf idx)
        (ModuleConstants.expression_wf offset)
  | Passive => exact .elemmode_case_1
  | Declarative => exact .elemmode_case_2

theorem dataMode_wf (mode : module.DataMode) : wf_datamode (dataMode mode) := by
  cases mode with
  | Active idx offset =>
      exact .datamode_case_0 _ _ (EnvTranslation.index_wf idx)
        (ModuleConstants.expression_wf offset)
  | Passive => exact .datamode_case_1

end Itasca.ModuleSegments

namespace Itasca.ModuleData

def raw (segment : module.Data) : ModuleBinary.Data := ⟨segment.mode, segment.init.val⟩

def Valid (env : module.Env) (segment : module.Data) : Prop :=
  match segment.mode with
  | .Active idx offset => idx.val < env.mem_types.val.length ∧ ModuleConstants.Valid env offset .I32
  | .Passive => True

def translate (segment : ModuleBinary.Data) : _root_.data :=
  .DATA (segment.init.map (fun b => .mk_byte b.val)) (ModuleSegments.dataMode segment.mode)

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
