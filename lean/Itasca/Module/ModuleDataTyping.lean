import Itasca.Module.ModuleSegmentSyntax
import Itasca.Module.ModuleConstantTyping

open Aeneas Aeneas.Std

namespace Itasca.ModuleData

/-- Both supported profiles retain one memory; passive segments need no memory. -/
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
