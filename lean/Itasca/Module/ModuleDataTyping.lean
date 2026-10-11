import Itasca.Module.ModuleData
import Itasca.Module.ModuleConstantTyping

open Aeneas Aeneas.Std

namespace Itasca.ModuleData

def translate (segment : ModuleBinary.Data) : _root_.data :=
  .DATA (segment.init.map (fun b => .mk_byte b.val))
    (.ACTIVE (.mk_uN segment.memoryIdx.val) (ModuleConstants.expression segment.offset))

theorem translate_wf (segment : ModuleBinary.Data) : wf_data (translate segment) := by
  constructor
  · simp only [Forall, List.mem_map]
    rintro _ ⟨b, _, rfl⟩
    constructor
    have h := b.hmax
    norm_num at h ⊢
    omega
  · exact .datamode_case_0 _ _ (EnvTranslation.index_wf segment.memoryIdx)
      (ModuleConstants.expression_wf segment.offset)

/-- The Wasm 1.0 memory cardinality forces every active segment to memory zero. -/
theorem Valid.typed {env : module.Env} {segment : module.Data} (h : Valid env segment)
    (hmems : env.mem_types.val.length ≤ 1) (C : context) (hC : wf_context C)
    (hglobals : ModuleConstants.GlobalContext env C)
    (hmem : C.MEMS = env.mem_types.val.map EnvTranslation.memType) :
    Data_ok C (translate (raw segment)) := by
  obtain ⟨hi, ho⟩ := h
  have hzero : segment.memory_idx.val = 0 := by omega
  have hpositive : 0 < env.mem_types.val.length := by omega
  let mt := env.mem_types.val[0]
  have hmt : C.MEMS[0]! = EnvTranslation.memType mt := by
    rw [hmem, getElem!_pos _ _ (by simpa using hpositive), List.getElem_map]
  have hw := translate_wf (raw segment)
  unfold translate raw at hw ⊢
  rw [hzero] at hw ⊢
  apply Data_ok.mk_Data_ok C _ _ _ hC hw
  apply Datamode_ok.active C _ (EnvTranslation.memType mt)
  · simpa [hmem] using hpositive
  · exact hmt
  · exact ho.expr_ok_const C hC hglobals
  · exact hC
  · exact EnvTranslation.memType_wf mt
  · exact .datamode_case_0 _ _ (EnvTranslation.index_wf 0#u32)
      (ModuleConstants.expression_wf segment.offset)

end Itasca.ModuleData
