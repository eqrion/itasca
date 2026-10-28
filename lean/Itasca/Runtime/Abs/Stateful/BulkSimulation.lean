import Itasca.Runtime.Abs.Core.Simulation
import Itasca.Runtime.Abs.Sim.Trace
import Itasca.Runtime.Abs.Sim.Typed
namespace Itasca.Runtime.Abs.Stateful
open SpecExt Itasca.Runtime.Spec

theorem mutable_counted_simulation (before afterStore : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (instruction : instr) (after : List instr)
    (baseValues consumed produced : List val) (count : Nat)
    (ha : wf_frame ambient) (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (step : StepsHN count ⟨⟨before,f.toFrame⟩,vals consumed ++ [admininstr_instr instruction]⟩ []
      ⟨⟨afterStore,f.toFrame⟩,vals produced⟩) :
    StepsHN count (decode ⟨before,ambient,{f with code := instruction::after,vals := baseValues++consumed}::rest,[]⟩) []
      (decode ⟨afterStore,ambient,{f with code := after,vals := baseValues++produced}::rest,[]⟩) := by
  have first := stepsHN_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have second := stepsHN_decodeLabels first f.labels baseValues hl hv
  have third := stepsHN_frame second f.arity (activeFrame ambient rest) (activeFrame_wf ha hr)
  have full := stepsHN_decodeFrames ambient rest third ha hr
  simp only [decode,decodeFrames,vals,List.map_nil,List.nil_append,List.map_cons,AFrame.toFrame,AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights,decodeLabels_move_values _ _ _ _ heights]
  simpa [instrContext,frameContext,vals,List.append_assoc,AFrame.arity,AFrame.toFrame] using full

/-- Every bulk operation reduces its redex at least once, including zero-length
operations. Wrapping it in source control contexts retains that positive count. -/
theorem bulk_empty_simulation (before afterStore : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (instruction : instr) (after : List instr) (baseValues consumed : List val)
    (ha : wf_frame ambient) (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (steps : StepsH ⟨⟨before,f.toFrame⟩,vals consumed ++ [admininstr_instr instruction]⟩ []
      ⟨⟨afterStore,f.toFrame⟩,[]⟩) :
    NextSim ⟨before,ambient,{f with code := instruction::after,vals := baseValues++consumed}::rest,[]⟩
      ⟨afterStore,ambient,{f with code := after,vals := baseValues}::rest,[]⟩ := by
  obtain ⟨count,trace⟩ := stepsH_count steps
  have positive : 0 < count := by
    by_contra no
    have zero : count=0 := by omega
    rw [zero] at trace
    have same := trace.zero.1
    have lengths := congrArg (fun | config.mk_config _ code => code.length) same
    simp only [List.length_append,List.length_singleton,List.length_nil] at lengths
    omega
  have full := mutable_counted_simulation before afterStore ambient f rest instruction after baseValues consumed [] count
    ha hl hv hc hr heights trace
  apply NextSim.counted (n:=count) _ positive
  simpa only [List.append_nil] using full
end Itasca.Runtime.Abs.Stateful
