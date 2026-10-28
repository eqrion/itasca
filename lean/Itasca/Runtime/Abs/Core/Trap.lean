import Itasca.Runtime.Abs.Core.Simulation
import Itasca.Runtime.Abs.Sim.Trap

namespace Itasca.Runtime.Abs
open SpecExt Itasca.Runtime.Spec

/-- An instruction-local bounds or arithmetic trap unwinds all labels and
callers after consuming exactly the typed redex operands. -/
theorem operand_trap_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (instruction : instr) (after : List instr)
    (front consumed : List val)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val front)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (step : StepH ⟨⟨s,f.toFrame⟩,vals consumed ++ [admininstr_instr instruction]⟩ []
      ⟨⟨s,f.toFrame⟩,[.TRAP]⟩) :
    ∃ n, 0 < n ∧ StepsHN n
      (decode ⟨s,ambient,{f with code := instruction :: after, vals := front ++ consumed} :: rest,[]⟩) []
      ⟨⟨s,ambient⟩,[.TRAP]⟩ := by
  have lifted := stepH_active ambient rest f.arity
    (stepH_decodeLabels (stepH_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc))
      f.labels front hl hv) ha hr
  have framesWf : Forall FrameWf ({f with code := after, vals := front} :: rest) := by
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨hf,hl,hv,hc⟩
    · exact hr frame member
  obtain ⟨n,tail⟩ := trap_frames s ambient ({f with code := after, vals := front} :: rest) hs ha framesWf
  refine ⟨n+1,by omega,?_⟩
  have combined := StepsHN.cons lifted tail
  simp only [decode,decodeFrames,vals,List.map_nil,List.nil_append,List.map_cons,AFrame.toFrame,AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights]
  simpa [decodeFrames,frameContext,instrContext,vals,List.append_assoc,AFrame.toFrame,AFrame.arity] using combined

end Itasca.Runtime.Abs
