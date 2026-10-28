import Exec.Abs.Sim.Call
import Exec.Abs.Sim.Trap
namespace Itasca.Runtime.Abs
open SpecExt Itasca.Runtime.Spec

/-- A direct host call resolves its module index and then returns atomically.
The host event and changed store survive all labels and suspended callers. -/
theorem host_return_simulation (s s' : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index address : Nat)
    (baseValues args results : List val) (events : List HostEvent)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (resolve : f.module.FUNCS[index]? = some address) (hi32 : index < 2 ^ 32)
    (hargs : Forall wf_val args)
    (host : StepH ⟨⟨s,f.toFrame⟩,vals args ++ [.CALL_ADDR address]⟩ events
      ⟨⟨s',f.toFrame⟩,vals results⟩) :
    StepsHN 2
      (decode ⟨s,ambient,{f with code := .CALL (.mk_uN index) :: after,vals := baseValues ++ args} :: rest,[]⟩)
      events
      (decode ⟨s',ambient,{f with code := after,vals := baseValues ++ results} :: rest,[]⟩) := by
  have first := stepH_active ambient rest f.arity
    (stepH_decodeLabels
      (stepH_instrs (call_resolve s f.toFrame index address hs hf resolve hi32)
        args (after.map admininstr_instr) hargs (wf_instrs hc)) f.labels baseValues hl hv) ha hr
  have second := stepH_active ambient rest f.arity
    (stepH_decodeLabels (stepH_instrs host [] (after.map admininstr_instr)
      (forall_nil _) (wf_instrs hc)) f.labels baseValues hl hv) ha hr
  simp only [vals,List.map_nil,List.nil_append,List.append_assoc] at first second
  have both := StepsHN.cons first (StepsHN.cons second (StepsHN.refl (stepH_wf second).2))
  simp only [decode,decodeFrames,vals,List.map_nil,List.nil_append,List.map_cons,AFrame.toFrame,AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights,decodeLabels_move_values _ _ _ _ heights]
  simpa [instrContext,vals,List.append_assoc,AFrame.arity,AFrame.toFrame,admininstr_instr] using both

/-- Host traps retain callback store effects while the source semantics unwinds
all remaining labels and callers. Unwinding emits no additional host events. -/
theorem host_trap_simulation (s s' : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index address : Nat)
    (baseValues args : List val) (events : List HostEvent)
    (hs : wf_store s) (hs' : wf_store s') (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (resolve : f.module.FUNCS[index]? = some address) (hi32 : index < 2 ^ 32)
    (hargs : Forall wf_val args)
    (host : StepH ⟨⟨s,f.toFrame⟩,vals args ++ [.CALL_ADDR address]⟩ events
      ⟨⟨s',f.toFrame⟩,[.TRAP]⟩) :
    ∃ n, 2 ≤ n ∧ StepsHN n
      (decode ⟨s,ambient,{f with code := .CALL (.mk_uN index) :: after,vals := baseValues ++ args} :: rest,[]⟩)
      events ⟨⟨s',ambient⟩,[.TRAP]⟩ := by
  have first := stepH_active ambient rest f.arity
    (stepH_decodeLabels
      (stepH_instrs (call_resolve s f.toFrame index address hs hf resolve hi32)
        args (after.map admininstr_instr) hargs (wf_instrs hc)) f.labels baseValues hl hv) ha hr
  have second := stepH_active ambient rest f.arity
    (stepH_decodeLabels (stepH_instrs host [] (after.map admininstr_instr)
      (forall_nil _) (wf_instrs hc)) f.labels baseValues hl hv) ha hr
  have frames : Forall FrameWf ({f with vals := baseValues,code := after} :: rest) := by
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨hf,hl,hv,hc⟩
    · exact hr frame member
  obtain ⟨n,tail⟩ := trap_frames s' ambient ({f with vals := baseValues,code := after} :: rest) hs' ha frames
  have tail' : StepsHN n _ [] ⟨⟨s',ambient⟩,[.TRAP]⟩ := tail
  simp only [vals,List.map_nil,List.nil_append,List.append_assoc] at first second
  have both := StepsHN.cons first (StepsHN.cons second tail')
  refine ⟨n+2,by omega,?_⟩
  simp only [decode,decodeFrames,vals,List.map_nil,List.nil_append,List.map_cons,AFrame.toFrame,AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights]
  simpa [decodeFrames,instrContext,vals,List.append_assoc,AFrame.arity,AFrame.toFrame,admininstr_instr,Nat.add_assoc] using both
end Itasca.Runtime.Abs
