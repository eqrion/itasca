import Exec.Abs.Simd.MemoryTransition
import Exec.Abs.Sim.ChosenMutable
import Exec.Abs.Sim.ChosenTyped
import Exec.Abs.Core.ChosenTrap
namespace Exec.Abs.Simd
open SpecExt Exec.Spec

theorem memory_transition_chosen_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) {s : _root_.store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {source inputs outputs} {next : AState}
    (signature : MemorySignature source inputs outputs)
    (typed : ATyped ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩)
    (step : MemoryTransition ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩
      {f with code := source :: after} rest after source inputs outputs (.next next)) :
    ChosenNextSim choices occurrence ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩ next := by
  cases step with
  | next front operands results store values types resultTypes change effect =>
    change f.vals = front ++ operands at values
    have hf : FrameTyped s {f with code := source :: after} [] := by
      cases typed.frames with | cons h _ => exact h
    have hr : Forall FrameWf rest := by
      cases typed.frames with | cons _ h => exact framesTyped_wf h
    obtain ⟨_,labelsWf,_,codeWf⟩ := frameTyped_wf hf
    obtain ⟨frontWf,heights⟩ := signature.prefix_bounds hf values types
    apply ChosenNextSim.single admissible
    have simulated := chosen_mutable_stack_simulation admissible s store ambient f rest source after front operands results
      typed.ambient labelsWf frontWf (fun op member => codeWf op (by simp [member])) hr heights
        (stepH_neutral_chosen admissible vector occurrence effect (by
          simp only [trapCode,neutralActive_vals]; cases signature <;> simp only [admininstr_instr,neutralActive]))
    simpa only [values] using simulated

theorem memory_transition_chosen_trap_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) {s : _root_.store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {source inputs outputs}
    (signature : MemorySignature source inputs outputs)
    (typed : ATyped ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩)
    (step : MemoryTransition ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩
      {f with code := source :: after} rest after source inputs outputs .trap) :
    ∃ n, 0 < n ∧ ChosenStepsN choices occurrence n
      (decode ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩) [] ⟨⟨s,ambient⟩,[.TRAP]⟩ := by
  cases step with
  | trap front operands values types effect =>
    change f.vals = front ++ operands at values
    have hf : FrameTyped s {f with code := source :: after} [] := by
      cases typed.frames with | cons h _ => exact h
    have hr : Forall FrameWf rest := by
      cases typed.frames with | cons _ h => exact framesTyped_wf h
    obtain ⟨frameWf,labelsWf,_,codeWf⟩ := frameTyped_wf hf
    obtain ⟨frontWf,heights⟩ := signature.prefix_bounds hf values types
    have simulated := chosen_operand_trap_simulation admissible vector occurrence s ambient f rest source after front operands
      typed.store typed.ambient frameWf labelsWf frontWf
      (fun op member => codeWf op (by simp [member])) hr heights effect
      (by rw [neutralActive_vals]; cases signature <;> simp only [admininstr_instr,neutralActive])
    simpa only [values] using simulated

end Exec.Abs.Simd
