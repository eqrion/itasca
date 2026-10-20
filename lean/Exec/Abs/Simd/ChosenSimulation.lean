import Exec.Abs.Simd.Transition
import Exec.Abs.Sim.ChosenPure
namespace Exec.Abs.Simd
open SpecExt Exec.Spec

/-- A selected SIMD primitive lifts through every active label and suspended
caller without consuming another reply occurrence. -/
theorem PureSignature.chosen_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence : Nat} {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
    {after : List instr} {source inputs output} (signature : PureSignature source inputs output)
    (typed : ATyped ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩)
    {front operands : List val} {value : val} (values : f.vals = front ++ operands)
    (types : operands.map valueType = inputs)
    (selected : ChosenPure choices occurrence (vals operands ++ [admininstr_instr source]) [admininstr_val value]) :
    ChoiceStep choices occurrence (decode ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩) []
      (decode ⟨s,ambient,{f with code := after,vals := front ++ [value]} :: rest,[]⟩) := by
  have hf : FrameTyped s {f with code := source :: after} [] := by
    cases typed.frames with | cons h _ => exact h
  have hr : Forall FrameWf rest := by
    cases typed.frames with | cons _ h => exact framesTyped_wf h
  obtain ⟨frameWf,labelsWf,_,codeWf⟩ := frameTyped_wf hf
  obtain ⟨frontWf,operandsWf,heights⟩ := signature.prefix_bounds hf values types
  have simulated := chosen_pure_stack admissible s ambient f rest source after front operands [value]
    typed.store typed.ambient frameWf labelsWf frontWf
    (fun op member => codeWf op (by simp [member])) hr heights operandsWf
    (by intro v member; have eq := List.mem_singleton.mp member; subst v; exact pure_singleton_wf (selected.erases admissible))
    (codeWf source (by simp)) selected
  simpa only [values] using simulated
end Exec.Abs.Simd
