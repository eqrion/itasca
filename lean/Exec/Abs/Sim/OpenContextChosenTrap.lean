import Exec.Abs.Sim.OpenContextTrap
import Exec.Spec.Choices.ActiveTrapChoices
namespace Exec.Spec.OpenHost
open SpecExt Exec.Abs

theorem Context.active_trap (context : Context) (s : store) (ambient : _root_.frame) :
    activeTrap (trapCode (context.plug ⟨⟨s,ambient⟩,[.TRAP]⟩))=true := by
  induction context with
  | hole => simp only [Context.plug,trapCode,activeTrap]
  | label arity continuation wf inner ih =>
    simpa only [Context.plug,labelContext,trapCode,activeTrap] using ih
  | frame arity outer wf inner ih =>
    simpa only [Context.plug,frameContext,trapCode,activeTrap] using ih
  | instructions values after valuesWf afterWf inner ih =>
    simpa only [Context.plug,instrContext,trapCode,activeTrap_vals] using activeTrap_append_true ih after

/-- A checked host trap unwinds the exact saved context under every fixed
primitive policy. Cleanup introduces no new host reply or platform choice. -/
theorem Pending.trap_unwind_chosen (choices : SourceChoices) (occurrence : Nat)
    (pending : Pending) (after : store) (storeWf : wf_store after) :
    ∃count,ChosenStepsN choices occurrence count (pending.completed ⟨after,none⟩) []
      ⟨⟨after,pending.context.outerFrame pending.ambient⟩,[.TRAP]⟩ := by
  obtain ⟨count,path⟩:=pending.trap_unwind after storeWf
  exact ⟨count,path.active_chosen choices occurrence (pending.context.active_trap after pending.ambient)⟩
end Exec.Spec.OpenHost
