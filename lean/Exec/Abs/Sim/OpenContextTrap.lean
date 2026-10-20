import Exec.Abs.Sim.OpenContext
import Exec.Abs.Sim.Trap
namespace Exec.Spec.OpenHost
open SpecExt Exec.Abs

/-- The ambient frame outside the saved evaluation context. -/
def Context.outerFrame : Context → _root_.frame → _root_.frame
  | .hole,f=>f
  | .label _ _ _ inner,f=>inner.outerFrame f
  | .frame _ outer _ _,_=>outer
  | .instructions _ _ _ _ inner,f=>inner.outerFrame f

theorem Context.outerFrame_wf (context : Context) (ambient : _root_.frame) (wellFormed : wf_frame ambient) :
    wf_frame (context.outerFrame ambient) := by
  induction context <;> simp_all [outerFrame]

/-- A rejected host reply unwinds its exact saved context silently, retaining
its committed store and producing the terminal source trap. -/
theorem Context.trap_unwind (context : Context) (s : store) (ambient : _root_.frame)
    (storeWf : wf_store s) (frameWf : wf_frame ambient) :
    ∃count,StepsHN count (context.plug ⟨⟨s,ambient⟩,[.TRAP]⟩) []
      ⟨⟨s,context.outerFrame ambient⟩,[.TRAP]⟩ := by
  induction context with
  | hole=>exact ⟨0,.refl (wf_config_make storeWf frameWf wf_trap)⟩
  | label arity continuation wellFormed inner ih=>
    obtain ⟨count,path⟩ := ih
    have lifted := stepsHN_label path arity continuation wellFormed
    have last := trap_label s (inner.outerFrame ambient) arity continuation storeWf (inner.outerFrame_wf ambient frameWf) wellFormed
    exact ⟨count+1,by simpa [Context.plug,Context.outerFrame] using lifted.trans (.cons last (.refl (stepH_wf last).2))⟩
  | frame arity outer wellFormed inner ih=>
    obtain ⟨count,path⟩ := ih
    have lifted := stepsHN_frame path arity outer wellFormed
    have last := trap_frame s outer (inner.outerFrame ambient) arity storeWf wellFormed (inner.outerFrame_wf ambient frameWf)
    exact ⟨count+1,by simpa [Context.plug,Context.outerFrame] using lifted.trans (.cons last (.refl (stepH_wf last).2))⟩
  | instructions values after valuesWf afterWf inner ih=>
    obtain ⟨count,path⟩ := ih
    have lifted := stepsHN_instrs path values after valuesWf afterWf
    obtain ⟨more,tail⟩ := trap_values s (inner.outerFrame ambient) values after storeWf (inner.outerFrame_wf ambient frameWf) valuesWf afterWf
    exact ⟨count+more,by simpa [Context.plug,Context.outerFrame,instrContext] using lifted.trans tail⟩

theorem Pending.trap_unwind (pending : Pending) (after : store) (storeWf : wf_store after) :
    ∃count,StepsHN count (pending.completed ⟨after,none⟩) []
      ⟨⟨after,pending.context.outerFrame pending.ambient⟩,[.TRAP]⟩ :=
  pending.context.trap_unwind after pending.ambient storeWf pending.ambientWf
end Exec.Spec.OpenHost
