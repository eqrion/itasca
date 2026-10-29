import Itasca.Runtime.Interp.Machine.Retention.StatefulOwnership
import Itasca.Runtime.Interp.Machine.Simulation.CoreErasure
import Itasca.Runtime.Interp.Machine.Retention.Ownership
import Itasca.Runtime.SourceMachine.Stateful.OwnershipStore
import Itasca.Runtime.Interp.Machine.Coverage.SyntaxClosure
import Itasca.Runtime.SourceMachine.Supported.PureCoverage
import Itasca.Runtime.SourceMachine.Supported.CumulativeStep
import Itasca.Runtime.Interp.Machine.Retention.CodeBounds
import Itasca.Runtime.SourceMachine.SupportedState

/-!
Source grammar, ownership and code-bound closure through control transitions.

Main declarations: `Machine.SyntaxClosure.supported` and `bound_transition`. A direct consumer is `Interp.Machine.Memory`.
-/

namespace Itasca.Runtime.Interp

theorem Machine.SyntaxClosure.supported {before after}
    (closure : Machine.SyntaxClosure before after)
    {s : store} {ambient : frame} {rest : List SourceMachine.AFrame}
    (covered : SourceMachine.SupportedState ⟨s,ambient,before::rest,[]⟩) :
    SourceMachine.SupportedState ⟨s,ambient,after::rest,[]⟩ :=
  SourceMachine.Supported.replace_frame covered (closure (covered.active _ (List.mem_cons_self ..)))

theorem ErasedStep.supported {before after : SourceMachine.AFrame} (step : ErasedStep before after)

    {s : store} {ambient : frame} {rest : List SourceMachine.AFrame}
    (covered : SourceMachine.SupportedState ⟨s,ambient,before::rest,[]⟩) :
    SourceMachine.SupportedState ⟨s,ambient,after::rest,[]⟩ := by
  cases step with
  | nop f after => exact (Machine.SyntaxClosure.tail f .NOP after f.locals f.vals).supported covered
  | drop f after front value =>
    exact (Machine.SyntaxClosure.tail {f with vals := front++[value]} .DROP after f.locals front).supported covered
  | block f bt body after front params results signature shape =>
    have current := covered.active _ (List.mem_cons_self ..)
    have bodyCovered := SourceMachine.BinaryInstr.block_body (current.1 _ (List.mem_cons_self ..))
    apply SourceMachine.Supported.replace_frame covered
    refine ⟨bodyCovered,?_⟩
    intro label member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨by intro i found; simp at found,fun i found => current.1 i (List.mem_cons_of_mem _ found)⟩
    · exact current.2 label member
  | label f label labels =>
    have current := covered.active _ (List.mem_cons_self ..)
    apply SourceMachine.Supported.replace_frame covered
    exact ⟨(current.2 label (List.mem_cons_self ..)).2,fun outer member => current.2 outer (List.mem_cons_of_mem _ member)⟩

end Itasca.Runtime.Interp

namespace Itasca.Runtime.Interp.Machine

/-- A non-erased core step of a typed supported state stays supported. -/
theorem core_step_supported {before next} (typed : SourceMachine.CoreTyped before) (covered : SourceMachine.SupportedState before)
    (step : SourceMachine.Core.step before = .next next) : SourceMachine.SupportedState next :=
  (SourceMachine.Cumulative.Step.core step (by intro h; cases h)).next_covered_supported typed covered

/-- A core step of a typed supported state preserves stateful reference ownership. -/
theorem core_step_owned {before next} (typed : SourceMachine.CoreTyped before) (covered : SourceMachine.SupportedState before)
    (step : SourceMachine.Core.step before = .next next) :
    ∀ bounds, SourceMachine.Ownership.StatefulOwned bounds before → SourceMachine.Ownership.StatefulOwned bounds next :=
  fun _ owned => (SourceMachine.Cumulative.Step.core step (by intro h; cases h)).next_owned_supported typed covered owned

/-- A core step of a typed supported state preserves source code bounds. -/
theorem core_step_bound {before next} (typed : SourceMachine.CoreTyped before) (covered : SourceMachine.SupportedState before)
    (step : SourceMachine.Core.step before = .next next) : ∀ bound, SourceMachine.CodeBound bound before → SourceMachine.CodeBound bound next :=
  fun _ bounded => (SourceMachine.Cumulative.Step.core step (by intro h; cases h)).next_bound_supported typed covered bounded

theorem erased_steps_supported {count before after s ambient rest} (steps : ErasedSteps count before after)
    (covered : SourceMachine.SupportedState ⟨s,ambient,before::rest,[]⟩) : SourceMachine.SupportedState ⟨s,ambient,after::rest,[]⟩ := by
  induction steps with
  | nil => exact covered
  | cons step tail ih => exact ih (step.supported covered)

theorem owned_transition {initial next} (typed : SourceMachine.CoreTyped initial) (covered : SourceMachine.SupportedState initial)
    (transition : initial = next ∨ SourceMachine.Core.step initial = .next next) :
    ∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds next := by
  rcases transition with same | step
  · exact fun _ h => same ▸ h
  · exact core_step_owned typed covered step

theorem bound_transition {initial next} (typed : SourceMachine.CoreTyped initial) (covered : SourceMachine.SupportedState initial)
    (transition : initial = next ∨ SourceMachine.Core.step initial = .next next) :
    ∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound next := by
  rcases transition with same | step
  · exact fun _ h => same ▸ h
  · exact core_step_bound typed covered step
end Itasca.Runtime.Interp.Machine
