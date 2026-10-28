import Itasca.Runtime.Interp.Cumulative.Erased
import Itasca.Runtime.Interp.Core.Erased
import Itasca.Runtime.Interp.Core.OwnershipClosure
import Itasca.Runtime.Abs.Stateful.OwnershipStore
import Itasca.Runtime.Interp.StructuredMachine.SyntaxClosure
import Itasca.Runtime.Abs.Supported.PureCoverage
import Itasca.Runtime.Abs.Supported.CumulativeStep
import Itasca.Runtime.Interp.Core.BoundClosure
import Itasca.Runtime.Abs.SupportedState
namespace Itasca.Runtime.Interp

theorem StructuredMachine.SyntaxClosure.supported {before after}
    (closure : StructuredMachine.SyntaxClosure before after)
    {s : store} {ambient : frame} {rest : List Abs.AFrame}
    (covered : Abs.SupportedState ⟨s,ambient,before::rest,[]⟩) :
    Abs.SupportedState ⟨s,ambient,after::rest,[]⟩ :=
  Abs.Supported.replace_frame covered (closure (covered.active _ (List.mem_cons_self ..)))

theorem ErasedStep.supported {before after : Abs.AFrame} (step : ErasedStep before after)

    {s : store} {ambient : frame} {rest : List Abs.AFrame}
    (covered : Abs.SupportedState ⟨s,ambient,before::rest,[]⟩) :
    Abs.SupportedState ⟨s,ambient,after::rest,[]⟩ := by
  cases step with
  | nop f after => exact (StructuredMachine.SyntaxClosure.tail f .NOP after f.locals f.vals).supported covered
  | drop f after front value =>
    exact (StructuredMachine.SyntaxClosure.tail {f with vals := front++[value]} .DROP after f.locals front).supported covered
  | block f bt body after front params results signature shape =>
    have current := covered.active _ (List.mem_cons_self ..)
    have bodyCovered := Abs.BinaryInstr.block_body (current.1 _ (List.mem_cons_self ..))
    apply Abs.Supported.replace_frame covered
    refine ⟨bodyCovered,?_⟩
    intro label member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨by intro i found; simp at found,fun i found => current.1 i (List.mem_cons_of_mem _ found)⟩
    · exact current.2 label member
  | label f label labels =>
    have current := covered.active _ (List.mem_cons_self ..)
    apply Abs.Supported.replace_frame covered
    exact ⟨(current.2 label (List.mem_cons_self ..)).2,fun outer member => current.2 outer (List.mem_cons_of_mem _ member)⟩

end Itasca.Runtime.Interp

namespace Itasca.Runtime.Interp.StructuredMachine

/-- A non-erased core step of a typed supported state stays supported. -/
theorem core_step_supported {before next} (typed : Abs.CoreTyped before) (covered : Abs.SupportedState before)
    (step : Abs.Core.step before = .next next) : Abs.SupportedState next :=
  (Abs.Cumulative.Step.core step (by intro h; cases h)).next_covered_supported typed covered

/-- A core step of a typed supported state preserves stateful reference ownership. -/
theorem core_step_owned {before next} (typed : Abs.CoreTyped before) (covered : Abs.SupportedState before)
    (step : Abs.Core.step before = .next next) :
    ∀ bounds, Abs.Ownership.StatefulOwned bounds before → Abs.Ownership.StatefulOwned bounds next :=
  fun _ owned => (Abs.Cumulative.Step.core step (by intro h; cases h)).next_owned_supported typed covered owned

/-- A core step of a typed supported state preserves source code bounds. -/
theorem core_step_bound {before next} (typed : Abs.CoreTyped before) (covered : Abs.SupportedState before)
    (step : Abs.Core.step before = .next next) : ∀ bound, Abs.CodeBound bound before → Abs.CodeBound bound next :=
  fun _ bounded => (Abs.Cumulative.Step.core step (by intro h; cases h)).next_bound_supported typed covered bounded

theorem erased_steps_supported {count before after s ambient rest} (steps : ErasedSteps count before after)
    (covered : Abs.SupportedState ⟨s,ambient,before::rest,[]⟩) : Abs.SupportedState ⟨s,ambient,after::rest,[]⟩ := by
  induction steps with
  | nil => exact covered
  | cons step tail ih => exact ih (step.supported covered)

theorem owned_transition {initial next} (typed : Abs.CoreTyped initial) (covered : Abs.SupportedState initial)
    (transition : initial = next ∨ Abs.Core.step initial = .next next) :
    ∀ bounds, Abs.Ownership.StatefulOwned bounds initial → Abs.Ownership.StatefulOwned bounds next := by
  rcases transition with same | step
  · exact fun _ h => same ▸ h
  · exact core_step_owned typed covered step

theorem bound_transition {initial next} (typed : Abs.CoreTyped initial) (covered : Abs.SupportedState initial)
    (transition : initial = next ∨ Abs.Core.step initial = .next next) :
    ∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound next := by
  rcases transition with same | step
  · exact fun _ h => same ▸ h
  · exact core_step_bound typed covered step
end Itasca.Runtime.Interp.StructuredMachine
