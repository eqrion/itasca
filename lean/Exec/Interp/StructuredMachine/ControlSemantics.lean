import Exec.Interp.StructuredMachine.SyntaxClosure
import Exec.Interp.Core.OwnershipClosure
import Exec.Interp.Core.BoundClosure
namespace Exec.Interp.StructuredMachine

/-- Source preservation facts used by the common control machine. Concrete
instruction grammars discharge this record from their checked source steps. -/
structure ControlSemantics (allowed : instr → Prop) (supported : Abs.AState → Prop)
    (owned : Abs.Ownership.Bounds → Abs.AState → Prop) : Prop where
  branch : ∀ depth, allowed (.BR (.mk_uN depth))
  next_covered : ∀ {before next}, Abs.CoreTyped before → supported before →
    Abs.Core.step before = .next next → supported next
  next_owned : ∀ {before next}, Abs.CoreTyped before → supported before →
    Abs.Core.step before = .next next → ∀ bounds, owned bounds before → owned bounds next
  next_bound : ∀ {before next}, Abs.CoreTyped before → supported before →
    Abs.Core.step before = .next next → ∀ bound, Abs.CodeBound bound before → Abs.CodeBound bound next
  syntax_preserved : ∀ {s ambient before after rest}, SyntaxClosure allowed before after →
    supported ⟨s,ambient,before::rest,[]⟩ → supported ⟨s,ambient,after::rest,[]⟩
  erased : ∀ {s ambient before after rest}, ErasedStep before after →
    supported ⟨s,ambient,before::rest,[]⟩ → supported ⟨s,ambient,after::rest,[]⟩
  ownership : ∀ {bounds s ambient before after rest}, FrameOwnershipClosure before after →
    owned bounds ⟨s,ambient,before::rest,[]⟩ → owned bounds ⟨s,ambient,after::rest,[]⟩

variable {allowed supported owned}
theorem ControlSemantics.erased_steps (semantics : ControlSemantics allowed supported owned)
    {count before after s ambient rest} (steps : ErasedSteps count before after)
    (covered : supported ⟨s,ambient,before::rest,[]⟩) : supported ⟨s,ambient,after::rest,[]⟩ := by
  induction steps with
  | nil => exact covered
  | cons step tail ih => exact ih (semantics.erased step covered)

theorem ControlSemantics.owned_transition (semantics : ControlSemantics allowed supported owned)
    {initial next} (typed : Abs.CoreTyped initial) (covered : supported initial)
    (transition : initial = next ∨ Abs.Core.step initial = .next next) :
    ∀ bounds, owned bounds initial → owned bounds next := by
  rcases transition with same | step
  · exact fun _ h => same ▸ h
  · exact semantics.next_owned typed covered step

theorem ControlSemantics.bound_transition (semantics : ControlSemantics allowed supported owned)
    {initial next} (typed : Abs.CoreTyped initial) (covered : supported initial)
    (transition : initial = next ∨ Abs.Core.step initial = .next next) :
    ∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound next := by
  rcases transition with same | step
  · exact fun _ h => same ▸ h
  · exact semantics.next_bound typed covered step
end Exec.Interp.StructuredMachine
