import Itasca.Visitor.ReaderAcceptance
import Itasca.Visitor.Recording

/-!
Equal successful recorder transitions name the same source event. This uses the independently defined recorder; it assumes no target behavior.

Main declarations: `recorder_invocation_unique` and `recorded_reader_available`. A direct consumer is `Compiler.Body.Reader.Acceptance.SourceBoundTypedSelectAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Equal successful recorder transitions name the same source event. This
uses the independently defined recorder; it assumes no target behavior. -/
theorem recorder_invocation_unique (before after : List Observation) (first second : Event)
    (left : invoke recorder before first = .ok (.Ok (),after))
    (right : invoke recorder before second = .ok (.Ok (),after)) : first = second := by
  have leftLog := recorder_records before first (.Ok ()) after left
  have rightLog := recorder_records before second (.Ok ()) after right
  dsimp only [id] at leftLog rightLog
  have same := List.append_cancel_left (leftLog.symm.trans rightLog)
  exact congrArg Observation.event (List.cons.inj same).1

/-- Replay a parsed single-event reader using the actual event established by
independent source analysis. Event uniqueness avoids assuming injective
callback behavior of arbitrary native visitors. -/
theorem recorded_reader_available {R W : Type}
    (read : Result (core.result.Result R error.OpError × code.OpIterState))
    (action : R → Action) (target : code.OpVisitor W) (compiler : W)
    (before after : List Observation) (out : code.OpIterState) (knownAction : Action) (post : W → Prop)
    (reference : CoreVisitor.run read (fun log state value => invoke recorder log (.op state (action value))) before =
      .ok (.Ok (),out,after))
    (known : invoke recorder before (.op out knownAction) = .ok (.Ok (),after))
    (acceptance : invoke target compiler (.op out knownAction) ⦃ result => result.1 = .Ok () ∧ post result.2 ⦄) :
    CoreVisitor.run read (fun current state value => invoke target current (.op state (action value))) compiler
      ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧ post result.2.2 ⦄ := by
  refine CoreVisitor.run.accepted_lift_on read _ _ before after compiler out post reference ?_
  intro value _ called
  have same := recorder_invocation_unique before after (.op out (action value)) (.op out knownAction) called known
  rw [same]
  exact acceptance

end Itasca.Runtime.Compiler
