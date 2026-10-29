import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions

/-!
A source-validated control-reader output followed by an available actual callback accepts with that exact source state.

Main declarations: `bodyRun.available_of_read` and `bodyRun.accepted_lift_on`. A direct consumer is `Compiler.Body.Reader.Calls.Acceptance`.
-/

namespace Itasca.Wasm2.CallbackTrace
open Aeneas Aeneas.Std VisitorTrace

/-- A source-validated control-reader output followed by an available actual
callback accepts with that exact source state. -/
theorem bodyRun.available_of_read {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.BodyState))
    (visitor : code.OpVisitor V) (action : A → Action) (before : V)
    (value : A) (final : code.BodyState) (post : V → Prop)
    (readCalled : read = .ok (.Ok value,final))
    (accepts : invoke visitor before (.op final.core (action value)) ⦃ result =>
      result.1 = .Ok () ∧ post result.2 ⦄) :
    bodyRun read visitor action before ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = final ∧ post result.2.2 ⦄ := by
  obtain ⟨⟨reply,after⟩,called,accepted,held⟩ := WP.spec_imp_exists accepts
  dsimp only at accepted held
  subst reply
  apply WP.exists_imp_spec
  refine ⟨(.Ok (),final,after),?_,rfl,rfl,held⟩
  simp [bodyRun,readCalled,called,hookResult]

/-- Replay the actual metadata-producing Wasm 2 control reader. Only its
independently accepted output invokes the target callback; unrelated visitor
states and unrelated metadata do not need to accept. -/
theorem bodyRun.accepted_lift_on {A V W : Type}
    (read : Result (core.result.Result A error.OpError × code.BodyState))
    (source : code.OpVisitor V) (target : code.OpVisitor W) (action : A → Action)
    (before after : V) (compiler : W) (final : code.BodyState) (post : W → Prop)
    (reference : bodyRun read source action before = .ok (.Ok (),final,after))
    (accepts : ∀ value, read = .ok (.Ok value,final) →
      invoke source before (.op final.core (action value)) = .ok (.Ok (),after) →
      invoke target compiler (.op final.core (action value)) ⦃ result => result.1 = .Ok () ∧ post result.2 ⦄) :
    bodyRun read target action compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = final ∧ post result.2.2 ⦄ := by
  obtain ⟨value,readCalled,sourceCalled⟩ := Itasca.Runtime.Code.reader_body_success _ _ _ _ _ _ reference
  obtain ⟨⟨reply,after⟩,called,accepted,held⟩ := WP.spec_imp_exists (accepts value readCalled sourceCalled)
  dsimp only at accepted held
  subst reply
  apply WP.exists_imp_spec
  refine ⟨(.Ok (),final,after),?_,rfl,rfl,held⟩
  simp [bodyRun,readCalled,called,hookResult]

end Itasca.Wasm2.CallbackTrace
