import Itasca.Visitor.RunTrace
import Itasca.Visitor.Erasure

/-!
Replay a successful reader with a replacement callback at the actual decoded state.
The replacement supplies its own postcondition; acceptance at unrelated states is
not required. Compiler capacity proofs instantiate these visitor-only lemmas.
-/

namespace Itasca.CoreVisitor
open Aeneas Aeneas.Std VisitorTrace

/-- A source-validated scalar reader output and an available actual callback
produce ordinary acceptance with the exact reader state. -/
theorem run.available_of_read {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (VisitResult × V))
    (before : V) (value : A) (final : code.OpIterState) (post : V → Prop)
    (readCalled : read = .ok (.Ok value,final))
    (accepts : hook before final value ⦃ out => out.1 = .Ok () ∧ post out.2 ⦄) :
    run read hook before ⦃ out => out.1 = .Ok () ∧ out.2.1 = final ∧ post out.2.2 ⦄ := by
  obtain ⟨⟨reply,after⟩,called,accepted,held⟩ := WP.spec_imp_exists accepts
  dsimp only at accepted held
  subst reply
  refine WP.exists_imp_spec ⟨(.Ok (),final,after),?_,rfl,rfl,held⟩
  exact (run.returned_iff _ _ _ _ _ _).mpr (Or.inr ⟨value,.Ok (),readCalled,called,rfl⟩)

/-- An independently accepted reference reader/hook run transfers to a
replacement that accepts the actual reader result. No acceptance at unrelated
reader outputs or unreachable visitor states is required. -/
theorem run.accepted_lift_on {A V W : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (sourceHook : V → code.OpIterState → A → Result (VisitResult × V))
    (targetHook : W → code.OpIterState → A → Result (VisitResult × W))
    (sourceBefore sourceAfter : V) (targetBefore : W) (final : code.OpIterState)
    (post : W → Prop)
    (reference : run read sourceHook sourceBefore = .ok (.Ok (),final,sourceAfter))
    (accepts : ∀ a, read = .ok (.Ok a,final) →
      sourceHook sourceBefore final a = .ok (.Ok (),sourceAfter) →
      targetHook targetBefore final a ⦃ out => out.1 = .Ok () ∧ post out.2 ⦄) :
    run read targetHook targetBefore ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = final ∧ post out.2.2 ⦄ := by
  obtain ⟨value, readCalled, sourceCalled⟩ := run.accepted _ _ _ _ _ reference
  exact run.available_of_read read targetHook targetBefore value final post readCalled
    (accepts value readCalled sourceCalled)

end Itasca.CoreVisitor
