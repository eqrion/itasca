import Exec.Spec.Open.ExecutionReplies
namespace Exec.Spec.OpenExecution
open SpecExt

/-- A host finish and its checked Wasm resumption retain both nesting events.
The dynamic result check uses source typing and keeps all committed effects. -/
theorem Trace.finish_checked {H : Type} (model : HostModel H) (control : H)
    (suspended : Suspension) (after : store) (proposed : Option (List val)) (stack : List (Continuation H))
    (finished : model.finish after control proposed)
    (extension : Extend_store suspended.pending.before after) (typed : Store_ok after) :
    let result:=checkedResult after suspended.pending.results proposed
    let completed:=suspended.pending.completed ⟨after,result⟩
    Trace model 2 ⟨after,.host control,.wasm suspended::stack⟩
      [.hostExit proposed,.completedHost (.call suspended.pending.address suspended.pending.arguments result)]
      ⟨after,.wasm completed.1.2 completed.2 suspended.expected,stack⟩ := by
  exact .next (.finish finished) (.next (Transition.checkedResume model suspended after proposed stack extension typed) (.nil _))
end Exec.Spec.OpenExecution
