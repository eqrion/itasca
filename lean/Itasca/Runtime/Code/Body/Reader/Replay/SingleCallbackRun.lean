import Itasca.Runtime.Code.Body.Reader.Publication.NonScopeCallbackPublication

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Extract the actual accepted callback at the reader's returned state. The
classification concerns event arguments only, independently of compiler code. -/
theorem reader_single_callback_of_run {X V : Type} (visitor : code.OpVisitor V)
    (read : Result (core.result.Result X error.OpError × code.OpIterState))
    (event : code.OpIterState → X → Action) (before after : V) (out : code.OpIterState)
    (supported : ∀ arg, NoScopeBoundary (event out arg) ∧ PublicationActionRange (event out arg))
    (accepted : CoreVisitor.run read (fun v state arg => invoke visitor v (.op state (event state arg))) before =
      .ok (.Ok (),out,after)) :
    ∃ action, NoScopeBoundary action ∧ PublicationActionRange action ∧
      invoke visitor before (.op out action) = .ok (.Ok (),after) := by
  obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
  exact ⟨event out arg,(supported arg).1,(supported arg).2,callback⟩

end Itasca.Runtime.Code
