import Itasca.Runtime.Code.Module.CompileSubmit
import Mathlib.Data.List.Forall2

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- A queued worker retains its issued identity and a proved successful finish. -/
def CompletedWorker (issued : StreamBatch.Issued) (worker : Itasca.stream.CodeBatch) : Prop :=
  StreamBatch.Identity issued worker ∧ Itasca.stream.CodeBatch.finish worker = .ok (.Ok ())

/-- The actual reverse-order poll selects the final logical issued worker. -/
theorem completed_workers_last {queue : List StreamBatch.Issued} {workers : List Itasca.stream.CodeBatch}
    (related : List.Forall₂ CompletedWorker queue workers) (nonempty : queue ≠ []) :
    ∃ issued rest worker previous, queue = rest++[issued] ∧ workers = previous++[worker] ∧
      List.Forall₂ CompletedWorker rest previous ∧ CompletedWorker issued worker := by
  induction related with
  | nil => exact False.elim (nonempty rfl)
  | @cons issued worker queue workers same related ih =>
    by_cases empty : queue = []
    · subst queue
      cases related
      exact ⟨issued,[],worker,[],rfl,rfl,.nil,same⟩
    · obtain ⟨last,rest,final,previous,queueEq,workersEq,paired,ready⟩ := ih empty
      exact ⟨last,issued::rest,final,worker::previous,by simp only [queueEq,List.cons_append],
        by simp only [workersEq,List.cons_append],.cons same paired,ready⟩

/-- Appending the actual successful worker retains the complete queue relation. -/
theorem completed_workers_append {queue workers issued worker}
    (held : List.Forall₂ CompletedWorker queue workers) (ready : CompletedWorker issued worker) :
    List.Forall₂ CompletedWorker (queue++[issued]) (workers++[worker]) :=
  List.rel_append held (.cons ready .nil)

end Itasca.Runtime.Code
