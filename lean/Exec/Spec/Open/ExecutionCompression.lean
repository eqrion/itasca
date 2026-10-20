import Exec.Spec.Open.ExecutionTraces
namespace Exec.Spec.OpenExecution
open SpecExt

/-- A completed expanded interaction compresses to the original atomic host
step. Its final store extension follows from the actual finite source trace;
the proposed values are checked at the resumption boundary. -/
theorem Trace.compress_host {H : Type} {model : HostModel H}
    (suspended : Suspension) (control : H) (stack : List (Continuation H))
    (initial : (State.mk suspended.pending.before (.host control) (.wasm suspended::stack)).Typed)
    {count : Nat} {events : List Observation} {after : store} {result : Option (List val)}
    (trace : Trace model count ⟨suspended.pending.before,.host control,.wasm suspended::stack⟩ events
      ⟨after,.hostReturn result,.wasm suspended::stack⟩)
    (checked : ∀values,result=some values → ResultsTyped after suspended.pending.results values) :
    (HostReply.mk after result).Admissible suspended.pending.before suspended.pending.results ∧
    StepH suspended.pending.initial [.call suspended.pending.address suspended.pending.arguments result]
      (suspended.pending.completed ⟨after,result⟩) ∧
    Config_ok (suspended.pending.completed ⟨after,result⟩) suspended.expected := by
  obtain ⟨final,extension⟩ := trace.preserves initial
  have admissible : (HostReply.mk after result).Admissible suspended.pending.before suspended.pending.results :=
    ⟨extension,final.1,checked⟩
  exact ⟨admissible,suspended.pending.compress _ admissible,
    suspended.pending.completed_typed _ admissible suspended.typed⟩

/-- Atomic compression does not discard the expanded observations: the same
finite trace extends with the checked outer completion event. -/
theorem Trace.complete_host {H : Type} {model : HostModel H}
    (suspended : Suspension) (control : H) (stack : List (Continuation H))
    (initial : (State.mk suspended.pending.before (.host control) (.wasm suspended::stack)).Typed)
    {count : Nat} {events : List Observation} {after : store} {result : Option (List val)}
    (trace : Trace model count ⟨suspended.pending.before,.host control,.wasm suspended::stack⟩ events
      ⟨after,.hostReturn result,.wasm suspended::stack⟩)
    (checked : ∀values,result=some values → ResultsTyped after suspended.pending.results values) :
    Trace model (count+1) ⟨suspended.pending.before,.host control,.wasm suspended::stack⟩
      (events++[.completedHost (.call suspended.pending.address suspended.pending.arguments result)])
      ⟨after,.wasm (suspended.pending.completed ⟨after,result⟩).1.2
        (suspended.pending.completed ⟨after,result⟩).2 suspended.expected,stack⟩ := by
  have admissible := (trace.compress_host suspended control stack initial checked).1
  have currentStore : (suspended.pending.completed ⟨after,result⟩).1.1=after :=
    context_store suspended.pending.context _
  have same : suspended.pending.completed ⟨after,result⟩=
      ⟨⟨after,(suspended.pending.completed ⟨after,result⟩).1.2⟩,(suspended.pending.completed ⟨after,result⟩).2⟩ := by
    generalize configurationEq : suspended.pending.completed ⟨after,result⟩=configuration at currentStore ⊢
    rcases configuration with ⟨⟨s,f⟩,body⟩
    dsimp only at currentStore
    subst s
    rfl
  exact trace.trans (.next (.resumeWasm admissible same) (.nil _))
end Exec.Spec.OpenExecution
