import Exec.Spec.Open.ExecutionTraces
noncomputable section
namespace Exec.Spec.OpenExecution
open SpecExt

/-- Dynamic reply validation is a source typing decision. Ill-typed proposed
values become a trap while retaining the current committed store. -/
def checkedResult (s : store) (types : List valtype) (proposed : Option (List val)) : Option (List val) := by
  classical
  exact match proposed with
  | none=>none
  | some values=>if ResultsTyped s types values then some values else none

theorem checkedResult_admissible (before after : store) (types : List valtype)
    (extension : Extend_store before after) (typed : Store_ok after) (proposed : Option (List val)) :
    (HostReply.mk after (checkedResult after types proposed)).Admissible before types := by
  classical
  refine ⟨extension,typed,?_⟩
  intro values selected
  cases proposed with
  | none=>simp [checkedResult] at selected
  | some returned=>
    simp only [checkedResult] at selected
    split at selected
    · rename_i accepted
      cases Option.some.inj selected
      exact accepted
    · cases selected

/-- Checked source resumption treats accepted values, rejected values and an
explicit host trap separately. It records exactly one outer completion. -/
theorem Transition.checkedResume {H : Type} (model : HostModel H) (suspended : Suspension)
    (after : store) (proposed : Option (List val)) (stack : List (Continuation H))
    (extension : Extend_store suspended.pending.before after) (typed : Store_ok after) :
    let result:=checkedResult after suspended.pending.results proposed
    let completed:=suspended.pending.completed ⟨after,result⟩
    Transition model ⟨after,.hostReturn proposed,.wasm suspended::stack⟩
      [.completedHost (.call suspended.pending.address suspended.pending.arguments result)]
      ⟨after,.wasm completed.1.2 completed.2 suspended.expected,stack⟩ := by
  classical
  dsimp only
  have admissible := checkedResult_admissible suspended.pending.before after suspended.pending.results extension typed proposed
  have same (result : Option (List val)) : suspended.pending.completed ⟨after,result⟩=
      ⟨⟨after,(suspended.pending.completed ⟨after,result⟩).1.2⟩,(suspended.pending.completed ⟨after,result⟩).2⟩ := by
    have current := context_store suspended.pending.context ((HostReply.mk after result).configuration suspended.pending.ambient)
    change (suspended.pending.completed ⟨after,result⟩).1.1=after at current
    generalize configurationEq : suspended.pending.completed ⟨after,result⟩=configuration at current ⊢
    rcases configuration with ⟨⟨s,f⟩,body⟩
    dsimp only at current
    subst s
    rfl
  cases proposed with
  | none=>
    simp only [checkedResult] at admissible ⊢
    exact Transition.resumeWasm admissible (same none)
  | some values=>
    by_cases accepted : ResultsTyped after suspended.pending.results values
    · simp only [checkedResult,if_pos accepted] at admissible ⊢
      exact Transition.resumeWasm admissible (same (some values))
    · simp only [checkedResult,if_neg accepted] at admissible ⊢
      exact Transition.rejectWasm accepted admissible (same none)
end Exec.Spec.OpenExecution
