import Exec.Spec.Choices.ChosenChunks
namespace Exec.Spec
open SpecExt

/-- Dispatch simulation with a fixed source policy and a conserved occurrence
ledger. The silent branch keeps the source configuration and consumes no choice. -/
def ChosenDispatchSim {S : Type} (choices : SourceChoices) (decode : S → config)
    (ledger potential : S → Nat) (before : S) (events : List HostEvent) (after : S) : Prop :=
  (decode before=decode after ∧ ledger after=ledger before ∧ events=[] ∧ potential after<potential before) ∨
  ∃ count, 0<count ∧ ledger after=ledger before+count ∧
    ChosenStepsN choices (ledger before) count (decode before) events (decode after)

/-- Actual transitions plus strict silent decrease produce a positive chosen
source chunk. Runtime use must establish both transition premises from dispatch. -/
theorem chosen_positive_history {S : Type} (choices : SourceChoices)
    (next : S → List HostEvent → S → Prop) (decode : S → config) (ledger potential : S → Nat)
    (successor : ∀ s, ∃ events after, next s events after)
    (simulation : ∀ before events after, next before events after → ChosenDispatchSim choices decode ledger potential before events after)
    (initial : S) :
    ∃ after events dispatches count, 0<dispatches ∧ Iterations next dispatches initial events after ∧
      0<count ∧ ledger after=ledger initial+count ∧ ChosenStepsN choices (ledger initial) count (decode initial) events (decode after) := by
  have bounded : ∀ budget s, potential s≤budget →
      ∃ after events dispatches count, 0<dispatches ∧ Iterations next dispatches s events after ∧
        0<count ∧ ledger after=ledger s+count ∧ ChosenStepsN choices (ledger s) count (decode s) events (decode after) := by
    intro budget
    induction budget with
    | zero =>
      intro s bound
      obtain ⟨events,after,edge⟩ := successor s
      rcases simulation s events after edge with ⟨sameCode,sameLedger,empty,decrease⟩ | ⟨count,positive,advanced,source⟩
      · omega
      · exact ⟨after,events,1,count,by omega,by simpa using Iterations.cons edge (.refl after),positive,advanced,source⟩
    | succ budget ih =>
      intro s bound
      obtain ⟨events,after,edge⟩ := successor s
      rcases simulation s events after edge with ⟨sameCode,sameLedger,rfl,decrease⟩ | ⟨count,positive,advanced,source⟩
      · obtain ⟨last,trace,dispatches,count,nonempty,history,positive,advanced,source⟩ := ih after (by omega)
        refine ⟨last,trace,dispatches+1,count,by omega,?_,positive,?_,?_⟩
        · simpa only [List.nil_append] using Iterations.cons edge history
        · simpa only [sameLedger] using advanced
        · simpa only [sameCode,sameLedger] using source
      · exact ⟨after,events,1,count,by omega,by simpa using Iterations.cons edge (.refl after),positive,advanced,source⟩
  exact bounded (potential initial) initial (Nat.le_refl _)

/-- Coherent actual histories retain every selected policy occurrence. This
lemma supplies no runtime dispatch or callback law on its own. -/
theorem infinite_chosen_histories {S : Type} (choices : SourceChoices)
    (next : S → List HostEvent → S → Prop) (decode : S → config) (ledger potential : S → Nat)
    (successor : ∀ s, ∃ events after, next s events after)
    (simulation : ∀ before events after, next before events after → ChosenDispatchSim choices decode ledger potential before events after)
    (initial : S) :
    ∃ states : Nat → S, ∃ events : Nat → List HostEvent, states 0=initial ∧
      ∀ n, ∃ dispatches count, 0<dispatches ∧ Iterations next dispatches (states n) (events n) (states (n+1)) ∧
        0<count ∧ ledger (states (n+1))=ledger (states n)+count ∧
          ChosenStepsN choices (ledger (states n)) count (decode (states n)) (events n) (decode (states (n+1))) := by
  classical
  have advance := chosen_positive_history choices next decode ledger potential successor simulation
  let stateAfter (s : S) : S := Classical.choose (advance s)
  let traceAfter (s : S) : List HostEvent := Classical.choose (Classical.choose_spec (advance s))
  let states : Nat → S := fun n => Nat.rec initial (fun _ previous => stateAfter previous) n
  refine ⟨states,(fun n => traceAfter (states n)),rfl,?_⟩
  intro n
  exact Classical.choose_spec (Classical.choose_spec (advance (states n)))

/-- A runtime instantiation must derive successor and chosen simulation from
actual operations. Once discharged, the reflected infinity uses this policy. -/
theorem infinite_chosen_of_decreasing_stutter {S : Type} (choices : SourceChoices)
    (next : S → List HostEvent → S → Prop) (decode : S → config) (ledger potential : S → Nat)
    (successor : ∀ s, ∃ events after, next s events after)
    (simulation : ∀ before events after, next before events after → ChosenDispatchSim choices decode ledger potential before events after)
    (initial : S) : InfiniteChosenSource choices (ledger initial) (decode initial) := by
  obtain ⟨states,events,first,edges⟩ := infinite_chosen_histories choices next decode ledger potential successor simulation initial
  apply InfiniteChosenChunks.to_infinite
  refine ⟨(fun n => decode (states n)),(fun n => ledger (states n)),events,congrArg decode first,congrArg ledger first,?_⟩
  intro n
  obtain ⟨dispatches,count,nonempty,history,positive,advanced,source⟩ := edges n
  exact ⟨count,positive,advanced,source⟩
end Exec.Spec
