import Exec.Spec.Choices.ChosenCounted
namespace Exec.Spec
open SpecExt

/-- Productive source chunks with one fixed policy and a coherent occurrence
ledger. Every chunk consumes at least one source reduction. -/
def InfiniteChosenChunks (choices : SourceChoices) (occurrence : Nat) (initial : config) : Prop :=
  ∃ states : Nat → config, ∃ ledger : Nat → Nat, ∃ events : Nat → List HostEvent,
    states 0=initial ∧ ledger 0=occurrence ∧ ∀ n, ∃ count, 0<count ∧
      ledger (n+1)=ledger n+count ∧ ChosenStepsN choices (ledger n) count (states n) (events n) (states (n+1))

theorem InfiniteChosenChunks.prepend {choices : SourceChoices} {occurrence count : Nat}
    {before after : config} {events : List HostEvent}
    (source : ChosenStepsN choices occurrence count before events after)
    (infinite : InfiniteChosenChunks choices (occurrence+count) after) :
    InfiniteChosenChunks choices occurrence before := by
  obtain ⟨states,ledger,trace,first,firstLedger,edges⟩ := infinite
  refine ⟨(fun n => match n with | 0 => before | n+1 => states (n+1)),
    (fun n => match n with | 0 => occurrence | n+1 => ledger (n+1)),
    (fun n => match n with | 0 => events++trace 0 | n+1 => trace (n+1)),rfl,rfl,?_⟩
  intro n
  cases n with
  | zero =>
    obtain ⟨nextCount,positive,nextLedger,nextChunk⟩ := edges 0
    rw [first,firstLedger] at nextChunk
    refine ⟨count+nextCount,by omega,?_,source.trans nextChunk⟩
    simpa only [firstLedger,Nat.add_assoc] using nextLedger
  | succ n => simpa only [Nat.add_assoc] using edges (n+1)

theorem InfiniteChosenChunks.uncons {choices : SourceChoices} {occurrence : Nat} {initial : config}
    (infinite : InfiniteChosenChunks choices occurrence initial) :
    ∃ events next, ChoiceStep choices occurrence initial events next ∧
      InfiniteChosenChunks choices (occurrence+1) next := by
  obtain ⟨states,ledger,events,first,firstLedger,edges⟩ := infinite
  have remaining : InfiniteChosenChunks choices (ledger 1) (states 1) :=
    ⟨(fun n => states (n+1)),(fun n => ledger (n+1)),(fun n => events (n+1)),rfl,rfl,
      (fun n => by simpa only [Nat.add_assoc] using edges (n+1))⟩
  obtain ⟨count,positive,ledgerEq,chunk⟩ := edges 0
  rw [first,firstLedger] at chunk
  rw [firstLedger] at ledgerEq
  generalize traceEq : events 0=trace at chunk
  generalize finalEq : states (0+1)=final at chunk
  cases chunk with
  | refl => omega
  | @cons occurrence count before middle after headEvents rest head tail =>
    refine ⟨headEvents,middle,head,?_⟩
    have suffix : InfiniteChosenChunks choices ((occurrence+1)+count) final := by
      simpa only [← finalEq,ledgerEq,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using remaining
    exact suffix.prepend tail

/-- Unrolling positive chunks preserves the same policy and advances its
occurrence by exactly one per source reduction. -/
theorem InfiniteChosenChunks.to_infinite {choices : SourceChoices} {occurrence : Nat} {initial : config}
    (infinite : InfiniteChosenChunks choices occurrence initial) : InfiniteChosenSource choices occurrence initial := by
  classical
  let Running := {entry : Nat × config // InfiniteChosenChunks choices entry.1 entry.2}
  have advance : ∀ current : Running, ∃ events next,
      ChoiceStep choices current.val.1 current.val.2 events next ∧
        InfiniteChosenChunks choices (current.val.1+1) next := fun current => current.property.uncons
  choose events next edge remaining using advance
  let successor (current : Running) : Running := ⟨(current.val.1+1,next current),remaining current⟩
  let states : Nat → Running := fun n => Nat.rec ⟨(occurrence,initial),infinite⟩ (fun _ previous => successor previous) n
  have ledger : ∀ n, (states n).val.1=occurrence+n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change (states n).val.1+1=occurrence+(n+1)
      rw [ih,Nat.add_assoc]
  refine ⟨(fun n => (states n).val.2),(fun n => events (states n)),rfl,?_⟩
  intro n
  simpa only [ledger] using edge (states n)
end Exec.Spec
