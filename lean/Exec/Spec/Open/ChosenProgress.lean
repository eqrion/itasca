import Exec.Spec.Open.ExecutionChosenCounted
namespace Exec.Spec.OpenExecution

theorem ChoiceTrace.first_step {H : Type} {model : HostModel H} {choices : Choices H}
    {occurrence count : Nat} {first last : State H} {events : List Observation}
    (trace : ChoiceTrace model choices occurrence count first events last) (positive : 0<count) :
    ∃remaining observed middle more,count=remaining+1 ∧
      ChoiceTransition model choices occurrence first observed middle ∧
      ChoiceTrace model choices (occurrence+1) remaining middle more last := by
  cases trace with
  | nil => omega
  | next step tail => exact ⟨_,_,_,_,rfl,step,tail⟩

/-- Strictly decreasing administrative work cannot hide an infinite native
computation. The occurrence ledger advances by exactly the selected trace's
length, including across any empty native administrative advance. -/
theorem chosen_positive_advance {H R : Type} (model : HostModel H) (choices : Choices H)
    (source : R → State H) (occurrence rank : R → Nat)
    (advance : ∀r,∃next count events,
      ChoiceTrace model choices (occurrence r) count (source r) events (source next) ∧
      occurrence next=occurrence r+count ∧ (count=0 → rank next<rank r)) (initial : R) :
    ∃next count events,0<count ∧ ChoiceTrace model choices (occurrence initial) count (source initial) events (source next) ∧
      occurrence next=occurrence initial+count := by
  have bounded : ∀budget r,rank r≤budget → ∃next count events,0<count ∧
      ChoiceTrace model choices (occurrence r) count (source r) events (source next) ∧
      occurrence next=occurrence r+count := by
    intro budget
    induction budget with
    | zero =>
      intro r bound
      obtain ⟨next,count,events,path,consumed,decrease⟩:=advance r
      exact ⟨next,count,events,(by by_contra absent;have := decrease (by omega);omega),path,consumed⟩
    | succ budget ih =>
      intro r bound
      obtain ⟨next,count,events,path,consumed,decrease⟩:=advance r
      cases count with
      | zero =>
        have less:=decrease rfl
        obtain ⟨last,more,observed,positive,tail,total⟩:=ih next (by omega)
        have same : occurrence next=occurrence r := by omega
        rw [same] at tail
        refine ⟨last,more,events++observed,positive,?_,by omega⟩
        simpa only [Nat.zero_add] using path.trans tail
      | succ count => exact ⟨next,count+1,events,by omega,path,consumed⟩
  exact bounded (rank initial) initial (Nat.le_refl _)

/-- A productive selected source stream retains one policy and its exact
occurrence ledger through finite source chunks and ranked native stutters. -/
theorem chosen_infinite_of_decreasing_stutter {H R : Type} (model : HostModel H) (choices : Choices H)
    (source : R → State H) (occurrence rank : R → Nat)
    (advance : ∀r,∃next count events,
      ChoiceTrace model choices (occurrence r) count (source r) events (source next) ∧
      occurrence next=occurrence r+count ∧ (count=0 → rank next<rank r)) (initial : R) :
    ChoiceInfinite model choices (occurrence initial) (source initial) := by
  classical
  let Reaches (point : Nat × State H) : Prop := ∃r count events,
    ChoiceTrace model choices point.1 count point.2 events (source r) ∧ occurrence r=point.1+count
  have progress : ∀position state,Reaches (position,state) → ∃events next,
      ChoiceTransition model choices position state events next ∧ Reaches (position+1,next) := by
    intro position state reachable
    obtain ⟨r,count,events,path,index⟩:=reachable
    cases path with
    | nil =>
      obtain ⟨next,count,events,positive,path,total⟩:=chosen_positive_advance model choices source occurrence rank advance r
      have same : occurrence r=position := by omega
      rw [same] at path
      obtain ⟨remaining,observed,middle,more,length,step,tail⟩:=path.first_step positive
      exact ⟨observed,middle,step,next,remaining,more,tail,by omega⟩
    | @next occurrence count first middle last observed more step tail =>
      exact ⟨observed,middle,step,r,count,more,tail,by omega⟩
  let Point := {point : Nat × State H // Reaches point}
  let nextPoint (point : Point) : Point :=
    ⟨(point.val.1+1,(progress point.val.1 point.val.2 point.property).choose_spec.choose),
      (progress point.val.1 point.val.2 point.property).choose_spec.choose_spec.2⟩
  let observation (point : Point) : List Observation := (progress point.val.1 point.val.2 point.property).choose
  let start : Point := ⟨(occurrence initial,source initial),initial,0,[],.nil _ _,rfl⟩
  let points : Nat → Point := fun n=>Nat.rec start (fun _ previous=>nextPoint previous) n
  have indices : ∀n,(points n).val.1=occurrence initial+n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change (points n).val.1+1=occurrence initial+(n+1)
      omega
  refine ⟨fun n=>(points n).val.2,fun n=>observation (points n),rfl,?_⟩
  intro n
  rw [←indices n]
  exact (progress (points n).val.1 (points n).val.2 (points n).property).choose_spec.choose_spec.1
end Exec.Spec.OpenExecution
