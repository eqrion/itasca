import Exec.Spec.Open.ExecutionTraces
namespace Exec.Spec.OpenExecution

theorem Trace.first_step {H : Type} {model : HostModel H} {count : Nat}
    {first last : State H} {events : List Observation} (trace : Trace model count first events last)
    (positive : 0<count) : ∃observed middle remaining more,
      Transition model first observed middle ∧ Trace model remaining middle more last := by
  cases trace with
  | nil state=>omega
  | next step tail=>exact ⟨_,_,_,_,step,tail⟩

/-- Strictly decreasing administrative potential prevents infinitely many
concrete dispatches from hiding behind an empty source trace. Applications
must derive each advance from their actual guarded computation. -/
theorem positive_advance {H R : Type} (model : HostModel H) (source : R → State H) (rank : R → Nat)
    (advance : ∀r,∃next count events,Trace model count (source r) events (source next) ∧
      (count=0 → rank next<rank r)) (initial : R) :
    ∃next count events,0<count ∧ Trace model count (source initial) events (source next) := by
  have bounded : ∀budget r,rank r≤budget →
      ∃next count events,0<count ∧ Trace model count (source r) events (source next) := by
    intro budget
    induction budget with
    | zero=>
      intro r bound
      obtain ⟨next,count,events,trace,decrease⟩ := advance r
      have positive : 0<count := by by_contra absent; have := decrease (by omega); omega
      exact ⟨next,count,events,positive,trace⟩
    | succ budget ih=>
      intro r bound
      obtain ⟨next,count,events,trace,decrease⟩ := advance r
      cases count with
      | zero=>
        have less := decrease rfl
        obtain ⟨last,more,observed,positive,tail⟩ := ih next (by omega)
        exact ⟨last,more,events++observed,positive,by simpa only [Nat.zero_add] using trace.trans tail⟩
      | succ count=>exact ⟨next,count+1,events,by omega,trace⟩
  exact bounded (rank initial) initial (Nat.le_refl _)

/-- Ranked finite-step simulation yields an actual source transition at every
position, not just an unlabelled divergence result or disconnected prefixes. -/
theorem infinite_of_decreasing_stutter {H R : Type} (model : HostModel H) (source : R → State H) (rank : R → Nat)
    (advance : ∀r,∃next count events,Trace model count (source r) events (source next) ∧
      (count=0 → rank next<rank r)) (initial : R) : InfiniteTrace model (source initial) := by
  classical
  let Reaches (state : State H) : Prop:=∃r count events,Trace model count state events (source r)
  have progress : ∀state,Reaches state → ∃events next,Transition model state events next ∧ Reaches next := by
    intro state reachable
    obtain ⟨r,count,events,path⟩ := reachable
    cases path with
    | nil state=>
      obtain ⟨next,count,events,positive,trace⟩ := positive_advance model source rank advance r
      obtain ⟨observed,middle,remaining,more,step,tail⟩ := trace.first_step positive
      exact ⟨observed,middle,step,next,remaining,more,tail⟩
    | @next count first middle last observed more step tail=>
      exact ⟨observed,middle,step,r,count,more,tail⟩
  let Point:= {state : State H // Reaches state}
  let nextPoint (point : Point) : Point:=
    ⟨(progress point.val point.property).choose_spec.choose,
      (progress point.val point.property).choose_spec.choose_spec.2⟩
  let observation (point : Point) : List Observation:=(progress point.val point.property).choose
  let start : Point:=⟨source initial,initial,0,[],.nil _⟩
  let points : Nat → Point:=fun n=>Nat.rec start (fun _ previous=>nextPoint previous) n
  refine ⟨fun n=>(points n).val,fun n=>observation (points n),rfl,?_⟩
  intro n
  exact (progress (points n).val (points n).property).choose_spec.choose_spec.1
end Exec.Spec.OpenExecution
