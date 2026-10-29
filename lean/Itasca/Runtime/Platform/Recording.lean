import Itasca.Generated.Types
import Itasca.Runtime.Spec.Steps

/-!
Exact host-event instrumentation. Erasure, bind composition, partial correctness and loop transport preserve the actual recorded event sequence used by invocation constructions.
-/

/-! ## Recording -/

section

namespace Itasca.Runtime.Platform.Recording
open Aeneas Aeneas.Std SpecExt

/-- Proof-only instrumentation records events at an interpreter call site,
after its result checker has determined the observable outcome. -/
def run {α : Type} (operation : Result α) (events : α → List HostEvent)
    (prior : List HostEvent) : Result (α × List HostEvent) := do
  let answer ← operation
  Result.ok (answer,prior ++ events answer)

/-- Erasing instrumentation preserves the exact computation, including
ordinary failure and divergence. -/
theorem erase {α : Type} (operation : Result α) (events : α → List HostEvent)
    (prior : List HostEvent) :
    (do let (answer,_) ← run operation events prior; Result.ok answer) = operation := by
  simp only [run,Std.bind_assoc,bind_ok,Std.uncurry,Std.bind_pure]

/-- Returning instrumented executions append precisely the site's event list. -/
theorem returned {α : Type} (operation : Result α) (events : α → List HostEvent)
    (prior : List HostEvent) (answer : α) (trace : List HostEvent) :
    run operation events prior = .ok (answer,trace) ↔
      operation = .ok answer ∧ trace = prior ++ events answer := by
  constructor
  · intro result
    have original := erase operation events prior
    rw [result,bind_ok] at original
    have exactRun : operation = .ok answer := original.symm
    refine ⟨exactRun,?_⟩
    simpa only [run,exactRun,bind_ok,Result.ok.injEq,Prod.mk.injEq,true_and] using result.symm
  · rintro ⟨operationEq,rfl⟩
    simp only [run,operationEq,bind_ok]

end Itasca.Runtime.Platform.Recording

end

/-! ## Recording Bind -/

section

namespace Itasca.Runtime.Platform.Recording
open Aeneas Aeneas.Std SpecExt

theorem bind_erase_cont {α β : Type}
    (recorded : Result (α × List HostEvent)) (original : Result α)
    (next : α × List HostEvent → Result β) (plainNext : α → Result β)
    (erase : (do let (answer,_) ← recorded; Result.ok answer)=original)
    (continued : ∀answer trace, next (answer,trace)=plainNext answer) :
    Std.bind recorded next = Std.bind original plainNext := by
  rw [←erase]
  simp only [Std.bind_assoc]
  apply congrArg (Std.bind recorded)
  funext pair
  rcases pair with ⟨answer,trace⟩
  simpa only [Std.uncurry,bind_ok] using continued answer trace
end Itasca.Runtime.Platform.Recording

end

/-! ## Recording Loop -/

section

namespace Itasca.Runtime.Platform.Recording
open Aeneas Aeneas.Std SpecExt Lean.Order Aeneas.Data.Coinductive
unseal Result

/-- The extracted Result effect has only terminal failure; its order is flat.
This fact is proved from the library's interaction-tree order. -/
theorem result_le_flat {α : Type} {a b : Result α} (h : a ⊑ b) : a=.div ∨ a=b := by
  have step := Eq.mp (ITree.le_unfold (E:=RustEffect) a b) h
  rcases step with same | ⟨value,ha,hb⟩ | ⟨eff,k,j,ha,hb,rest⟩
  · exact Or.inl same
  · exact Or.inr (ha.trans hb.symm)
  · right
    apply ha.trans
    apply Eq.trans _ hb.symm
    congr 1
    funext x
    cases eff
    cases x

/-- Any predicate containing divergence is admissible for this flat result. -/
theorem result_admissible {α : Type} (P : Result α → Prop) (bottom : P .div) : admissible P := by
  intro c hc hp
  by_cases hasNondiv : ∃ a,c a ∧ a≠.div
  · obtain ⟨a,member,nondiv⟩ := hasNondiv
    have upper : ∀b,c b → b ⊑ a := by
      intro b present
      rcases hc a b member present with order | order
      · rcases result_le_flat order with impossible | same
        · exact False.elim (nondiv impossible)
        · rw [same]
      · exact order
    have equal : CCPO.csup hc=a := PartialOrder.rel_antisymm (csup_le hc upper) (le_csup hc member)
    rw [equal]
    exact hp a member
  · have upper : ∀b,c b → b ⊑ Result.div := by
      intro b present
      have same : b=Result.div := by
        by_contra different
        exact hasNondiv ⟨b,present,different⟩
      rw [same]
    have equal : CCPO.csup hc=Result.div := ITree.le_div_is_div _ (csup_le hc upper)
    rw [equal]
    exact bottom

seal Result

/-- Append each concrete body outcome before taking its continue/done branch. -/
def loopBody {α β : Type} (body : α → Result (ControlFlow α β))
    (events : α → ControlFlow α β → List HostEvent) (state : α × List HostEvent) :
    Result (ControlFlow (α × List HostEvent) (β × List HostEvent)) := do
  let out ← body state.1
  let trace := state.2++events state.1 out
  match out with
  | .cont next => .ok (.cont (next,trace))
  | .done result => .ok (.done (result,trace))

/-- Proof-only writer instrumentation of the original least-fixed-point loop. -/
def loop {α β : Type} (body : α → Result (ControlFlow α β))
    (events : α → ControlFlow α β → List HostEvent) (initial : α) (prior : List HostEvent) :
    Result (β × List HostEvent) := Aeneas.Std.loop (loopBody body events) (initial,prior)

private theorem bind_right_mono {α β : Type} (r : Result α) (f g : α → Result β)
    (h : ∀x,f x ⊑ g x) : (do let x←r; f x) ⊑ (do let x←r; g x) := by
  exact Aeneas.Std.bind_mono (fun _ : α → Result β=>r) (fun k=>k) (monotone_const _) monotone_id f g h

unseal Result in
private theorem result_div_le {α : Type} (r : Result α) : Result.div ⊑ r := by
  exact Eq.mpr (ITree.le_unfold (E:=RustEffect) _ _) (Or.inl rfl)

/-- Removing the log recovers the exact original computation, including
failure and divergence, without any body correctness or termination premise. -/
theorem loop_erase {α β : Type} (body : α → Result (ControlFlow α β))
    (events : α → ControlFlow α β → List HostEvent) (initial : α) (prior : List HostEvent) :
    (do let (answer,_) ← loop body events initial prior; Result.ok answer) = Aeneas.Std.loop body initial := by
  apply PartialOrder.rel_antisymm
  · have adm : admissible (fun run : α × List HostEvent → Result (β × List HostEvent) =>
      ∀state,(do let (answer,_)←run state; Result.ok answer) ⊑ Aeneas.Std.loop body state.1) := by
      apply admissible_pi
      intro state
      apply admissible_apply (fun (_ : α × List HostEvent) (value : Result (β × List HostEvent))=>(do let (answer,_)←value; Result.ok answer) ⊑ Aeneas.Std.loop body state.1) state
      apply result_admissible
      simpa only [bind_div] using result_div_le (Aeneas.Std.loop body state.1)
    change (do let (answer,_)←Aeneas.Std.loop (loopBody body events) (initial,prior); Result.ok answer) ⊑ _
    apply Aeneas.Std.loop.fixpoint_induct (loopBody body events) _ adm ?_ (initial,prior)
    intro run ih state
    rw [Aeneas.Std.loop.eq_def body state.1]
    simp only [loopBody,Std.bind_assoc]
    apply bind_right_mono
    intro out
    cases out with
    | done result => simp only [bind_ok]; exact PartialOrder.rel_refl
    | cont next => simpa only [bind_ok] using ih (next,state.2++events state.1 (.cont next))
  · have adm : admissible (fun run : α → Result β =>
      ∀state prior,run state ⊑ (do let (answer,_)←loop body events state prior; Result.ok answer)) := by
      apply admissible_pi
      intro state
      apply admissible_pi
      intro prior
      apply admissible_apply (fun (_ : α) (value : Result β)=>value ⊑ (do let (answer,_)←loop body events state prior; Result.ok answer)) state
      exact result_admissible _ (result_div_le _)
    apply Aeneas.Std.loop.fixpoint_induct body _ adm ?_ initial prior
    intro run ih state prior
    unfold loop
    rw [Aeneas.Std.loop.eq_def (loopBody body events) (state,prior)]
    simp only [loopBody,Std.bind_assoc]
    apply bind_right_mono
    intro out
    cases out with
    | done result => simp only [bind_ok]; exact PartialOrder.rel_refl
    | cont next => simpa only [bind_ok,loop] using ih next (prior++events state (.cont next))

end Itasca.Runtime.Platform.Recording

end

/-! ## Recording Spec -/

section

namespace Itasca.Runtime.Platform.Recording
open Aeneas Aeneas.Std SpecExt
/-- A returning trace witness lifts partial correctness through exact erasure.
The divergence branch follows from erasure and adds no termination premise. -/
theorem lift_dspec {α : Type} (recorded : Result (α × List HostEvent)) (original : Result α)
    (P : α → Prop) (Q : α × List HostEvent → Prop)
    (erase : (do let (answer,_) ← recorded; Result.ok answer)=original)
    (checked : original ⦃ answer => P answer ⦄div)
    (returned : ∀answer,P answer → ∃trace, recorded=.ok (answer,trace) ∧ Q (answer,trace)) :
    recorded ⦃ pair => Q pair ⦄div := by
  cases checked with
  | ret held =>
    obtain ⟨trace,same,post⟩ := returned _ held
    rw [same]
    exact WP.dspec.ret post
  | div =>
    cases recorded using Result.cases with
    | ret pair =>
      rcases pair with ⟨answer,trace⟩
      simp only [bind_ok] at erase
      change Result.ok answer = .div at erase
      exact False.elim (ok_not_div erase)
    | div => exact WP.dspec.div _
    | vis e k => simp only [bind_vis,vis_not_div] at erase
/-- Erasure retains a graph witness identifying the exact returned log. -/
theorem erase_dspec {α : Type} (recorded : Result (α × List HostEvent)) (original : Result α)
    (Q : α × List HostEvent → Prop)
    (erase : (do let (answer,_) ← recorded; Result.ok answer)=original)
    (checked : recorded ⦃ pair => Q pair ⦄div) :
    original ⦃ answer => ∃trace, recorded=.ok (answer,trace) ∧ Q (answer,trace) ⦄div := by
  generalize actual : recorded=operation at checked
  cases checked with
  | ret held =>
    rw [←erase,actual,bind_ok]
    exact WP.dspec.ret ⟨_,rfl,held⟩
  | div =>
    rw [←erase,actual,bind_div]
    exact WP.dspec.div _
end Itasca.Runtime.Platform.Recording

end
