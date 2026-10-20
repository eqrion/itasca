import Exec.Theorems.Host.Open.Erasure.EraseHistory
import Exec.Theorems.Host.Open.Driver.DriverPrefixes
noncomputable section
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std

def Erased.run {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (select : Selector) (current : Erased.State M) : Result (Erased.Outcome M) :=
  loop (Erased.tick memory floats allocator select) current

/-- Physical execution is safe under the same checked prefix invariant as the
observed driver. This law is derived from its actual native tick proof. -/
theorem erased_run_safe {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (current : State M) (guard : StateGuard memory view code current) :
    Erased.run memory floats allocator select (Erased.state current) ⦃answer=>∃count,
      Interp.NormalTrace (Erased.tick memory floats allocator select) count (Erased.state current) answer⦄div := by
  let invariant := fun next : Erased.State M=>RunningFrom memory view code current.store (Erased.restore next)
  apply WP.dspec_mono (Interp.loop_trace_dspec (Erased.tick memory floats allocator select) invariant (fun _=>True) ?_ _ ?_)
  · intro answer post
    exact ⟨post.choose,post.choose_spec.1⟩
  · intro next held
    obtain ⟨flow,actual,post⟩ := WP.spec_imp_exists
      (tick_accumulated memory floats allocator correct allocation view laws select code current.store (Erased.restore next) held)
    simp only [Erased.tick,actual,bind_ok]
    apply WP.spec.ret
    cases flow with
    | done answer=>trivial
    | cont next=>exact post
  · exact ⟨code,.refl guard.1,guard⟩

/-- Erasing expanded observations agrees with the actual synchronous driver
on both return and divergence. It introduces neither extra finite runs nor a
callback-normality premise. -/
theorem erase_run_history {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (current : State M) (guard : StateGuard memory view code current) :
    (do let answer←run memory floats allocator select current
        .ok (Erased.outcome answer))=Erased.run memory floats allocator select (Erased.state current) := by
  have observedSafe:=run_safe memory floats allocator correct allocation view laws select code current guard
  have physicalSafe:=erased_run_safe memory floats allocator correct allocation view laws select code current guard
  generalize observed : run memory floats allocator select current=left at observedSafe ⊢
  cases observedSafe with
  | ret post=>
    rename_i answer
    obtain ⟨count,trace,rest⟩ := post
    simpa only [bind_ok,Erased.run] using (erase_normal_trace memory floats allocator select trace).result.symm
  | div=>
    simp only [bind_div]
    generalize physical : Erased.run memory floats allocator select (Erased.state current)=right at physicalSafe ⊢
    cases physicalSafe with
    | div=>rfl
    | ret post=>
      obtain ⟨count,trace⟩ := post
      obtain ⟨answer,erased,actual⟩ := lift_normal_trace memory floats allocator select trace current rfl
      have returns:=actual.result
      change run memory floats allocator select current=.ok answer at returns
      rw [observed] at returns
      exact False.elim (div_not_ok returns)
end Exec.Theorems.OpenReentrantControl
