import Exec.Theorems.Host.Open.Driver.DriverTick
import Exec.Theorems.Host.Open.Driver.ReentrantHistory
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std

/-- Accumulated effects are indexed by the original entered world, retaining
committed writes and publications even if the whole interaction diverges. -/
def RunningFrom {M : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (original : Store.CodeInterpretation) (before : runtime.store.Store M) (state : State M) : Prop :=
  ∃code,ReentrantCallbacks.Effect view original before code state.store ∧ StateGuard memory view code state

def ReturnedFrom {M : Type} (view : M → Slice U8) (original : Store.CodeInterpretation)
    (before : runtime.store.Store M) (answer : Outcome M) : Prop :=
  ∃code,ReentrantCallbacks.Effect view original before code answer.store ∧ OutcomeGuard view code answer

theorem tick_accumulated {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (original : Store.CodeInterpretation) (before : runtime.store.Store M) (state : State M)
    (held : RunningFrom memory view original before state) :
    tick memory floats allocator select state ⦃out=>match out with
      | .cont next=>RunningFrom memory view original before next
      | .done answer=>ReturnedFrom view original before answer⦄ := by
  obtain ⟨code,effect,guard⟩ := held
  apply WP.spec_mono (tick_guard memory floats allocator correct allocation view laws select code state guard)
  intro out post
  cases out with
  | cont next =>
    obtain ⟨afterCode,more,fresh⟩ := post
    exact ⟨afterCode,effect.trans more,fresh⟩
  | done answer =>
    obtain ⟨afterCode,more,fresh⟩ := post
    exact ⟨afterCode,effect.trans more,fresh⟩

/-- The synchronous loop is safe without any callback-normality premise.
Every ordinary return has an exact finite trace and a checked cumulative effect. -/
theorem run_safe {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (state : State M) (guard : StateGuard memory view code state) :
    run memory floats allocator select state ⦃answer=>∃count,
      Interp.NormalTrace (tick memory floats allocator select) count state answer ∧
      ReturnedFrom view code state.store answer⦄div := by
  exact Interp.loop_trace_dspec (tick memory floats allocator select)
    (RunningFrom memory view code state.store) (ReturnedFrom view code state.store)
    (fun current held=>WP.spec_mono (tick_accumulated memory floats allocator correct allocation view laws select code state.store current held)
      (by intro out post; cases out <;> exact post))
    state ⟨code,.refl guard.1,guard⟩

/-- Divergence of a guarded driver is productive: no finite prefix can become
blocked inside a tick. Each state retains the entered world's complete checked
effect and every prior observation, including pending host entries. -/
theorem run_divergent_stream {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (state : State M) (guard : StateGuard memory view code state)
    (divergent : run memory floats allocator select state=.div) :
    ∃states : Nat → State M,states 0=state ∧ ∀n,
      RunningFrom memory view code state.store (states n) ∧
      tick memory floats allocator select (states n)=.ok (.cont (states (n+1))) ∧
      run memory floats allocator select (states n)=.div ∧
      ∃events,(states n).history=state.history++events := by
  have total : ∀current,RunningFrom memory view code state.store current →
      tick memory floats allocator select current ⦃out=>match out with
        | .cont next=>RunningFrom memory view code state.store next | .done _=>True⦄ := by
    intro current held
    apply WP.spec_mono (tick_accumulated memory floats allocator correct allocation view laws select code state.store current held)
    intro out post
    cases out with
    | cont next => exact post
    | done answer => trivial
  obtain ⟨states,initial,steps⟩ := Interp.loop_divergent_stream (tick memory floats allocator select)
    (RunningFrom memory view code state.store) (fun current held=>WP.spec_mono (total current held)
      (by intro out post; cases out <;> exact post)) state ⟨code,.refl guard.1,guard⟩ divergent
  have histories : ∀n,∃events,(states n).history=state.history++events := by
    intro n
    induction n with
    | zero => exact ⟨[],by rw [initial,List.append_nil]⟩
    | succ n ih =>
      obtain ⟨events,same⟩ := tick_history memory floats allocator select _ _ (steps n).2.1
      obtain ⟨earlier,before⟩ := ih
      exact ⟨earlier++events,by simpa only [outputHistory,before,List.append_assoc] using same⟩
  exact ⟨states,initial,fun n=>⟨(steps n).1,(steps n).2.1,(steps n).2.2,histories n⟩⟩
end Exec.Theorems.OpenReentrantControl
