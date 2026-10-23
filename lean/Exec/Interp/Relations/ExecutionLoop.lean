import Exec.Interp.Control.LoopBasis

/-! Actual execution-loop trace and safety composition. The body contract is a
local proof interface, to be discharged by the concrete instruction refinements. -/
namespace Exec.Interp
open Aeneas Aeneas.Std

abbrev ExecutionState (M P : Type) :=
  runtime.interp.Execution × runtime.store.Store M × P × core.result.Result Unit runtime.ExecError
abbrev ExecutionResult (M P : Type) :=
  Usize × alloc.vec.Vec U64 × alloc.vec.Vec runtime.interp.Frame × alloc.vec.Vec runtime.Value ×
    alloc.vec.Vec runtime.Value × runtime.store.Store M × P × core.result.Result Unit runtime.ExecError

def finishExecution {M P : Type} (state : ExecutionState M P) : ExecutionResult M P :=
  (state.1.store, state.1.slots, state.1.frames, state.1.host_args, state.1.host_results,
    state.2.1, state.2.2.1, state.2.2.2)

def ActiveExecution {M P : Type} (state : ExecutionState M P) : Prop :=
  0 < state.1.frames.length ∧ state.2.2.2 = .Ok ()

variable {M P F A : Type}
  (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
  (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)

def executionBody (state : ExecutionState M P) :
    Result (ControlFlow (ExecutionState M P) (ExecutionResult M P)) :=
  runtime.interp.invoke_with_loop1.body memory hooks floats allocator
    state.1 state.2.1 state.2.2.1 state.2.2.2

/-- A running iteration invokes exactly one instruction step. -/
theorem executionBody_active (state : ExecutionState M P) (active : ActiveExecution state) :
    executionBody memory hooks floats allocator state = (do
      let (status, exec, store, platform) ← runtime.interp.step memory hooks floats allocator
        state.1 state.2.1 state.2.2.1
      .ok (.cont (exec, store, platform, status))) := by
  obtain ⟨frames, status⟩ := active
  have hframes : state.1.frames.len > 0#usize := by scalar_tac
  simp [executionBody, runtime.interp.invoke_with_loop1.body, hframes, status,
    core.result.Result.is_ok]

/-- Finite returns have exact concrete step histories; divergence is allowed,
and panic or out-of-bounds failure is excluded by the local step contract. -/
theorem execution_loop_trace_safe
    (invariant : ExecutionState M P → Prop) (post : ExecutionResult M P → Prop)
    (stepTotal : ∀ exec store platform, invariant (exec, store, platform, .Ok ()) →
      0 < exec.frames.length →
      runtime.interp.step memory hooks floats allocator exec store platform
        ⦃ (status, exec', store', platform') => invariant (exec', store', platform', status) ⦄)
    (finished : ∀ state, invariant state → ¬ActiveExecution state → post (finishExecution state))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (status : core.result.Result Unit runtime.ExecError)
    (initial : invariant (exec, store, platform, status)) :
    runtime.interp.invoke_with_loop1 memory hooks floats allocator exec store platform status
      ⦃ result => ∃ count, NormalTrace (executionBody memory hooks floats allocator)
        count (exec, store, platform, status) result ∧ post result ⦄div := by
  change loop (executionBody memory hooks floats allocator) (exec, store, platform, status) ⦃ _ ⦄div
  apply loop_trace_dspec _ invariant post ?_ _ initial
  rintro ⟨current, currentStore, currentPlatform, currentStatus⟩ hinv
  unfold executionBody runtime.interp.invoke_with_loop1.body
  dsimp only
  split
  · have hframes : 0 < current.frames.length := by scalar_tac
    cases currentStatus with
    | Ok u =>
      cases u
      simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
      step with stepTotal current currentStore currentPlatform hinv hframes
      assumption
    | Err error =>
      have hp := finished (current, currentStore, currentPlatform, .Err error) hinv (by simp [ActiveExecution])
      simpa [core.result.Result.is_ok, finishExecution] using hp
  · have hframes : current.frames.length = 0 := by scalar_tac
    have hp := finished (current, currentStore, currentPlatform, currentStatus) hinv (by simp [ActiveExecution, hframes])
    simpa [finishExecution] using hp

/-- A stream of actual continuing instructions forces actual loop divergence. -/
theorem execution_loop_diverges (states : Nat → ExecutionState M P)
    (active : ∀ n, ActiveExecution (states n))
    (steps : ∀ n, runtime.interp.step memory hooks floats allocator
      (states n).1 (states n).2.1 (states n).2.2.1 =
      .ok ((states (n + 1)).2.2.2, (states (n + 1)).1,
        (states (n + 1)).2.1, (states (n + 1)).2.2.1)) :
    runtime.interp.invoke_with_loop1 memory hooks floats allocator
      (states 0).1 (states 0).2.1 (states 0).2.2.1 (states 0).2.2.2 = .div := by
  change loop (executionBody memory hooks floats allocator) (states 0) = .div
  apply loop_diverges_of_stream
  intro n
  rw [executionBody_active memory hooks floats allocator (states n) (active n), steps n]
  simp


/-- Every normal return stops at an invariant state with either no remaining
frames or a reported error. This is the outer-loop interface used by invocation. -/
theorem execution_loop_stops
    (invariant : ExecutionState M P → Prop)
    (stepTotal : ∀ exec store platform, invariant (exec, store, platform, .Ok ()) →
      0 < exec.frames.length →
      runtime.interp.step memory hooks floats allocator exec store platform
        ⦃ (status, exec', store', platform') => invariant (exec', store', platform', status) ⦄)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (status : core.result.Result Unit runtime.ExecError)
    (initial : invariant (exec, store, platform, status)) :
    runtime.interp.invoke_with_loop1 memory hooks floats allocator exec store platform status
      ⦃ result => ∃ state, invariant state ∧ ¬ActiveExecution state ∧ finishExecution state = result ⦄div := by
  apply WP.dspec_mono (execution_loop_trace_safe memory hooks floats allocator invariant
    (fun result => ∃ state, invariant state ∧ ¬ActiveExecution state ∧ finishExecution state = result)
    stepTotal (by intro state hi hs; exact ⟨state, hi, hs, rfl⟩)
    exec store platform status initial)
  rintro result ⟨count, trace, finalState⟩
  exact finalState

end Exec.Interp

