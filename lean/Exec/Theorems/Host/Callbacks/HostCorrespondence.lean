import Exec.Theorems.Host.Callbacks.HostControl

/-! Bidirectional correspondence for resumable host-local control. Finite
independent traces give actual normal return; infinite streams give actual
divergence. This module does not add suspended or nested Wasm transitions. -/

namespace Exec.Theorems.OpenHostControl
open Aeneas Aeneas.Std

/-- Every independently permitted local step is an actual executable tick. -/
theorem Transition.actual {M : Type} (memory : runtime.platform.MemoryBuffer M)
    {program : Code} {state : State M} {out : ControlFlow (State M) (Reply M)}
    (source : Transition program state out) : tick memory program state = .ok out := by
  cases source with
  | missing selected => simp [tick,selected]
  | trapped selected => simp [tick,selected]
  | returned values selected => simp [tick,selected]
  | jump target selected => simp [tick,selected]
  | branch condition yes no selected => simp [tick,selected]
  | action selected effect =>
    obtain ⟨values,actual,_⟩ := effect.actual memory
    simp [tick,selected,actual]
  | @rejected segment next error after values selected effect =>
    obtain ⟨returned,actual,same⟩ := effect.actual memory
    have identical : returned = values := Slice.ext _ _ same
    simp [tick,selected,actual,identical]

theorem Transition.deterministic {M : Type} (memory : runtime.platform.MemoryBuffer M)
    {program : Code} {state : State M} {first second : ControlFlow (State M) (Reply M)}
    (left : Transition program state first) (right : Transition program state second) :
    first = second := by
  simpa only [Result.ok.injEq] using (left.actual memory).symm.trans (right.actual memory)

/-- Finite local execution supplies normal callback return without a ranking
or an assumed normality law. -/
theorem ReturnedControl.actual {M : Type} (memory : runtime.platform.MemoryBuffer M)
    {program : Code} {state : State M} {answer : Reply M}
    (source : ReturnedControl program state answer) : run memory program state = .ok answer := by
  induction source with
  | done source =>
    rw [run,loop.eq_def,source.actual memory,bind_ok]
  | next source tail ih =>
    rw [run,loop.eq_def,source.actual memory,bind_ok]
    exact ih

/-- Actual normal return has a finite independent trace on arbitrary stores;
semantic store invariants are required separately for preservation. -/
theorem run_refines {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (program : Code) (state : State M) :
    run memory program state ⦃ answer => ReturnedControl program state answer ⦄div := by
  have body : ∀ current, True → tick memory program current ⦃ out =>
      match out with
      | .cont _ => True
      | .done _ => True ⦄ := by
    intro current _
    exact WP.spec_mono (tick_refines memory program current) (fun out _ => by cases out <;> trivial)
  have traced := Interp.loop_trace_dspec (tick memory program) (fun _ => True) (fun _ => True)
    (fun current valid => WP.spec_mono (body current valid)
      (by intro out held; cases out <;> exact held)) state trivial
  exact WP.dspec_mono traced (fun _ ⟨_,trace,_⟩ => normal_trace_refines memory program trace)

theorem returned_control_iff {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (program : Code) (state : State M) (answer : Reply M) :
    ReturnedControl program state answer ↔ run memory program state = .ok answer := by
  constructor
  · exact ReturnedControl.actual memory
  · intro actual
    have refined := run_refines memory program state
    rw [actual,WP.dspec_ok] at refined
    exact refined

/-- A productive stream of independent host-local transitions implies actual
synchronous divergence. It does not assert divergence inside Wasm. -/
theorem infinite_control_diverges {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (program : Code) (states : Nat → State M)
    (edges : ∀ n, Transition program (states n) (.cont (states (n+1)))) :
    run memory program (states 0) = .div := by
  exact Interp.loop_diverges_of_stream (tick memory program) states (fun n => (edges n).actual memory)

/-- Independent transitions preserve the same checked prefix properties as
the executable implementation, rather than assuming them in the semantics. -/
theorem Transition.preserves {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    {program : Code} {state : State M} {out : ControlFlow (State M) (Reply M)}
    (held : ExecutableInv view code state.store) (source : Transition program state out) :
    Effect view code state.store (outputStore out) ∧
      match out with
      | .cont next => next.identity = state.identity ∧ next.arguments = state.arguments
      | .done answer => ∀ value ∈ answer.2.2.val, Store.IssuedValue answer.2.1 value := by
  have preserved := tick_preserves memory program view code state held
  rw [source.actual memory,WP.spec_ok] at preserved
  cases out <;> exact preserved

/-- Finite independent traces retain every committed store effect and issue
their returned values. Their implementation normality is derived above. -/
theorem ReturnedControl.preserves {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    {program : Code} {state : State M} {answer : Reply M}
    (held : ExecutableInv view code state.store) (source : ReturnedControl program state answer) :
    Effect view code state.store answer.2.1 ∧
      ∀ value ∈ answer.2.2.val, Store.IssuedValue answer.2.1 value := by
  have safe := run_safe memory program view code state held
  rw [source.actual memory,WP.dspec_ok] at safe
  exact safe.2

end Exec.Theorems.OpenHostControl

