import Itasca.Results.Definitions.Platform

/-! # Transparent callback observation

The observer changes only ghost platform state. These equations hold without
callback correctness or termination assumptions, including failing and divergent
computations. Execution transport builds on these boundary equations.
-/
namespace Itasca.Platform
open Aeneas Aeneas.Std

theorem observing_interrupt_erase {M P : Type} (hooks : runtime.platform.Platform P M)
    (platform : P) (prior : List (HostObservation M)) :
    (do let (action, next, _) ← (observing hooks).interrupt (platform, prior)
        Result.ok (action, next)) = hooks.interrupt platform := by
  simp only [observing, Std.bind_assoc, bind_ok, Std.uncurry, Prod.mk.eta, Std.bind_pure]

theorem observing_call_erase {M P : Type} (hooks : runtime.platform.Platform P M)
    (platform : P) (prior : List (HostObservation M)) (before : runtime.store.Store M)
    (identity : U64) (arguments defaults : Slice runtime.Value) :
    (do let (result, (next, _), after, returned) ←
          (observing hooks).call_host (platform, prior) before identity arguments defaults
        Result.ok (result, next, after, returned)) =
      hooks.call_host platform before identity arguments defaults := by
  simp only [observing, Std.bind_assoc, bind_ok, Std.uncurry, Prod.mk.eta, Std.bind_pure]

/-- A completed observation contains the exact callback request and reply.
Neither function-address selection nor result validation is inferred here. -/
theorem observing_call_returned {M P : Type} (hooks : runtime.platform.Platform P M)
    (platform : P) (prior : List (HostObservation M)) (before : runtime.store.Store M)
    (identity : U64) (arguments defaults : Slice runtime.Value)
    (result : core.result.Result Unit runtime.platform.HostError) (next : P)
    (after : runtime.store.Store M) (returned : Slice runtime.Value)
    (trace : List (HostObservation M)) :
    (observing hooks).call_host (platform, prior) before identity arguments defaults =
      .ok (result, (next, trace), after, returned) ↔
    hooks.call_host platform before identity arguments defaults = .ok (result, next, after, returned) ∧
      trace = prior ++ [⟨before, identity, arguments, defaults, result, after, returned⟩] := by
  constructor
  · intro observed
    have erased := observing_call_erase hooks platform prior before identity arguments defaults
    rw [observed, bind_ok] at erased
    dsimp only [Std.uncurry] at erased
    have actual := erased.symm
    refine ⟨actual, ?_⟩
    simpa only [observing, actual, bind_ok, Std.uncurry, Result.ok.injEq, Prod.mk.injEq,
      true_and, and_true] using observed.symm
  · rintro ⟨actual, rfl⟩
    simp only [observing, actual, bind_ok, Std.uncurry]

def eraseLoopState {M P : Type}
    (s : runtime.interp.Execution × runtime.store.Store M ×
      (P × List (HostObservation M)) × core.result.Result Unit runtime.ExecError) :=
  (s.1, s.2.1, s.2.2.1.1, s.2.2.2)

def eraseLoopAnswer {M P : Type}
    (out : Usize × alloc.vec.Vec U64 × alloc.vec.Vec runtime.interp.Frame ×
      alloc.vec.Vec runtime.Value × alloc.vec.Vec runtime.Value × runtime.store.Store M ×
      (P × List (HostObservation M)) × core.result.Result Unit runtime.ExecError) :=
  (out.1, out.2.1, out.2.2.1, out.2.2.2.1, out.2.2.2.2.1,
    out.2.2.2.2.2.1, out.2.2.2.2.2.2.1.1, out.2.2.2.2.2.2.2)


end Itasca.Platform

namespace Itasca.Platform
open Aeneas Aeneas.Std

/-- Observation leaves every platform premise intact. Interrupts return the
same decision and do not append a callback entry. -/
theorem Laws.observing {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} (laws : Laws memory hooks floats allocator view) :
    Laws memory (observing hooks) floats allocator view := by
  refine ⟨laws.floatsCorrect, laws.allocCorrect, ?_, laws.memoryLaws⟩
  rintro ⟨platform, prior⟩
  obtain ⟨⟨decision, next⟩, returned, _⟩ := WP.spec_imp_exists (laws.interruptsReturn platform)
  simp only [Itasca.Platform.observing, returned, bind_ok, WP.spec_ok, Std.uncurry]

end Itasca.Platform

/-! Internal writer instrumentation used to relate source histories to callback observations. -/

namespace Itasca.Platform.Recording

open Aeneas Aeneas.Std WebAssembly

/-- Proof-only instrumentation records events at an interpreter call site,
after its result checker has determined the observable outcome. -/
def run {α : Type} (operation : Result α) (events : α → List HostEvent)
    (prior : List HostEvent) : Result (α × List HostEvent) := do
  let answer ← operation
  Result.ok (answer,prior ++ events answer)

end Itasca.Platform.Recording

namespace Itasca.Platform.Recording

open Aeneas Aeneas.Std WebAssembly Lean.Order Aeneas.Data.Coinductive

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

end Itasca.Platform.Recording
