import Exec.Theorems.Host.Open.Driver.ReentrantHistory
noncomputable section
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std
namespace Erased

/-- Physical driver state, with observation history omitted. -/
structure State (M : Type) where
  store : runtime.store.Store M
  mode : Mode M
  stack : List Continuation

inductive Outcome (M : Type) where
  | host (answer : Reply M)
  | invocation (answer : Interp.OpenCall.InvokeAnswer M Unit)

def state {M : Type} (raw : OpenReentrantControl.State M) : State M := ⟨raw.store,raw.mode,raw.stack⟩
def restore {M : Type} (raw : State M) : OpenReentrantControl.State M := ⟨raw.store,raw.mode,raw.stack,[]⟩
def outcome {M : Type} : OpenReentrantControl.Outcome M → Outcome M
  | .host answer _=>.host answer
  | .invocation answer _=>.invocation answer

def output {M : Type} : ControlFlow (OpenReentrantControl.State M) (OpenReentrantControl.Outcome M) → ControlFlow (State M) (Outcome M)
  | .cont next=>.cont (state next)
  | .done answer=>.done (outcome answer)

def tick {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (select : Selector) (current : State M) : Result (ControlFlow (State M) (Outcome M)) := do
  let out←OpenReentrantControl.tick memory floats allocator select (restore current)
  .ok (output out)
end Erased

/-- Expanded observations do not affect any physical native computation,
including divergent computations inside a primitive operation. -/
theorem erase_tick_history {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (select : Selector) (current : State M) :
    (do let out←tick memory floats allocator select current
        .ok (Erased.output out))=Erased.tick memory floats allocator select (Erased.state current) := by
  cases current with | mk store mode stack history=>
    cases mode <;> simp only [Erased.tick,Erased.restore,Erased.state,tick,Std.bind_assoc,bind_ok]
    repeat' first
      | rfl
      | (congr 1; funext x)
      | (cases x <;> simp_all only [Std.uncurry,Std.bind_assoc,bind_ok,Erased.output,Erased.outcome,Erased.state,acceptCall])
      | (split <;> simp_all only [Std.uncurry,Std.bind_assoc,bind_ok,Erased.output,Erased.outcome,Erased.state,acceptCall])

/-- Every actual finite driver return erases to the same physical task result. -/
theorem erase_normal_trace {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    {count : Nat} {first : State M} {answer : Outcome M}
    (trace : Interp.NormalTrace (tick memory floats allocator select) count first answer) :
    Interp.NormalTrace (Erased.tick memory floats allocator select) count (Erased.state first) (Erased.outcome answer) := by
  induction trace with
  | done actual=>
    apply Interp.NormalTrace.done
    rw [←erase_tick_history,actual,bind_ok]
    rfl
  | next actual tail ih=>
    apply Interp.NormalTrace.next (next:=Erased.state _) _ ih
    rw [←erase_tick_history,actual,bind_ok]
    rfl

/-- Erasing observations introduces no additional finite returns: every erased
trace lifts to actual driver ticks with their expanded nested history. -/
theorem lift_normal_trace {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    {count : Nat} {first : Erased.State M} {answer : Erased.Outcome M}
    (trace : Interp.NormalTrace (Erased.tick memory floats allocator select) count first answer)
    (raw : State M) (same : Erased.state raw=first) :
    ∃actual,Erased.outcome actual=answer ∧ Interp.NormalTrace (tick memory floats allocator select) count raw actual := by
  induction trace generalizing raw with
  | @done state result step=>
    have graph:=erase_tick_history memory floats allocator select raw
    rw [same,step] at graph
    obtain ⟨flow,called,projected⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ graph
    cases flow with
    | cont next=>simp [Erased.output] at projected
    | done actual=>
      have equal : Erased.outcome actual=result := by simpa [Erased.output] using projected
      exact ⟨actual,equal,.done called⟩
  | @next count state middle result step tail ih=>
    have graph:=erase_tick_history memory floats allocator select raw
    rw [same,step] at graph
    obtain ⟨flow,called,projected⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ graph
    cases flow with
    | done actual=>simp [Erased.output] at projected
    | cont next=>
      have equal : Erased.state next=middle := by simpa [Erased.output] using projected
      obtain ⟨actual,erased,trace⟩ := ih next equal
      exact ⟨actual,erased,.next called trace⟩
end Exec.Theorems.OpenReentrantControl
