import Exec.Interp.Machines.Slice.SliceTotal
import Exec.Interp.Relations.ExecutionLoop

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- A concrete/source machine state with all invariants needed to execute the
next dispatch. The code bound is fixed for an entire invocation. -/
structure SliceMachine {M : Type} (P : Type) (store : runtime.store.Store M)
    (sourceStore : _root_.store) (ambient : frame) (expected : List valtype) (bound : Nat) where
  exec : runtime.interp.Execution
  platform : P
  source : Abs.AState
  pc : Nat
  pending : Bool
  invariant : SliceExecution store exec source expected pc pending
  bounded : Abs.CodeBound bound source
  decoded : source.store = sourceStore
  ambient_eq : source.ambient = ambient

/-- A successful history edge records the actual extracted step equation as
well as its checked positive reduction or administrative decrease. -/
def SliceTransition {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame} {expected : List valtype} {bound : Nat}
    (before : SliceMachine P store sourceStore ambient expected bound) (events : List SpecExt.HostEvent)
    (after : SliceMachine P store sourceStore ambient expected bound) : Prop :=
  events = [] ∧ runtime.interp.step memory hooks floats allocator before.exec store before.platform =
    .ok (.Ok (), after.exec, store, after.platform) ∧
  ConcreteSim U32.max before.pc after.pc before.pending after.pending before.source after.source ∧
  (∀ bound, Abs.StateReferencesBound bound before.source → Abs.StateReferencesBound bound after.source)

def slicePotentialBound (bound : Nat) : Nat := (bound + 1) * (2 * (U32.max + 1))

def SliceMachine.potential {M P store sourceStore ambient expected bound}
    (machine : @SliceMachine M P store sourceStore ambient expected bound) : Nat :=
  dispatchMeasure machine.pending U32.max machine.pc machine.source

theorem SliceMachine.potential_le {M P store sourceStore ambient expected bound}
    (machine : @SliceMachine M P store sourceStore ambient expected bound) :
    machine.potential ≤ slicePotentialBound bound := by
  have bounded := Nat.mul_le_mul_right (2 * (U32.max + 1)) machine.bounded.measure
  unfold SliceMachine.potential slicePotentialBound
  rw [Nat.add_mul, Nat.one_mul]
  cases phase : machine.pending <;> simp only [dispatchMeasure, phase, ite_true, Bool.false_eq_true, ite_false] <;> omega

theorem history_append {S : Type} {next : S → List SpecExt.HostEvent → S → Prop}
    {n m : Nat} {first middle last : S} {events rest : List SpecExt.HostEvent}
    (left : Spec.Iterations next n first events middle) (right : Spec.Iterations next m middle rest last) :
    Spec.Iterations next (n + m) first (events ++ rest) last := by
  induction left with
  | refl _ => simpa using right
  | cons step _ ih => simpa [Nat.add_assoc, Nat.add_comm, List.append_assoc] using Spec.Iterations.cons step (ih right)

theorem history_snoc {S : Type} {next : S → List SpecExt.HostEvent → S → Prop}
    {n : Nat} {first middle last : S}
    (run : Spec.Iterations next n first [] middle) (step : next middle [] last) :
    Spec.Iterations next (n + 1) first [] last := by
  simpa using history_append run (Spec.Iterations.cons step (Spec.Iterations.refl last))

/-- Counted simulation of the exact successful dispatch history. The finite
bound applies uniformly across recursive calls and backward branches. -/
theorem SliceMachine.history_progress {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame} {expected : List valtype} {bound n : Nat}
    {before after : SliceMachine P store sourceStore ambient expected bound}
    (run : Spec.Iterations (SliceTransition memory hooks floats allocator) n before [] after) :
    ∃ count, Spec.StepsHN count (Abs.decode before.source) [] (Abs.decode after.source) ∧
      n / (slicePotentialBound bound + 1) ≤ count := by
  apply Spec.iterations_progress (fun state => Abs.decode state.source) SliceMachine.potential
    (slicePotentialBound bound) (fun state => state.invariant.typed.decode_wf)
    SliceMachine.potential_le ?_ run
  intro first events last step
  obtain ⟨eventsEq, actual, simulation, references⟩ := step
  rcases simulation with ⟨same, decrease⟩ | reductions
  · exact Or.inl ⟨same, eventsEq, decrease⟩
  · exact Or.inr (by simpa only [eventsEq] using reductions)

theorem SliceExecution.finished {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {source : Abs.AState} {expected : List valtype} {pc : Nat} {pending : Bool}
    (invariant : SliceExecution store exec source expected pc pending) (empty : exec.frames.val = []) :
    source.frames = [] ∧ SpecExt.ResultsTyped source.store expected source.results ∧
      ValuesAt exec.slots.val 0 source.results := by
  have sourceEmpty : source.frames = [] := by
    cases frames : source.frames with
    | nil => rfl
    | cons f rest =>
      have stack := invariant.stack
      rw [frames] at stack
      cases stack with
      | active concrete top saved => simp [empty] at concrete
  refine ⟨sourceEmpty, ?_, ?_⟩
  · simpa only [Abs.InvocationResult, sourceEmpty] using invariant.result
  · have cursor := invariant.cursor
    simp only [ExecutionCursor, sourceEmpty] at cursor
    exact cursor.2.2

/-- Every exact successful dispatch history retains the initial issued-reference bound. -/
theorem SliceMachine.history_references {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound n referencesBound : Nat} {events : List SpecExt.HostEvent}
    {before after : SliceMachine P store sourceStore ambient expected bound}
    (run : Spec.Iterations (SliceTransition memory hooks floats allocator) n before events after)
    (bounded : Abs.StateReferencesBound referencesBound before.source) :
    Abs.StateReferencesBound referencesBound after.source := by
  induction run with
  | refl => exact bounded
  | cons transition tail ih => exact ih (transition.2.2.2 referencesBound bounded)

end Exec.Interp
