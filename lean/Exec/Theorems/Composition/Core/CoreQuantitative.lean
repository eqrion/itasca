import Exec.Theorems.Composition.Core.CoreHistory
import Exec.Spec.CountedInvariant
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

def corePotentialBound (bound : Nat) : Nat := (bound+1)*(2*(U32.max+1))

def CoreMachine.potential {M P view code expected} (machine : CoreMachine M P view code expected) : Nat :=
  dispatchMeasure machine.pending U32.max machine.pc machine.source

theorem CoreMachine.potential_le {M P view code expected bound}
    (machine : CoreMachine M P view code expected) (bounded : Abs.CodeBound bound machine.source) :
    machine.potential ≤ corePotentialBound bound := by
  have estimate := Nat.mul_le_mul_right (2*(U32.max+1)) bounded.measure
  unfold CoreMachine.potential corePotentialBound
  rw [Nat.add_mul,Nat.one_mul]
  cases phase : machine.pending <;> simp only [dispatchMeasure,phase,ite_true,Bool.false_eq_true,ite_false] <;> omega

theorem CoreTransition.bound {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {before after : CoreMachine M P view code expected} {events : List SpecExt.HostEvent}
    (edge : CoreTransition memory hooks floats allocator before events after)
    {bound : Nat} (bounded : Abs.CodeBound bound before.source) : Abs.CodeBound bound after.source := by
  obtain ⟨_,_,_,_,_,_,preserved,_⟩ := edge
  exact preserved bound bounded

theorem CoreMachine.history_bound {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {before after : CoreMachine M P view code expected} {events : List SpecExt.HostEvent} {n bound : Nat}
    (run : Spec.Iterations (CoreTransition memory hooks floats allocator) n before events after)
    (bounded : Abs.CodeBound bound before.source) : Abs.CodeBound bound after.source :=
  run.invariant (fun machine => Abs.CodeBound bound machine.source) (fun _ _ _ bound edge => edge.bound bound) bounded

/-- The same finite source bound covers recursion, backward branches and mutable
object writes. Each bounded block of concrete dispatches pays for a source step. -/
theorem CoreMachine.history_progress {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {before after : CoreMachine M P view code expected} {n bound : Nat}
    (run : Spec.Iterations (CoreTransition memory hooks floats allocator) n before [] after)
    (bounded : Abs.CodeBound bound before.source) :
    ∃ count, Spec.StepsHN count (Abs.decode before.source) [] (Abs.decode after.source) ∧
      n / (corePotentialBound bound+1) ≤ count := by
  apply Spec.iterations_progress_invariant (fun machine => Abs.CodeBound bound machine.source)
    (fun _ _ _ bound edge => edge.bound bound) (fun machine => Abs.decode machine.source)
    CoreMachine.potential (corePotentialBound bound)
    (fun machine _ => machine.invariant.typed.typed.decode_wf)
    (fun machine bounded => machine.potential_le bounded) ?_ run bounded
  intro first events last bounded edge
  obtain ⟨eventEq,actual,simulation,rest⟩ := edge
  rcases simulation with ⟨same,decrease⟩ | reductions
  · exact Or.inl ⟨same,eventEq,decrease⟩
  · exact Or.inr (by simpa only [eventEq] using reductions)
end Exec.Theorems
