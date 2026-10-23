import Exec.Interp.Machines.Slice.SliceDivergence

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- A diverging actual loop supplies a coherent infinite source execution.
Every link has a positive number of checked specification reductions, so the
witness cannot consist of an infinite sequence of administrative stutters. -/
theorem slice_infinite_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    (decoded : sourceStore = Store.decodeStore view code store) (compiled : CompiledFunctions code store)
    (initial : SliceMachine P store sourceStore ambient expected bound)
    (divergent : runtime.interp.invoke_with_loop1 memory hooks floats allocator
      initial.exec store initial.platform (.Ok ()) = .div) :
    ∃ states : Nat → config, states 0 = Abs.decode initial.source ∧ ∀ n,
      ∃ count, 0 < count ∧ Spec.StepsHN count (states n) [] (states (n + 1)) := by
  classical
  let Running := { machine : SliceMachine P store sourceStore ambient expected bound //
    runtime.interp.invoke_with_loop1 memory hooks floats allocator
      machine.exec store machine.platform (.Ok ()) = .div }
  have successor (current : Running) : ∃ next : Running, ∃ count, 0 < count ∧
      Spec.StepsHN count (Abs.decode current.val.source) [] (Abs.decode next.val.source) := by
    obtain ⟨next, history, stillDivergent⟩ := slice_divergent_history memory hooks floats allocator
      allocation interrupts view code decoded compiled (slicePotentialBound bound + 1) current.val current.property
    obtain ⟨count, reductions, cost⟩ := SliceMachine.history_progress memory hooks floats allocator history
    have positive : 0 < count := by simp only [Nat.div_self (by omega : 0 < slicePotentialBound bound + 1)] at cost; omega
    exact ⟨⟨next, stillDivergent⟩, count, positive, reductions⟩
  let advance (current : Running) : Running := Classical.choose (successor current)
  let states : Nat → Running := fun n => Nat.rec ⟨initial, divergent⟩ (fun _ previous => advance previous) n
  refine ⟨fun n => Abs.decode (states n).val.source, rfl, ?_⟩
  intro n
  exact Classical.choose_spec (successor (states n))

end Exec.Interp
