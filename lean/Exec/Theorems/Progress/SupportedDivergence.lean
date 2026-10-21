import Exec.Theorems.Progress.SilentHistory
import Exec.Theorems.Composition.Supported.SupportedLoop
import Exec.Theorems.Composition.Supported.SupportedQuantitative
import Exec.Interp.Machines.Slice.SliceDivergence

/-! Supported divergence reflection. Local step evidence feeds the shared silent-history
induction, then quantitative simulation supplies positive source progress. -/
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

theorem supported_divergent_next
    [∀ compiled, StructuredMachine.FloatHeads (emission compiled)]
    [∀ compiled, StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀ compiled, StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.SimdProjection (emission compiled) compiled.simd.val compiled.v128_pool.val]
    [∀ compiled, StructuredMachine.TypedSelectHeads (emission compiled)]
    [∀ compiled, StructuredMachine.SupportedHeads (emission compiled)]
    [∀ compiled, StructuredMachine.ErasedHeads (emission compiled)]
    (language : Abs.Supported.Language allowed) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    {expected : List valtype} (machine : SupportedMachine emission allowed M P view code expected)
    (divergent : loop (executionBody memory hooks floats allocator) (machine.exec,machine.store,machine.platform,.Ok ()) = .div) :
    ∃ next, SupportedTransition memory hooks floats allocator machine [] next ∧
      loop (executionBody memory hooks floats allocator) (next.exec,next.store,next.platform,.Ok ()) = .div := by
  have active := execution_loop_divergent_active memory hooks floats allocator machine.exec machine.store machine.platform divergent
  obtain ⟨⟨status,nextExec,nextStore,nextPlatform⟩,returned,fresh,extension,bounds,hostFree,mutation,outcome⟩ :=
    WP.spec_imp_exists (step_supported_host_free language memory hooks floats allocator correct allocation interrupts view laws code machine.exec machine.store machine.platform
      machine.source expected machine.pc machine.pending machine.certified machine.hostFree machine.owned machine.invariant active)
  rw [loop.eq_def,executionBody_active memory hooks floats allocator _ ⟨active,rfl⟩,returned] at divergent
  simp [bind_ok] at divergent
  cases status with
  | Err error => rw [execution_loop_error memory hooks floats allocator] at divergent; simp at divergent
  | Ok value =>
    cases value
    obtain ⟨pc,pending,source,invariant,simulation,ownership,ambient,bounded⟩ := outcome
    have owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds nextStore) source := by
      rw [bounds]
      exact ownership _ machine.owned
    let next : SupportedMachine emission allowed M P view code expected :=
      ⟨nextStore,nextExec,nextPlatform,source,pc,pending,invariant,fresh,owned,hostFree⟩
    exact ⟨next,⟨rfl,returned,simulation,extension,mutation.metadata,ambient,bounded,mutation.segmentCounts,mutation.limits⟩,divergent⟩

theorem supported_divergent_history
    [∀ compiled, StructuredMachine.FloatHeads (emission compiled)]
    [∀ compiled, StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀ compiled, StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.SimdProjection (emission compiled) compiled.simd.val compiled.v128_pool.val]
    [∀ compiled, StructuredMachine.TypedSelectHeads (emission compiled)]
    [∀ compiled, StructuredMachine.SupportedHeads (emission compiled)]
    [∀ compiled, StructuredMachine.ErasedHeads (emission compiled)]
    (language : Abs.Supported.Language allowed) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    {expected : List valtype} (dispatches : Nat) (initial : SupportedMachine emission allowed M P view code expected)
    (divergent : runtime.interp.invoke_with_loop2 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ()) = .div) :
    ∃ final, Spec.Iterations (SupportedTransition memory hooks floats allocator) dispatches initial [] final ∧
      runtime.interp.invoke_with_loop2 memory hooks floats allocator final.exec final.store final.platform (.Ok ()) = .div := by
  exact silent_history (supported_divergent_next language memory hooks floats allocator correct allocation interrupts view laws code) dispatches initial divergent

theorem supported_no_silent_divergence
    [∀ compiled, StructuredMachine.FloatHeads (emission compiled)]
    [∀ compiled, StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀ compiled, StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.SimdProjection (emission compiled) compiled.simd.val compiled.v128_pool.val]
    [∀ compiled, StructuredMachine.TypedSelectHeads (emission compiled)]
    [∀ compiled, StructuredMachine.SupportedHeads (emission compiled)]
    [∀ compiled, StructuredMachine.ErasedHeads (emission compiled)]
    (language : Abs.Supported.Language allowed) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    {expected : List valtype} (initial : SupportedMachine emission allowed M P view code expected)
    (divergent : runtime.interp.invoke_with_loop2 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ()) = .div)
    (requested : Nat) :
    ∃ final count,
      Spec.Iterations (SupportedTransition memory hooks floats allocator)
        (requested*(corePotentialBound (sizeOf initial.source)+1)) initial [] final ∧
      Spec.StepsHN count (Abs.decode initial.source) [] (Abs.decode final.source) ∧ requested ≤ count := by
  obtain ⟨final,history,_⟩ := supported_divergent_history language memory hooks floats allocator correct allocation interrupts view laws code
    (requested*(corePotentialBound (sizeOf initial.source)+1)) initial divergent
  obtain ⟨count,reductions,cost⟩ := SupportedMachine.history_progress memory hooks floats allocator history (Abs.codeBound_initial initial.source)
  exact ⟨final,count,history,reductions,by simpa using cost⟩

/-- Actual divergence yields a coherent infinite chain of positive source
reductions, even when the concrete execution mutates globals or memories. -/
theorem supported_infinite_source
    [∀ compiled, StructuredMachine.FloatHeads (emission compiled)]
    [∀ compiled, StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀ compiled, StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.SimdProjection (emission compiled) compiled.simd.val compiled.v128_pool.val]
    [∀ compiled, StructuredMachine.TypedSelectHeads (emission compiled)]
    [∀ compiled, StructuredMachine.SupportedHeads (emission compiled)]
    [∀ compiled, StructuredMachine.ErasedHeads (emission compiled)]
    (language : Abs.Supported.Language allowed) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    {expected : List valtype} (initial : SupportedMachine emission allowed M P view code expected)
    (divergent : runtime.interp.invoke_with_loop2 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ()) = .div) :
    ∃ states : Nat → config, states 0 = Abs.decode initial.source ∧ ∀ n,
      ∃ count, 0 < count ∧ Spec.StepsHN count (states n) [] (states (n+1)) := by
  classical
  let Running := {machine : SupportedMachine emission allowed M P view code expected //
    runtime.interp.invoke_with_loop2 memory hooks floats allocator machine.exec machine.store machine.platform (.Ok ()) = .div}
  have successor (current : Running) : ∃ next : Running, ∃ count, 0 < count ∧
      Spec.StepsHN count (Abs.decode current.val.source) [] (Abs.decode next.val.source) := by
    obtain ⟨next,history,stillDivergent⟩ := supported_divergent_history language memory hooks floats allocator correct allocation interrupts view laws code
      (corePotentialBound (sizeOf current.val.source)+1) current.val current.property
    obtain ⟨count,reductions,cost⟩ := SupportedMachine.history_progress memory hooks floats allocator history (Abs.codeBound_initial current.val.source)
    have positive : 0 < count := by
      simp only [Nat.div_self (by omega : 0 < corePotentialBound (sizeOf current.val.source)+1)] at cost
      omega
    exact ⟨⟨next,stillDivergent⟩,count,positive,reductions⟩
  let advance (current : Running) : Running := Classical.choose (successor current)
  let states : Nat → Running := fun n => Nat.rec ⟨initial,divergent⟩ (fun _ previous => advance previous) n
  refine ⟨fun n => Abs.decode (states n).val.source,rfl,?_⟩
  intro n
  exact Classical.choose_spec (successor (states n))
end Exec.Theorems
