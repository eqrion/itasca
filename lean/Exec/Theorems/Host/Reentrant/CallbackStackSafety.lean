import Exec.Theorems.Host.Reentrant.FiniteReentrantCallbacks
import Exec.Theorems.Composition.World.ChosenWorldResourceBounds
namespace Exec.Theorems
open Aeneas Aeneas.Std

theorem PureCallbacks.Returns.no_overflow {program status values}
    (source : PureCallbacks.Returns program status values) : status≠.Err .StackOverflow := by
  induction source <;> first | assumption | simp

theorem StoreCallbacks.Returns.no_overflow {M : Type} {program : StoreCallbacks.Program}
    {before after : runtime.store.Store M} {status values}
    (source : StoreCallbacks.Returns program before status after values) : status≠.Err .StackOverflow := by
  induction source <;> first | assumption | (apply PureCallbacks.Returns.no_overflow; assumption) | simp

theorem AllocationCallbacks.Returns.no_overflow {M : Type} {program : AllocationCallbacks.Program}
    {before after : runtime.store.Store M} {status values}
    (source : AllocationCallbacks.Returns program before status after values) : status≠.Err .StackOverflow := by
  induction source <;> first | assumption | (apply StoreCallbacks.Returns.no_overflow; assumption) | simp

theorem ReadCallbacks.Returns.no_overflow {M : Type} {program : ReadCallbacks.Program}
    {before after : runtime.store.Store M} {status values}
    (source : ReadCallbacks.Returns program before status after values) : status≠.Err .StackOverflow := by
  induction source <;> first | assumption | (apply AllocationCallbacks.Returns.no_overflow; assumption) | simp

theorem GrowthCallbacks.Returns.no_overflow {M : Type} {program : GrowthCallbacks.Program}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {before after : runtime.store.Store M} {status values}
    (source : GrowthCallbacks.Returns view code program before status after values) : status≠.Err .StackOverflow := by
  induction source <;> first | assumption | (apply ReadCallbacks.Returns.no_overflow; assumption) | simp

theorem CallbackActions.Returns.no_overflow {M : Type} {program : CallbackActions.Program}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {before after : runtime.store.Store M} {status values}
    (source : CallbackActions.Returns view code program before status after values) : status≠.Err .StackOverflow := by
  induction source <;> first | assumption | (apply ReadCallbacks.Returns.no_overflow; assumption) |
    (apply GrowthCallbacks.Returns.no_overflow; assumption) | (apply AllocationCallbacks.Returns.no_overflow; assumption) | simp

theorem ReentrantCallbacks.Returns.no_overflow {M : Type} {program : ReentrantCallbacks.Program}
    {view : M → Slice U8} {before after : runtime.store.Store M} {status values}
    (source : ReentrantCallbacks.Returns view program before status after values) : status≠.Err .StackOverflow := by
  induction source <;> first | assumption | (apply CallbackActions.Returns.no_overflow; assumption) | simp

/-- No host stack-exhaustion law is assumed for these implementations. Nested
Wasm resource errors become host traps, with their committed stores retained. -/
theorem ReentrantCallbacks.platform_no_stack_overflow {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (select : Nat → U64 → Slice runtime.Value → ReentrantCallbacks.Program)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (finite : ∀depth identity args,(select depth identity args).SourceFinite view) (depth : Nat) :
    NoHostStackOverflow (ReentrantCallbacks.platform memory floats allocator select depth) (ExecutableInv view) := by
  intro code store held token identity args defaults nextToken after results actual
  cases depth with
  | zero => simp [ReentrantCallbacks.platform] at actual
  | succ depth =>
    obtain ⟨answer,run,source,rest⟩ := WP.spec_imp_exists
      ((select depth identity args).correct memory (ReentrantCallbacks.platform memory floats allocator select depth) floats allocator
        correct allocation (ReentrantCallbacks.platform_interrupts memory floats allocator select depth) view laws
        (ReentrantCallbacks.platform_package memory floats allocator correct allocation select view laws finite depth)
        (finite depth identity args) code store held)
    have impossible := source.no_overflow
    simp only [ReentrantCallbacks.platform,run,bind_ok,Result.ok.injEq,Prod.mk.injEq] at actual
    exact impossible actual.1
end Exec.Theorems
