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

end Exec.Theorems
