import Exec.Theorems.Api.ExecutableInv
namespace Exec.Theorems
open Aeneas Aeneas.Std

/-- The public invariant with independent configured resource floors. Callback
preservation of these floors is an explicit primitive embedding condition. -/
structure ExecutableResourceInv {M : Type} (view : M → Slice U8) (valueLimit frameLimit : Nat)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) : Prop
    extends ExecutableInv view code store where
  values : valueLimit≤store.limits.max_values.val
  frames : frameLimit≤store.limits.max_frames.val

theorem ExecutableResourceInv.update {M : Type} {view : M → Slice U8} {valueLimit frameLimit : Nat}
    {code : Store.CodeInterpretation} {before after : runtime.store.Store M}
    (valid : ExecutableResourceInv view valueLimit frameLimit code before)
    (mutation : CumulativeStoreMutation view code before after) :
    ExecutableResourceInv view valueLimit frameLimit code after := by
  refine ⟨valid.toExecutableInv.update mutation,?_,?_⟩
  · simpa only [mutation.limits] using valid.values
  · simpa only [mutation.limits] using valid.frames
end Exec.Theorems
