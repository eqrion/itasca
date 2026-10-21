import Exec.Store.Invariant.IssuedArguments
import Exec.Theorems.Host.HostWorldSound
import Exec.Theorems.Api.ExecutableInv
import Exec.Interp.Relations.FrameStorePrefix

/-! Stable platform and evolving-host obligations for public invocation.
Each field remains an explicit embedding obligation; raw preservation is not
inferred from source extension or callback soundness. -/
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

/-- Exactly the existing platform and callback premises of public invocation.
Construct with `⟨correct,allocation,interrupts,memory,sound,frames,externs,results⟩`;
the named projections recover every original premise independently. -/
structure WorldInvocationLaws {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) : Prop where
  float_correct : Platform.FloatOpsCorrect floats
  allocation : Platform.AllocCorrect allocator
  interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄
  memory_laws : Platform.MemoryLaws memory view
  host_sound : HostWorldSound hooks view (ExecutableInv view)
  frames : ∀ c store, ExecutableInv view c store → ∀ host p args results answer,
    hooks.call_host p store host args results = .ok answer → FrameStorePrefix store answer.2.2.1
  externs : ∀ c store, ExecutableInv view c store → ∀ host p args results answer,
    hooks.call_host p store host args results = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length
  results : ∀ c store, ExecutableInv view c store → ∀ host p args results answer,
    hooks.call_host p store host args results = .ok answer →
    ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value
end Exec.Theorems
