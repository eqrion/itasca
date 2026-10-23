import Exec.Theorems.Host.Open.Driver.ReentrantControl
import Exec.Theorems.Host.Reentrant.ReentrantInvocation
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- The combined driver recovers the existing finite checked-action callback
implementation exactly. Its two host-control ticks introduce only history,
which the synchronous Platform method erases. -/
theorem returning_actions_erases {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view)
    (select : U64 → Slice runtime.Value → CallbackActions.Program)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (token : Unit) (identity : U64) (args defaults : Slice runtime.Value) :
    (platform memory floats allocator (fun identity args=>[.returnAction (select identity args)])).call_host token store identity args defaults=
      (CallbackActions.platform memory allocator select).call_host token store identity args defaults := by
  cases token
  obtain ⟨answer,actual,effect,issued⟩:=WP.spec_imp_exists
    ((select identity args).correct memory allocator allocation view laws code store held)
  rcases answer with ⟨status,after,values⟩
  unfold platform run CallbackActions.platform
  dsimp only
  rw [loop.eq_def]
  simp only [tick,initialHost,List.getElem?_cons_zero,actual,bind_ok]
  rw [loop.eq_def]
  simp only [tick,bind_ok]

/-- Returning checked-action callbacks recover the full stage-4 world package
from their implementations: ordinary return, retained code/metadata, source
store typing, extern retention and issued results. -/
theorem returning_actions_package {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view)
    (select : U64 → Slice runtime.Value → CallbackActions.Program) :
    ReentrantCallbacks.Package
      (platform memory floats allocator (fun identity args=>[.returnAction (select identity args)])) view := by
  intro code store held token identity args defaults
  rw [returning_actions_erases memory floats allocator allocation view laws select code store held token identity args defaults]
  exact ReentrantCallbacks.actions_package memory allocator allocation select view laws code store held token identity args defaults
end Exec.Theorems.OpenReentrantControl
