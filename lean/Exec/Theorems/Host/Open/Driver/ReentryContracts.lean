import Exec.Theorems.Host.Open.Driver.FiniteReentry
import Exec.Theorems.Host.Open.Driver.PlatformEffects
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- A concrete returning callback contract is derived from the nested driver
trace. The full world effect is reflexive because this wrapper and its inner
trapping host commit no writes; no callback-normality assumption is supplied. -/
theorem finite_reentry_contract {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (w : EmptyReentry store) (select : Selector) (outer : U64)
    (arguments defaults : Slice runtime.Value) (next : Nat)
    (outerInstruction : (select outer arguments)[0]?=some (.invoke w.wasmIndex (Slice.new _) next))
    (innerInstruction : (select w.identity (Slice.new _))[0]?=some .trapped) :
    (platform memory floats allocator select).call_host () store outer arguments defaults=
        .ok (.Err .Trap,(),store,Slice.new _) ∧
      ReentrantCallbacks.Effect view code store code store ∧ Store_ok (Store.decodeStore view code store) := by
  obtain ⟨history,actual,trace⟩ := finite_reentry_trap memory floats allocator allocation available store w select outer arguments next
    outerInstruction innerInstruction
  exact ⟨by simp [platform,actual],.refl held,held.source_typed⟩

/-- The explicit mutual-reentry stream retains source store typing at every
observable prefix, including all pending nested entries. -/
theorem mutual_reentry_typed {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) (w : EmptyReentry store)
    (tail : List Continuation) (history : List Observation) (n : Nat) :
    Store_ok (Store.decodeStore view code (w.states tail history n).store) := by
  rw [mutual_reentry_store]
  exact held.source_typed

/-- The actual synchronous callback also diverges for mutual reentrancy, while
the productive stream separately records its unbounded suspended stack. -/
theorem mutual_reentry_platform_diverges {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (store : runtime.store.Store M) (w : EmptyReentry store) (defaults : Slice runtime.Value) :
    (platform memory floats allocator (fun _ _=>w.host.code)).call_host () store w.identity (Slice.new _) defaults=.div := by
  have actual := mutual_reentry_diverges memory floats allocator allocation available store w []
    [.hostEnter none w.identity (Slice.new _)]
  change run memory floats allocator (fun _ _=>w.host.code)
    (initialHost (fun _ _=>w.host.code) store w.identity (Slice.new _))=.div at actual
  simp [platform,actual]
end Exec.Theorems.OpenReentrantControl
