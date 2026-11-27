import Itasca.Runtime.Integration.Execution.Certificates
import Itasca.Runtime.Integration.Api.CreationAndGrowth
import Itasca.Runtime.Integration.Invocation.Outcomes

/-! Concrete host and allocator witnesses for closed runtime examples.
The callbacks trap without changing the store; every reservation succeeds. -/

namespace Itasca.Examples.Runtime
open Aeneas Aeneas.Std WebAssembly Integration

/-- Every callback traps and returns the store unchanged. -/
def trapHost {M : Type} (memory : runtime.platform.MemoryBuffer M) : runtime.platform.Platform Unit M where
  MemoryBufferInst := memory
  interrupt _ := .ok (.Continue,())
  call_host p store _ _ _ := .ok (.Err .Trap,p,store,Slice.new runtime.Value)

/-- Every reservation succeeds and leaves the vector unchanged. -/
def grantAll : runtime.platform.Alloc Unit where
  reserve values _ := .ok (true,values)

theorem grant_all_correct : Platform.AllocCorrect grantAll := by
  intro _ _ _
  rw [grantAll,WP.spec_ok]

theorem grant_all_available (bound : Nat) : Platform.AllocationAvailable grantAll bound :=
  fun _ _ _ _ => rfl

/-- The callbacks of `trapHost` satisfy every host law. -/
theorem trap_host_laws {M : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (wellFormed : ∀ code store, Inv code store → wf_store (Representation.decodeStore view code store))
    (typed : ∀ code store, Inv code store → Store_ok (Representation.decodeStore view code store)) :
    HostLaws (trapHost memory) view Inv := by
  refine HostLaws.of_parts ?_ (fun _ store _ _ => ⟨?_,?_,?_⟩)
  · intro code store held p host args results
    rw [trapHost,WP.dspec_ok]
    exact ⟨code,(by intro index inst found fn; rfl),held,Spec.extend_store_refl _ (wellFormed code store held),typed code store held⟩
  all_goals
    intro p args results result nextPlatform after returned called
    simp only [trapHost,Result.ok.injEq,Prod.mk.injEq] at called
    rcases called with ⟨rfl, _, rfl, rfl⟩
  · exact .refl store
  · exact Nat.le_refl _
  · intro value member; cases member

/-- The single answer of every callback. -/
theorem trap_host_answer {M : Type} {memory : runtime.platform.MemoryBuffer M} {p : Unit}
    {store : runtime.store.Store M} {host : U64} {args results : Slice runtime.Value} {answer}
    (called : (trapHost memory).call_host p store host args results=.ok answer) :
    answer=(.Err .Trap,p,store,Slice.new runtime.Value) := by
  simp only [trapHost,Result.ok.injEq] at called
  exact called.symm

/-- No callback of `trapHost` diverges, so `terminates` needs only the source premise. -/
theorem trap_host_returns {M : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (initial : config) : ¬ HostCallDiverged (trapHost memory) view initial := by
  rintro ⟨_,_,_,_,_,_,_,_,_,_,diverged⟩
  simp [trapHost] at diverged

end Itasca.Examples.Runtime
