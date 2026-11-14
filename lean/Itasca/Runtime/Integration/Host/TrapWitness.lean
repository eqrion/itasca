import Itasca.Runtime.Contracts
import Itasca.Runtime.Integration.Invocation.HostOutcomes

/-! Concrete host and allocator witnesses for closed runtime examples.
The callbacks trap without changing the store; every reservation succeeds. -/

namespace Itasca.Runtime.Examples
open Aeneas Aeneas.Std SpecExt Integration

/-- Every callback traps and returns the store unchanged. -/
def trapHost {M : Type} (memory : runtime.platform.MemoryBuffer M) : runtime.platform.Platform Unit M where
  MemoryBufferInst := memory
  interrupt _ := .ok (.Continue,())
  call_host p store _ _ _ := .ok (.Err .Trap,p,store,Slice.new runtime.Value)

/-- Every reservation succeeds and leaves the vector unchanged. -/
def grantAll : runtime.platform.Alloc Unit where
  reserve values _ := .ok (true,values)

theorem grantAll_correct : Platform.AllocCorrect grantAll := by
  intro _ _ _
  rw [grantAll,WP.spec_ok]

theorem grantAll_available (bound : Nat) : Platform.AllocationAvailable grantAll bound :=
  fun _ _ _ _ => rfl

/-- The callbacks of `trapHost` satisfy every host law. -/
theorem trapHost_laws {M : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8) :
    HostLaws (trapHost memory) view (ExecutableInv view) := by
  refine ⟨?_,fun _ store _ _ => ⟨?_,?_,?_⟩⟩
  · intro code store held p host args results
    rw [trapHost,WP.dspec_ok]
    exact ⟨code,(by intro index inst found fn; rfl),held,Spec.extend_store_refl _ held.well_formed,held.source_typed⟩
  all_goals
    intro p args results answer called
    simp only [trapHost,Result.ok.injEq] at called
    subst answer
  · exact .refl store
  · exact Nat.le_refl _
  · intro value member; cases member

/-- The single answer of every callback. -/
theorem trapHost_answer {M : Type} {memory : runtime.platform.MemoryBuffer M} {p : Unit}
    {store : runtime.store.Store M} {host : U64} {args results : Slice runtime.Value} {answer}
    (called : (trapHost memory).call_host p store host args results=.ok answer) :
    answer=(.Err .Trap,p,store,Slice.new runtime.Value) := by
  simp only [trapHost,Result.ok.injEq] at called
  exact called.symm

/-- No callback of `trapHost` diverges, so `terminates` needs only the source premise. -/
theorem trapHost_returns {M : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (initial : config) : ¬ HostCallDiverged (trapHost memory) view initial := by
  rintro ⟨_,_,_,_,_,_,_,_,_,_,diverged⟩
  simp [trapHost] at diverged

end Itasca.Runtime.Examples
