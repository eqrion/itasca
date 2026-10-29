import Itasca.Main

/-!
# A platform satisfying every host and allocator contract

Callbacks trap without touching the store, interrupts always continue and the allocator grants
every request. Together they discharge every host, interrupt and allocator premise of
`runtime.interp.invoke_with.no_spurious_errors` and the callback premise of `terminates`; floats,
memory and the source program remain parameters.
-/

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

theorem trapHost_no_spurious_errors {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (correct : Platform.FloatOpsCorrect floats)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store=store.id) (issued : Store.ExternalIssued store (.Func address))
    (owned : ∀value∈args.val,Store.ValueInStore store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map Interp.sourceValue) initial)
    (typedArguments : InvocationArgumentsTyped (Store.decodeStore view code store) address.index.val
      (args.val.map Interp.sourceValue))
    (fits : SourceResourcesFit (Store.decodeStore view code store) address.index.val initial
      store.limits.max_values.val store.limits.max_frames.val) :
    runtime.interp.invoke_with memory (trapHost memory) floats grantAll exec store () address args results
      ⦃ out => ∀error,out.1=.Err error → ∃trap,error=.Trap trap ⦄div :=
  runtime.interp.invoke_with.no_spurious_errors memory (trapHost memory) floats grantAll view
    ⟨correct,grantAll_correct,fun _ => by rw [trapHost,WP.spec_ok]; trivial,laws⟩ code (trapHost_laws memory view)
    (fun _ _ _ _ _ _ _ _ called => by rw [trapHost_answer called])
    exec store () valid address args results owner issued owned initial invoked typedArguments fits
    (grantAll_available _) (fun _ _ refused => by simp [trapHost] at refused)
    (fun _ _ _ _ _ _ _ _ _ _ refused => by have same := trapHost_answer refused; simp at same)

end Itasca.Runtime.Examples
