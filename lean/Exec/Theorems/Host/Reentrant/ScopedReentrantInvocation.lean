import Exec.Theorems.Host.Reentrant.ReentrantInvocation

/-! Retained source-function worlds for finite reentrancy. Stability is a pure
closure law under code agreement, raw metadata prefixes and source extension;
it does not assume callback execution correctness. -/
namespace Exec.Theorems.ReentrantCallbacks
open Aeneas Aeneas.Std SpecExt Exec.Interp
abbrev WorldScope (M : Type) := Store.CodeInterpretation → runtime.store.Store M → Prop

def ScopeStable {M : Type} (view : M → Slice U8) (scope : WorldScope M) : Prop :=
  ∀code before afterCode after,FrameStorePrefix before after → Store.CodeAgreesOn before code afterCode →
    Extend_store (Store.decodeStore view code before) (Store.decodeStore view afterCode after) →
    scope code before → scope afterCode after

def ScopedPackage {M : Type} (hooks : runtime.platform.Platform Unit M) (view : M → Slice U8)
    (scope : WorldScope M) : Prop :=
  ∀code store,ExecutableInv view code store → scope code store → ∀token identity args defaults,
    hooks.call_host token store identity args defaults ⦃ answer => ∃afterCode,
      ReturnedWorldEffect view (ExecutableInv view) code store afterCode answer.2.2.1 ∧
      scope afterCode answer.2.2.1 ∧ store.externs.length≤answer.2.2.1.externs.length ∧
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value ⦄

def ScopedFloorInv {M : Type} (view : M → Slice U8) (scope : WorldScope M) (floor : Nat)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) : Prop :=
  ExecutableInv view code store ∧ scope code store ∧ floor≤store.externs.length

theorem ScopedFloorInv.update {M : Type} {view : M → Slice U8} {scope : WorldScope M} {floor : Nat}
    (stable : ScopeStable view scope) {code : Store.CodeInterpretation} {before after : runtime.store.Store M}
    (held : ScopedFloorInv view scope floor code before) (mutation : CumulativeStoreMutation view code before after) :
    ScopedFloorInv view scope floor code after :=
  ⟨held.1.update mutation,stable code before code after mutation.metadata.prefix
    (by intro index inst found fn; rfl) mutation.extension held.2.1,
    by simpa only [mutation.externs] using held.2.2⟩

theorem invoke_scoped_terminates {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform Unit M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _=>True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (scope : WorldScope M) (stable : ScopeStable view scope)
    (package : ScopedPackage hooks view scope) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (held : ExecutableInv view code store) (heldScope : scope code store) (token : Unit)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (finite : ¬Spec.InfiniteSourceWithEvents initial) :
    runtime.interp.invoke_with memory hooks floats allocator exec store token address args results
      ⦃ answer => ∃afterCode,
        ReturnedWorldEffect view (ExecutableInv view) code store afterCode answer.2.2.1 ∧
        scope afterCode answer.2.2.1 ∧ store.externs.length≤answer.2.2.1.externs.length ∧
        ExecutableWorldInvocationOutcome view code store exec token results initial answer ⦄ := by
  let Inv := ScopedFloorInv view scope store.externs.length
  have sound : HostWorldSound hooks view Inv := by
    intro current before valid platform identity arguments defaults
    apply WP.spec_mono (package current before valid.1 valid.2.1 platform identity arguments defaults)
    rintro answer ⟨afterCode,effect,scopedAfter,externs,issuedResults⟩
    exact ⟨afterCode,effect.agrees,⟨effect.invariant,scopedAfter,Nat.le_trans valid.2.2 externs⟩,effect.extension,effect.invariant.source_typed⟩
  have raw : ∀current before,Inv current before → ∀identity platform arguments defaults answer,
      hooks.call_host platform before identity arguments defaults=.ok answer →
      FrameStorePrefix before answer.2.2.1 ∧ before.externs.length≤answer.2.2.1.externs.length ∧
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value := by
    intro current before valid identity platform arguments defaults answer actual
    have post := package current before valid.1 valid.2.1 platform identity arguments defaults
    rw [actual,WP.spec_ok] at post
    obtain ⟨afterCode,effect,scopedAfter,externs,issuedResults⟩ := post
    exact ⟨effect.metadata,externs,issuedResults⟩
  apply WP.spec_mono (invoke_world_invariant_terminates memory hooks floats allocator correct allocation interrupts
    view laws code Inv (fun _ _ valid=>valid.1) (fun _ _ _ valid mutation=>valid.update stable mutation) sound
    (fun current before valid identity platform arguments defaults answer actual=>(raw current before valid identity platform arguments defaults answer actual).1)
    (fun current before valid identity platform arguments defaults answer actual=>(raw current before valid identity platform arguments defaults answer actual).2.1)
    (fun current before valid identity platform arguments defaults answer actual=>(raw current before valid identity platform arguments defaults answer actual).2.2)
    exec store token ⟨held,heldScope,Nat.le_refl _⟩ address args results issued argumentIssued initial invoked finite)
  rintro answer ⟨afterCode,agrees,fresh,metadata,extension,rest⟩
  exact ⟨afterCode,⟨agrees,fresh.1,metadata,extension⟩,fresh.2.1,fresh.2.2,afterCode,agrees,fresh.1,metadata,extension,rest⟩
end Exec.Theorems.ReentrantCallbacks
