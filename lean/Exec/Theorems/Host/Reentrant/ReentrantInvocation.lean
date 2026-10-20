import Exec.Theorems.Invocation.PublicExecutableWorldInvocation
import Exec.Theorems.Invocation.InvocationWorldInvariant
import Exec.Theorems.Host.Callbacks.CallbackActions
import Exec.Theorems.Host.HostReturnedActions

/-! A noncircular nested-call adapter: its child callback package must already
be proved (for example at a smaller depth). Source termination is a separate
premise; a bound on reentrancy depth does not terminate a Wasm loop. -/
namespace Exec.Theorems.ReentrantCallbacks
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Complete primitive callback package, including raw reference retention.
Concrete program interpreters below establish this property from their code. -/
def Package {M : Type} (hooks : runtime.platform.Platform Unit M) (view : M → Slice U8) : Prop :=
  ∀code store,ExecutableInv view code store → ∀token identity args defaults,
    hooks.call_host token store identity args defaults ⦃ answer => ∃afterCode,
      ReturnedWorldEffect view (ExecutableInv view) code store afterCode answer.2.2.1 ∧
      store.externs.length≤answer.2.2.1.externs.length ∧
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value ⦄

/-- An independent raw extern-count floor, retained by every nonhost dispatch.
It is bookkeeping about issued references, not an execution-correctness field. -/
def FloorInv {M : Type} (view : M → Slice U8) (floor : Nat)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) : Prop :=
  ExecutableInv view code store ∧ floor≤store.externs.length

theorem FloorInv.update {M : Type} {view : M → Slice U8} {floor : Nat}
    {code : Store.CodeInterpretation} {before after : runtime.store.Store M}
    (held : FloorInv view floor code before) (mutation : CumulativeStoreMutation view code before after) :
    FloorInv view floor code after :=
  ⟨held.1.update mutation,by simpa only [mutation.externs] using held.2⟩

/-- Existing checked programs supply the child package without assuming a
callback law. Their selectors have no access to raw store metadata. -/
theorem actions_package {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (select : U64 → Slice runtime.Value → CallbackActions.Program) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view) :
    Package (CallbackActions.platform memory allocator select) view := by
  intro code store held token identity args defaults
  apply WP.spec_mono (CallbackActions.callback_package memory allocator allocation select view laws code store held token identity args defaults)
  rintro answer ⟨effect,issued⟩
  refine ⟨code,⟨(by intro index inst found fn; rfl),effect.invariant,effect.metadata,effect.extension⟩,?_,issued⟩
  rw [effect.externs]

/-- A child invocation uses a previously proved callback package. The public
composition theorem propagates the raw floor as well as the full invariant.
An independent source no-divergence proof establishes ordinary return. -/
theorem invoke_terminates {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform Unit M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _=>True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (package : Package hooks view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (held : ExecutableInv view code store) (token : Unit)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (finite : ¬Spec.InfiniteSourceWithEvents initial) :
    runtime.interp.invoke_with memory hooks floats allocator exec store token address args results
      ⦃ answer => ∃afterCode,
        ReturnedWorldEffect view (ExecutableInv view) code store afterCode answer.2.2.1 ∧
        store.externs.length≤answer.2.2.1.externs.length ∧
        ExecutableWorldInvocationOutcome view code store exec token results initial answer ⦄ := by
  let Inv := FloorInv view store.externs.length
  have sound : HostWorldSound hooks view Inv := by
    intro current before valid platform identity arguments defaults
    apply WP.spec_mono (package current before valid.1 platform identity arguments defaults)
    rintro answer ⟨afterCode,effect,externs,issuedResults⟩
    exact ⟨afterCode,effect.agrees,⟨effect.invariant,Nat.le_trans valid.2 externs⟩,effect.extension,effect.invariant.source_typed⟩
  have raw : ∀current before,Inv current before → ∀identity platform arguments defaults answer,
      hooks.call_host platform before identity arguments defaults=.ok answer →
      FrameStorePrefix before answer.2.2.1 ∧ before.externs.length≤answer.2.2.1.externs.length ∧
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value := by
    intro current before valid identity platform arguments defaults answer actual
    have post := package current before valid.1 platform identity arguments defaults
    rw [actual,WP.spec_ok] at post
    obtain ⟨afterCode,effect,externs,issuedResults⟩ := post
    exact ⟨effect.metadata,externs,issuedResults⟩
  apply WP.spec_mono (invoke_world_invariant_terminates memory hooks floats allocator correct allocation interrupts
    view laws code Inv (fun _ _ valid=>valid.1) (fun _ _ _ valid mutation=>valid.update mutation) sound
    (fun current before valid identity platform arguments defaults answer actual=>(raw current before valid identity platform arguments defaults answer actual).1)
    (fun current before valid identity platform arguments defaults answer actual=>(raw current before valid identity platform arguments defaults answer actual).2.1)
    (fun current before valid identity platform arguments defaults answer actual=>(raw current before valid identity platform arguments defaults answer actual).2.2)
    exec store token ⟨held,Nat.le_refl _⟩ address args results issued argumentIssued initial invoked finite)
  rintro answer ⟨afterCode,agrees,fresh,metadata,extension,rest⟩
  exact ⟨afterCode,⟨agrees,fresh.1,metadata,extension⟩,fresh.2,afterCode,agrees,fresh.1,metadata,extension,rest⟩
end Exec.Theorems.ReentrantCallbacks
