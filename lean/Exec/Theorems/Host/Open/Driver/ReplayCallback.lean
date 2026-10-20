import Exec.Theorems.Host.Reentrant.ReentrantInvocation
import Exec.Theorems.Composition.Eventful.EventfulWorldTotal
import Exec.Interp.Host.OpenStepIndependent

/-! A logical returning dictionary used to prove a suspended native
continuation's safety. The executable combined driver never uses this
dictionary. Its laws follow from one checked returned effect, and its entry
world is pinned by retained raw metadata and old-key code agreement. -/
noncomputable section
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp

structure ReplayInv {M : Type} (view : M → Slice U8) (original : Store.CodeInterpretation)
    (before : runtime.store.Store M) (code : Store.CodeInterpretation) (store : runtime.store.Store M) : Prop where
  executable : ExecutableInv view code store
  metadata : FrameStorePrefix before store
  agrees : Store.CodeAgreesOn before original code
  externs : before.externs.length≤store.externs.length

theorem ReplayInv.initial {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} (held : ExecutableInv view code store) : ReplayInv view code store code store :=
  ⟨held,.refl _,(by intro index inst found fn; rfl),Nat.le_refl _⟩

theorem ReplayInv.update {M : Type} {view : M → Slice U8} {original code : Store.CodeInterpretation}
    {initial before after : runtime.store.Store M} (held : ReplayInv view original initial code before)
    (mutation : CumulativeStoreMutation view code before after) : ReplayInv view original initial code after :=
  ⟨held.executable.update mutation,held.metadata.trans mutation.metadata.prefix,held.agrees,by simpa only [mutation.externs] using held.externs⟩

def replay {M : Type} (memory : runtime.platform.MemoryBuffer M) (before after : runtime.store.Store M)
    (status : core.result.Result Unit runtime.platform.HostError) (values : Slice runtime.Value) :
    runtime.platform.Platform Unit M := by
  classical
  exact {
    MemoryBufferInst:=memory
    interrupt token:=.ok (.Continue,token)
    call_host token store _ _ _:=if store=before then .ok (status,token,after,values)
      else .ok (.Err .Trap,token,store,Slice.new _) }

theorem replay_sound {M : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (before after : runtime.store.Store M) (oldCode afterCode : Store.CodeInterpretation)
    (status : core.result.Result Unit runtime.platform.HostError) (values : Slice runtime.Value)
    (effect : ReturnedWorldEffect view (ExecutableInv view) oldCode before afterCode after)
    (externs : before.externs.length≤after.externs.length) :
    HostWorldSound (replay memory before after status values) view (ReplayInv view oldCode before) := by
  classical
  intro code store held token identity args defaults
  by_cases same : store=before
  · subst store
    have agrees : Store.CodeAgreesOn before code afterCode := by
      intro index inst found fn
      exact (effect.agrees index inst found fn).trans (held.agrees index inst found fn).symm
    have extension : Extend_store (Store.decodeStore view code before) (Store.decodeStore view afterCode after) := by
      rw [Store.decodeStore_code_agrees view held.agrees]
      exact effect.extension
    simpa only [replay,if_pos rfl,ite_true] using WP.spec.ret
      ⟨afterCode,agrees,⟨effect.invariant,effect.metadata,effect.agrees,externs⟩,extension,effect.invariant.source_typed⟩
  · simpa only [replay,if_neg same] using WP.spec.ret
      ⟨code,(by intro index inst found fn; rfl),held,Spec.extend_store_refl _ held.executable.well_formed,held.executable.source_typed⟩

theorem replay_retained {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (before after : runtime.store.Store M)
    (status : core.result.Result Unit runtime.platform.HostError) (values : Slice runtime.Value)
    (metadata : FrameStorePrefix before after) (externs : before.externs.length≤after.externs.length)
    (issued : ∀value∈values.val,Store.IssuedValue after value)
    (store : runtime.store.Store M) (token : Unit) (identity : U64) (args defaults : Slice runtime.Value) :
    (replay memory before after status values).call_host token store identity args defaults ⦃ answer=>
      FrameStorePrefix store answer.2.2.1 ∧ store.externs.length≤answer.2.2.1.externs.length ∧
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value ⦄ := by
  classical
  by_cases same : store=before
  · subst store
    simpa only [replay,if_pos rfl,ite_true] using WP.spec.ret ⟨metadata,externs,issued⟩
  · simpa only [replay,if_neg same] using WP.spec.ret ⟨FrameStorePrefix.refl store,Nat.le_refl _,by simp⟩
end Exec.Theorems.OpenReentrantControl
