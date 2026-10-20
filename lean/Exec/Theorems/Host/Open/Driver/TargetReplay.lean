import Exec.Theorems.Host.Open.Driver.ReplayCallback
import Exec.Theorems.Api.ExecutableInvCode
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp

/-- The logical replay also fixes meanings at keys published during the host
interaction. Native resumption cannot silently reinterpret those fresh keys. -/
structure TargetReplayInv {M : Type} (view : M → Slice U8) (original target : Store.CodeInterpretation)
    (before : runtime.store.Store M) (code : Store.CodeInterpretation) (store : runtime.store.Store M) : Prop
    extends ReplayInv view original before code store where
  targetAgrees : Store.CodeAgreesOn store code target

theorem TargetReplayInv.initial {M : Type} {view : M → Slice U8} {code target : Store.CodeInterpretation}
    {store : runtime.store.Store M} (held : ExecutableInv view code store)
    (agrees : Store.CodeAgreesOn store code target) : TargetReplayInv view code target store code store :=
  ⟨ReplayInv.initial held,agrees⟩

theorem TargetReplayInv.update {M : Type} {view : M → Slice U8} {original target code : Store.CodeInterpretation}
    {initial before after : runtime.store.Store M} (held : TargetReplayInv view original target initial code before)
    (mutation : CumulativeStoreMutation view code before after) : TargetReplayInv view original target initial code after := by
  refine ⟨held.toReplayInv.update mutation,?_⟩
  simpa only [Store.CodeAgreesOn,mutation.metadata.instances] using held.targetAgrees

theorem target_replay_sound {M : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (before after : runtime.store.Store M) (oldCode afterCode : Store.CodeInterpretation)
    (status : core.result.Result Unit runtime.platform.HostError) (values : Slice runtime.Value)
    (effect : ReturnedWorldEffect view (ExecutableInv view) oldCode before afterCode after)
    (externs : before.externs.length≤after.externs.length) :
    HostWorldSound (replay memory before after status values) view (TargetReplayInv view oldCode afterCode before) := by
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
      ⟨afterCode,agrees,⟨⟨effect.invariant,effect.metadata,effect.agrees,externs⟩,(by intro index inst found fn; rfl)⟩,
        extension,effect.invariant.source_typed⟩
  · simpa only [replay,if_neg same] using WP.spec.ret
      ⟨code,(by intro index inst found fn; rfl),held,Spec.extend_store_refl _ held.executable.well_formed,held.executable.source_typed⟩
end Exec.Theorems.OpenReentrantControl
