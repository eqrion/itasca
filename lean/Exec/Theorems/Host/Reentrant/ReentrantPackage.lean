import Exec.Theorems.Host.Reentrant.ReentrantInvocation
namespace Exec.Theorems.ReentrantCallbacks
open Aeneas Aeneas.Std

theorem Package.world_sound {M : Type} {hooks : runtime.platform.Platform Unit M}
    {view : M → Slice U8} (package : Package hooks view) :
    HostWorldSound hooks view (ExecutableInv view) := by
  intro code store held token identity args defaults
  apply WP.spec_mono (package code store held token identity args defaults)
  rintro answer ⟨afterCode,effect,externs,issued⟩
  exact ⟨afterCode,effect.agrees,effect.invariant,effect.extension,effect.invariant.source_typed⟩

theorem Package.retained {M : Type} {hooks : runtime.platform.Platform Unit M}
    {view : M → Slice U8} (package : Package hooks view)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (identity : U64) (token : Unit) (args defaults : Slice runtime.Value) (answer)
    (actual : hooks.call_host token store identity args defaults=.ok answer) :
    Interp.FrameStorePrefix store answer.2.2.1 ∧ store.externs.length≤answer.2.2.1.externs.length ∧
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value := by
  have post := package code store held token identity args defaults
  rw [actual,WP.spec_ok] at post
  obtain ⟨afterCode,effect,externs,issued⟩ := post
  exact ⟨effect.metadata,externs,issued⟩
end Exec.Theorems.ReentrantCallbacks
