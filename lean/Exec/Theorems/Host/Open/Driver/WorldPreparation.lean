import Exec.Theorems.Host.Open.Driver.CompletedWorld
import Exec.Interp.Host.OpenStepFootprint
import Itasca.Support.Result
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

def PreparedWorldResult {M : Type} {view : M → Slice U8} {expected : List valtype}
    (world : EventfulWorld M Unit view expected) : CallPhase M Unit → Prop
  | .done out => ResumedWorldResult world out
  | .pending _ store _ _ _ _ _ _ => store=world.machine.store

/-- One typed active Wasm task prepares normally. Its host branch exposes the
unchanged entry store, and its completed branch has the full native source
certificate. No contract on a real returning callback is used. -/
theorem prepare_world_step {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    {expected : List valtype}
    (world : EventfulWorld M Unit view expected)
    (held : ExecutableInv view world.code world.machine.store) (active : 0<world.machine.exec.frames.length) :
    prepareStep memory (inert memory) floats allocator world.machine.exec world.machine.store world.machine.platform
      ⦃phase=>PreparedWorldResult world phase⦄ := by
  have raw : ∀before token identity args defaults,
      (inert memory).call_host token before identity args defaults ⦃ answer=>
        FrameStorePrefix before answer.2.2.1 ∧ before.externs.length≤answer.2.2.1.externs.length ∧
        ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value ⦄ := by
    intro before token identity args defaults
    exact WP.spec.ret ⟨.refl _,Nat.le_refl _,by simp [PureCallbacks.Program.evaluate]⟩
  let Inv := ReentrantCallbacks.FloorInv view world.machine.store.externs.length
  have sound : HostWorldSound (inert memory) view Inv := by
    intro code before valid token identity args defaults
    exact WP.spec.ret ⟨code,(by intro index inst found fn; rfl),valid,
      Spec.extend_store_refl _ valid.1.well_formed,valid.1.source_typed⟩
  have post := world_step_outcomes memory (inert memory) floats allocator correct allocation
    (fun _=>WP.spec.ret trivial) view laws Inv
    (fun _ _ valid=>valid.1.toCertifiedApiStore.toCertifiedSupportedStore)
    (fun _ _ _ valid mutation=>valid.update mutation) sound
    (fun _ before _ identity token args defaults answer actual=>by
      have law := raw before token identity args defaults
      rw [actual,WP.spec_ok] at law
      exact law.1)
    (fun _ before _ identity token args defaults answer actual=>by
      have law := raw before token identity args defaults
      rw [actual,WP.spec_ok] at law
      exact law.2.1)
    (fun _ before _ identity token args defaults answer actual=>by
      have law := raw before token identity args defaults
      rw [actual,WP.spec_ok] at law
      exact law.2.2)
    expected world ⟨held,Nat.le_refl _⟩ active
  obtain ⟨out,actual,outcome⟩ := WP.spec_imp_exists post
  have graph := erase_step memory (inert memory) floats allocator world.machine.exec world.machine.store world.machine.platform
  rw [actual] at graph
  obtain ⟨phase,prepared,resumed⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ graph
  rw [prepared,WP.spec_ok]
  cases phase with
  | done answer => exact completed_world memory floats allocator correct allocation view laws world held active answer prepared
  | pending exec store token address base identity args defaults =>
    exact prepareStep_pending_store memory (inert memory) floats allocator world.machine.exec world.machine.store world.machine.platform _ prepared
end Exec.Theorems.OpenReentrantControl
