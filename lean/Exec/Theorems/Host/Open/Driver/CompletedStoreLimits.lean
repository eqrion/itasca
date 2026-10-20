import Exec.Theorems.Host.Open.Driver.Resumption
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- A completed resumable dispatch preserves configured invocation limits.
The actual inert callback and ordinary store mutations establish this fact;
raw metadata prefixes alone do not imply it. -/
theorem completed_store_limits {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    {expected : List valtype}
    (world : EventfulWorld Executable.emission Abs.ExecutableInstr M Unit view expected)
    (held : ExecutableInv view world.code world.machine.store) (active : 0<world.machine.exec.frames.length)
    (out : Answer M Unit)
    (completed : prepareStep memory (inert memory) floats allocator world.machine.exec world.machine.store world.machine.platform=
      .ok (.done out)) : out.2.2.1.limits=world.machine.store.limits := by
  have raw : ∀before token identity args defaults,
      (inert memory).call_host token before identity args defaults ⦃ answer=>
        FrameStorePrefix before answer.2.2.1 ∧ before.externs.length≤answer.2.2.1.externs.length ∧
        ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value ⦄ := by
    intro before token identity args defaults
    exact WP.spec.ret ⟨.refl _,Nat.le_refl _,by simp [PureCallbacks.Program.evaluate]⟩
  let Inv : Store.CodeInterpretation → runtime.store.Store M → Prop :=
    fun code store=>ExecutableInv view code store ∧ store.limits=world.machine.store.limits
  have sound : HostWorldSound (inert memory) view Inv := by
    intro code before valid token identity args defaults
    exact WP.spec.ret ⟨code,(by intro index inst found fn; rfl),valid,
      Spec.extend_store_refl _ valid.1.well_formed,valid.1.source_typed⟩
  have post := world_step_outcomes Abs.executable_language memory (inert memory) floats allocator correct allocation
    (fun _=>WP.spec.ret trivial) view laws Inv
    (fun _ _ valid=>valid.1.toCertifiedApiStore.toCertifiedSupportedStore)
    (fun _ _ _ valid mutation=>⟨valid.1.update mutation,mutation.limits.trans valid.2⟩) sound
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
    expected world ⟨held,rfl⟩ active
  have graph := erase_step memory (inert memory) floats allocator world.machine.exec world.machine.store world.machine.platform
  simp only [completed,bind_ok,resume] at graph
  rw [←graph,WP.spec_ok] at post
  cases kind : out.1 with
  | Ok unit =>
    simp only [WorldStepResult,kind] at post
    obtain ⟨next,fresh,sameOut,edge⟩:=post
    rw [sameOut]
    exact fresh.2
  | Err error =>
    simp only [WorldStepResult,kind] at post
    obtain ⟨afterCode,fresh,certified,metadata,agrees,extension,source,cause⟩:=post
    exact fresh.2
end Exec.Theorems.OpenReentrantControl
