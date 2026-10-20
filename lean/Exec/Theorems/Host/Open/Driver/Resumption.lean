import Exec.Theorems.Host.Open.Driver.ReplayCallback
import Exec.Theorems.Host.Open.Driver.ReentrantControl
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- The source/certificate part of a resumed native step. It omits the replay
dictionary's artificial call graph; actual resumption has its own graph. -/
def ResumedWorldResult {M : Type} {view : M → Slice U8} {expected : List valtype}
    (before : EventfulWorld Executable.emission Abs.ExecutableInstr M Unit view expected)
    (out : Answer M Unit) : Prop :=
  match out.1 with
  | .Ok _ => ∃next : EventfulWorld Executable.emission Abs.ExecutableInstr M Unit view expected,
      ExecutableInv view next.code next.machine.store ∧ out=(.Ok (),next.machine.exec,next.machine.store,next.machine.platform) ∧
      EventfulConcreteSim U32.max before.machine.pc next.machine.pc before.machine.pending next.machine.pending
        before.machine.source next.machine.source (stepHostEvents before.machine.exec before.machine.store out) ∧
      Extend_store (Store.decodeStore view before.code before.machine.store) (Store.decodeStore view next.code next.machine.store) ∧
      FrameStorePrefix before.machine.store next.machine.store ∧ before.machine.store.externs.length≤next.machine.store.externs.length ∧ next.machine.source.ambient=before.machine.source.ambient ∧
      Store.CodeAgreesOn before.machine.store before.code next.code
  | .Err error => ∃afterCode,ExecutableInv view afterCode out.2.2.1 ∧
      FrameStorePrefix before.machine.store out.2.2.1 ∧ before.machine.store.externs.length≤out.2.2.1.externs.length ∧ Store.CodeAgreesOn before.machine.store before.code afterCode ∧
      Extend_store (Store.decodeStore view before.code before.machine.store) (Store.decodeStore view afterCode out.2.2.1) ∧
      EventfulInvocationError (Abs.decode before.machine.source)
        (stepHostEvents before.machine.exec before.machine.store out)
        (Store.decodeStore view afterCode out.2.2.1) before.machine.source.ambient error

/-- A checked entry world and an actual suspension point suffice to certify
resumption from any checked returned effect. This is a continuation theorem:
it contains no assumption that the suspended host interaction returns. -/
theorem resume_world {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    {expected : List valtype}
    (world : EventfulWorld Executable.emission Abs.ExecutableInstr M Unit view expected)
    (held : ExecutableInv view world.code world.machine.store) (active : 0<world.machine.exec.frames.length)
    (ready : runtime.interp.Execution) (address : runtime.FuncAddr) (base : Usize) (identity : U64)
    (args defaults : alloc.vec.Vec runtime.Value)
    (pending : prepareStep memory (inert memory) floats allocator world.machine.exec world.machine.store world.machine.platform=
      .ok (.pending ready world.machine.store world.machine.platform address base identity args defaults))
    (afterCode : Store.CodeInterpretation) (after : runtime.store.Store M)
    (status : core.result.Result Unit runtime.platform.HostError) (values : Slice runtime.Value)
    (effect : ReturnedWorldEffect view (ExecutableInv view) world.code world.machine.store afterCode after)
    (externs : world.machine.store.externs.length≤after.externs.length)
    (issued : ∀value∈values.val,Store.IssuedValue after value) :
    (do let (result,finished) ← hostResume memory ready after address base ⟨values⟩ status
        .ok (result,finished,after,world.machine.platform)) ⦃ out=>ResumedWorldResult world out ⦄ := by
  let hooks := replay memory world.machine.store after status values
  let Inv := ReplayInv view world.code world.machine.store
  have raw := replay_retained memory world.machine.store after status values effect.metadata externs issued
  have sound := replay_sound memory view world.machine.store after world.code afterCode status values effect externs
  have total := world_step_outcomes Abs.executable_language memory hooks floats allocator correct allocation
    (fun _=>WP.spec.ret trivial) view laws Inv
    (fun _ _ valid=>valid.executable.toCertifiedApiStore.toCertifiedSupportedStore)
    (fun _ _ _ valid mutation=>valid.update mutation) sound
    (fun _ before _ identity token args defaults answer actual=>by
      have post := raw before token identity args defaults
      rw [actual,WP.spec_ok] at post
      exact post.1)
    (fun _ before _ identity token args defaults answer actual=>by
      have post := raw before token identity args defaults
      rw [actual,WP.spec_ok] at post
      exact post.2.1)
    (fun _ before _ identity token args defaults answer actual=>by
      have post := raw before token identity args defaults
      rw [actual,WP.spec_ok] at post
      exact post.2.2)
    expected world (ReplayInv.initial held) active
  have same := prepareStep_independent memory hooks (inert memory) floats allocator world.machine.exec
    world.machine.store world.machine.platform (fun _=>rfl)
  have graph := erase_step memory hooks floats allocator world.machine.exec world.machine.store world.machine.platform
  rw [same,pending,bind_ok] at graph
  conv_lhs at graph => simp only [resume,hooks,replay,if_pos rfl,ite_true,bind_ok]
  rw [←graph] at total
  apply WP.spec_mono total
  intro out post
  cases kind : out.1 with
  | Ok unit =>
    simp only [WorldStepResult,kind] at post
    simp only [ResumedWorldResult,kind]
    obtain ⟨next,fresh,sameOut,edge⟩ := post
    exact ⟨next,fresh.executable,sameOut,edge.simulation,edge.extension,edge.metadata,fresh.externs,edge.ambient,edge.agrees⟩
  | Err error =>
    simp only [WorldStepResult,kind] at post
    simp only [ResumedWorldResult,kind]
    obtain ⟨afterCode,fresh,certified,metadata,agrees,extension,source,cause⟩ := post
    exact ⟨afterCode,fresh.executable,metadata,fresh.externs,agrees,extension,source⟩
end Exec.Theorems.OpenReentrantControl
