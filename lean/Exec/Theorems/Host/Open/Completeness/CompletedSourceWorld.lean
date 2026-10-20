import Exec.Theorems.Host.Open.Driver.CompletedEvents
import Exec.Theorems.Host.Reentrant.FiniteReentrantCallbacks
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- A completed native step has a silent source simulation or an error prefix
with its actual cause. Pending host entry is handled by a separate constructor
of the full combined refinement. -/
def QuietWorldResult {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (world : EventfulWorld Executable.emission Abs.ExecutableInstr M Unit view expected) (out : Answer M Unit) : Prop :=
  match out.1 with
  | .Ok _=>∃next : EventfulWorld Executable.emission Abs.ExecutableInstr M Unit view expected,
      ExecutableInv view next.code next.machine.store ∧ out=(.Ok (),next.machine.exec,next.machine.store,next.machine.platform) ∧
      ConcreteSim U32.max world.machine.pc next.machine.pc world.machine.pending next.machine.pending world.machine.source next.machine.source ∧
      ReentrantCallbacks.Effect view world.code world.machine.store next.code next.machine.store ∧
      next.machine.source.ambient=world.machine.source.ambient
  | .Err error=>∃afterCode,ReentrantCallbacks.Effect view world.code world.machine.store afterCode out.2.2.1 ∧
      EventfulInvocationError (Abs.decode world.machine.source) [] (Store.decodeStore view afterCode out.2.2.1) world.machine.source.ambient error ∧
      EventfulDispatchCause memory (inert memory) floats allocator world.machine out error

theorem completed_source_world {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    {expected : List valtype}
    (world : EventfulWorld Executable.emission Abs.ExecutableInstr M Unit view expected)
    (held : ExecutableInv view world.code world.machine.store) (active : 0<world.machine.exec.frames.length)
    (typed : Config_ok (Abs.decode world.machine.source) (.mk_list expected)) (out : Answer M Unit)
    (prepared : prepareStep memory (inert memory) floats allocator world.machine.exec world.machine.store world.machine.platform=.ok (.done out)) :
    QuietWorldResult memory floats allocator world out := by
  obtain ⟨post,causes⟩ := completed_world_causes memory floats allocator correct allocation view laws world held active out prepared
  have quiet := completed_step_events memory floats allocator allocation view world held active typed out prepared
  cases status : out.1 with
  | Ok unit=>
    simp only [ResumedWorldResult,status] at post
    simp only [QuietWorldResult,status]
    obtain ⟨next,fresh,same,simulation,extension,retained,externs,ambient,agrees⟩ := post
    have concrete : ConcreteSim U32.max world.machine.pc next.machine.pc world.machine.pending next.machine.pending
        world.machine.source next.machine.source := EventfulConcreteSim.empty_iff.mp (by simpa only [quiet] using simulation)
    exact ⟨next,fresh,same,concrete,⟨⟨agrees,fresh,retained,extension⟩,externs⟩,ambient⟩
  | Err error=>
    simp only [ResumedWorldResult,status] at post
    simp only [QuietWorldResult,status]
    obtain ⟨afterCode,fresh,retained,externs,agrees,extension,source⟩ := post
    exact ⟨afterCode,⟨⟨agrees,fresh,retained,extension⟩,externs⟩,
      by simpa only [quiet] using source,causes error status⟩
end Exec.Theorems.OpenReentrantControl
