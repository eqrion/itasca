import Exec.Theorems.Host.Open.Source.State.World
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

theorem PreparedSourceHost.done_events {M P : Type}
    {memory : runtime.platform.MemoryBuffer M} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution} {source : config} {expected : resulttype}
    {out : Answer M P} (guard : PreparedSourceHost memory view code store exec source expected (.done out)) :
    stepHostEvents exec store out=[] := by
  rcases guard with silent|⟨error,failed,kind,sameStore⟩
  · simp only [stepHostEvents,silent]
  · cases selected : hostStepAddress exec store with
    | none=>simp only [stepHostEvents,selected]
    | some address=>
      simp only [stepHostEvents,selected]
      cases error <;> simp_all only [HostPreparationError,hostCallEvents]
      rename_i limit
      cases limit <;> simp_all only [HostPreparationError,hostCallEvents]

/-- A completed preparation emits no host event. Native noncall instructions
have no selected host address; host preparation errors occur before entry.
Administrative jumps are retained as silent completed instructions. -/
theorem completed_step_events {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) {expected : List valtype}
    (world : EventfulWorld M Unit view expected)
    (held : ExecutableInv view world.code world.machine.store) (active : 0<world.machine.exec.frames.length)
    (typed : Config_ok (Abs.decode world.machine.source) (.mk_list expected)) (out : Answer M Unit)
    (prepared : prepareStep memory (inert memory) floats allocator world.machine.exec world.machine.store world.machine.platform=.ok (.done out)) :
    stepHostEvents world.machine.exec world.machine.store out=[] := by
  cases selected : hostStepAddress world.machine.exec world.machine.store with
  | none=>simp only [stepHostEvents,selected]
  | some address=>
    have site := recording_host_site view world.code world.machine.exec world.machine.store
      world.machine.source expected world.machine.pc world.machine.pending world.machine.invariant.storeEq held.shape
      world.machine.owned.values world.machine.invariant active address selected
    have certified := prepare_site_source memory (inert memory) floats allocator allocation (fun _=>WP.spec.ret trivial)
      view world.code world.machine.exec world.machine.store world.machine.platform held.shape site world.machine.invariant.typed.typed typed
    rw [prepared,WP.spec_ok] at certified
    exact certified.done_events
end Exec.Theorems.OpenReentrantControl
