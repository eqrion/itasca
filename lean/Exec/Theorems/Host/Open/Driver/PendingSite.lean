import Exec.Theorems.Host.Open.Driver.WorldPreparation
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- A proof-only dictionary detecting whether native preparation would call a
host. The executable driver never runs this divergent dictionary. -/
private def pendingProbe {M : Type} (memory : runtime.platform.MemoryBuffer M) : runtime.platform.Platform Unit M where
  MemoryBufferInst:=memory
  interrupt token:=.ok (.Continue,token)
  call_host _ _ _ _ _:=.div

/-- Actual suspension identifies a typed direct or indirect source host site.
The native nonhost proof works for arbitrary callback dictionaries; applying it
to a divergent probe excludes every ordinary-dispatch branch. -/
theorem pending_source_site {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    {expected : List valtype}
    (world : EventfulWorld M Unit view expected)
    (held : ExecutableInv view world.code world.machine.store) (active : 0<world.machine.exec.frames.length)
    (ready : runtime.interp.Execution) (after : runtime.store.Store M) (token : Unit)
    (address : runtime.FuncAddr) (base : Usize) (identity : U64) (args defaults : alloc.vec.Vec runtime.Value)
    (pending : prepareStep memory (inert memory) floats allocator world.machine.exec world.machine.store world.machine.platform=
      .ok (.pending ready after token address base identity args defaults)) :
    StructuredHostSite view world.code world.machine.exec world.machine.store
      expected world.machine.pc world.machine.pending world.machine.source := by
  rcases world_step_or_host memory (pendingProbe memory) floats allocator correct allocation
    (fun _=>WP.spec.ret trivial) view laws world.code (ExecutableInv view) (fun _ _ _ held mutation=>held.update mutation)
    world.machine held active with site|ordinary
  · exact site
  · have same := prepareStep_independent memory (pendingProbe memory) (inert memory) floats allocator
      world.machine.exec world.machine.store world.machine.platform (fun _=>rfl)
    have graph := erase_step memory (pendingProbe memory) floats allocator world.machine.exec world.machine.store world.machine.platform
    rw [same,pending,bind_ok] at graph
    simp only [resume,pendingProbe,bind_div] at graph
    obtain ⟨out,actual,post⟩ := WP.spec_imp_exists ordinary
    have impossible : (.div : Result (Answer M Unit))=.ok out := graph.trans actual
    simp at impossible
end Exec.Theorems.OpenReentrantControl
