import Exec.Theorems.Host.Reentrant.FiniteReentrantCallbacks
import Exec.Theorems.Host.Open.Source.State.World
import Exec.Theorems.Host.Open.Driver.PendingMetadata
import Exec.Theorems.Host.Open.Driver.ResumptionAt
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- Native resumption and atomic source completion are checked together at the
exact post-callback code interpretation. Committed effects and dynamic type
rejection are retained without any premise that the host control terminates. -/
theorem resume_selected_source {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    {expected : List valtype}
    (world : EventfulWorld Executable.emission Abs.ExecutableInstr M Unit view expected)
    (held : ExecutableInv view world.code world.machine.store) (active : 0<world.machine.exec.frames.length)
    (ready : runtime.interp.Execution) (address : runtime.FuncAddr) (base : Usize) (identity : U64)
    (args defaults : alloc.vec.Vec runtime.Value)
    (prepared : prepareStep memory (inert memory) floats allocator world.machine.exec world.machine.store world.machine.platform=
      .ok (.pending ready world.machine.store world.machine.platform address base identity args defaults))
    (pending : Spec.OpenHost.Pending) (beforeEq : pending.before=Store.decodeStore view world.code world.machine.store)
    (addressEq : pending.address=address.index.val) (argumentsEq : ready.host_args.val.map sourceValue=pending.arguments)
    (typed : Config_ok pending.initial (.mk_list expected))
    (afterCode : Store.CodeInterpretation) (after : runtime.store.Store M)
    (status : HostStatus) (values : Slice runtime.Value)
    (effect : ReentrantCallbacks.Effect view world.code world.machine.store afterCode after)
    (issued : ∀value∈values.val,Store.IssuedValue after value) :
    (do let (result,finished) ← hostResume memory ready after address base ⟨values⟩ status
        .ok (result,finished,after,world.machine.platform)) ⦃out=>
      ResumedWorldResultAt world afterCode out ∧ ∃signature,
        let reply:=checkedHostReply memory view afterCode after signature ⟨values⟩ status
        reply.Admissible pending.before pending.results ∧
        StepH pending.initial (hostCallEvents address out) (pending.completed reply) ∧
        Config_ok (pending.completed reply) (.mk_list expected)⦄ := by
  obtain ⟨function,signature,functionAt,signatureAt,resultsEq⟩ := pending_raw_metadata view world.code world.machine.store held.shape pending address beforeEq addressEq
  have total := resume_world_at memory floats allocator correct allocation view laws world held active ready address base identity args defaults
    prepared afterCode after status values effect.1 effect.2 issued
  obtain ⟨out,actual,post⟩ := WP.spec_imp_exists total
  obtain ⟨pair,resumed,packed⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
  cases pair with | mk result finished=>
    simp only [Std.uncurry,Result.ok.injEq] at packed
    subst out
    rw [resumed,bind_ok]
    dsimp only [Std.uncurry]
    apply WP.spec.ret
    refine ⟨post,signature,?_,?_,?_⟩
    · have admissible := checked_reply_admissible memory view world.code afterCode world.machine.store after effect.1 signature ⟨values⟩ status issued
      simpa only [beforeEq,resultsEq] using admissible
    · exact pending_checked_compress memory view world.code afterCode world.machine.store after effect.1 pending address function signature
        beforeEq addressEq functionAt signatureAt ready base ⟨values⟩ status issued argumentsEq (result,finished) world.machine.platform resumed
    · apply pending.completed_typed _ _ typed
      have admissible := checked_reply_admissible memory view world.code afterCode world.machine.store after effect.1 signature ⟨values⟩ status issued
      simpa only [beforeEq,resultsEq] using admissible
end Exec.Theorems.OpenReentrantControl
