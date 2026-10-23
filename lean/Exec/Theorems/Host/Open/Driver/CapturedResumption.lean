import Exec.Theorems.Host.Open.Source.State.Continuation
import Exec.Theorems.Host.Open.Driver.HostCompletion
import Exec.Theorems.Host.Reentrant.FiniteReentrantCallbacks
import Exec.Theorems.Composition.FrameStorePrefixStaged
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.StructuredMachine

/-- A captured source continuation resumes at the same checked reply and
post-publication code interpretation as the actual native caller. The final
source configuration is identified, rather than independently existential. -/
theorem resume_captured_source {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (held : ExecutableInv view code store) (ready : runtime.interp.Execution)
    (address : runtime.FuncAddr) (base : Usize) (sourcePending : Spec.OpenHost.Pending)
    (expected : List valtype) (typed : Config_ok sourcePending.initial (.mk_list expected))
    (beforeEq : sourcePending.before=Store.decodeStore view code store)
    (addressEq : sourcePending.address=address.index.val)
    (argumentsEq : ready.host_args.val.map sourceValue=sourcePending.arguments)
    (saved : SourceContinuation memory view code store ready address base sourcePending expected)
    (afterCode : Store.CodeInterpretation) (after : runtime.store.Store M)
    (effect : ReentrantCallbacks.Effect view code store afterCode after)
    (values : alloc.vec.Vec runtime.Value) (status : core.result.Result Unit runtime.platform.HostError)
    (issued : ∀value∈values.val,Store.IssuedValue after value) :
    hostResume memory ready after address base values status ⦃out=>∃signature,
      let reply:=checkedHostReply memory view afterCode after signature values status
      sourcePending.results=signature.results.val.map sourceType ∧
      hostCallEvents address (out.1,out.2,after,())=[.call sourcePending.address sourcePending.arguments reply.result] ∧
      reply.Admissible sourcePending.before sourcePending.results ∧
      StepH sourcePending.initial (hostCallEvents address (out.1,out.2,after,())) (sourcePending.completed reply) ∧
      Config_ok (sourcePending.completed reply) (.mk_list expected) ∧
      (out.1=.Ok () → ∃source pc pendingFlag,
        Execution view afterCode after out.2 source expected pc pendingFlag ∧
        Abs.Ownership.StatefulOwned (Store.ownershipBounds after) source ∧
        Abs.decode source=sourcePending.completed reply)⦄ := by
  obtain ⟨function,signature,functionAt,signatureAt,resume⟩ := saved
  obtain ⟨out,actual,post⟩ := WP.spec_imp_exists (resume afterCode after effect.agrees effect.metadata effect.externs
    (frame_type_bounds_of_shape held.shape) effect.extension effect.invariant.source_typed
    effect.invariant.toCertifiedApiStore.toCertifiedSupportedStore values status issued)
  rw [actual,WP.spec_ok]
  have resultsEq := pending_signature_results view code store sourcePending address function signature beforeEq addressEq functionAt signatureAt
  have admissible : (checkedHostReply memory view afterCode after signature values status).Admissible sourcePending.before sourcePending.results := by
    have checked := checked_reply_admissible memory view code afterCode store after effect.toReturnedWorldEffect signature values status issued
    simpa only [beforeEq,resultsEq] using checked
  have recorded := host_resume_events memory view afterCode after ready address base function signature
    (effect.metadata.function_lookup functionAt) (effect.metadata.type_lookup signatureAt) values status out () actual
  have events : hostCallEvents address (out.1,out.2,after,())=
      [.call sourcePending.address sourcePending.arguments (checkedHostReply memory view afterCode after signature values status).result] := by
    simpa only [addressEq,argumentsEq] using recorded
  exact ⟨signature,resultsEq,events,admissible,pending_checked_compress memory view code afterCode store after effect.toReturnedWorldEffect
    sourcePending address function signature beforeEq addressEq functionAt signatureAt ready base values status issued argumentsEq out () actual,
    sourcePending.completed_typed _ admissible typed,post⟩
end Exec.Theorems.OpenReentrantControl
