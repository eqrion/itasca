import Exec.Theorems.Host.Open.Source.State.SavedCaller
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.StructuredMachine

/-- The reached caller frame supplies a checked resumption in the current
world, retaining its particular source context and both result signatures. -/
theorem SourceSavedCaller.resumption {M : Type} {memory : runtime.platform.MemoryBuffer M} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {address root : runtime.FuncAddr} {base : Usize} {suspended : Spec.OpenExecution.Suspension}
    (saved : SourceSavedCaller memory view code store exec address base root suspended)
    (values : alloc.vec.Vec runtime.Value) (status : core.result.Result Unit runtime.platform.HostError)
    (issued : ∀value∈values.val,Store.IssuedValue store value) :
    ∃signature,RootMetadata store root signature ∧ suspended.expected=.mk_list (signature.results.val.map sourceType) ∧
      hostResume memory exec store address base values status ⦃out=>∃calledSignature,
        let reply:=checkedHostReply memory view code store calledSignature values status
        suspended.pending.results=calledSignature.results.val.map sourceType ∧
        hostCallEvents address (out.1,out.2,store,())=[.call suspended.pending.address suspended.pending.arguments reply.result] ∧
        reply.Admissible suspended.pending.before suspended.pending.results ∧
        StepH suspended.pending.initial (hostCallEvents address (out.1,out.2,store,())) (suspended.pending.completed reply) ∧
        Config_ok (suspended.pending.completed reply) suspended.expected ∧
        (out.1=.Ok () → ∃source pc pendingFlag,
          Execution Executable.emission (Abs.SupportedState Abs.ExecutableInstr) view code store out.2 source
            (signature.results.val.map sourceType) pc pendingFlag ∧
          Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source ∧ Abs.decode source=suspended.pending.completed reply)⦄ := by
  obtain ⟨entryCode,entryStore,signature,held,effect,metadata,expected,beforeEq,addressEq,argsEq,continuation⟩ := saved
  refine ⟨signature,metadata.prefix effect.metadata,expected,?_⟩
  have typed : Config_ok suspended.pending.initial (.mk_list (signature.results.val.map sourceType)) := by
    simpa only [expected] using suspended.typed
  have post:=resume_captured_source memory view entryCode entryStore held exec address base suspended.pending
    (signature.results.val.map sourceType) typed beforeEq addressEq argsEq continuation code store effect values status issued
  apply WP.spec_mono post
  rintro out ⟨calledSignature,resultTypes,events,admissible,atomic,typed,future⟩
  exact ⟨calledSignature,resultTypes,events,admissible,atomic,by simpa only [expected] using typed,future⟩
end Exec.Theorems.OpenReentrantControl
