import Exec.Theorems.Host.HostResumeOwned
import Exec.Theorems.Host.HostReturnedActions
import Exec.Theorems.Host.Chosen.TerminalSupportedWorld
import Exec.Store.Invariant.HostSignature
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Root host return retains the actual source event and a terminal machine
certificate; dynamic result rejection and host traps retain the returned store. -/
theorem root_host_supported_resume {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (beforeCode afterCode : Store.CodeInterpretation)
    (before after : runtime.store.Store M)
    (agrees : Store.CodeAgreesOn before beforeCode afterCode)
    (retained : FrameStorePrefix before after)
    (extension : Extend_store (Store.decodeStore view beforeCode before) (Store.decodeStore view afterCode after))
    (sourceTyped : Store_ok (Store.decodeStore view afterCode after))
    (certified : CertifiedSupportedStore view afterCode after)
    (ready : runtime.interp.Execution) (empty : ready.frames.val=[])
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (identity : U64)
    (signature : Itasca.types.FuncType)
    (functionAt : before.funcs.val[address.index.val]?=some function)
    (host : function.code=.Host identity)
    (signatureAt : before.types.val[function.signature.val]?=some signature)
    (ambient : frame) (ambientWf : wf_frame ambient) (args : List val)
    (arguments : ResultsTyped (Store.decodeStore view beforeCode before) (signature.params.val.map sourceType) args)
    (values : Slice runtime.Value) (issued : ∀value∈values.val,Store.IssuedValue after value)
    (status : core.result.Result Unit runtime.platform.HostError)
    (capacity : Code.slots (signature.results.val.map sourceType)≤ready.slots.length) :
    hostResume memory ready after address 0#usize ⟨values⟩ status ⦃ out=>
      out.2.host_results.val=values.val ∧ out.2.frames.val=[] ∧ out.2.store=ready.store ∧
      ((out.1=.Ok () ∧
        StepH ⟨⟨Store.decodeStore view beforeCode before,ambient⟩,vals args++[.CALL_ADDR address.index.val]⟩
          [.call address.index.val args (some (values.val.map sourceValue))]
          ⟨⟨Store.decodeStore view afterCode after,ambient⟩,vals (values.val.map sourceValue)⟩ ∧
        StructuredMachine.Execution
          view afterCode after out.2 ⟨Store.decodeStore view afterCode after,ambient,[],values.val.map sourceValue⟩
          (signature.results.val.map sourceType) 0 false ∧
        Abs.Ownership.StatefulOwned (Store.ownershipBounds after)
          ⟨Store.decodeStore view afterCode after,ambient,[],values.val.map sourceValue⟩) ∨
       ((out.1=.Err (.Trap .Host) ∨ out.1=.Err (.Exhausted .CallStack) ∧ status=.Err .StackOverflow) ∧
        StepH ⟨⟨Store.decodeStore view beforeCode before,ambient⟩,vals args++[.CALL_ADDR address.index.val]⟩
          [.call address.index.val args none] ⟨⟨Store.decodeStore view afterCode after,ambient⟩,[.TRAP]⟩)) ⦄ := by
  have same := Store.decodeStore_code_agrees view agrees
  have sourceHost := Store.decode_host_function view afterCode before address function identity signature functionAt host signatureAt
  have sourceArgs : ResultsTyped (Store.decodeStore view afterCode before) (signature.params.val.map sourceType) args := by
    simpa only [same] using arguments
  have extension : Extend_store (Store.decodeStore view afterCode before) (Store.decodeStore view afterCode after) := by
    simpa only [same] using extension
  apply WP.spec_mono (host_resume_source_owned memory view afterCode before after ambient ready address 0#usize function signature
    identity.val (signature.params.val.map sourceType) args ⟨values⟩ status sourceHost sourceArgs extension
    sourceTyped ambientWf (retained.function_lookup functionAt)
    (retained.type_lookup signatureAt) issued (by simpa using capacity))
  rintro ⟨result,finished⟩ ⟨hostArgs,hostResults,frames,owner,outcome⟩
  have emptyFinished : finished.frames.val=[] := by rw [frames,empty]
  refine ⟨by simpa only [alloc.vec.Vec.val] using congrArg alloc.vec.Vec.val hostResults,emptyFinished,owner,?_⟩
  rcases outcome with success | failure
  · obtain ⟨ok,edge,typed,owned,words,length,preserved⟩ := success
    obtain ⟨machine,ownership⟩ := terminal_supported_execution view afterCode after certified sourceTyped finished ambient ambientWf
      (signature.results.val.map sourceType) (values.val.map sourceValue) emptyFinished typed owned words
    exact Or.inl ⟨ok,by simpa only [same,alloc.vec.Vec.val] using edge,machine,ownership⟩
  · exact Or.inr ⟨failure.1,by simpa only [same,alloc.vec.Vec.val] using failure.2.2⟩
end Exec.Theorems.OpenReentrantControl
