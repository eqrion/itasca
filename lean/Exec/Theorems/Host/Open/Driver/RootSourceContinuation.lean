import Exec.Theorems.Host.Open.Driver.RootSupportedHost
import Exec.Theorems.Host.Open.Source.State.Continuation
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.StructuredMachine

/-- The root host request uses the source invocation frame and an empty
surrounding evaluation context. Nested host requests retain their own contexts. -/
def rootSourcePending {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (identity : U64) (signature : Itasca.types.FuncType) (arguments : List val)
    (host : HostFunction (Store.decodeStore view code store) address.index.val identity.val
      (signature.params.val.map sourceType) (signature.results.val.map sourceType))
    (typed : ResultsTyped (Store.decodeStore view code store) (signature.params.val.map sourceType) arguments) : Spec.OpenHost.Pending :=
  ⟨Store.decodeStore view code store,ambient,.hole,address.index.val,identity.val,
    signature.params.val.map sourceType,signature.results.val.map sourceType,arguments,host,typed,ambientWf⟩

/-- Root host setup constructs the same future-world saved-source certificate
as internal direct/indirect sites, using the actual empty native call stack. -/
theorem root_source_continuation {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (ready : runtime.interp.Execution) (empty : ready.frames.val=[])
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (identity : U64)
    (signature : Itasca.types.FuncType) (functionAt : store.funcs.val[address.index.val]?=some function)
    (hostCode : function.code=.Host identity) (signatureAt : store.types.val[function.signature.val]?=some signature)
    (ambient : frame) (ambientWf : wf_frame ambient) (arguments : List val)
    (typed : ResultsTyped (Store.decodeStore view code store) (signature.params.val.map sourceType) arguments)
    (capacity : Code.slots (signature.results.val.map sourceType)≤ready.slots.length) :
    SourceContinuation memory view code store ready address 0#usize
      (rootSourcePending view code store ambient ambientWf address identity signature arguments
        (Store.decode_host_function view code store address function identity signature functionAt hostCode signatureAt) typed)
      (signature.results.val.map sourceType) := by
  refine ⟨function,signature,functionAt,signatureAt,?_⟩
  intro afterCode after agrees retained externs bounds extension sourceTyped certified values status issued
  obtain ⟨out,actual,resultsEq,emptyAfter,owner,outcome⟩ := WP.spec_imp_exists
    (root_host_supported_resume memory view code afterCode store after agrees retained extension sourceTyped certified
      ready empty address function identity signature functionAt hostCode signatureAt ambient ambientWf arguments typed
      values.slice issued status capacity)
  rw [actual,WP.spec_ok]
  intro successful
  rcases outcome with returned|failed
  · obtain ⟨ok,step,machine,owned⟩ := returned
    refine ⟨_,0,false,machine,owned,?_⟩
    have replyResult := host_resume_checked_result memory view afterCode after ready address 0#usize function signature
      (retained.function_lookup functionAt) (retained.type_lookup signatureAt) values status out actual successful
    rw [resultsEq] at replyResult
    have replyEq : checkedHostReply memory view afterCode after signature values status=
        ⟨Store.decodeStore view afterCode after,(checkedHostReply memory view afterCode after signature values status).result⟩ := rfl
    rw [replyEq,replyResult]
    rfl
  · rcases failed.1 with trapped|⟨exhausted,stack⟩ <;> rw [successful] at * <;> contradiction
end Exec.Theorems.OpenReentrantControl
