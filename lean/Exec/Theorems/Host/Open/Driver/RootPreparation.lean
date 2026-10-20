import Exec.Theorems.Host.Open.Driver.DefinedEntry
import Exec.Interp.Host.OpenPreparation
import Exec.Store.Invariant.CheckedValues
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- A root call is either rejected before execution, enters a certified Wasm
machine, or exposes a typed host request with its native continuation. -/
inductive RootCallReady {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (ambient : frame) (address : runtime.FuncAddr)
    (signature : Itasca.types.FuncType) (arguments : List val) : CallPhase M Unit → Prop
  | rejected (answer : Answer M Unit) (error : runtime.ExecError)
      (status : answer.1=.Err error) (sameStore : answer.2.2.1=store) : RootCallReady view code store ambient address signature arguments (.done answer)
  | defined (answer : Answer M Unit) (entry : Abs.AState)
      (status : answer.1=.Ok ()) (sameStore : answer.2.2.1=store)
      (machine : StructuredMachine.Execution Executable.emission (Abs.SupportedState Abs.ExecutableInstr)
        view code store answer.2.1 entry (signature.results.val.map sourceType) 0 false)
      (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store) entry)
      (ambientEq : entry.ambient=ambient)
      (source : StepH ⟨⟨Store.decodeStore view code store,ambient⟩,vals arguments++[.CALL_ADDR address.index.val]⟩ [] (Abs.decode entry)) :
      RootCallReady view code store ambient address signature arguments (.done answer)
  | host (ready : runtime.interp.Execution) (token : Unit) (identity : U64)
      (args defaults : alloc.vec.Vec runtime.Value) (function : runtime.store.Function)
      (functionAt : store.funcs.val[address.index.val]?=some function)
      (host : function.code=.Host identity)
      (signatureAt : store.types.val[function.signature.val]?=some signature)
      (empty : ready.frames.val=[]) (capacity : Code.slots (signature.results.val.map sourceType)≤ready.slots.length)
      (argumentsEq : args.val.map sourceValue=arguments)
      (argumentsTyped : ResultsTyped (Store.decodeStore view code store) (signature.params.val.map sourceType) arguments) :
      RootCallReady view code store ambient address signature arguments (.pending ready store token address 0#usize identity args defaults)

/-- Both raw function kinds establish the root guard using native preparation
proofs. No premise asserts termination or correctness of a host callback. -/
theorem prepare_root_call {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform Unit M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _=>True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (token : Unit)
    (held : ExecutableInv view code store) (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.Function) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (empty : exec.frames.val=[]) (owner : exec.store=store.id)
    (words : ValuesAt exec.slots.val 0 (args.val.map sourceValue))
    (accepted : runtime.interp.check_values memory store args signature.params.deref=.ok (.Ok ()))
    (owned : ∀value∈args.val,Store.ValueInStore store value)
    (functionAt : store.funcs.val[address.index.val]?=some function)
    (signatureAt : store.types.val[function.signature.val]?=some signature)
    (typed : ResultsTyped (Store.decodeStore view code store) (signature.params.val.map sourceType) (args.val.map sourceValue)) :
    prepareCall memory hooks floats allocator exec store token address 0#usize
      ⦃phase=>RootCallReady view code store ambient address signature (args.val.map sourceValue) phase⦄ := by
  cases kind : function.code with
  | Wasm instanceIndex functionIndex =>
    apply WP.spec_mono (prepare_defined_entry memory hooks floats allocator allocation interrupts view code exec store token
      held ambient ambientWf address function signature instanceIndex functionIndex args empty owner words accepted owned functionAt signatureAt kind)
    rintro phase ⟨out,rfl,sameStore,entered,failed⟩
    cases status : out.1 with
    | Ok unit =>
      cases unit
      obtain ⟨entry,machine,owned,ambientEq,source⟩ := entered status
      exact .defined out entry status sameStore machine owned ambientEq source
    | Err error => exact .rejected out error status sameStore
  | Host identity =>
    have tags : signature.params.val.map sourceType=(args.val.map sourceValue).map Code.valueType := by
      simpa only [show Code.valueType=Abs.valueType from funext valueType_eq_abs] using (Abs.results_type_of_typed typed).symm
    apply WP.spec_mono (prepare_host_call memory hooks floats allocator allocation interrupts exec store token address 0#usize
      function identity signature functionAt kind signatureAt (args.val.map sourceValue) tags (Spec.resultsTyped_wf typed)
      (fun value member=>Store.owned_result_fits store value (Store.source_values_owned store args.val owned value member)) words)
    rintro phase (rejected|pending)
    · obtain ⟨out,rfl,error,status,cause,sameStore⟩ := rejected
      exact .rejected out error status sameStore
    · obtain ⟨ready,nextToken,args,defaults,rfl,padding,frames,capacity,argsEq,defaultsEq⟩ := pending
      exact .host _ nextToken identity args defaults function functionAt kind signatureAt
        (by simpa only [frames] using empty) (by simpa using capacity) argsEq typed
end Exec.Theorems.OpenReentrantControl
