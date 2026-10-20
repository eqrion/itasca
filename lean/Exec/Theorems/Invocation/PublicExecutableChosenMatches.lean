import Exec.Theorems.Invocation.InvokeSupportedChosenMatches
import Exec.Theorems.Invocation.PublicExecutableTyped
import Exec.Theorems.Api.ExecutableInv
import Exec.Theorems.Api.CertifiedApiMetadata
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Full-profile public fixed-policy completeness for host-free stores. Typed
owned inputs, source storage capacities and primitive platform compatibility
are explicit; neither compilation success nor invocation success is assumed. -/
theorem invoke_executable_chosen_matches {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vector : choices.vector=Spec.firstVectorChoice)
    {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p,hooks.interrupt p ⦃ _=>True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store) (hostFree : CoreHostFree store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store=store.id) (issued : Store.ExternalIssued store (.Func address))
    (owned : ∀ value∈args.val,Store.ValueInStore store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (sourceFunction : funcinst) (params resultsTypes : List valtype)
    (sourceAt : (Store.decodeStore view code store).FUNCS[address.index.val]?=some sourceFunction)
    (sourceType : sourceFunction.TYPE=.mk_functype (.mk_list params) (.mk_list resultsTypes))
    (typedArguments : ResultsTyped (Store.decodeStore view code store) params (args.val.map sourceValue))
    {events : List HostEvent} {target : config}
    (run : Spec.ChoiceSteps choices 0 initial events target) (terminal : Spec.SourceTerminal target)
    (resources : SourceInvocationResources initial (Store.decodeStore view code store) sourceFunction.TYPE address.index.val
      store.limits.max_values.val store.limits.max_frames.val)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after)) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ExecutableInv view code out.2.2.1 ∧ Store_ok (Store.decodeStore view code out.2.2.1) ∧
        FrameStoreMetadata store out.2.2.1 ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧ events=[] ∧
        match out.1 with
        | .Ok _ => target=⟨⟨Store.decodeStore view code out.2.2.1,Spec.invocationFrame⟩,vals (out.2.2.2.2.val.map sourceValue)⟩
        | .Err (.Trap trap) => CumulativeTrap trap ∧ target=⟨⟨Store.decodeStore view code out.2.2.1,Spec.invocationFrame⟩,[.TRAP]⟩
        | .Err _ => False ⦄ := by
  have bound : address.index.val<store.funcs.val.length := issued owner
  let function := store.funcs.val[address.index.val]
  have hf : store.funcs.val[address.index.val]?=some function := List.getElem?_eq_getElem bound
  have signatureBound : function.signature.val<store.types.val.length :=
    (valid.shape.functions function (List.mem_of_getElem? hf)).1
  let signature := store.types.val[function.signature.val]
  have hs : store.types.val[function.signature.val]?=some signature := List.getElem?_eq_getElem signatureBound
  have decoded : Store.decodeFunction code store function=sourceFunction := by
    simpa only [Store.decodeStore,List.getElem?_map,hf,Option.map_some,Option.some.injEq] using sourceAt
  have typeEq : Store.decodeFuncType signature=sourceFunction.TYPE := by
    rw [←decoded,Store.decodeFunction_type code store function signatureBound]
  have paramsEq : signature.params.val.map Interp.sourceType=params := by
    have eqs := typeEq.trans sourceType
    simp only [Store.decodeFuncType,functype.mk_functype.injEq,list.mk_list.injEq] at eqs
    exact eqs.1
  obtain ⟨ii,fi,wasm⟩ : ∃ ii fi,function.code=.Wasm ii fi := by
    cases kind : function.code with
    | Host identity => exact False.elim (hostFree function (List.mem_of_getElem? hf) identity kind)
    | Wasm ii fi => exact ⟨ii,fi,rfl⟩
  have sourceEq := Spec.invocation_config invoked
  have checked := typed_arguments_accepted memory store (Store.decodeStore view code store) args signature.params
    (by simpa only [paramsEq] using typedArguments) (fun value member=>(owned value member).1)
  apply WP.spec_mono (invoke_defined_supported_chosen_matches admissible numericChoice vector 0 Abs.executable_language
    memory hooks floats allocator correct allocation interrupts view laws code compatible exec store platform
    valid.toCertifiedApiStore.toCertifiedSupportedStore hostFree Spec.invocationFrame (Spec.invocation_frame_wf invoked)
    address function signature ii fi args results owner owned hf hs wasm checked
    (by simpa only [sourceEq] using run) terminal valid.capacities
    (by simpa only [sourceEq,typeEq] using resources) available continuing)
  rintro out ⟨⟨fresh,metadata,extension,segments⟩,empty,agreement⟩
  have retained : ExecutableInv view code out.2.2.1 :=
    ⟨valid.toCertifiedApiStore.frame_metadata fresh metadata,
      segments.accounting metadata.instances valid.segmentAccounting,
      valid.capacities.metadata metadata.functions metadata.instances metadata.types metadata.identity⟩
  exact ⟨retained,retained.source_typed,metadata,extension,empty,agreement⟩
end Exec.Theorems
