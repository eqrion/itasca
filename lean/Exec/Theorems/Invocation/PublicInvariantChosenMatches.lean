import Exec.Theorems.Invocation.InvokeWorldChosenMatches
import Exec.Theorems.Invocation.InvokeHostWorldChosenMatches
import Exec.Theorems.Invocation.PublicWorldChosenOutcomes
import Exec.Theorems.Api.ExecutableResourceInv
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
/-- Public corresponding-outcome completeness for both complete profiles and
issued Wasm/host functions. Source capacities and primitive platform/callback
compatibility exclude resource errors; recorder events and final stores match
one preselected terminating source run. -/
theorem invoke_world_invariant_chosen_matches {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vector : choices.vector=Spec.firstVectorChoice)
    {M P F A : Type} {valueLimit frameLimit : Nat}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p,hooks.interrupt p ⦃ _=>True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (project : ∀code store,Inv code store → ExecutableResourceInv view valueLimit frameLimit code store)
    (update : ∀code before after,Inv code before → CumulativeStoreMutation view code before after → Inv code after)
    (sound : HostWorldChosenSound memory hooks view Inv choices)
    (preserve : ∀code store,Inv code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀code store,Inv code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀code store,Inv code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
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
    (signatureFits : signatureWords sourceFunction.TYPE≤valueLimit)
    (entryCapacity : ∀words,SourceCanonicalFunctionCapacity (Store.decodeStore view code store) address.index.val words → words≤valueLimit)
    (positiveFrames : 0<frameLimit)
    (resources : ChosenWorldResources choices 0 initial valueLimit frameLimit)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after))
    (noOverflow : NoHostStackOverflow hooks Inv) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ∃afterCode,Inv afterCode out.2.2.1 ∧
        Store_ok (Store.decodeStore view afterCode out.2.2.1) ∧ FrameStorePrefix store out.2.2.1 ∧
        Store.CodeAgreesOn store code afterCode ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode out.2.2.1) ∧
        recordedInvokeWith memory hooks floats allocator exec store platform address args results []=.ok (out,events) ∧
        match out.1 with
        | .Ok _ => target=⟨⟨Store.decodeStore view afterCode out.2.2.1,Spec.invocationFrame⟩,vals (out.2.2.2.2.val.map sourceValue)⟩ ∧
            (∀value∈out.2.2.2.2.val,Store.ValueInStore out.2.2.1 value)
        | .Err (.Trap _) => target=⟨⟨Store.decodeStore view afterCode out.2.2.1,Spec.invocationFrame⟩,[.TRAP]⟩
        | .Err _ => False ⦄ := by
  have bound : address.index.val<store.funcs.val.length := issued owner
  let function := store.funcs.val[address.index.val]
  have hf : store.funcs.val[address.index.val]?=some function := List.getElem?_eq_getElem bound
  have signatureBound : function.signature.val<store.types.val.length :=
    ((project code store valid).shape.functions function (List.mem_of_getElem? hf)).1
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
  have sourceEq := Spec.invocation_config invoked
  have checked := typed_arguments_accepted memory store (Store.decodeStore view code store) args signature.params
    (by simpa only [paramsEq] using typedArguments) (fun value member=>(owned value member).1)
  cases kind : function.code with
  | Wasm ii fi =>
    exact invoke_defined_world_chosen_matches admissible numericChoice vector 0 Abs.executable_language memory hooks floats allocator
      correct allocation interrupts view laws code compatible Inv
      (fun c s held=>(project c s held).toExecutableInv.toCertifiedApiStore.toCertifiedSupportedStore)
      update (fun c s held=>(project c s held).toExecutableInv.source_typed)
      sound preserve externs issuedResults exec store platform valid Spec.invocationFrame (Spec.invocation_frame_wf invoked)
      address function signature ii fi args results owner owned hf hs kind checked
      (fun c s held=>(project c s held).toExecutableInv.capacities) (fun c s held=>⟨(project c s held).values,(project c s held).frames⟩)
      (by simpa only [typeEq] using signatureFits) entryCapacity positiveFrames
      (by simpa only [sourceEq] using resources) available continuing noOverflow
      (by simpa only [sourceEq] using run) terminal
  | Host identity =>
    exact invoke_host_world_chosen_matches admissible 0 memory hooks floats allocator allocation interrupts view code
      Inv (fun c s held=>(project c s held).toExecutableInv.shape) exec store platform valid
      (project code store valid).toExecutableInv.well_formed (project code store valid).toExecutableInv.source_typed Spec.invocationFrame (Spec.invocation_frame_wf invoked)
      address function identity signature args results owner hf kind hs owned checked
      (fun p arguments defaults=>WP.spec_mono (sound 0 code store valid p identity arguments defaults) (by
        rintro answer ⟨afterCode,agrees,fresh,extension,typed,matching⟩
        exact ⟨afterCode,agrees,fresh,extension,typed,matching address function signature hf kind hs⟩))
      (fun p=>preserve code store valid identity p) (fun p=>externs code store valid identity p) (fun p=>issuedResults code store valid identity p)
      (fun c s held=>(project c s held).toExecutableInv.source_typed)
      (Nat.le_trans (by simpa only [typeEq] using signatureFits) (project code store valid).values) available continuing
      (fun p arguments defaults nextPlatform after returned=>noOverflow code store valid p identity arguments defaults nextPlatform after returned)
      (by simpa only [sourceEq] using run) terminal
end Exec.Theorems
