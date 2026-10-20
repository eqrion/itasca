import Exec.Theorems.Invocation.InvokeWorldChosenOutcomes
import Exec.Theorems.Invocation.InvokeHostWorldChosenOutcomes
import Exec.Theorems.Invocation.PublicExecutableChosenMatches
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
/-- Actual public invocation preserves one preselected policy through returning
callbacks and their newly published code. Resource errors retain selected
source prefixes; values and traps retain their exact final interpreted store. -/
theorem invoke_executable_world_chosen_outcomes {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vector : choices.vector=Spec.firstVectorChoice)
    {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p,hooks.interrupt p ⦃ _=>True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    (sound : HostWorldChosenSound memory hooks view (ExecutableInv view) choices)
    (preserve : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store=store.id) (issued : Store.ExternalIssued store (.Func address))
    (owned : ∀ value∈args.val,Store.ValueInStore store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (sourceFunction : funcinst) (params resultsTypes : List valtype)
    (sourceAt : (Store.decodeStore view code store).FUNCS[address.index.val]?=some sourceFunction)
    (sourceType : sourceFunction.TYPE=.mk_functype (.mk_list params) (.mk_list resultsTypes))
    (typedArguments : ResultsTyped (Store.decodeStore view code store) params (args.val.map sourceValue))
 :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ∃ afterCode,Store.CodeAgreesOn store code afterCode ∧ ExecutableInv view afterCode out.2.2.1 ∧
        Store_ok (Store.decodeStore view afterCode out.2.2.1) ∧ FrameStorePrefix store out.2.2.1 ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode out.2.2.1) ∧
        (out.1=.Ok () → (∃ events,Spec.ChoiceSteps choices 0 initial events
          ⟨⟨Store.decodeStore view afterCode out.2.2.1,Spec.invocationFrame⟩,vals (out.2.2.2.2.val.map sourceValue)⟩) ∧
          (∀ value∈out.2.2.2.2.val,Store.ValueInStore out.2.2.1 value)) ∧
        (∀ error,out.1=.Err error → ∃ events,ChosenEventfulInvocationError choices 0 initial events
          (Store.decodeStore view afterCode out.2.2.1) Spec.invocationFrame error) ⦄div := by
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
  have sourceEq := Spec.invocation_config invoked
  have checked := typed_arguments_accepted memory store (Store.decodeStore view code store) args signature.params
    (by simpa only [paramsEq] using typedArguments) (fun value member=>(owned value member).1)
  cases kind : function.code with
  | Wasm ii fi =>
    apply WP.dspec_mono (invoke_defined_world_chosen_outcomes admissible numericChoice vector 0 Abs.executable_language memory hooks floats allocator
      correct allocation interrupts view laws code compatible (ExecutableInv view)
      (fun _ _ held=>held.toCertifiedApiStore.toCertifiedSupportedStore) (fun _ _ _ held mutation=>held.update mutation)
      (fun _ _ held=>held.source_typed) sound preserve externs issuedResults exec store platform valid Spec.invocationFrame
      (Spec.invocation_frame_wf invoked) address function signature ii fi args results owner owned hf hs kind checked)
    rintro out ⟨afterCode,fresh,kept,agrees,extension,success,failure⟩
    refine ⟨afterCode,agrees,fresh,fresh.source_typed,kept,extension,?_,?_⟩
    · intro ok
      obtain ⟨typed,sourceOwned,⟨events,steps⟩,rawOwned⟩ := success ok
      exact ⟨⟨events,by simpa only [sourceEq] using steps⟩,rawOwned⟩
    · intro error failed
      simpa only [sourceEq] using failure error failed
  | Host identity =>
    have total := invoke_host_world_chosen_outcomes admissible 0 memory hooks floats allocator allocation interrupts view code
      (ExecutableInv view) (fun _ _ held=>held.shape) exec store platform valid valid.well_formed valid.source_typed
      Spec.invocationFrame (Spec.invocation_frame_wf invoked) address function identity signature args results owner hf kind hs owned checked
      (fun p arguments defaults => WP.spec_mono (sound 0 code store valid p identity arguments defaults) (by
        rintro answer ⟨afterCode,agrees,fresh,extension,typed,matching⟩
        exact ⟨afterCode,agrees,fresh,extension,typed,matching address function signature hf kind hs⟩))
      (fun p=>preserve code store valid identity p) (fun p=>externs code store valid identity p) (fun p=>issuedResults code store valid identity p)
    apply WP.dspec_mono (WP.spec_dspec _ _ _ total)
    rintro out ⟨afterCode,⟨fresh,agrees,kept,extension,count⟩,success,failure⟩
    refine ⟨afterCode,agrees,fresh,fresh.source_typed,kept,extension,?_,?_⟩
    · intro ok
      obtain ⟨typed,sourceOwned,step,rawOwned⟩ := success ok
      refine ⟨⟨[.call address.index.val (args.val.map sourceValue) (some (out.2.2.2.2.val.map sourceValue))],?_⟩,rawOwned⟩
      simpa only [sourceEq,List.append_nil] using Spec.ChoiceSteps.cons step (Spec.ChoiceSteps.refl 1 (step.wf admissible).2)
    · intro error failed
      simpa only [sourceEq] using failure error failed
end Exec.Theorems
