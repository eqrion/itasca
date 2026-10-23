import Exec.Theorems.Api.DefinedEventfulInvocationCauses
import Exec.Theorems.Composition.Eventful.EventfulSourceResources
import Exec.Theorems.Api.InvocationEntryResources
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- The public source entry and actual runtime history identify the machine
whose source needs and current limits explain a failure. -/
def ReachedEventfulResourceCause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (expected : List valtype)
    (Inv : runtime.store.Store M → Prop) (store : runtime.store.Store M)
    (initial : config) (after : runtime.store.Store M) (error : runtime.ExecError) : Prop :=
  ∃ first previous : EventfulMachine emission allowed M P view code expected,
    first.store=store ∧ StepH initial [] (Abs.decode first.source) ∧
    ∃ count events afterExec afterPlatform,
      Spec.Iterations (EventfulTransition memory hooks floats allocator) count first events previous ∧
      StepsH initial events (Abs.decode previous.source) ∧ Inv previous.store ∧
      runtime.interp.step memory hooks floats allocator previous.exec previous.store previous.platform=
        .ok (.Err error,afterExec,after,afterPlatform) ∧
      EventfulSourceResourceCause hooks allocator previous (.Err error,afterExec,after,afterPlatform) error

theorem DefinedEventfulInvocationCause.source_resources {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {Inv : runtime.store.Store M → Prop}
    (capacities : ∀store,Inv store → Store.FunctionCapacities code store)
    {exec : runtime.interp.Execution} {store : runtime.store.Store M}
    {ambient : frame} {address : runtime.FuncAddr} {signature : Itasca.types.FuncType}
    {instanceIndex functionIndex : Usize} {args : Slice runtime.Value} {results : alloc.vec.Vec runtime.Value}
    {after : runtime.store.Store M} {error : runtime.ExecError}
    (valid : Inv store) (typed : CoreFunctionsTyped view code store)
    (function : runtime.store.FuncInst)
    (hf : store.funcs.val[address.index.val]?=some function) (hw : function.code=.Wasm instanceIndex functionIndex)
    (cause : DefinedEventfulInvocationCause (emission:=emission) (allowed:=allowed)
      memory hooks floats allocator view code Inv exec store ambient address signature instanceIndex functionIndex args results after error) :
    CanonicalInvocationResourceCause allocator hooks
      ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩
      (Store.decodeStore view code store) (Store.decodeFuncType signature) address.index.val
      store.limits.max_values.val store.limits.max_frames.val error ∨
    ReachedEventfulResourceCause (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code
      (signature.results.val.map sourceType) Inv store
      ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ after error := by
  rcases cause with ⟨same,setup⟩ | ⟨same,prepared,p,out,inst,compiled,identity,empty,argsAt,hi,hc,actual,failed,afterEq,entry⟩ |
    ⟨first,same,firstValid,ambientEq,sourceStep,result,afterEq,failure⟩ | ⟨rfl,values,events,typedResults,source,refused⟩
  · exact Or.inl (InvocationResourceCause.canonical _ _ _ setup)
  · exact Or.inl (CallCause.invocation_canonical view code _ (capacities store valid) typed address function
      instanceIndex functionIndex inst compiled hf hw hi hc empty entry)
  · apply Or.inr
    obtain ⟨previous,count,events,afterExec,afterStore,afterPlatform,history,previousValid,actual,causal,finished⟩ := failure
    have storeEq : afterStore=after := by
      rw [←finished] at afterEq
      exact afterEq
    subst afterStore
    obtain ⟨steps,source⟩ := EventfulMachine.history_source history
    refine ⟨first,previous,same,sourceStep,count,events,afterExec,afterPlatform,history,?_,previousValid,actual,
      causal.source_resources (capacities previous.store previousValid)⟩
    simpa only [List.nil_append] using StepsH.cons sourceStep source.erase
  · apply Or.inl; apply Or.inl; apply Or.inr
    obtain ⟨n,amount,refusal⟩ := refused
    exact ⟨results,n,by simpa only [Store.decodeFuncType,List.length_map] using Nat.le_trans (Nat.le_of_eq amount) (Nat.sub_le _ _),refusal⟩
end Exec.Theorems
