import Exec.Theorems.Invocation.InvokeEventful
import Exec.Interp.Invocation.InvokeDivergence
import Exec.Interp.Invocation.InvokePrefixDivergence
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

theorem invoke_defined_eventful_infinite_source
    [∀ compiled, StructuredMachine.FloatHeads (emission compiled)]
    [∀ compiled, StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀ compiled, StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.SimdProjection (emission compiled) compiled.simd.val compiled.v128_pool.val]
    [∀ compiled, StructuredMachine.TypedSelectHeads (emission compiled)]
    [∀ compiled, StructuredMachine.SupportedHeads (emission compiled)]
    [∀ compiled, StructuredMachine.ErasedHeads (emission compiled)]
    (language : Abs.Supported.Language allowed) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (sound : Platform.HostSound hooks (CertifiedSupportedStore emission allowed view code) (Store.decodeStore view code))
    (preserve : ∀ store, CertifiedSupportedStore emission allowed view code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀ store, CertifiedSupportedStore emission allowed view code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀ store, CertifiedSupportedStore emission allowed view code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer →
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedSupportedStore emission allowed view code store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.Function)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (divergent : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results=.div) :
    Spec.InfiniteSourceWithEvents
      ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ := by
  let entry := fun (after : runtime.store.Store M) (prepared : runtime.interp.Execution) => after=store ∧ ∃source,
    StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store prepared source
      (signature.results.val.map sourceType) 0 false ∧
    Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source ∧ source.ambient=ambient ∧
    StepH ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ [] (Abs.decode source)
  have accepted := invoke_divergent_arguments memory hooks floats allocator exec store platform address
    function signature args results owner hf hs divergent
  have reached : ∃after prepared p,entry after prepared ∧
      runtime.interp.invoke_with_loop2 memory hooks floats allocator prepared after p (.Ok ())=.div := by
    apply invoke_prefix_divergent_entry memory hooks floats allocator allocation exec store platform address
      function signature args results owner hf hs accepted (fun value member=>(owned value member).1) entry ?_ ?_ divergent
    · intro prepared p identity empty represented
      apply WP.spec_mono (call_defined_supported_entry memory hooks floats allocator allocation interrupts view code
        prepared store p certified.shape certified.storeSyntax certified.segmentBounds certified.typed certified.supported certified.compiled
        ambient ambientWf address function signature instanceIndex functionIndex args empty identity represented accepted owned hf hs hw)
      intro out effect success
      exact ⟨effect.1,effect.2 success⟩
    · intro after prepared p entered
      obtain ⟨same,source,invariant,ownedSource,ambientEq,sourceStep⟩ := entered
      subst after
      let machine : EventfulMachine emission allowed M P view code (signature.results.val.map sourceType) :=
        ⟨store,prepared,p,source,0,false,invariant,certified,ownedSource⟩
      apply WP.dspec_mono (eventful_loop_results memory hooks floats allocator
        (eventful_step_outcomes language memory hooks floats allocator correct allocation interrupts view laws code sound preserve externs issued _) machine)
      intro out outcome
      refine ⟨outcome.2.1,?_⟩
      intro success
      obtain ⟨values,events,typed,ownedValues,represented,reductions⟩ := outcome.2.2.2.1 success
      refine ⟨values,?_,Spec.resultsTyped_wf typed,?_,represented⟩
      · simpa only [show Code.valueType=Abs.valueType from funext valueType_eq_abs] using (Abs.results_type_of_typed typed).symm
      · intro value member
        exact Store.owned_result_fits _ value (ownedValues value member)
  obtain ⟨after,prepared,p,⟨same,source,invariant,ownedSource,ambientEq,sourceStep⟩,bodyDivergent⟩ := reached
  subst after
  let machine : EventfulMachine emission allowed M P view code (signature.results.val.map sourceType) :=
    ⟨store,prepared,p,source,0,false,invariant,certified,ownedSource⟩
  have infinite := eventful_loop_infinite memory hooks floats allocator
    (eventful_step_total language memory hooks floats allocator correct allocation interrupts view laws code sound preserve externs issued _) machine bodyDivergent
  exact infinite.prepend (StepsH.cons sourceStep (StepsH.refl invariant.typed.typed.decode_wf))
end Exec.Theorems
