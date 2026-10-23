import Exec.Theorems.Invocation.InvokeSupported
import Exec.Theorems.Api.InvocationCanonicalResources
import Exec.Theorems.Composition.Supported.SupportedSourceResources
import Exec.Interp.Invocation.InvokeMutableCauses
import Exec.Theorems.Api.InvocationBoundary
import Exec.Theorems.Composition.Supported.SupportedBoundaries
import Exec.Theorems.Composition.Supported.SupportedEntryOutcomes
import Exec.Theorems.Composition.Supported.SupportedLoopReadback
import Exec.Theorems.Composition.Supported.SupportedErrors
import Exec.Interp.Invocation.InvokeMutable
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Actual invocation uses the common supported machine. Results and traps
retain source execution, the updated store, and segment counts. -/
theorem invoke_defined_supported_resources
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
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedSupportedStore emission allowed view code store) (hostFree : CoreHostFree store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (capacities : Store.FunctionCapacities code store)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ())) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out =>
        (CertifiedSupportedStore emission allowed view code out.2.2.1 ∧ Interp.FrameStoreMetadata store out.2.2.1 ∧
          Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
          Store.SegmentCounts store out.2.2.1 ∧ out.2.2.1.limits = store.limits) ∧
        (out.1 = .Ok () →
          signature.results.val.map Interp.sourceType = (out.2.2.2.2.val.map Interp.sourceValue).map Code.valueType ∧
          StepsH ⟨⟨Store.decodeStore view code store,ambient⟩,
            vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩ []
            ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,vals (out.2.2.2.2.val.map Interp.sourceValue)⟩) ∧
        (∀ error, out.1 = .Err error → SupportedInvocationError
          ⟨⟨Store.decodeStore view code store,ambient⟩,
            vals (args.val.map sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩
          (Store.decodeStore view code out.2.2.1) ambient error ∧ CanonicalInvocationResourceCause allocator hooks
          ⟨⟨Store.decodeStore view code store,ambient⟩,
            vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩
          (Store.decodeStore view code store) (Store.decodeFuncType signature) address.index.val
          store.limits.max_values.val store.limits.max_frames.val error) ⦄div := by
  let entry (prepared : runtime.interp.Execution) : Prop := ∃ source,
    Interp.StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store prepared source (signature.results.val.map Interp.sourceType) 0 false ∧
    Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source ∧ source.ambient = ambient ∧
    StepH ⟨⟨Store.decodeStore view code store,ambient⟩,
      vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩ [] (Abs.decode source)
  apply Interp.invoke_with_mutable_causes_composition memory hooks floats allocator allocation exec store platform
    address function signature args results owner hf hs accepted (fun value member => (owned value member).1) entry
    (fun after => CertifiedSupportedStore emission allowed view code after ∧ Interp.FrameStoreMetadata store after ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code after) ∧ Store.SegmentCounts store after ∧ after.limits = store.limits)
    ⟨certified,.refl _,Spec.extend_store_refl _ (Store.decodeStore_wf view code store certified.shape certified.storeSyntax),.refl store,rfl⟩
    (fun after values => signature.results.val.map Interp.sourceType = values.map Code.valueType ∧
      StepsH ⟨⟨Store.decodeStore view code store,ambient⟩,
        vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩ []
        ⟨⟨Store.decodeStore view code after,ambient⟩,vals values⟩)
    (fun after error => SupportedInvocationError
      ⟨⟨Store.decodeStore view code store,ambient⟩,
        vals (args.val.map sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩
      (Store.decodeStore view code after) ambient error ∧ CanonicalInvocationResourceCause allocator hooks ⟨⟨Store.decodeStore view code store,ambient⟩,
      vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩
      (Store.decodeStore view code store) (Store.decodeFuncType signature) address.index.val
      store.limits.max_values.val store.limits.max_frames.val error)
  · intro after error cause
    rcases cause.kind with rfl | rfl
    · refine ⟨True.intro,?_⟩
      apply Or.inl
      simpa only [InvocationResourceCause,signatureWords,Store.decodeFuncType,typeSlots] using cause
    · refine ⟨True.intro,?_⟩
      apply Or.inl
      rcases cause with ⟨n,amount,refused⟩ | ⟨n,amount,refused⟩
      · exact Or.inl ⟨exec.slots,n,amount,refused⟩
      · exact Or.inr ⟨results,n,by simpa only [Store.decodeFuncType,List.length_map] using Nat.le_trans (Nat.le_of_eq amount) (Nat.sub_le _ _),refused⟩
  · intro prepared p identity empty arguments
    apply WP.spec_mono (call_defined_supported_entry_outcomes memory hooks floats allocator allocation interrupts view code
      prepared store p certified.shape certified.storeSyntax certified.segmentBounds certified.typed certified.supported certified.compiled ambient ambientWf address function signature instanceIndex functionIndex
      args empty identity arguments accepted owned hf hs hw)
    intro out post
    refine ⟨post.1,post.2.1,?_⟩
    intro error rejected
    obtain ⟨inst,compiled,hi,hc,cause⟩ := post.2.2 error rejected
    refine ⟨?_,?_⟩
    · rcases cause.kind with rfl | rfl | rfl | rfl <;> trivial
    · cases error with
      | Terminated => exact ⟨p,cause⟩
      | Exhausted reason =>
        cases reason with
        | CallStack =>
          apply Or.inl
          change store.limits.max_frames.val ≤ prepared.frames.length at cause
          have zero : prepared.frames.length = 0 := by simp only [alloc.vec.Vec.length,empty,List.length_nil]
          have limit : store.limits.max_frames.val = 0 := by omega
          simp [limit]
        | Values =>
          obtain ⟨words,capacity,bound⟩ := function_canonical_capacity_decoded view code store capacities certified.typed
            address function instanceIndex functionIndex inst compiled hf hw hi hc
          change store.limits.max_values.val<(0#usize).val+compiled.slot_count.val at cause
          exact Or.inr (Or.inl ⟨words,capacity,by scalar_tac⟩)
        | Allocation =>
          obtain ⟨words,capacity,bound⟩ := function_canonical_capacity_decoded view code store capacities certified.typed
            address function instanceIndex functionIndex inst compiled hf hw hi hc
          apply Or.inr;apply Or.inl;refine ⟨words,capacity,?_⟩
          rcases CallCause.source_allocation bound cause with ⟨n,amount,refused⟩ | refused
          · exact Or.inl ⟨prepared.slots,n,by simpa using amount,refused⟩
          · exact Or.inr ⟨prepared.frames,refused⟩
        | Objects => trivial
      | _ => trivial
  · intro prepared p entered
    obtain ⟨source,invariant,ownedSource,ambientEq,sourceStep⟩ := entered
    let machine : SupportedMachine emission allowed M P view code (signature.results.val.map Interp.sourceType) :=
      ⟨store,prepared,p,source,0,false,invariant,certified,ownedSource,hostFree⟩
    apply WP.dspec_mono (supported_loop language memory hooks floats allocator correct allocation interrupts view laws code machine)
    intro out outcome
    obtain ⟨fresh,metadata,extension,segments,readback⟩ := outcome.readback
    refine ⟨metadata.identity,metadata.functions,metadata.types,⟨fresh,metadata,extension,segments,outcome.limits⟩,?_,?_⟩
    · intro success
      obtain ⟨values,tags,wellFormed,fits,represented,reductions⟩ := readback success
      refine ⟨values,tags,wellFormed,fits,represented,tags,?_⟩
      simpa only [machine,ambientEq,List.nil_append] using StepsH.cons sourceStep reductions
    · intro error rejected
      refine ⟨?_,?_⟩
      · rcases outcome.error_kind rejected with ⟨trap,rfl,allowed⟩ | rfl | rfl | rfl | rfl
        · obtain ⟨_,count,positive,trapped⟩ := outcome.trap rejected
          refine ⟨allowed,?_⟩
          simpa only [machine,ambientEq,List.nil_append] using StepsH.cons sourceStep trapped.erase
        all_goals trivial
      · cases error with
        | Terminated => exact outcome.interrupted rejected
        | Exhausted reason =>
          cases reason with
          | CallStack =>
            obtain ⟨final,reductions,depth⟩ := outcome.frame_depth rejected
            exact Or.inr ⟨final,by simpa only [machine,List.nil_append] using StepsH.cons sourceStep reductions,depth⟩
          | Values =>
            obtain ⟨state,callee,base,words,reductions,site,capacity,exceeds⟩ := outcome.source_values capacities rejected
            exact Or.inr (Or.inr ⟨state,callee,base,words,by simpa only [machine,List.nil_append] using StepsH.cons sourceStep reductions,site,capacity,exceeds⟩)
          | Allocation =>
            obtain ⟨state,reductions,refused⟩ := outcome.source_allocation capacities rejected
            exact Or.inr (Or.inr ⟨state,by simpa only [machine,List.nil_append] using StepsH.cons sourceStep reductions,refused⟩)
          | Objects =>
            rcases outcome.error_kind rejected with ⟨trap,impossible,allowed⟩ | impossible | impossible | impossible | impossible <;>
              cases impossible
        | _ => trivial

end Exec.Theorems
