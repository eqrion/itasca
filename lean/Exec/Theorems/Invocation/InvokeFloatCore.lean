import Exec.Theorems.Composition.FloatCore.FloatCoreEntryOutcomes
import Exec.Theorems.Composition.FloatCore.FloatCoreLoopReadback
import Exec.Theorems.Composition.FloatCore.FloatCoreErrors
import Exec.Interp.Invocation.InvokeMutable
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- Source meaning of the error classes reachable after accepting owned Core
arguments. Stronger local theorems retain exact resource and hook witnesses. -/
def FloatCoreInvocationError (initial : config) (s : _root_.store) (ambient : frame) : runtime.ExecError → Prop
  | .Trap trap => Interp.FloatCoreTrap trap ∧ StepsH initial [] ⟨⟨s,ambient⟩,[.TRAP]⟩
  | .Exhausted _ | .Terminated => True
  | _ => False

/-- Actual public invocation preserves the certified mutable store and agrees
with source execution on results and traps. Defined-only Core code includes
integer/control operations, scalar constants, globals, and scalar memory. -/
theorem invoke_defined_float_core_outcomes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedFloatCoreStore view code store) (hostFree : CoreHostFree store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.Function)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ())) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out =>
        (CertifiedFloatCoreStore view code out.2.2.1 ∧ Interp.FrameStoreMetadata store out.2.2.1 ∧
          Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
          out.2.2.1.elems = store.elems ∧ out.2.2.1.datas = store.datas) ∧
        (out.1 = .Ok () →
          signature.results.val.map Interp.sourceType = (out.2.2.2.2.val.map Interp.sourceValue).map Code.valueType ∧
          StepsH ⟨⟨Store.decodeStore view code store,ambient⟩,
            vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩ []
            ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,vals (out.2.2.2.2.val.map Interp.sourceValue)⟩) ∧
        (∀ error, out.1 = .Err error → FloatCoreInvocationError
          ⟨⟨Store.decodeStore view code store,ambient⟩,
            vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩
          (Store.decodeStore view code out.2.2.1) ambient error) ⦄div := by
  let entry (prepared : runtime.interp.Execution) : Prop := ∃ source,
    Interp.FloatCoreExecution view code store prepared source (signature.results.val.map Interp.sourceType) 0 false ∧
    Abs.Ownership.CoreOwned (Store.ownershipBounds store) source ∧ source.ambient = ambient ∧
    StepH ⟨⟨Store.decodeStore view code store,ambient⟩,
      vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩ [] (Abs.decode source)
  apply Interp.invoke_with_mutable_error_composition memory hooks floats allocator allocation exec store platform
    address function signature args results owner hf hs accepted (fun value member => (owned value member).1) entry
    (fun after => CertifiedFloatCoreStore view code after ∧ Interp.FrameStoreMetadata store after ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code after) ∧ after.elems = store.elems ∧ after.datas = store.datas)
    ⟨certified,.refl _,Spec.extend_store_refl _ (Store.decodeStore_wf view code store certified.shape certified.storeSyntax),rfl,rfl⟩
    (fun after values => signature.results.val.map Interp.sourceType = values.map Code.valueType ∧
      StepsH ⟨⟨Store.decodeStore view code store,ambient⟩,
        vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩ []
        ⟨⟨Store.decodeStore view code after,ambient⟩,vals values⟩)
    (fun after => FloatCoreInvocationError ⟨⟨Store.decodeStore view code store,ambient⟩,
      vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩
      (Store.decodeStore view code after) ambient) (by intro after reason; trivial)
  · intro prepared p identity empty arguments
    apply WP.spec_mono (call_defined_float_core_entry_outcomes memory hooks floats allocator allocation interrupts view code
      prepared store p certified ambient ambientWf address function signature instanceIndex functionIndex
      args empty identity arguments accepted owned hf hs hw)
    intro out post
    refine ⟨post.1,post.2.1,?_⟩
    intro error rejected
    obtain ⟨inst,compiled,hi,hc,cause⟩ := post.2.2 error rejected
    rcases cause.kind with rfl | rfl | rfl | rfl <;> trivial
  · intro prepared p entered
    obtain ⟨source,invariant,ownedSource,ambientEq,sourceStep⟩ := entered
    let machine : FloatCoreMachine M P view code (signature.results.val.map Interp.sourceType) :=
      ⟨store,prepared,p,source,0,false,invariant,certified,ownedSource,hostFree⟩
    apply WP.dspec_mono (float_core_loop memory hooks floats allocator correct allocation interrupts view laws code machine)
    intro out outcome
    obtain ⟨fresh,metadata,extension,readback⟩ := outcome.readback
    refine ⟨metadata.identity,metadata.functions,metadata.types,⟨fresh,metadata,extension,outcome.segment_vectors⟩,?_,?_⟩
    · intro success
      obtain ⟨values,tags,wellFormed,fits,represented,reductions⟩ := readback success
      refine ⟨values,tags,wellFormed,fits,represented,tags,?_⟩
      simpa only [machine,ambientEq,List.nil_append] using StepsH.cons sourceStep reductions
    · intro error rejected
      rcases outcome.error_kind rejected with ⟨trap,rfl,allowed⟩ | rfl | rfl | rfl | rfl
      · obtain ⟨_,count,positive,trapped⟩ := outcome.trap rejected
        refine ⟨allowed,?_⟩
        simpa only [machine,ambientEq,List.nil_append] using StepsH.cons sourceStep trapped.erase
      all_goals trivial
end Exec.Theorems
