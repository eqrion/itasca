import Itasca.Runtime.Integration.Execution.Dispatch.Entry
import Itasca.Runtime.Interp.Calls.CallCauses
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt

/-- Entry rejections retain the exact allocator, frame limit, value limit, or interrupt witness. -/
theorem call_defined_supported_entry_outcomes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (before : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store)
    (functionTyping : Interp.CoreFunctionsTyped view code store)
    (coveredFunctions : SourceMachine.FunctionsSupported (Store.decodeStore view code store))
    (compiledFunctions : Interp.Machine.CompiledFunctions code store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.wasm_types.FuncType) (instanceIndex functionIndex : Usize)
    (args : Slice runtime.Value)
    (empty : before.frames.val = []) (identity : before.store = store.id)
    (arguments : Interp.ValuesAt before.slots.val 0 (args.val.map Interp.sourceValue))
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()))
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex) :
    runtime.interp.call memory hooks floats allocator before store platform address 0#usize ⦃ out =>
      out.2.2.1 = store ∧ (out.1 = .Ok () → ∃ entry,
        Interp.Machine.Execution view code store out.2.1 entry
          (signature.results.val.map Interp.sourceType) 0 false ∧
        SourceMachine.Ownership.StatefulOwned (Store.ownershipBounds store) entry ∧
        entry.ambient = ambient ∧
        StepH ⟨⟨Store.decodeStore view code store, ambient⟩,
          vals (args.val.map Interp.sourceValue) ++ [.CALL_ADDR address.index.val]⟩ [] (SourceMachine.decode entry)) ∧
      (∀ error, out.1 = .Err error → ∃ inst compiled,
        store.instances.val[instanceIndex.val]? = some inst ∧
        inst.module.functions.val[functionIndex.val]? = some compiled ∧
        Interp.CallCause allocator hooks before store platform 0#usize compiled error) ⦄ := by
  obtain ⟨out,returned,unchanged,entered⟩ := WP.spec_imp_exists
    (call_defined_supported_entry memory hooks floats allocator allocation interrupts view code
      before store platform shaped sourceSyntax bounds functionTyping coveredFunctions compiledFunctions ambient ambientWf address function signature instanceIndex functionIndex
      args empty identity arguments accepted owned hf hs hw)
  obtain ⟨inst,compiled,actualSignature,declared,body,epilogue,hi,hc,actualHs,table,certificate,bindings,lookup⟩ :=
    compiledFunctions.defined view functionTyping address function instanceIndex functionIndex hf hw
  have params : compiled.param_slots.val ≤ compiled.local_slots.val := by
    rw [certificate.2.parameterSlots,certificate.2.localSlots,Compiler.slots_append]
    omega
  have causes := Interp.call_wasm_causes memory hooks floats allocator allocation interrupts before store platform address 0#usize
    function instanceIndex functionIndex inst compiled hf hw hi hc params certificate.2.capacity
  rw [returned] at causes ⊢
  simp only [WP.spec_ok] at causes ⊢
  exact ⟨unchanged,entered,fun error rejected => ⟨inst,compiled,hi,hc,causes error rejected⟩⟩
end Itasca.Runtime.Integration
