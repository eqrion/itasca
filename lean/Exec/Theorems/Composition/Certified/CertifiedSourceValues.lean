import Exec.Theorems.Composition.Certified.CertifiedSlice
import Exec.Theorems.Invocation.InvokeSourceValues
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- Values exhaustion at public invocation has a decoded source storage cause. -/
theorem invoke_certified_source_values {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedSliceStore view code store)
    (capacities : Store.FunctionCapacities code store)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (typed : ResultsTyped (Store.decodeStore view code store) (signature.params.val.map Interp.sourceType)
      (args.val.map Interp.sourceValue))
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val
      (args.val.map Interp.sourceValue) initial) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => out.2.2.1 = store ∧ (out.1 = .Err (.Exhausted .Values) →
        InvocationValuesCause initial (Store.decodeStore view code store)
          (Store.decodeFuncType signature) address.index.val store.limits.max_values.val) ⦄div := by
  obtain ⟨instanceIndex, functionIndex, inst, compiled, functions, declared, body, epilogue,
    wasm, hi, hc, sourceCode, table, certificate⟩ := certified.resolve address function signature hf hs
  have accepted := Interp.typed_arguments_accepted memory store (Store.decodeStore view code store)
    args signature.params typed (fun value member => (owned value member).1)
  rw [Spec.invocation_config invoked]
  exact invoke_defined_source_values memory hooks floats allocator allocation interrupts view code exec store platform
    certified.shape certified.storeSyntax certified.typed certified.slice Spec.invocationFrame (Spec.invocation_frame_wf invoked)
    address function signature instanceIndex functionIndex inst compiled functions declared body epilogue args results owner
    certified.compiled capacities owned certificate table hf hs wasm hi hc sourceCode accepted

end Exec.Theorems
