import Exec.Theorems.Invocation.InvokeSliceOutcomes
import Exec.Theorems.Invocation.InvokeSliceDivergence
import Exec.Interp.Relations.TypedArguments
import Exec.Spec.Invocation
import Exec.Store.Invariant.Typing
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- Static store and compiler evidence for the integer slice. No field assumes
interpreter correctness; producing these certificates from compilation and
instantiation remains a separate obligation. -/
structure CertifiedSliceStore {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) : Prop where
  shape : Store.Shape view store
  storeSyntax : Store.StoreSyntax code store
  typed : Abs.FunctionsTyped (Store.decodeStore view code store)
  slice : Abs.StoreSlice (Store.decodeStore view code store)
  compiled : Interp.CompiledFunctions code store
  segmentBounds : Store.SegmentBounds store

/-- Resolve actual retained function certificates from slice-wide static
coverage. Host functions are excluded by the independent source restriction. -/
theorem CertifiedSliceStore.resolve {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} (certified : CertifiedSliceStore view code store)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.types.FuncType)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature) :
    ∃ instanceIndex functionIndex inst compiled functions declared body epilogue,
      function.code = .Wasm instanceIndex functionIndex ∧
      store.instances.val[instanceIndex.val]? = some inst ∧
      inst.module.functions.val[functionIndex.val]? = some compiled ∧
      code instanceIndex.val inst.module functionIndex.val =
        .FUNC (.mk_uN compiled.type_index.val) (declared.map local.LOCAL) body ∧
      Interp.FunctionTable store inst functions ∧
      Code.FunctionCode (Store.decodeInstance store inst).TYPES functions
        (signature.params.val.map Interp.sourceType) declared (signature.results.val.map Interp.sourceType)
        body compiled epilogue := by
  let source : Abs.AState := ⟨Store.decodeStore view code store, Spec.invocationFrame, [], []⟩
  have sliced : Abs.SliceState source := ⟨by simp [source, Forall], certified.slice⟩
  obtain ⟨instanceIndex, functionIndex, wasm⟩ := Interp.slice_function_defined view code store source rfl sliced address function hf
  obtain ⟨inst, compiled, actualSignature, functions, declared, body, epilogue,
      hi, hc, signatureLookup, sourceCode, table, certificate⟩ :=
    certified.compiled function (List.mem_of_getElem? hf) instanceIndex functionIndex wasm
  have same : actualSignature = signature := Option.some.inj (signatureLookup.symm.trans hs)
  subst actualSignature
  exact ⟨instanceIndex, functionIndex, inst, compiled, functions, declared, body, epilogue,
    wasm, hi, hc, sourceCode, table, certificate⟩

/-- Public invocation from the generated fun_invoke configuration: source-typed
owned arguments cannot be rejected as BadArguments, and successes and traps
match source execution. The integer slice leaves the exact store unchanged. -/
theorem invoke_certified_slice {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedSliceStore view code store)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (typed : ResultsTyped (Store.decodeStore view code store) (signature.params.val.map Interp.sourceType)
      (args.val.map Interp.sourceValue))
    (nonreference : ∀ ty ∈ signature.results.val.map Interp.sourceType, ty ≠ .FUNCREF ∧ ty ≠ .EXTERNREF)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val
      (args.val.map Interp.sourceValue) initial) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => out.2.2.1 = store ∧
        (out.1 = .Ok () → StepsH initial []
          ⟨⟨Store.decodeStore view code store, Spec.invocationFrame⟩,
            vals (out.2.2.2.2.val.map Interp.sourceValue)⟩) ∧
        (∀ error, out.1 = .Err error →
          SliceInvocationError initial (Store.decodeStore view code store) Spec.invocationFrame error) ⦄div := by
  obtain ⟨instanceIndex, functionIndex, inst, compiled, functions, declared, body, epilogue,
    wasm, hi, hc, sourceCode, table, certificate⟩ := certified.resolve address function signature hf hs
  have accepted := Interp.typed_arguments_accepted memory store (Store.decodeStore view code store)
    args signature.params typed (fun value member => (owned value member).1)
  rw [Spec.invocation_config invoked]
  exact invoke_defined_slice_outcomes memory hooks floats allocator allocation interrupts view code exec store platform
    certified.shape certified.storeSyntax certified.typed certified.slice Spec.invocationFrame (Spec.invocation_frame_wf invoked)
    address function signature instanceIndex functionIndex inst compiled functions declared body epilogue args results owner
    certified.compiled nonreference owned certificate table hf hs wasm hi hc sourceCode accepted

/-- Actual public divergence gives source executions of every finite length,
from the generated invocation configuration and under the same static evidence. -/
theorem invoke_certified_slice_divergence {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedSliceStore view code store)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (nonreference : ∀ ty ∈ signature.results.val.map Interp.sourceType, ty ≠ .FUNCREF ∧ ty ≠ .EXTERNREF)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val
      (args.val.map Interp.sourceValue) initial)
    (divergent : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results = .div)
    (requested : Nat) :
    ∃ final count, Spec.StepsHN count initial [] final ∧ requested ≤ count := by
  obtain ⟨instanceIndex, functionIndex, inst, compiled, functions, declared, body, epilogue,
    wasm, hi, hc, sourceCode, table, certificate⟩ := certified.resolve address function signature hf hs
  rw [Spec.invocation_config invoked]
  exact invoke_defined_slice_no_silent_divergence memory hooks floats allocator allocation interrupts view code exec store platform
    certified.shape certified.storeSyntax certified.typed certified.slice Spec.invocationFrame (Spec.invocation_frame_wf invoked)
    address function signature instanceIndex functionIndex inst compiled functions declared body epilogue args results owner
    certified.compiled nonreference owned certificate table hf hs wasm hi hc sourceCode divergent requested
end Exec.Theorems
