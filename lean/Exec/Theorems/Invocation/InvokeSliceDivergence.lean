import Exec.Theorems.Invocation.InvokeSlice
import Exec.Interp.Invocation.InvokeDivergence
import Exec.Interp.Machines.Slice.SliceDivergence
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- Divergence of the actual public wrapper entails arbitrarily long counted
source executions. Allocation, marshaling, and readback cannot introduce an
independent divergence under their normal-return laws. -/
theorem invoke_defined_slice_no_silent_divergence {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (shape : Store.Shape view store) (storeSyntax : Store.StoreSyntax code store)
    (functionsTyped : Abs.FunctionsTyped (Store.decodeStore view code store))
    (slice : Abs.StoreSlice (Store.decodeStore view code store))
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (functions : List functype) (declared : List valtype) (body : List instr) (epilogue : U32)
    (args : Slice runtime.Value)
    (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (compiledFunctions : Interp.CompiledFunctions code store)
    (nonreference : ∀ ty ∈ signature.results.val.map Interp.sourceType, ty ≠ .FUNCREF ∧ ty ≠ .EXTERNREF)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (certificate : Code.FunctionCode (Store.decodeInstance store inst).TYPES functions
      (signature.params.val.map Interp.sourceType) declared (signature.results.val.map Interp.sourceType)
      body compiled epilogue)
    (table : Interp.FunctionTable store inst functions)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (hi : store.instances.val[instanceIndex.val]? = some inst)
    (hc : inst.module.functions.val[functionIndex.val]? = some compiled)
    (source : code instanceIndex.val inst.module functionIndex.val =
      .FUNC (.mk_uN compiled.type_index.val) (declared.map local.LOCAL) body)
    (divergent : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results = .div)
    (requested : Nat) :
    ∃ final count, Spec.StepsHN count
      ⟨⟨Store.decodeStore view code store, ambient⟩,
        vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩ [] final ∧ requested ≤ count := by
  let entry (prepared : runtime.interp.Execution) : Prop := ∃ defaults,
    Abs.defaultLocals (declared.map local.LOCAL) = some defaults ∧
      let initial := Abs.entryState (Store.decodeStore view code store) ambient address.index.val
        (Store.decodeInstance store inst) (signature.results.val.map Interp.sourceType)
        body (args.val.map Interp.sourceValue) defaults
      Interp.SliceExecution store prepared initial (signature.results.val.map Interp.sourceType) 0 false ∧
      StepH ⟨⟨Store.decodeStore view code store, ambient⟩,
        vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩ [] (Abs.decode initial)
  have accepted := Interp.invoke_divergent_arguments memory hooks floats allocator exec store platform address
    function signature args results owner hf hs divergent
  have reached : ∃ prepared p, entry prepared ∧
      runtime.interp.invoke_with_loop1 memory hooks floats allocator prepared store p (.Ok ()) = .div := by
    apply Interp.invoke_divergent_entry memory hooks floats allocator allocation exec store platform address
      function signature args results owner hf hs accepted (fun value member => (owned value member).1)
      entry (fun _ => True) ?_ ?_ divergent
    · intro prepared p identity empty arguments
      exact call_defined_entry_certified memory hooks floats allocator allocation interrupts view code prepared store p
        shape storeSyntax functionsTyped slice ambient ambientWf address function signature instanceIndex functionIndex
        inst compiled functions declared body epilogue args empty identity arguments accepted owned certificate table hf hs hw hi hc source
    · intro prepared p entered
      obtain ⟨defaults, default, invariant, sourceStep⟩ := entered
      let initial := Abs.entryState (Store.decodeStore view code store) ambient address.index.val
        (Store.decodeInstance store inst) (signature.results.val.map Interp.sourceType)
        body (args.val.map Interp.sourceValue) defaults
      let machine : Interp.SliceMachine P store (Store.decodeStore view code store) ambient
          (signature.results.val.map Interp.sourceType) (sizeOf initial) :=
        ⟨prepared, p, initial, 0, false, invariant, Abs.codeBound_initial initial, rfl, rfl⟩
      apply WP.dspec_mono (Interp.slice_loop_readback memory hooks floats allocator allocation interrupts
        view code rfl compiledFunctions machine nonreference)
      rintro out ⟨unchanged, success⟩
      refine ⟨unchanged, fun ok => ?_⟩
      obtain ⟨values, tags, wellformed, fits, represented, reductions⟩ := success ok
      exact ⟨values, tags, wellformed, fits, represented, trivial⟩
  obtain ⟨prepared, p, ⟨defaults, default, invariant, sourceStep⟩, bodyDivergent⟩ := reached
  let initial := Abs.entryState (Store.decodeStore view code store) ambient address.index.val
    (Store.decodeInstance store inst) (signature.results.val.map Interp.sourceType)
    body (args.val.map Interp.sourceValue) defaults
  let machine : Interp.SliceMachine P store (Store.decodeStore view code store) ambient
      (signature.results.val.map Interp.sourceType) (sizeOf initial) :=
    ⟨prepared, p, initial, 0, false, invariant, Abs.codeBound_initial initial, rfl, rfl⟩
  obtain ⟨final, count, history, reductions, cost⟩ := Interp.slice_no_silent_divergence memory hooks floats allocator
    allocation interrupts view code rfl compiledFunctions machine bodyDivergent requested
  exact ⟨Abs.decode final.source, count + 1, by simpa using Spec.StepsHN.cons sourceStep reductions, by omega⟩
end Exec.Theorems
