import Exec.Theorems.Composition.Entry
import Exec.Interp.Calls.CallStackEntry
import Exec.Interp.Machines.Slice.SliceExecution

namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- Checked API arguments and a retained compiler certificate establish the
complete invocation frame relation through the actual defined-function call.
The source entry is reached by a generated CALL_ADDR step. -/
theorem call_defined_entry_certified {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (before : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (shape : Store.Shape view store) (storeSyntax : Store.StoreSyntax code store)
    (functionsTyped : Abs.FunctionsTyped (Store.decodeStore view code store))
    (slice : Abs.StoreSlice (Store.decodeStore view code store))
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.Function)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (functions : List functype) (declared : List valtype) (body : List instr) (epilogue : U32)
    (args : Slice runtime.Value)
    (empty : before.frames.val = []) (identity : before.store = store.id)
    (arguments : Interp.ValuesAt before.slots.val 0 (args.val.map Interp.sourceValue))
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()))
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
      .FUNC (.mk_uN compiled.type_index.val) (declared.map local.LOCAL) body) :
    runtime.interp.call memory hooks floats allocator before store platform address 0#usize ⦃ out =>
      out.2.2.1 = store ∧ (out.1 = .Ok () →
        ∃ defaults, Abs.defaultLocals (declared.map local.LOCAL) = some defaults ∧
          let entry := Abs.entryState (Store.decodeStore view code store) ambient address.index.val
            (Store.decodeInstance store inst) (signature.results.val.map Interp.sourceType)
            body (args.val.map Interp.sourceValue) defaults
          Interp.SliceExecution store out.2.1 entry
            (signature.results.val.map Interp.sourceType) 0 false ∧
          StepH ⟨⟨Store.decodeStore view code store, ambient⟩,
            vals (args.val.map Interp.sourceValue) ++ [.CALL_ADDR address.index.val]⟩ [] (Abs.decode entry)) ⦄ := by
  obtain ⟨defaults, default, typed, sourceSlice, sourceStep⟩ := defined_entry_source memory view code store
    shape storeSyntax functionsTyped slice ambient ambientWf address function signature instanceIndex functionIndex
    inst (.mk_uN compiled.type_index.val) declared body args hf hs hw hi source accepted owned
  have tags := checked_argument_type_tags memory store args signature.params accepted
  apply WP.spec_mono (Interp.call_wasm_stack memory hooks floats allocator allocation interrupts
    before store platform address 0#usize function signature instanceIndex functionIndex inst compiled epilogue
    functions declared body (args.val.map Interp.sourceValue) defaults certificate hf hs hw hi hc table identity
    arguments tags default [] [] empty (.nil _))
  intro out result
  refine ⟨result.1, fun success => ⟨defaults, default, ?_, sourceStep⟩⟩
  obtain ⟨stack, top, ready⟩ := result.2 success
  obtain ⟨pc, cursor⟩ := ready.cursor
  have zero : pc = 0 := by
    have position := cursor.pc
    simp only [top, Option.map_some, Option.some.injEq] at position
    scalar_tac
  subst pc
  exact ⟨typed, sourceSlice, Abs.entry_result _ _ _ _ _ _ _ _, stack, cursor⟩

end Exec.Theorems
