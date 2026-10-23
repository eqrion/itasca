import Exec.Theorems.Composition.SignatureWords
import Exec.Theorems.Invocation.InvokeSliceReferenceOutcomes
import Exec.Interp.Relations.SourceValueCauses
import Exec.Interp.Invocation.InvokeResourceCauses
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- The actual source storage requirements behind a Values rejection: public
signature buffers, entry frame storage, or a reachable call sharing arguments. -/
def InvocationValuesCause (initial : config) (store : _root_.store) (signature : functype)
    (address : funcaddr) (limit : Nat) : Prop :=
  limit < signatureWords signature ∨
  (∃ words, Interp.SourceFunctionCapacity store address words ∧ limit < words) ∨
  ∃ (state : Abs.AState) (callee : funcaddr) (base words : Nat),
    StepsH initial [] (Abs.decode state) ∧ Interp.SourceCallSite state callee base ∧
    Interp.SourceFunctionCapacity store callee words ∧ limit < base + words

/-- Actual public invocation relates Values exhaustion to decoded source
storage requirements, including exact shared call-argument positions. -/
theorem invoke_defined_source_values {M P F A : Type}
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
    (capacities : Store.FunctionCapacities code store)
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
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ())) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => out.2.2.1 = store ∧ (out.1 = .Err (.Exhausted .Values) →
        InvocationValuesCause
          ⟨⟨Store.decodeStore view code store, ambient⟩,
            vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩
          (Store.decodeStore view code store) (Store.decodeFuncType signature) address.index.val
          store.limits.max_values.val) ⦄div := by
  let entry (prepared : runtime.interp.Execution) : Prop := ∃ defaults,
    Abs.defaultLocals (declared.map local.LOCAL) = some defaults ∧
      let initial := Abs.entryState (Store.decodeStore view code store) ambient address.index.val
        (Store.decodeInstance store inst) (signature.results.val.map Interp.sourceType)
        body (args.val.map Interp.sourceValue) defaults
      Interp.SliceExecution store prepared initial (signature.results.val.map Interp.sourceType) 0 false ∧
      StepH ⟨⟨Store.decodeStore view code store, ambient⟩,
        vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩ [] (Abs.decode initial)
  let failure := InvocationValuesCause
    ⟨⟨Store.decodeStore view code store, ambient⟩,
      vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩
    (Store.decodeStore view code store) (Store.decodeFuncType signature) address.index.val store.limits.max_values.val
  have composed : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => out.2.2.1 = store ∧ (out.1 = .Ok () → True) ∧
        (∀ error, out.1 = .Err error → error = .Exhausted .Values → failure) ⦄div := by
    apply Interp.invoke_with_resource_composition memory hooks floats allocator allocation exec store platform
      address function signature args results owner hf hs accepted (fun value member => (owned value member).1) entry
      (fun _ => True) (fun error => error = .Exhausted .Values → failure)
    · intro error cause same
      subst error
      apply Or.inl
      simpa only [Interp.InvocationResourceCause, signatureWords, Store.decodeFuncType, Interp.typeSlots] using cause
    · intro prepared p identity empty arguments
      obtain ⟨out, returned, unchanged, entered⟩ := WP.spec_imp_exists
        (call_defined_entry_certified memory hooks floats allocator allocation interrupts view code prepared store p
          shape storeSyntax functionsTyped slice ambient ambientWf address function signature instanceIndex functionIndex
          inst compiled functions declared body epilogue args empty identity arguments accepted owned certificate table hf hs hw hi hc source)
      have params : compiled.param_slots.val ≤ compiled.local_slots.val := by
        rw [certificate.parameterSlots, certificate.localSlots, Code.slots_append]
        omega
      have causes := Interp.call_wasm_causes memory hooks floats allocator allocation interrupts prepared store p address 0#usize
        function instanceIndex functionIndex inst compiled hf hw hi hc params certificate.capacity
      rw [returned] at causes ⊢
      simp only [WP.spec_ok] at causes ⊢
      refine ⟨unchanged, entered, ?_⟩
      intro error rejected same
      subst error
      obtain ⟨words, capacity, bound⟩ := Interp.function_capacity_decoded view code store capacities address function
        instanceIndex functionIndex inst compiled hf hw hi hc
      have exceeded := causes _ rejected
      change store.limits.max_values.val < (0#usize).val + compiled.slot_count.val at exceeded
      exact Or.inr (Or.inl ⟨words, capacity, by scalar_tac⟩)
    · intro prepared p entered
      obtain ⟨defaults, default, invariant, sourceStep⟩ := entered
      let initial := Abs.entryState (Store.decodeStore view code store) ambient address.index.val
        (Store.decodeInstance store inst) (signature.results.val.map Interp.sourceType)
        body (args.val.map Interp.sourceValue) defaults
      let machine : Interp.SliceMachine P store (Store.decodeStore view code store) ambient
          (signature.results.val.map Interp.sourceType) (sizeOf initial) :=
        ⟨prepared, p, initial, 0, false, invariant, Abs.codeBound_initial initial, rfl, rfl⟩
      apply WP.dspec_mono (Interp.slice_loop memory hooks floats allocator allocation interrupts
        view code rfl compiledFunctions machine)
      intro out outcome
      obtain ⟨unchanged, success⟩ := outcome.readback_references
        (Interp.entry_reference_bound store.id _ ambient address.index.val _ _ body args.val
          (declared.map local.LOCAL) defaults (fun value member => (owned value member).1) default)
      refine ⟨unchanged, ?_, ?_⟩
      · intro ok
        obtain ⟨values, tags, wellformed, fits, represented, reductions⟩ := success ok
        exact ⟨values, tags, wellformed, fits, represented, True.intro⟩
      · intro error rejected same
        subst error
        obtain ⟨callee, base, words, site, capacity, exceeded⟩ := outcome.source_values view code rfl capacities rejected
        refine Or.inr (Or.inr ⟨initial, callee, base, words, ?_, site, capacity, exceeded⟩)
        exact StepsH.cons sourceStep (.refl invariant.typed.decode_wf)
  apply WP.dspec_mono composed
  intro out post
  exact ⟨post.1, fun rejected => post.2.2 _ rejected rfl⟩
end Exec.Theorems
