import Exec.Store.Invariant.Typing
import Exec.Interp.Relations.Arguments
import Exec.Interp.Calls.CallRegions
import Exec.Interp.Relations.FrameBindings
import Exec.Abs.Invoke

/-! Invocation entry bridges checked API arguments and retained function
metadata to the typed abstract state. Compiler/body certificates remain explicit. -/
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

theorem arguments_typed {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (storeWf : wf_store (Store.decodeStore view code store))
    (args : List runtime.Value) (types : List Itasca.types.ValueType)
    (matched : List.Forall₂ (Interp.ArgumentMatches store.id) args types)
    (owned : ∀ value ∈ args, Store.ValueInStore store value) :
    ResultsTyped (Store.decodeStore view code store) (types.map Interp.sourceType)
      (args.map Interp.sourceValue) := by
  unfold ResultsTyped
  revert owned
  induction matched with
  | nil => intro owned; exact .nil
  | @cons value ty values types head tail ih =>
    intro owned
    apply List.Forall₂.cons
    · rw [← head.2]
      exact Store.value_in_store_typed view code store storeWf value (owned value (by simp))
    · apply ih
      intro v hv
      exact owned v (by simp [hv])

theorem checked_arguments_typed {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (storeWf : wf_store (Store.decodeStore view code store))
    (args : Slice runtime.Value) (types : alloc.vec.Vec Itasca.types.ValueType)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref types) = .ok (.Ok ()))
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value) :
    ResultsTyped (Store.decodeStore view code store) (types.val.map Interp.sourceType)
      (args.val.map Interp.sourceValue) := by
  have h := Interp.check_values_accepts_iff memory store args (alloc.vec.Vec.deref types)
  rw [accepted] at h
  simp only [WP.spec_ok] at h
  apply arguments_typed view code store storeWf args.val types.val _ owned
  simpa [alloc.vec.Vec.deref] using h.mp trivial

/-- Concrete function, signature, and owning-instance lookups resolve the
source function selected by the retained interpretation. -/
theorem decoded_defined_lookup {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (address : runtime.FuncAddr) (function : runtime.store.Function)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.Instance) (sourceCode : funccode)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (hi : store.instances.val[instanceIndex.val]? = some inst)
    (hc : code instanceIndex.val inst.module functionIndex.val = sourceCode) :
    (Store.decodeStore view code store).FUNCS[address.index.val]? =
      some ⟨Store.decodeFuncType signature, Store.decodeInstance store inst, sourceCode⟩ := by
  exact Interp.defined_function_lookup view code store address function signature instanceIndex functionIndex
    inst sourceCode hf hs hw hi hc

/-- The actual argument checker and retained function bindings establish the
abstract invocation entry. This theorem does not yet assert execution of the
compiled body; its source typing certificate is a separate compiler obligation. -/
theorem defined_entry_source {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (shape : Store.Shape view store) (storeSyntax : Store.StoreSyntax code store)
    (functions : Abs.FunctionsTyped (Store.decodeStore view code store))
    (slice : Abs.StoreSlice (Store.decodeStore view code store))
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.Function)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.Instance) (typeIndex : idx) (localTypes : List valtype) (body : List instr)
    (args : Slice runtime.Value)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (hi : store.instances.val[instanceIndex.val]? = some inst)
    (hc : code instanceIndex.val inst.module functionIndex.val = .FUNC typeIndex (localTypes.map local.LOCAL) body)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()))
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value) :
    ∃ defaults, Abs.defaultLocals (localTypes.map local.LOCAL) = some defaults ∧
      let entry := Abs.entryState (Store.decodeStore view code store) ambient address.index.val
        (Store.decodeInstance store inst) (signature.results.val.map Interp.sourceType)
        body (args.val.map Interp.sourceValue) defaults
      Abs.ATyped entry ∧ Abs.SliceState entry ∧
      StepH ⟨⟨Store.decodeStore view code store, ambient⟩,
          vals (args.val.map Interp.sourceValue) ++ [.CALL_ADDR address.index.val]⟩ [] (Abs.decode entry) := by
  have storeWf := Store.decodeStore_wf view code store shape storeSyntax
  have argumentTypes := checked_arguments_typed memory view code store storeWf args signature.params accepted owned
  have lookup := decoded_defined_lookup view code store address function signature instanceIndex functionIndex
    inst (.FUNC typeIndex (localTypes.map local.LOCAL) body) hf hs hw hi hc
  exact Abs.defined_invocation _ ambient address.index.val (Store.decodeInstance store inst) typeIndex
    (signature.params.val.map Interp.sourceType) (signature.results.val.map Interp.sourceType)
    (localTypes.map local.LOCAL) body (args.val.map Interp.sourceValue)
    storeWf ambientWf functions slice lookup argumentTypes


def EntryData {M : Type} (store : runtime.store.Store M) (after : runtime.interp.Execution)
    (address : runtime.FuncAddr) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.Instance) (signature : Itasca.types.FuncType)
    (args defaults : List val) (body : List instr) : Prop :=
    let raw : runtime.interp.Frame := ⟨instanceIndex, functionIndex, 0#u32, 0#usize⟩
    let source : Abs.AFrame := ⟨address.index.val, signature.results.val.map Interp.sourceType,
      args ++ defaults, Store.decodeInstance store inst,
      [⟨signature.results.val.map Interp.sourceType, signature.results.val.map Interp.sourceType, [], 0, []⟩],
      body, []⟩
    after.frames.val = [raw] ∧ Interp.FrameSlots after raw source ∧
      Interp.FrameBinding store after raw source

/-- Real defined-call initialization establishes the sole entry frame's data
binding and local-slot representation. The emitted-code certificate is attached
separately by compiler correctness. -/
theorem defined_entry_storage {M : Type}
    (store : runtime.store.Store M) (before after : runtime.interp.Execution)
    (address : runtime.FuncAddr) (function : runtime.store.Function)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (args defaults : List val) (localTypes : List valtype) (body : List instr)
    (effect : Interp.CallEntryEffect before after instanceIndex functionIndex 0#usize compiled)
    (empty : before.frames.val = []) (identity : before.store = store.id)
    (arguments : Interp.ValuesAt before.slots.val 0 args)
    (params : compiled.param_slots.val = Code.slots (args.map Code.valueType))
    (locals : compiled.local_slots.val = compiled.param_slots.val + Code.slots localTypes)
    (capacity : compiled.local_slots.val ≤ compiled.slot_count.val)
    (default : Abs.defaultLocals (localTypes.map local.LOCAL) = some defaults)
    (localTypesMatch : (args ++ defaults).map Code.valueType = compiled.locals.val.map Interp.sourceType)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (hi : store.instances.val[instanceIndex.val]? = some inst)
    (hc : inst.module.functions.val[functionIndex.val]? = some compiled) :
    EntryData store after address instanceIndex functionIndex inst signature args defaults body := by
  dsimp only [EntryData]
  have frames := effect.1
  simp only [empty, List.nil_append] at frames
  have values := effect.callee_values arguments params locals capacity default
  have storeId : after.store = store.id := by
    have h := congrArg runtime.interp.Execution.store effect.2.2
    exact h.trans identity
  refine ⟨frames, ?_, ?_⟩
  · simpa [Interp.FrameSlots] using values
  · refine ⟨inst, function, compiled, signature, storeId, ?_, hi, hf, hw, hc, hs,
      rfl, rfl, localTypesMatch, ?_⟩
    · simp [frames]
    · change 0 + compiled.slot_count.val ≤ after.slots.val.length
      rw [effect.2.1, Interp.zeroWords_length, List.length_append, List.length_replicate]
      scalar_tac


theorem argument_type_tags {id : Usize} {args : List runtime.Value} {types : List Itasca.types.ValueType}
    (matched : List.Forall₂ (Interp.ArgumentMatches id) args types) :
    (args.map Interp.sourceValue).map Code.valueType = types.map Interp.sourceType := by
  induction matched with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, Interp.sourceValue_type, head.2, ih]

theorem checked_argument_type_tags {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (args : Slice runtime.Value) (types : alloc.vec.Vec Itasca.types.ValueType)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref types) = .ok (.Ok ())) :
    (args.val.map Interp.sourceValue).map Code.valueType = types.val.map Interp.sourceType := by
  have h := Interp.check_values_accepts_iff memory store args (alloc.vec.Vec.deref types)
  rw [accepted] at h
  simp only [WP.spec_ok] at h
  have matched : List.Forall₂ (Interp.ArgumentMatches store.id) args.val types.val := by
    simpa [alloc.vec.Vec.deref] using h.mp trivial
  exact argument_type_tags matched

/-- The actual defined-function call establishes entry data on success. All
normal-return and storage effects come from the extracted call proof; metadata
premises describe the compiler's layout, not an assumed execution theorem. -/
theorem call_defined_entry {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (before : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (function : runtime.store.Function)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (args : Slice runtime.Value) (defaults : List val) (localTypes : List valtype) (body : List instr)
    (empty : before.frames.val = []) (identity : before.store = store.id)
    (arguments : Interp.ValuesAt before.slots.val 0 (args.val.map Interp.sourceValue))
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()))
    (params : compiled.param_slots.val = Code.slots (signature.params.val.map Interp.sourceType))
    (locals : compiled.local_slots.val = compiled.param_slots.val + Code.slots localTypes)
    (capacity : compiled.local_slots.val ≤ compiled.slot_count.val)
    (default : Abs.defaultLocals (localTypes.map local.LOCAL) = some defaults)
    (localTypesMatch : compiled.locals.val.map Interp.sourceType = signature.params.val.map Interp.sourceType ++ localTypes)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (hi : store.instances.val[instanceIndex.val]? = some inst)
    (hc : inst.module.functions.val[functionIndex.val]? = some compiled) :
    runtime.interp.call memory hooks floats allocator before store platform address 0#usize
      ⦃ out => out.2.2.1 = store ∧ (out.1 = .Ok () → EntryData store out.2.1 address
        instanceIndex functionIndex inst signature (args.val.map Interp.sourceValue) defaults body) ⦄ := by
  have tags := checked_argument_type_tags memory store args signature.params accepted
  step with Interp.call_wasm_effect memory hooks floats allocator allocation interrupts before store platform
    address 0#usize function instanceIndex functionIndex inst compiled hf hw hi hc (by omega) capacity
    as ⟨out, storeSame, entered⟩
  refine ⟨storeSame, ?_⟩
  intro success
  apply defined_entry_storage store before out.2.1 address function signature instanceIndex functionIndex inst compiled
    (args.val.map Interp.sourceValue) defaults localTypes body (entered success) empty identity arguments
    (by simpa [tags] using params) locals capacity default _ hf hs hw hi hc
  rw [List.map_append, tags, Interp.defaultLocals_types localTypes defaults default, localTypesMatch]

end Exec.Theorems


