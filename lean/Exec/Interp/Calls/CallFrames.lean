import Exec.Interp.Calls.CallRegions

namespace Exec.Interp
open Aeneas Aeneas.Std

theorem CallEntryEffect.slots_length {before after : runtime.interp.Execution}
    {instanceIndex functionIndex base : Usize} {code : runtime.bytecode.CompiledFunction}
    (effect : CallEntryEffect before after instanceIndex functionIndex base code) :
    before.slots.length ≤ after.slots.length ∧ base.val + code.slot_count.val ≤ after.slots.length := by
  change before.slots.val.length ≤ after.slots.val.length ∧ _ ≤ after.slots.val.length
  rw [effect.2.1, zeroWords_length, List.length_append, List.length_replicate]
  simp only [alloc.vec.Vec.length, alloc.vec.Vec.val]
  omega

/-- Entering a callee retains every existing frame's module/function binding
and allocated capacity. Suspended operand contents are handled separately. -/
theorem CallEntryEffect.preserve_binding {M : Type} {store : runtime.store.Store M}
    {before after : runtime.interp.Execution} {instanceIndex functionIndex base : Usize}
    {code : runtime.bytecode.CompiledFunction} {raw : runtime.interp.Frame} {source : Abs.AFrame}
    (effect : CallEntryEffect before after instanceIndex functionIndex base code)
    (binding : FrameBinding store before raw source) : FrameBinding store after raw source := by
  obtain ⟨inst, fn, compiled, signature, identity, member, hi, hf, hw, hc, hs, hm, hr, hl, bound⟩ := binding
  refine ⟨inst, fn, compiled, signature, ?_, ?_, hi, hf, hw, hc, hs, hm, hr, hl, ?_⟩
  · exact (congrArg runtime.interp.Execution.store effect.2.2).trans identity
  · rw [effect.1]
    exact List.mem_append_left _ member
  · exact bound.trans effect.slots_length.1

/-- The caller's live prefix ends at the callee argument base. Its locals and
remaining operands survive initialization and any backing-vector growth. -/
theorem CallEntryEffect.caller_values
    {before after : runtime.interp.Execution} {instanceIndex functionIndex base : Usize}
    {code : runtime.bytecode.CompiledFunction} {raw : runtime.interp.Frame}
    {source : Abs.AFrame} {front args : List val}
    (effect : CallEntryEffect before after instanceIndex functionIndex base code)
    (represented : FrameSlots before raw { source with vals := front ++ args })
    (offset : base.val = raw.base.val + Code.slots ((source.locals ++ front).map Code.valueType))
    (params : code.param_slots.val ≤ code.local_slots.val)
    (capacity : code.local_slots.val ≤ code.slot_count.val) :
    FrameSlots after raw { source with vals := front } := by
  have prefixValues : ValuesAt before.slots.val raw.base.val (source.locals ++ front) := by
    apply WordsAt.append_left (right := Code.encodeValues args)
    simpa only [FrameSlots, ValuesAt, Code.encodeValues_append, List.append_assoc] using represented
  apply effect.preserve_prefix prefixValues _ params capacity
  rw [Code.encodeValues_length, offset]

/-- Exact retained metadata for the newly pushed callee. -/
theorem CallEntryEffect.callee_binding {M : Type}
    (store : runtime.store.Store M) (before after : runtime.interp.Execution)
    (address : runtime.FuncAddr) (function : runtime.store.Function)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex base : Usize)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (args defaults : List val) (body : List instr)
    (effect : CallEntryEffect before after instanceIndex functionIndex base compiled)
    (identity : before.store = store.id)
    (localTypes : (args ++ defaults).map Code.valueType = compiled.locals.val.map sourceType)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (hi : store.instances.val[instanceIndex.val]? = some inst)
    (hc : inst.module.functions.val[functionIndex.val]? = some compiled) :
    FrameBinding store after ⟨instanceIndex, functionIndex, 0#u32, base⟩
      ⟨address.index.val, signature.results.val.map sourceType, args ++ defaults,
        Store.decodeInstance store inst,
        [⟨signature.results.val.map sourceType, signature.results.val.map sourceType, [], 0, []⟩],
        body, []⟩ := by
  refine ⟨inst, function, compiled, signature, ?_, ?_, hi, hf, hw, hc, hs, rfl, rfl, localTypes, ?_⟩
  · exact (congrArg runtime.interp.Execution.store effect.2.2).trans identity
  · simp [effect.1]
  · exact effect.slots_length.2

end Exec.Interp
