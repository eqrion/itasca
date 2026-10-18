import Exec.Representation.StoreCapacity
import Exec.Interp.Relations.SourceCallCause
import Exec.Interp.Machines.Slice.SliceBoundary
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- The type and function tables used by the integer/control trace match the
source module and its issued function signatures. The selected signature also
matches the source function itself; no compiled slot counter appears here. -/
structure SourceCapacityEnvironment (store : _root_.store) (function : funcinst)
    (env : Itasca.module.Env) (typeIndex : U32) : Prop where
  types : function.MODULE.TYPES = env.types.val.map Store.decodeFuncType
  functions : Interp.FunctionsMatch store function.MODULE (env.func_types.val.map Store.decodeFuncType)
  signature : ∃ signature, env.types.val[typeIndex.val]? = some signature ∧
    function.TYPE = Store.decodeFuncType signature

theorem SourceCapacityEnvironment.selected {store function env typeIndex}
    (coherent : SourceCapacityEnvironment store function env typeIndex) :
    function.MODULE.TYPES[typeIndex.val]? = some function.TYPE := by
  obtain ⟨signature, found, decoded⟩ := coherent.signature
  simp only [coherent.types, List.getElem?_map, found, Option.map_some, decoded]

def SourceFunctionCapacity (store : _root_.store) (address : funcaddr) (words : Nat) : Prop :=
  ∃ (function : funcinst) (profile : Itasca.ValidationProfile) (env : Itasca.module.Env) (typeIndex : U32),
    store.FUNCS[address]? = some function ∧ SourceCapacityEnvironment store function env typeIndex ∧
    Code.SourceFrameCapacity profile env typeIndex function.CODE words

theorem function_capacity_decoded {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (capacities : Store.FunctionCapacities code store)
    (address : runtime.FuncAddr) (function : runtime.store.Function)
    (instanceIndex functionIndex : Usize) (inst : runtime.store.Instance)
    (compiled : runtime.bytecode.CompiledFunction)
    (found : store.funcs.val[address.index.val]? = some function)
    (defined : function.code = .Wasm instanceIndex functionIndex)
    (instanceFound : store.instances.val[instanceIndex.val]? = some inst)
    (codeFound : inst.module.functions.val[functionIndex.val]? = some compiled) :
    ∃ words, SourceFunctionCapacity (Store.decodeStore view code store) address.index.val words ∧
      compiled.slot_count.val ≤ words := by
  obtain ⟨actualInst, actualCode, typeIndex, actualFound, actualCodeFound,
      ⟨words, sourceCapacity, bound⟩, entries, table, signature, typeFound, signatureFound⟩ :=
    capacities function (List.mem_of_getElem? found) instanceIndex functionIndex defined
  have sameInst : actualInst = inst := Option.some.inj (actualFound.symm.trans instanceFound)
  subst actualInst
  have sameCode : actualCode = compiled := Option.some.inj (actualCodeFound.symm.trans codeFound)
  subst actualCode
  refine ⟨words, ⟨Store.decodeFunction code store function, inst.module.profile,
    inst.module.module.env, typeIndex, ?_, ?_, ?_⟩, bound⟩
  · simp only [Store.decodeStore, List.getElem?_map, found, Option.map_some]
  · constructor
    · simpa only [Store.decodeFunction, defined, instanceFound, Store.decodeInstance] using entries.capacity_decode
    · simpa only [Store.decodeFunction, defined, instanceFound] using table.source view code
    · refine ⟨signature, typeFound, ?_⟩
      simp only [Store.decodeFunction, defined, instanceFound, List.getD_eq_getElem?_getD,
        List.getElem?_map, signatureFound, Option.map_some, Option.getD_some]
  · simpa only [Store.decodeFunction, defined, instanceFound] using sourceCapacity

/-- A value-limit rejection at a direct call exceeds the configured limit at
that source call's shared argument position plus its callee's source frame
requirement. No internal slot count remains in this conclusion. -/
theorem SourceDirectCallCause.source_values {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {index : Usize}
    {raw : runtime.interp.Frame} {inst : runtime.store.Instance}
    {compiled : runtime.bytecode.CompiledFunction} {source : Abs.AState}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (decoded : source.store = Store.decodeStore view code store)
    (capacities : Store.FunctionCapacities code store)
    (cause : SourceDirectCallCause allocator hooks exec store platform index raw inst compiled source (.Exhausted .Values)) :
    ∃ address base words, SourceCallSite source address base ∧
      SourceFunctionCapacity source.store address words ∧ store.limits.max_values.val < base + words := by
  obtain ⟨target, offset, pc, address, base, function, instanceIndex, functionIndex,
    callee, codeObject, fetch, resolved, lookup, wasm, instanceLookup, codeLookup, baseEq, pcEq, rejection, site⟩ := cause
  obtain ⟨words, capacity, bound⟩ := function_capacity_decoded view code store capacities address function
    instanceIndex functionIndex callee codeObject lookup wasm instanceLookup codeLookup
  refine ⟨address.index.val, base.val, words, site, by simpa only [decoded] using capacity, ?_⟩
  change store.limits.max_values.val < base.val + codeObject.slot_count.val at rejection
  omega

theorem SliceFailure.source_values {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : Abs.AState}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (decoded : source.store = Store.decodeStore view code store)
    (capacities : Store.FunctionCapacities code store)
    (failure : SliceFailure allocator hooks exec store platform source (.Exhausted .Values)) :
    ∃ address base words, SourceCallSite source address base ∧
      SourceFunctionCapacity source.store address words ∧ store.limits.max_values.val < base + words := by
  rcases failure with ⟨⟨trap, kind, _⟩, _⟩ | ⟨kind, _⟩ | rejected
  · cases kind
  · cases kind
  · obtain ⟨index, raw, inst, compiled, _, _, _, _, cause⟩ := rejected
    exact cause.source_values view code decoded capacities

/-- The actual execution loop can reach Values exhaustion only at a source
call whose validated static storage requirement exceeds the limit. -/
theorem SliceLoopOutcome.source_values {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    {initial : SliceMachine P store sourceStore ambient expected bound}
    {result : ExecutionResult M P}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (decoded : sourceStore = Store.decodeStore view code store)
    (capacities : Store.FunctionCapacities code store)
    (outcome : SliceLoopOutcome memory hooks floats allocator initial result)
    (failed : result.2.2.2.2.2.2.2 = .Err (.Exhausted .Values)) :
    ∃ address base words, SourceCallSite initial.source address base ∧
      SourceFunctionCapacity sourceStore address words ∧ store.limits.max_values.val < base + words := by
  obtain ⟨previous, dispatches, count, finalExec, finalPlatform, run, steps, cost, actual, failure, returned⟩ :=
    outcome.error_reachable failed
  obtain ⟨address, base, words, site, capacity, exceeds⟩ :=
    failure.source_values view code (previous.decoded.trans decoded) capacities
  exact ⟨address, base, words, site.prepend steps
    (previous.decoded.trans initial.decoded.symm) (previous.ambient_eq.trans initial.ambient_eq.symm),
    by simpa only [previous.decoded] using capacity, exceeds⟩
end Exec.Interp
