import Itasca.Runtime.Interp.Calls.IndirectCall
import Itasca.Runtime.Store.Invariant.CanonicalSignatures

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Store shape discharges reference/address safety; canonical signatures turn
the runtime comparison into the exact source function-type comparison. -/
theorem execute_call_indirect_shaped {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (instanceIndex functionIndex base : Usize) (entry index callee : U32)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (table type : U32) (tableAddress : runtime.TableAddr) (object : runtime.store.TableInst)
    (position : U32) (signature calleeBase : Usize)
    (expected : Itasca.wasm_types.FuncType) (shape : Store.Shape view store)
    (funcref : object.ty = .FuncRef)
    (instanceFound : store.instances.val[instanceIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[functionIndex.val]? = some compiled)
    (pairFound : compiled.indirect.val[entry.val]? = some (table,type))
    (tableMapped : inst.tables.val[table.val]? = some tableAddress)
    (tableFound : store.tables.val[tableAddress.index.val]? = some object)
    (input : UScalar.cast .U32 exec.slots.val[base.val+index.val]! = position)
    (indexBound : base.val+index.val < exec.slots.length)
    (signatureFound : inst.types.val[type.val]? = some signature)
    (baseOffset : calleeBase.val = base.val+callee.val)
    (expectedFound : store.types.val[signature.val]? = some expected)
    (cause : Prop) (post : core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
      runtime.store.Store M × P → Prop)
    (outside : ¬position.val < object.elements.length →
      post (.Err (.Trap .TableOutOfBounds),exec,store,platform))
    (null : object.elements.val[position.val]? = some (0#u64) →
      post (.Err (.Trap .UninitializedElement),exec,store,platform))
    (mismatch : ∀ (reference : U64) (address : Usize) (function : runtime.store.FuncInst),
      object.elements.val[position.val]? = some reference → reference ≠ 0#u64 →
      reference.val = address.val+1 →
      store.funcs.val[address.val]? = some function → (Store.decodeFunction code store function).TYPE ≠ Store.decodeFuncType expected →
      post (.Err (.Trap .IndirectCallTypeMismatch),exec,store,platform))
    (called : ∀ (reference : U64) (address : Usize) (function : runtime.store.FuncInst),
      object.elements.val[position.val]? = some reference → reference ≠ 0#u64 →
      reference.val = address.val+1 →
      store.funcs.val[address.val]? = some function → (Store.decodeFunction code store function).TYPE = Store.decodeFuncType expected →
      DivSpec cause (runtime.interp.call memory hooks floats allocator exec store platform
        {store := store.id,index := address} calleeBase) post) :
    DivSpec cause (runtime.interp.execute_call_indirect memory hooks floats allocator exec store platform
      instanceIndex functionIndex base entry index callee) post := by
  apply execute_call_indirect_effect memory hooks floats allocator exec store platform
    instanceIndex functionIndex base entry index callee inst compiled table type tableAddress
    object position signature calleeBase instanceFound functionFound pairFound tableMapped
    tableFound input indexBound signatureFound baseOffset
    (fun reference selected nonzero => shape.table_function_target object
      (List.mem_of_getElem? tableFound) funcref position reference selected nonzero)
    cause post outside null
  · intro reference address function selected nonzero addressEq targetFound different
    have rawEq : reference.val = address.val+1 := by
      simpa only [shape.table_function_reference_cast object (List.mem_of_getElem? tableFound)
        funcref position reference selected] using addressEq
    exact mismatch reference address function selected nonzero rawEq targetFound
      (fun same => different ((shape.function_signature_eq_iff code function
        (List.mem_of_getElem? targetFound) signature expected expectedFound).mpr same))
  · intro reference address function selected nonzero addressEq targetFound same
    have rawEq : reference.val = address.val+1 := by
      simpa only [shape.table_function_reference_cast object (List.mem_of_getElem? tableFound)
        funcref position reference selected] using addressEq
    exact called reference address function selected nonzero rawEq targetFound
      ((shape.function_signature_eq_iff code function (List.mem_of_getElem? targetFound)
        signature expected expectedFound).mp same)

/-- Shaped indirect-call resolution after the actual instruction fetch and PC advance. -/
theorem step_indirect_call_shaped {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (frame : runtime.interp.Frame) (entry index callee : U32)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (table type : U32) (tableAddress : runtime.TableAddr) (object : runtime.store.TableInst)
    (position : U32) (signature calleeBase : Usize)
    (expected : Itasca.wasm_types.FuncType) (shape : Store.Shape view store)
    (funcref : object.ty = .FuncRef)
    (last : frameIndex.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[frameIndex.val]? = some frame)
    (opcodeFound : compiled.code.val[frame.pc.val]? = some (.CallIndirect entry index callee))
    (pcBound : frame.pc.val < U32.max)
    (instanceFound : store.instances.val[frame.instance.val]? = some inst)
    (functionFound : inst.module.functions.val[frame.function.val]? = some compiled)
    (pairFound : compiled.indirect.val[entry.val]? = some (table,type))
    (tableMapped : inst.tables.val[table.val]? = some tableAddress)
    (tableFound : store.tables.val[tableAddress.index.val]? = some object)
    (input : UScalar.cast .U32 exec.slots.val[frame.base.val+index.val]! = position)
    (indexBound : frame.base.val+index.val < exec.slots.length)
    (signatureFound : inst.types.val[type.val]? = some signature)
    (baseOffset : calleeBase.val = frame.base.val+callee.val)
    (expectedFound : store.types.val[signature.val]? = some expected)
    (cause : Prop) (post : core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
      runtime.store.Store M × P → Prop)
    (outside : ∀ next : U32, next.val = frame.pc.val+1 → ¬position.val < object.elements.length →
      post (.Err (.Trap .TableOutOfBounds),{exec with frames := exec.frames.set frameIndex {frame with pc := next}},store,platform))
    (null : ∀ next : U32, next.val = frame.pc.val+1 → object.elements.val[position.val]? = some (0#u64) →
      post (.Err (.Trap .UninitializedElement),{exec with frames := exec.frames.set frameIndex {frame with pc := next}},store,platform))
    (mismatch : ∀ next : U32, next.val = frame.pc.val+1 → ∀ (reference : U64) (address : Usize) (function : runtime.store.FuncInst),
      object.elements.val[position.val]? = some reference → reference ≠ 0#u64 →
      reference.val = address.val+1 →
      store.funcs.val[address.val]? = some function → (Store.decodeFunction code store function).TYPE ≠ Store.decodeFuncType expected →
      post (.Err (.Trap .IndirectCallTypeMismatch),{exec with frames := exec.frames.set frameIndex {frame with pc := next}},store,platform))
    (called : ∀ next : U32, next.val = frame.pc.val+1 → ∀ (reference : U64) (address : Usize) (function : runtime.store.FuncInst),
      object.elements.val[position.val]? = some reference → reference ≠ 0#u64 →
      reference.val = address.val+1 →
      store.funcs.val[address.val]? = some function → (Store.decodeFunction code store function).TYPE = Store.decodeFuncType expected →
      DivSpec cause (runtime.interp.call memory hooks floats allocator
        {exec with frames := exec.frames.set frameIndex {frame with pc := next}} store platform
        {store := store.id,index := address} calleeBase) post) :
    DivSpec cause (runtime.interp.step memory hooks floats allocator exec store platform) post := by
  apply step_fetch_div memory hooks floats allocator exec store platform frameIndex frame
    inst compiled (.CallIndirect entry index callee) last frameFound instanceFound functionFound
    opcodeFound pcBound cause post
  intro next nextEq
  exact execute_call_indirect_shaped memory hooks floats allocator view code
    {exec with frames := exec.frames.set frameIndex {frame with pc := next}} store platform
    frame.instance frame.function frame.base entry index callee inst compiled table type
    tableAddress object position signature calleeBase expected shape funcref instanceFound
    functionFound pairFound tableMapped tableFound input indexBound signatureFound baseOffset
    expectedFound cause post (outside next nextEq) (null next nextEq) (mismatch next nextEq) (called next nextEq)

end Itasca.Runtime.Interp
