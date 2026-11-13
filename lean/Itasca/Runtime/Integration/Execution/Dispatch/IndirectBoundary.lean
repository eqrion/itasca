import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Interp.Calls.ReturnRefinement
import Itasca.Runtime.Interp.Relations.SuspendedPoint
import Itasca.Runtime.SourceMachine.BrTable
import Itasca.Runtime.Integration.Execution.Ownership.Publication
import Itasca.Runtime.Interp.Machine.Calls.CallStackEntry
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.SourceMachine.Supported.PureCoverage
import Itasca.Runtime.Interp.Calls.IndirectResolve
import Itasca.Runtime.Store.Invariant.HostSignature
import Itasca.Runtime.Interp.State.StatefulSegmentLookup
import Itasca.Runtime.Interp.State.TableSource
import Itasca.Runtime.Representation.StoreCapacity
import Itasca.Runtime.Interp.Machine.Frames.SourceBase
import Itasca.Runtime.Integration.Execution.Resources.InvocationErrors
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallExclusions
import Itasca.Runtime.SourceMachine.Cumulative.Step
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered
import Itasca.Runtime.SourceMachine.Indirect.HostSimulation
import Itasca.Runtime.Interp.Machine.Progress.SupportedAdvance
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Compiler.Local.Control.Function.CumulativeFunctionContext
import Itasca.Runtime.Interp.Machine.Functions.CompiledFunctions
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixFinish
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalTerminal
import Itasca.Runtime.Interp.Machine.Calls.IndirectOperands
import Itasca.Runtime.Interp.Relations.StepActive
import Itasca.Runtime.Interp.Machine.Control.BranchSource

/-!
Sections, each formerly its own module: Arguments, Entry, IndirectCall, IndirectLookup, IndirectBoundary.
-/

/-! ## Arguments -/

section

/-! Invocation entry bridges checked API arguments and retained function
metadata to the typed abstract state. Compiler/body certificates remain explicit. -/
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt

theorem arguments_typed {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (storeWf : wf_store (Store.decodeStore view code store))
    (args : List runtime.Value) (types : List Itasca.wasm_types.ValueType)
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
    (args : Slice runtime.Value) (types : alloc.vec.Vec Itasca.wasm_types.ValueType)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref types) = .ok (.Ok ()))
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value) :
    ResultsTyped (Store.decodeStore view code store) (types.val.map Interp.sourceType)
      (args.val.map Interp.sourceValue) := by
  have h := Interp.check_values_accepts_iff memory store args (alloc.vec.Vec.deref types)
  rw [accepted] at h
  simp only [WP.spec_ok] at h
  apply arguments_typed view code store storeWf args.val types.val _ owned
  simpa [alloc.vec.Vec.deref] using h.mp trivial

theorem argument_type_tags {id : Usize} {args : List runtime.Value} {types : List Itasca.wasm_types.ValueType}
    (matched : List.Forall₂ (Interp.ArgumentMatches id) args types) :
    (args.map Interp.sourceValue).map Compiler.valueType = types.map Interp.sourceType := by
  induction matched with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, Interp.source_value_type, head.2, ih]

theorem checked_argument_type_tags {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (args : Slice runtime.Value) (types : alloc.vec.Vec Itasca.wasm_types.ValueType)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref types) = .ok (.Ok ())) :
    (args.val.map Interp.sourceValue).map Compiler.valueType = types.val.map Interp.sourceType := by
  have h := Interp.check_values_accepts_iff memory store args (alloc.vec.Vec.deref types)
  rw [accepted] at h
  simp only [WP.spec_ok] at h
  have matched : List.Forall₂ (Interp.ArgumentMatches store.id) args.val types.val := by
    simpa [alloc.vec.Vec.deref] using h.mp trivial
  exact argument_type_tags matched

end Itasca.Runtime.Integration

end

/-! ## Entry -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt

/-- A real defined-function call establishes the complete mutable-machine entry
from checked arguments and retained source/compiler certificates. -/
theorem call_defined_supported_entry {M P F A : Type}
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
          vals (args.val.map Interp.sourceValue) ++ [.CALL_ADDR address.index.val]⟩ [] (SourceMachine.decode entry)) ⦄ := by
  obtain ⟨inst,compiled,actualSignature,declared,body,epilogue,hi,hc,actualHs,table,certificate,bindings,lookup⟩ :=
    compiledFunctions.defined view functionTyping address function instanceIndex functionIndex hf hw
  have same : actualSignature = signature := Option.some.inj (actualHs.symm.trans hs)
  subst actualSignature
  have storeWf := Store.decode_store_wf view code store shaped sourceSyntax
  have argumentTypes := checked_arguments_typed memory view code store storeWf args signature.params accepted owned
  obtain ⟨defaults,default,typed,covered,sourceStep⟩ := SourceMachine.defined_supported_invocation
    (Store.decodeStore view code store) ambient address.index.val (Store.decodeInstance store inst)
    (.mk_uN compiled.type_index.val) (signature.params.val.map Interp.sourceType)
    (signature.results.val.map Interp.sourceType) (declared.map local.LOCAL) body
    (args.val.map Interp.sourceValue) storeWf ambientWf functionTyping.functions_typed coveredFunctions lookup argumentTypes
  have tags := checked_argument_type_tags memory store args signature.params accepted
  apply WP.spec_mono (Interp.Machine.call_wasm_stack memory hooks floats allocator allocation interrupts
    before store platform address 0#usize function signature instanceIndex functionIndex inst compiled epilogue
    (Store.decodeStore view code store)
    (Compiler.moduleFunctionContext inst.module (signature.params.val.map Interp.sourceType++declared)
      (signature.results.val.map Interp.sourceType)) bindings declared body
    (args.val.map Interp.sourceValue) defaults certificate hf hs hw hi hc table identity
    arguments tags default [] [] empty (.nil _))
  intro out result
  refine ⟨result.1,fun success => ?_⟩
  obtain ⟨stack,top,ready⟩ := result.2 success
  obtain ⟨pc,cursor⟩ := ready.cursor
  have zero : pc = 0 := by
    have position := cursor.pc
    simp only [top,Option.map_some,Option.some.injEq] at position
    scalar_tac
  subst pc
  refine ⟨_,?_,?_,rfl,sourceStep⟩
  · exact ⟨rfl,⟨typed,Store.decode_store_contents_typed view code store shaped sourceSyntax bounds⟩,covered,SourceMachine.entry_result _ _ _ _ _ _ _ _,stack,cursor⟩
  · exact stateful_entry_owned shaped ambient address.index.val (Store.decodeInstance store inst)
      (signature.results.val.map Interp.sourceType) body args.val (declared.map local.LOCAL) defaults owned default
end Itasca.Runtime.Integration

end

/-! ## IndirectCall -/

section

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

end

/-! ## IndirectLookup -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt

/-- Canonical source type bindings reconstruct the actual instance signature
index and its checked store lookup. -/
theorem signature_binding_raw {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (C : context)
    (shape : Store.Shape view store) (present : inst ∈ store.instances.val)
    (bindings : SourceMachine.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst) C)
    (index : Nat) (type : functype) (selected : C.TYPES[index]? = some type) :
    ∃ signature rawType, inst.types.val[index]? = some signature ∧
      store.types.val[signature.val]? = some rawType ∧ Store.decodeFuncType rawType = type := by
  rw [bindings.types] at selected
  change (inst.types.val.map (fun i => (store.types.val.map Store.decodeFuncType).getD i.val default))[index]? = some type at selected
  rw [List.getElem?_map] at selected
  obtain ⟨signature,mapped,decoded⟩ := Option.map_eq_some_iff.mp selected
  obtain ⟨_,_,_,_,_,_,_,typeBounds,_⟩ := shape.instances inst present
  have bound := typeBounds signature (List.mem_of_getElem? mapped)
  have found : store.types.val[signature.val]? = some store.types.val[signature.val] := List.getElem?_eq_getElem bound
  refine ⟨signature,store.types.val[signature.val],mapped,found,?_⟩
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_map,found,Option.map_some,Option.getD_some] using decoded

/-- The runtime type map and the generated `fun_type` select the same signature. -/
theorem signature_lookup_decodes {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (index : U32) (signature : Usize) (type : Itasca.wasm_types.FuncType)
    (moduleEq : ambient.MODULE = Store.decodeInstance store inst)
    (mapped : inst.types.val[index.val]? = some signature)
    (found : store.types.val[signature.val]? = some type) :
    fun_type ⟨Store.decodeStore view code store,ambient⟩ (.mk_uN index.val) = Store.decodeFuncType type := by
  simp [fun_type,moduleEq,Store.decodeInstance,proj_uN_0,List.getElem!_eq_getElem?_getD,
    List.getD_eq_getElem?_getD,mapped,found]

/-- Both independent namespaces of CALL_INDIRECT resolve to actual retained
objects, with exact source lookup equations. -/
theorem indirect_bindings_raw {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame) (C : context)
    (shape : Store.Shape view store) (present : inst ∈ store.instances.val)
    (bindings : SourceMachine.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst) C)
    (moduleEq : ambient.MODULE = Store.decodeInstance store inst)
    (typeIndex tableIndex : U32) (type : functype) (limits : limits)
    (typeSelected : C.TYPES[typeIndex.val]? = some type)
    (tableSelected : C.TABLES[tableIndex.val]? = some (.mk_tabletype limits .FUNCREF)) :
    ∃ signature rawType address object,
      inst.types.val[typeIndex.val]? = some signature ∧
      store.types.val[signature.val]? = some rawType ∧ Store.decodeFuncType rawType = type ∧
      inst.tables.val[tableIndex.val]? = some address ∧
      store.tables.val[address.index.val]? = some object ∧ object.ty = .FuncRef ∧
      fun_type ⟨Store.decodeStore view code store,ambient⟩ (.mk_uN typeIndex.val) = type ∧
      fun_table ⟨Store.decodeStore view code store,ambient⟩ (.mk_uN tableIndex.val) = Store.decodeTable object := by
  obtain ⟨signature,rawType,typeMapped,typeFound,typeEq⟩ :=
    signature_binding_raw view code store inst C shape present bindings typeIndex.val type typeSelected
  obtain ⟨address,object,tableMapped,tableFound,elementType⟩ :=
    Stateful.table_binding_raw view code store inst C tableIndex.val _ bindings tableSelected
  have rawFuncref : object.ty = .FuncRef := by
    cases h : object.ty <;> simp [h,Store.decodeElemType,SourceMachine.Stateful.tableElementType] at elementType ⊢
  exact ⟨signature,rawType,address,object,typeMapped,typeFound,typeEq,tableMapped,tableFound,rawFuncref,
    (signature_lookup_decodes view code store inst ambient typeIndex signature rawType moduleEq typeMapped typeFound).trans typeEq,
    table_lookup_decodes view code store inst ambient tableIndex address object moduleEq tableMapped tableFound⟩

end Itasca.Runtime.Interp

end

/-! ## IndirectBoundary -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

def SourceIndirectHostBoundary {M : Type} (store : runtime.store.Store M) (source : SourceMachine.AState) : Prop :=
  ∃ (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (table type position : Nat) (after : List instr) (front : List val)
    (address : Usize) (function : runtime.store.FuncInst) (host : U64),
    source.frames={f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest ∧
    f.vals=front++[SourceMachine.integerVal .I32 position] ∧ position<2^32 ∧
    SourceMachine.Indirect.resolve source.store f table type position=some address.val ∧
    store.funcs.val[address.val]?=some function ∧ function.code=.Host host

def IndirectTrap (trap : runtime.Trap) : Prop :=
  trap=.TableOutOfBounds ∨ trap=.UninitializedElement ∨ trap=.IndirectCallTypeMismatch

end Itasca.Runtime.Integration

end
