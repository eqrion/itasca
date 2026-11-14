import Itasca.Runtime.Interp.State.GlobalCoreStep
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Compiler.Local.Capacity.GlobalCapacity
import Itasca.Runtime.Interp.State.TableSource
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.SourceMachine.Stateful.TableRead
import Itasca.Runtime.Representation.StoreCapacity

/-!
Sections, each formerly its own module: GlobalMutationStep, TableMutation, StatefulPrepare, StatefulLookup, StatefulContinue, StatefulSegmentLookup.
-/

/-! ## GlobalMutationStep -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem dispatch_global_set_mutation
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (src index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (f : SourceMachine.AFrame) (front : List val) (value : val)
    (platform : P) (frameIndex : Usize)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (slots : FrameSlots exec raw f) (values : f.vals = front ++ [value])
    (position : src.val = Compiler.slots ((f.locals ++ front).map Compiler.valueType))
    (mutable : object.ty.mutability = .Var)
    (typed : sourceType object.ty.valtype = Compiler.valueType value) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Compiler.globalSetInstruction (decide (Compiler.width (sourceType object.ty.valtype) = 2)) src index)
      ⦃ out => GlobalMutation store out.2.2.1 value ⦄ := by
  classical
  have handler : (if decide (Compiler.width (sourceType object.ty.valtype) = 2) then
      runtime.interp.execute_global_set2 memory exec store raw.instance raw.base src index
      else runtime.interp.execute_global_set memory exec store raw.instance raw.base src index)
      ⦃ out => GlobalMutation store out.2.2 value ⦄ := by
    simp only [source_type_width_two]
    by_cases vector : object.ty.valtype = .V128
    · simp only [vector,decide_true,ite_true]
      exact global_set2_mutation memory exec store raw src index inst address object f front value
        found mapped issued slots values position vector mutable typed
    · simp only [vector,decide_false,ite_false]
      exact global_set_mutation memory exec store raw src index inst address object f front value
        found mapped issued slots values position vector mutable typed
  apply WP.spec_mono (dispatch_global_set memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
    (decide (Compiler.width (sourceType object.ty.valtype) = 2)) src index handler)
  exact fun _ effect => effect.1

theorem step_global_set_mutation
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (src index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (f : SourceMachine.AFrame) (front : List val) (value : val)
    (platform : P) (frameIndex : Usize)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (slots : FrameSlots exec raw f) (values : f.vals = front ++ [value])
    (position : src.val = Compiler.slots ((f.locals ++ front).map Compiler.valueType))
    (mutable : object.ty.mutability = .Var)
    (typed : sourceType object.ty.valtype = Compiler.valueType value)
    (compiled : runtime.bytecode.CompiledFunction)
    (last : frameIndex.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetched : compiled.code.val[raw.pc.val]? = some (Compiler.globalSetInstruction (decide (Compiler.width (sourceType object.ty.valtype) = 2)) src index))
    (pcBound : raw.pc.val < U32.max) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out => GlobalMutation store out.2.2.1 value ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform frameIndex raw inst compiled
    (Compiler.globalSetInstruction (decide (Compiler.width (sourceType object.ty.valtype) = 2)) src index) last frameFound found codeFound fetched pcBound
  intro pc pcNext
  exact dispatch_global_set_mutation memory hooks floats allocator
    {exec with frames := exec.frames.set frameIndex {raw with pc := pc}} store raw src index inst address object f front value
    platform frameIndex found mapped issued slots values position mutable typed

end Itasca.Runtime.Interp

end

/-! ## TableMutation -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std Itasca.Runtime.Store

/-- A table content update retains the object's reference type, maximum and
length; every word is either retained or the explicit replacement reference. -/
def TableMutation {M : Type} (before after : runtime.store.Store M)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (replacement : U64) : Prop :=
  ∃ words, after = {before with tables := before.tables.set address.index {object with elements := words}} ∧
    words.length = object.elements.length ∧
    ∀ word ∈ words.val, word ∈ object.elements.val ∨ word = replacement

end Itasca.Runtime.Interp

end

/-! ## StatefulPrepare -/

section

namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec

theorem operand_heights {s : store} {f : SourceMachine.AFrame} {op : SourceMachine.Stateful.Instruction} {after : List instr}
    (typed : SourceMachine.FrameTyped s {f with code:=op.source::after} [])
    (front operands : List val) (values : f.vals=front++operands) (arity : operands.length=op.arity) :
    ∀ label ∈ f.labels, label.height≤front.length := by
  obtain ⟨C,actualFront,actualOperands,inputs,outputs,bindings,locals,operation,split,operandTypes,wf,heights,continuation⟩ := SourceMachine.Stateful.frame_operands typed
  have actualArity := (SourceMachine.Stateful.Signature.of_typed operation).input_length
  have operandLength := results_typed_length operandTypes
  have lengths := congrArg List.length (values.symm.trans split)
  simp only [List.length_append] at lengths
  intro label member
  have height := heights label member
  omega

end Itasca.Runtime.Interp.Stateful

end

/-! ## StatefulLookup -/

section

namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std SpecExt

theorem table_binding_raw {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (C : context) (index : Nat) (type : tabletype)
    (bindings : SourceMachine.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst) C)
    (selected : C.TABLES[index]?=some type) :
    ∃ address object, inst.tables.val[index]?=some address ∧ store.tables.val[address.index.val]?=some object ∧
      Store.decodeElemType object.ty=SourceMachine.Stateful.tableElementType type := by
  obtain ⟨sourceAddress,sourceObject,mapped,found,objectType⟩ := SourceMachine.Stateful.table_lookup bindings selected
  simp only [Store.decodeInstance,List.getElem?_map] at mapped
  obtain ⟨address,rawMapped,addressEq⟩ := Option.map_eq_some_iff.mp mapped
  simp only [Store.decodeStore,List.getElem?_map] at found
  obtain ⟨object,rawFound,objectEq⟩ := Option.map_eq_some_iff.mp found
  refine ⟨address,object,rawMapped,by simpa only [addressEq] using rawFound,?_⟩
  rw [←objectEq] at objectType
  exact objectType

theorem memory_binding_raw {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (C : context) (type : memtype)
    (bindings : SourceMachine.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst) C)
    (selected : C.MEMS[0]?=some type) :
    ∃ address object, inst.memories.val[0]?=some address ∧ store.memories.val[address.index.val]?=some object := by
  obtain ⟨sourceAddress,sourceObject,mapped,found⟩ := bindings.memory_lookup (List.getElem?_eq_some_iff.mp selected).1
  simp only [Store.decodeInstance,List.getElem?_map] at mapped
  obtain ⟨address,rawMapped,addressEq⟩ := Option.map_eq_some_iff.mp mapped
  simp only [Store.decodeStore,List.getElem?_map] at found
  obtain ⟨object,rawFound,objectEq⟩ := Option.map_eq_some_iff.mp found
  exact ⟨address,object,rawMapped,by simpa only [addressEq] using rawFound⟩

theorem function_binding_raw {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (C : context) (index : Nat) (type : functype)
    (bindings : SourceMachine.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst) C)
    (selected : C.FUNCS[index]?=some type) :
    ∃ address, inst.funcs.val[index]?=some address ∧ address.index.val<store.funcs.length := by
  have right := (List.getElem?_eq_some_iff.mp selected).1
  have left : index<(Store.decodeInstance store inst).FUNCS.length := by rw [bindings.funcs.length_eq]; exact right
  obtain ⟨sourceFunction,found,sourceType⟩ := bindings.funcs.get left right
  have mapped : (Store.decodeInstance store inst).FUNCS[index]?=some ((Store.decodeInstance store inst).FUNCS[index]) := List.getElem?_eq_getElem left
  simp only [Store.decodeInstance,List.getElem?_map] at mapped
  obtain ⟨address,rawMapped,addressEq⟩ := Option.map_eq_some_iff.mp mapped
  have issued := (List.getElem?_eq_some_iff.mp found).1
  simp only [List.get_eq_getElem,Store.decodeStore,List.length_map] at issued
  change address.index.val=(Store.decodeInstance store inst).FUNCS[index] at addressEq
  rw [←addressEq] at issued
  exact ⟨address,rawMapped,issued⟩
end Itasca.Runtime.Interp.Stateful

end

/-! ## StatefulContinue -/

section

namespace Itasca.Runtime.Interp.Machine
open Aeneas.Std

/-- An ordinary source suffix may consume and produce values above every live
label. The exact static continuation and source extension retain its point. -/
theorem FramePoint.continue {before afterStore raw f compiled C targets next output}
    (point : FramePoint before raw f compiled C targets next output)
    (extension : Extend_store before afterStore)
    (front operands results : List val) (after : List instr)
    (values : f.vals=front++operands)
    (heights : ∀ label ∈ f.labels, label.height≤front.length)
    (tail : Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Compiler.valueType++results.map Compiler.valueType) after (raw.pc.val+1) next output)
    (pc : U32) (pcNext : pc.val=raw.pc.val+1) :
    FramePoint afterStore {raw with pc:=pc} {f with code:=after,vals:=front++results}
      compiled C targets next output := by
  refine ⟨point.bindings.extend extension,point.locals,?_,?_⟩
  · have labels := point.labels
    rw [values] at labels
    exact labels.replace_suffix heights
  · simpa only [List.map_append,pcNext] using tail
end Itasca.Runtime.Interp.Machine

end

/-! ## StatefulSegmentLookup -/

section

namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std SpecExt

theorem element_binding_raw {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (C : context) (index : Nat) (type : reftype)
    (bindings : SourceMachine.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst) C)
    (selected : C.ELEMS[index]?=some type) :
    ∃ address,inst.elems.val[index]?=some address ∧ address.val<store.elems.length := by
  have right := (List.getElem?_eq_some_iff.mp selected).1
  have left : index<(Store.decodeInstance store inst).ELEMS.length := by rw [bindings.elems.length_eq];exact right
  obtain ⟨object,found,typed⟩ := bindings.elems.get left right
  have mapped : (Store.decodeInstance store inst).ELEMS[index]?=some ((Store.decodeInstance store inst).ELEMS[index]) := List.getElem?_eq_getElem left
  simp only [Store.decodeInstance,List.getElem?_map] at mapped
  obtain ⟨address,rawMapped,addressEq⟩ := Option.map_eq_some_iff.mp mapped
  have issued := (List.getElem?_eq_some_iff.mp found).1
  simp only [List.get_eq_getElem,Store.decodeStore,List.length_map] at issued
  change address.val=(Store.decodeInstance store inst).ELEMS[index] at addressEq
  rw [←addressEq] at issued
  exact ⟨address,rawMapped,issued⟩

theorem data_binding_raw {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (C : context) (index : Nat) (type : datatype)
    (bindings : SourceMachine.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst) C)
    (selected : C.DATAS[index]?=some type) :
    ∃ address,inst.datas.val[index]?=some address ∧ address.val<store.datas.length := by
  have right := (List.getElem?_eq_some_iff.mp selected).1
  have left : index<(Store.decodeInstance store inst).DATAS.length := by rw [bindings.datas.length_eq];exact right
  obtain ⟨object,found,typed⟩ := bindings.datas.get left right
  have mapped : (Store.decodeInstance store inst).DATAS[index]?=some ((Store.decodeInstance store inst).DATAS[index]) := List.getElem?_eq_getElem left
  simp only [Store.decodeInstance,List.getElem?_map] at mapped
  obtain ⟨address,rawMapped,addressEq⟩ := Option.map_eq_some_iff.mp mapped
  have issued := (List.getElem?_eq_some_iff.mp found).1
  simp only [List.get_eq_getElem,Store.decodeStore,List.length_map] at issued
  change address.val=(Store.decodeInstance store inst).DATAS[index] at addressEq
  rw [←addressEq] at issued
  exact ⟨address,rawMapped,issued⟩
theorem decode_elem_type_injective {a b : Itasca.wasm_types.ElemType}
    (equal : Store.decodeElemType a=Store.decodeElemType b) : a=b := by
  cases a <;> cases b <;> simp_all [Store.decodeElemType]

theorem element_object_binding_raw {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (C : context) (index : Nat) (type : reftype)
    (bindings : SourceMachine.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst) C)
    (selected : C.ELEMS[index]?=some type) :
    ∃ address object,inst.elems.val[index]?=some address ∧ store.elems.val[address.val]?=some object ∧ Store.decodeElemType object.ty=type := by
  have right := (List.getElem?_eq_some_iff.mp selected).1
  have left : index<(Store.decodeInstance store inst).ELEMS.length := by rw [bindings.elems.length_eq];exact right
  obtain ⟨object,found,typed⟩ := bindings.elems.get left right
  have actualType := (SourceMachine.Stateful.element_refs_typed typed).1
  have selectedEq := (List.getElem?_eq_some_iff.mp selected).2
  simp only [List.get_eq_getElem,selectedEq] at actualType
  have mapped : (Store.decodeInstance store inst).ELEMS[index]?=some ((Store.decodeInstance store inst).ELEMS[index]) := List.getElem?_eq_getElem left
  simp only [Store.decodeInstance,List.getElem?_map] at mapped
  obtain ⟨address,rawMapped,addressEq⟩ := Option.map_eq_some_iff.mp mapped
  simp only [Store.decodeStore,List.getElem?_map,List.get_eq_getElem] at found
  obtain ⟨rawObject,rawFound,objectEq⟩ := Option.map_eq_some_iff.mp found
  refine ⟨address,rawObject,rawMapped,by simpa only [addressEq,Store.decodeInstance] using rawFound,?_⟩
  rw [←objectEq] at actualType
  exact actualType
end Itasca.Runtime.Interp.Stateful

end
