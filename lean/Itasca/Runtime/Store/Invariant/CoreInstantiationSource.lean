import Itasca.Runtime.Store.Invariant.SemanticApi
import Itasca.Runtime.Store.Initialization.ElementTypes
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Store.Initialization.SegmentExtension
import Itasca.Runtime.Compiler.Local.Source.SourceFunctionTyping
import Itasca.Runtime.Store.Invariant.OwnedInitializerErrors
import Itasca.Runtime.Store.Invariant.CodeAgreement
import Itasca.Runtime.Store.Invariant.ErrorPost
import Itasca.Runtime.Interp.Machine.Functions.CompiledFunctions
import Itasca.Runtime.Compiler.Local.Source.SourceBatchLookup
import Itasca.Runtime.Compiler.Local.Source.SourceSlice

/-!
Sections, each formerly its own module: BindingMaps, SourceBindings, CoreInstantiationSource.
-/

/-! ## BindingMaps -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

theorem GlobalTypeMap.source {M : Type} {store : runtime.store.Store M} {types addresses}
    (mapping : GlobalTypeMap store types addresses) (view : M → Slice U8) (code : CodeInterpretation)
    (wellformed : wf_store (decodeStore view code store)) :
    List.Forall₂ (fun address ty => Externaddr_ok (decodeStore view code store) (.GLOBAL address) (.GLOBAL ty))
      (addresses.map (fun address => address.index.val)) (types.map Translate.globalType) := by
  induction mapping with
  | nil => exact .nil
  | cons linked rest ih => exact .cons (imported_global_typed view code store wellformed _ _ linked) ih

theorem TableBindings.source {M : Type} {store : runtime.store.Store M} {types addresses}
    (mapping : TableBindings store types addresses) (view : M → Slice U8) (code : CodeInterpretation)
    (wellformed : wf_store (decodeStore view code store)) (shape : Shape view store) :
    List.Forall₂ (fun address ty => Externaddr_ok (decodeStore view code store) (.TABLE address) (.TABLE ty))
      (addresses.map (fun address => address.index.val)) (types.map EnvTranslation.tableType) := by
  induction mapping with
  | nil => exact .nil
  | cons linked rest ih => exact .cons (imported_table_typed view code store wellformed shape _ _ linked) ih

theorem MemoryBindings.source {M : Type} {view : M → Slice U8} {store : runtime.store.Store M} {types addresses}
    (mapping : MemoryBindings view store types addresses) (code : CodeInterpretation)
    (wellformed : wf_store (decodeStore view code store)) (shape : Shape view store) :
    List.Forall₂ (fun address ty => Externaddr_ok (decodeStore view code store) (.MEM address) (.MEM ty))
      (addresses.map (fun address => address.index.val)) (types.map EnvTranslation.memType) := by
  induction mapping with
  | nil => exact .nil
  | cons linked rest ih => exact .cons (imported_memory_typed view code store wellformed shape _ _ linked) ih

theorem ElementTypeMap.source {M : Type} {store : runtime.store.Store M} {entries addresses}
    (mapping : ElementTypeMap store entries addresses) (view : M → Slice U8) (code : CodeInterpretation)
    (wellformed : wf_store (decodeStore view code store)) (shape : Shape view store)
    (bounds : SegmentBounds store) :
    List.Forall₂ (fun address ty => ∃ element,
      (decodeStore view code store).ELEMS[address]? = some element ∧
      Eleminst_ok (decodeStore view code store) element ty)
      (addresses.map UScalar.val) (entries.map (fun entry => Translate.referenceType entry.elem)) := by
  induction mapping with
  | nil => exact .nil
  | cons linked rest ih =>
    obtain ⟨segment, found, typed⟩ := linked
    apply List.Forall₂.cons ?_ ih
    refine ⟨decodeElement segment, ?_, ?_⟩
    · simp only [decodeStore, List.getElem?_map, found, Option.map_some]
    · have checked := decode_element_typed view code store wellformed segment
        (shape.elements segment (List.mem_of_getElem? found)) (bounds.elements segment (List.mem_of_getElem? found))
      simpa only [decodeElement, typed, decode_elem_type_source] using checked

theorem data_addresses_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (addresses : List Usize)
    (wellformed : wf_store (decodeStore view code store)) (bounds : SegmentBounds store)
    (issued : ∀ address ∈ addresses, address.val < store.datas.length) :
    List.Forall₂ (fun address ty => ∃ segment,
      (decodeStore view code store).DATAS[address]? = some segment ∧
      Datainst_ok (decodeStore view code store) segment ty)
      (addresses.map UScalar.val) (List.replicate addresses.length datatype.OK) := by
  induction addresses with
  | nil => exact .nil
  | cons address rest ih =>
    have bound := issued address (by simp)
    let segment := store.datas.val[address.val]
    have found : store.datas.val[address.val]? = some segment := List.getElem?_eq_getElem bound
    apply List.Forall₂.cons
    · refine ⟨decodeData segment, ?_, ?_⟩
      · simp only [decodeStore, List.getElem?_map, found, Option.map_some]
      · exact decode_data_typed _ wellformed segment (bounds.data segment (List.mem_of_getElem? found))
    · exact ih (fun value member => issued value (by simp [member]))

end Itasca.Runtime.Store

end

/-! ## SourceBindings -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

theorem decode_func_type_source (ty : wasm_types.FuncType) : decodeFuncType ty = EnvTranslation.funcType ty := by
  have same : Interp.sourceType = Translate.valueType := by funext t; cases t <;> rfl
  simp only [decodeFuncType, EnvTranslation.funcType, same]

theorem SegmentTypeBindings.element_map {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} (bindings : SegmentTypeBindings store inst)
    (shape : InstanceShape store inst) :
    ElementTypeMap store inst.module.module.env.elements.val inst.elems.val := by
  obtain ⟨_, _, _, _, _, count, _, _, _, _, _, _, issued, _⟩ := shape
  apply List.forall₂_of_length_eq_of_get (by exact count.symm)
  intro index sourceBound addressBound
  let source := inst.module.module.env.elements.val[index]
  let address := inst.elems.val[index]
  have mapped : inst.elems.val[index]? = some address := List.getElem?_eq_getElem addressBound
  have bound := issued address (List.mem_of_getElem? mapped)
  let element := store.elems.val[address.val]
  have found : store.elems.val[address.val]? = some element := List.getElem?_eq_getElem bound
  refine ⟨element, found, ?_⟩
  exact bindings.elements index source address element (List.getElem?_eq_getElem sourceBound) mapped found

/-- All module namespaces are tied to their issued runtime maps and the exact
canonical source environment. Import subtyping is discharged by the generated
external-address rules. -/
theorem module_bindings_env {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store)
    (instanceShape : InstanceShape store inst) (bounds : SegmentBounds store)
    (types : TypeEntries store inst.module.module.env.types.val inst.types.val)
    (functions : Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map decodeFuncType))
    (globals : GlobalTypeMap store inst.module.module.env.global_types.val inst.globals.val)
    (tables : TableBindings store inst.module.module.env.table_types.val inst.tables.val)
    (memories : MemoryBindings view store inst.module.module.env.mem_types.val inst.memories.val)
    (segments : SegmentTypeBindings store inst) :
    SourceMachine.ModuleBindings (decodeStore view code store) (decodeInstance store inst)
      (ModuleElaboration.moduleContext inst.module.module.env
        (EnvTranslation.elementTypes inst.module.module.env) inst.module.module.tail.data.length) := by
  have decoded : decodeFuncType = EnvTranslation.funcType := funext decode_func_type_source
  have wellformed := decode_store_wf view code store shape sourceSyntax
  have elementMap := segments.element_map instanceShape
  obtain ⟨_, _, _, _, _, _, dataCount, _, _, _, _, _, _, dataIssued⟩ := instanceShape
  constructor
  · simpa only [ModuleElaboration.moduleContext, ← decoded, decodeInstance] using (type_entries_decoded types).symm
  · simpa only [ModuleElaboration.moduleContext, Interp.FunctionsMatch, ← decoded] using functions.source view code
  · exact globals.source view code wellformed
  · exact tables.source view code wellformed shape
  · exact memories.source code wellformed shape
  · exact elementMap.source view code wellformed shape bounds
  · have result := data_addresses_typed view code store inst.datas.val wellformed bounds dataIssued
    change List.Forall₂ _ (inst.datas.val.map UScalar.val) (List.replicate inst.module.module.tail.data.length datatype.OK)
    simpa only [dataCount] using result
  · exact ModuleElaboration.moduleContext_wf _ _ _

/-- Source uniqueness identifies this same binding context with the independent
module used by generated function typing. -/
theorem module_bindings_source {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (raw : ModuleBinary.Module)
    (matched : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store)
    (instanceShape : InstanceShape store inst) (bounds : SegmentBounds store)
    (types : TypeEntries store inst.module.module.env.types.val inst.types.val)
    (functions : Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map decodeFuncType))
    (globals : GlobalTypeMap store inst.module.module.env.global_types.val inst.globals.val)
    (tables : TableBindings store inst.module.module.env.table_types.val inst.tables.val)
    (memories : MemoryBindings view store inst.module.module.env.mem_types.val inst.memories.val)
    (segments : SegmentTypeBindings store inst) :
    SourceMachine.ModuleBindings (decodeStore view code store) (decodeInstance store inst) (ModuleElaboration.contextOf raw) := by
  have contextEq : ModuleElaboration.contextOf raw =
      ModuleElaboration.moduleContext inst.module.module.env
        (EnvTranslation.elementTypes inst.module.module.env) inst.module.module.tail.data.length := by
    conv_lhs => rw [matched.1]
    exact ModuleElaboration.contextOf_fromEnv matched.2
  rw [contextEq]
  exact module_bindings_env view code store inst shape sourceSyntax instanceShape bounds types functions globals tables memories segments

end Itasca.Runtime.Store

end

/-! ## CoreInstantiationSource -/

section

/-!
Source function-instance typing after publication. Published Wasm function bodies establish the core source-typing component of the instantiation code certificate.
-/

/-! ## Core Source Function Instances -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca Itasca.ModuleEnv

/-- New defined functions get their source typing from the independently
validated module; old function bodies use checked semantic store extension. -/
theorem core_source_functions_publish_wf {M : Type} (view : M → Slice U8)
    (before after : runtime.store.Store M) (oldCode : CodeInterpretation)
    (raw : ModuleBinary.Module)
    (beforeShape : Shape view before)
    (beforeSyntax : StoreSyntax oldCode before)
    (afterWf : wf_store (decodeStore view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) after))
    (retained : StagedPrefix before after)
    (oldTyped : Interp.CoreFunctionsTyped view oldCode before)
    (inst : runtime.store.ModuleInst)
    (found : after.instances.val[before.instances.len.val]? = some inst)
    (elaborated : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw))
    (matched : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw)
    (bindings : SourceMachine.ModuleBindings
      (decodeStore view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) after)
      (decodeInstance after inst) (ModuleElaboration.contextOf raw))
    (staged : StagedFunctionSignatures before after before.instances.len
      (inst.module.module.env.func_types.val.drop (importedFuncs inst.module.module.env.imports.val).length)) :
    Interp.CoreFunctionsTyped view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) after := by
  intro function member
  rcases staged function member with old | ⟨index, bound, encoded, signature⟩
  · have agrees := install_code_agrees before oldCode (Compiler.sourceFunctions raw)
    have prior : Interp.CoreFunctionsTyped view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) before :=
      core_functions_typed_code_agrees agrees oldTyped
    exact staged_core_function_typed_old_wf view _ before after beforeShape (beforeSyntax.code_agrees agrees)
      afterWf retained prior function old
  · let defined := inst.module.module.env.func_types.val.drop (importedFuncs inst.module.module.env.imports.val).length
    have resolves : List.Forall₂ (Resolves inst.module.module.env.types.val)
        inst.module.module.env.func_type_indices.val defined := by
      simpa only [defined, List.drop_left] using
        List.forall₂_drop (importedFuncs inst.module.module.env.imports.val).length matched.2.funcs
    have sourceBound : index.val < inst.module.module.env.func_type_indices.val.length := by
      rw [resolves.length_eq]; exact bound
    let typeIndex := inst.module.module.env.func_type_indices.val[index.val]
    have sourceIndex : inst.module.module.env.func_type_indices.val[index.val]? = some typeIndex := List.getElem?_eq_getElem sourceBound
    have functionsEq := congrArg ModuleBinary.Module.functions matched.1
    have typesEq := congrArg ModuleBinary.Module.types matched.1
    simp only [ModuleElaboration.fromEnv] at functionsEq typesEq
    have rawIndex : raw.functions[index.val]? = some typeIndex := by rw [functionsEq]; exact sourceIndex
    have codeBound : index.val < raw.codes.length := by rw [← elaborated.code_count, functionsEq]; exact sourceBound
    let entry := raw.codes[index.val]
    have entryFound : raw.codes[index.val]? = some entry := List.getElem?_eq_getElem codeBound
    have sourceFound := Compiler.source_functions_lookup rawIndex entryFound
    have resolved := resolves.get sourceBound bound
    simp only [List.get_eq_getElem] at resolved
    obtain ⟨typeBound, equal⟩ := resolved
    have typeFound : raw.types[typeIndex.val]? = some defined[index.val] := by
      rw [typesEq, List.getElem?_eq_getElem typeBound, equal]
    have sourceTyped := Compiler.source_function_typed elaborated typed index.val typeIndex entry rawIndex entryFound
    have actualType : ModuleElaboration.functionType raw.types typeIndex = decodeFuncType defined[index.val] := by
      simp only [ModuleElaboration.functionType, typeFound, Option.map_some, Option.getD_some,
        decode_func_type_source]
    rw [actualType] at sourceTyped
    have contextEq : ModuleElaboration.contextOf raw = Compiler.moduleSourceContext inst.module := by
      conv_lhs => rw [matched.1]
      exact ModuleElaboration.contextOf_fromEnv matched.2
    simp only [Interp.CoreFunctionTyped, encoded]
    refine ⟨inst, .mk_uN typeIndex.val, entry.declared.map (fun ty => local.LOCAL (Translate.valueType ty)), entry.body, found, ?_, ?_, ?_⟩
    · exact install_code_lookup oldCode before.instances.len.val (Compiler.sourceFunctions raw) inst.module index.val _ sourceFound
    · rwa [← contextEq]
    · rw [← contextEq]
      simpa only [decodeFunction, encoded, found, List.getD_eq_getElem?_getD, List.getElem?_map, signature,
        Option.map_some, Option.getD_some, ← alloc.vec.Vec.len_val, Compiler.sourceFunctionCode, CodeEntry.function, defined] using sourceTyped

end Itasca.Runtime.Store

end

/-! ## Core Instantiation Source -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

theorem InstantiationCode.core_typed {M : Type} {view : M → Slice U8}
    {before ready : runtime.store.Store M} {inst : runtime.store.ModuleInst}
    (code : InstantiationCode before ready inst) (oldCode : CodeInterpretation)
    (raw : ModuleBinary.Module) (shape : Shape view before)
    (oldSyntax : StoreSyntax oldCode before)
    (oldTyped : Interp.CoreFunctionsTyped view oldCode before)
    (freshWf : wf_store (decodeStore view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) ready))
    (found : ready.instances.val[before.instances.len.val]? = some inst)
    (elaborated : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw))
    (matched : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw)
    (bindings : SourceMachine.ModuleBindings
      (decodeStore view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) ready)
      (decodeInstance ready inst) (ModuleElaboration.contextOf raw)) :
    Interp.CoreFunctionsTyped view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) ready := by
  obtain ⟨staged, count, rfl, retained, entries, table, signatures⟩ := code
  exact core_source_functions_publish_wf view before staged oldCode raw shape oldSyntax freshWf retained
    oldTyped inst found elaborated typed matched bindings signatures

end Itasca.Runtime.Store

end

end
