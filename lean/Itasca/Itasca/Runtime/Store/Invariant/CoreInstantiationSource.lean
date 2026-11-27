import Itasca.Runtime.Compiler.Local.Source.ModuleSourceAndSubmission
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Representation.Store
import Itasca.Runtime.SourceMachine.EntryAndBranchTables
import Itasca.Runtime.Store.Api.ObjectStaging
import Itasca.Runtime.Interp.Machine.CompiledFunctions
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Store.Initialization.SegmentSyntheticPreservation
import Itasca.Runtime.Store.Invariant.SemanticApi
import Itasca.Runtime.Store.Initialization.SegmentSourceStaging

open WebAssembly

/-!
Proofs for Runtime / Store / Invariant.

This module collects OwnedInitializerErrors, CoreInstantiationSource.
Each section documents its contracts and consumers.
-/

/-! ## OwnedInitializerErrors -/

section

open Itasca.Representation

/-! ## SourceSyntax -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca

/-- Canonical source typing supplies the syntax for an installed instance. -/
theorem instance_syntax_source (oldCode : CodeInterpretation) (fresh : Nat)
    (inst : runtime.store.ModuleInst) (raw : Binary.Module)
    (elaborates : Module.Elaboration.Elaborates raw (Module.Elaboration.moduleOf raw))
    (typed : Module_ok (Module.Elaboration.moduleOf raw))
    (matched : Module.Elaboration.Matches inst.module.module.env inst.module.module.tail raw) :
    InstanceSyntax (installCode oldCode fresh (Compiler.sourceFunctions raw)) fresh inst := by
  constructor
  · intro entry member
    have exports := congrArg Binary.Module.exports matched.1
    simp only [Module.Elaboration.fromEnv] at exports
    exact Compiler.source_export_name_wf elaborates typed (Module.Environment.rawExport entry)
      (by rw [exports]; exact List.mem_map.mpr ⟨entry, member, rfl⟩)
  · intro function bound
    have functions := congrArg Binary.Module.functions matched.1
    simp only [Module.Elaboration.fromEnv] at functions
    have length : (Compiler.sourceFunctions raw).length = raw.functions.length := by
      simp only [Compiler.sourceFunctions, List.length_zipWith, elaborates.code_count, Nat.min_self]
    have sourceBound : function < (Compiler.sourceFunctions raw).length := by
      rw [length, functions]; exact bound
    let source := (Compiler.sourceFunctions raw)[function]
    have found : (Compiler.sourceFunctions raw)[function]? = some source :=
      List.getElem?_eq_some_iff.mpr ⟨sourceBound, rfl⟩
    rw [install_code_lookup oldCode fresh _ inst.module function source found]
    exact Compiler.source_functions_wf elaborates typed source (List.mem_of_getElem? found)

/-- Reinterpreting only fresh instance keys preserves all old syntax. -/
theorem StoreSyntax.code_agrees {M : Type} {store : runtime.store.Store M}
    {before after : CodeInterpretation} (hsyntax : StoreSyntax before store)
    (agrees : CodeAgreesOn store before after) : StoreSyntax after store := by
  intro index inst found
  exact ⟨(hsyntax index inst found).exportNames, fun function bound => by
    rw [agrees index inst found function]
    exact (hsyntax index inst found).functionCodes function bound⟩

/-- Store content updates do not affect the retained source syntax. -/
theorem StoreSyntax.instances_eq {M : Type} {before after : runtime.store.Store M}
    {code : CodeInterpretation} (prior : StoreSyntax code before)
    (same : after.instances = before.instances) : StoreSyntax code after := by
  simpa only [StoreSyntax, same] using prior

/-- Staging may update the fresh instance's maps while old instances remain
an exact prefix. Source syntax depends only on the retained module. -/
theorem StoreSyntax.staged {M : Type} {before after : runtime.store.Store M}
    {oldCode newCode : CodeInterpretation} (prior : StoreSyntax oldCode before)
    (agrees : CodeAgreesOn before oldCode newCode) (retained : StagedPrefix before after)
    (count : after.instances.length ≤ before.instances.length + 1)
    (fresh : ∀ inst, after.instances.val[before.instances.length]? = some inst →
      InstanceSyntax newCode before.instances.length inst) : StoreSyntax newCode after := by
  intro index inst found
  by_cases bound : index < before.instances.length
  · have same := congrArg (fun values : List runtime.store.ModuleInst => values[index]?) retained.instances
    have oldFound : before.instances.val[index]? = some inst := by
      simpa only [List.getElem?_take, if_pos bound, found] using same.symm
    exact prior.code_agrees agrees index inst oldFound
  · have room := (List.getElem?_eq_some_iff.mp found).1
    change index < after.instances.length at room
    have equal : index = before.instances.length := by omega
    subst index
    exact fresh inst found

end Itasca.Store

end

/-! ## SourceStoreTyping -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

private theorem get_d_member {α : Type} (values : List α) (index : Nat) (fallback : α)
    (bound : index < values.length) : values.getD index fallback ∈ values := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound, Option.getD_some]
  exact List.getElem_mem bound

/-- Each validated export resolves to one of its owning instance's actual
address maps, rather than merely some well-typed address in the store. -/
theorem decoded_export_member {M : Type} (s : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (bounds : ModuleExportBounds inst.module.module.env) (shape : InstanceShape s inst)
    (entry : Itasca.metadata.Export) (member : entry ∈ inst.module.module.env.exports.val) :
    (decodeExport inst entry).ADDR ∈ SourceMachine.moduleAddresses (decodeInstance s inst) := by
  have bound := export_address_bounds bounds shape entry member
  cases descriptor : entry.desc <;> simp only [descriptor] at bound
  · have mapped := get_d_member (inst.funcs.val.map (fun a => a.index.val)) _ 0 (by simpa using bound)
    simp only [decodeExport, descriptor, SourceMachine.moduleAddresses, decodeInstance, List.mem_append]
    exact Or.inr (Or.inr (Or.inr (List.mem_map.mpr ⟨_, mapped, rfl⟩)))
  · have mapped := get_d_member (inst.tables.val.map (fun a => a.index.val)) _ 0 (by simpa using bound)
    simp only [decodeExport, descriptor, SourceMachine.moduleAddresses, decodeInstance, List.mem_append]
    exact Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨_, mapped, rfl⟩)))
  · have mapped := get_d_member (inst.memories.val.map (fun a => a.index.val)) _ 0 (by simpa using bound)
    simp only [decodeExport, descriptor, SourceMachine.moduleAddresses, decodeInstance, List.mem_append]
    exact Or.inr (Or.inl (List.mem_map.mpr ⟨_, mapped, rfl⟩))
  · have mapped := get_d_member (inst.globals.val.map (fun a => a.index.val)) _ 0 (by simpa using bound)
    simp only [decodeExport, descriptor, SourceMachine.moduleAddresses, decodeInstance, List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨_, mapped, rfl⟩)

/-- Existing body certificates, component typing, completed address maps and
validated export metadata establish full source store typing, including hosts. -/
theorem decode_store_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (shape : Shape view s) (sourceSyntax : StoreSyntax code s)
    (typed : Interp.CoreFunctionsTyped view code s) (segments : SegmentBounds s)
    (exports : ExportBounds s) : Store_ok (decodeStore view code s) := by
  have storeWf := decode_store_wf view code s shape sourceSyntax
  obtain ⟨globals, tables, memories, elements, data⟩ := decoded_components_typed view code s shape sourceSyntax segments
  apply (show SourceMachine.StoreContentsTyped (decodeStore view code s) from ⟨globals, tables, memories, elements, data⟩).store_ok storeWf
  intro fn member
  obtain ⟨function, present, rfl⟩ := List.mem_map.mp member
  have body := typed function present
  have functionWf := decode_function_wf code s sourceSyntax function (shape.functions function present)
  cases kind : function.code with
  | Host id =>
    simp only [Interp.CoreFunctionTyped, kind] at body
    simp only [decodeFunction, kind] at body functionWf ⊢
    exact Funcinst_ok.host _ _ _ id.val body storeWf functionWf
  | Wasm ii fi =>
    simp only [Interp.CoreFunctionTyped, kind] at body
    obtain ⟨inst, index, locals, instructions, found, source, bindings, body⟩ := body
    have instShape := shape.instances inst (List.mem_of_getElem? found)
    have moduleWf := decode_instance_wf code ii.val s inst (sourceSyntax _ _ found)
    have exportBounds := exports ii.val inst found
    have environment : Moduleinst_ok (decodeStore view code s) (decodeInstance s inst)
        (Compiler.moduleSourceContext inst.module) := by
      apply bindings.moduleinst_ok storeWf moduleWf rfl rfl rfl
      · simpa only [decodeInstance, List.map_map, Function.comp_def, decodeExport] using exportBounds.names
      · intro entry member
        obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp member
        exact decoded_export_member s inst exportBounds instShape raw rawMember
    have signature : Functype_ok (decodeFunction code s function).TYPE := by
      cases (decodeFunction code s function).TYPE with
      | mk_functype params results => cases params; cases results; constructor
    simp only [decodeFunction, kind, found, source] at signature body functionWf ⊢
    simpa only [funccode_func] using
      Funcinst_ok.mk_Funcinst_ok _ _ _ (.FUNC index locals instructions)
        (Compiler.moduleSourceContext inst.module) signature environment body storeWf bindings.wf functionWf

end Itasca.Store

end

/-! ## SupportedFunctionTables -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem supported_function_compiled_prefix {M : Type} {view : M → Slice U8}
    {before after : runtime.store.Store M} {oldCode newCode : CodeInterpretation}
    (shape : Shape view before) (retained : StagedPrefix before after)
    (agrees : CodeAgreesOn before oldCode newCode) {function : runtime.store.FuncInst}
    (compiled : Interp.Machine.FunctionCompiled oldCode before function) :
    Interp.Machine.FunctionCompiled newCode after function := by
  intro instanceIndex functionIndex defined
  obtain ⟨inst, code, signature, declared, body, epilogue,
    found, functionFound, signatureFound, source, table, types, certificate⟩ := compiled instanceIndex functionIndex defined
  refine ⟨inst, code, signature, declared, body, epilogue,
    Itasca.Representation.lookup_prefix _ _ retained.instances found, functionFound,
    Itasca.Representation.lookup_prefix _ _ retained.types signatureFound, ?_, function_table_prefix retained table, ?_, certificate⟩
  · rw [agrees instanceIndex.val inst found functionIndex.val]
    exact source
  · rw [decode_instance_prefix before after retained inst (shape.instances inst (List.mem_of_getElem? found))]
    exact types

end Itasca.Store

end

/-! ## OwnedInitializerErrors -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)
theorem eval_const_owned_errors (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Compiler.InitializerCode code expr ty)
    (resolved : Interp.InitializerResolution store inst expr ty words)
    (bindings : InitializerBindings store inst) :
    runtime.interp.eval_const memory hooks floats allocator store platform instIndex function ty
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧
        (∀ value, out.1 = .Ok value → ValueInStore store value ∧ Representation.rawType value = ty) ∧
        ErrorAllowed ResourceError out.1 ⦄ := by
  obtain ⟨out, called, sameStore, sameHost, values⟩ := WP.spec_imp_exists
    (eval_const_owned memory hooks floats allocator law store platform instIndex function
      inst code expr ty words hi hc compiled resolved bindings)
  have errors := eval_const_errors memory hooks floats allocator law store platform instIndex function
    inst code expr ty words hi hc compiled resolved (initializer_reference_bound resolved bindings)
  rw [called] at errors
  simp only [WP.spec_ok] at errors
  refine WP.exists_imp_spec ⟨out, called, sameStore, sameHost, values, ?_⟩
  cases status : out.1 with
  | Ok value => trivial
  | Err error =>
    obtain ⟨resource, rfl⟩ := errors.2.2.2 error status
    trivial

end Itasca.Store

end

end

/-! ## CoreInstantiationSource -/

section

open Itasca.Representation

/-! ## BindingMaps -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca

theorem GlobalTypeMap.source {M : Type} {store : runtime.store.Store M} {types addresses}
    (mapping : GlobalTypeMap store types addresses) (view : M → Slice U8) (code : CodeInterpretation)
    (wellformed : wf_store (decodeStore view code store)) :
    List.Forall₂ (fun address ty => Externaddr_ok (decodeStore view code store) (.GLOBAL address) (.GLOBAL ty))
      (addresses.map (fun address => address.index.val)) (types.map Translation.globalType) := by
  induction mapping with
  | nil => exact .nil
  | cons linked rest ih => exact .cons (imported_global_typed view code store wellformed _ _ linked) ih

theorem TableBindings.source {M : Type} {store : runtime.store.Store M} {types addresses}
    (mapping : TableBindings store types addresses) (view : M → Slice U8) (code : CodeInterpretation)
    (wellformed : wf_store (decodeStore view code store)) (shape : Shape view store) :
    List.Forall₂ (fun address ty => Externaddr_ok (decodeStore view code store) (.TABLE address) (.TABLE ty))
      (addresses.map (fun address => address.index.val)) (types.map Translation.Environment.tableType) := by
  induction mapping with
  | nil => exact .nil
  | cons linked rest ih => exact .cons (imported_table_typed view code store wellformed shape _ _ linked) ih

theorem MemoryBindings.source {M : Type} {view : M → Slice U8} {store : runtime.store.Store M} {types addresses}
    (mapping : MemoryBindings view store types addresses) (code : CodeInterpretation)
    (wellformed : wf_store (decodeStore view code store)) (shape : Shape view store) :
    List.Forall₂ (fun address ty => Externaddr_ok (decodeStore view code store) (.MEM address) (.MEM ty))
      (addresses.map (fun address => address.index.val)) (types.map Translation.Environment.memType) := by
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
      (addresses.map UScalar.val) (entries.map (fun entry => Translation.referenceType entry.elem)) := by
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

end Itasca.Store

end

/-! ## SourceBindings -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca

theorem decode_func_type_source (ty : wasm_types.FuncType) : Itasca.Translation.Environment.funcType ty = Translation.Environment.funcType ty := by
  have same : Itasca.Translation.valueType = Translation.valueType := by funext t; cases t <;> rfl
  simp only [Itasca.Translation.Environment.funcType, Translation.Environment.funcType, same]

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
    (functions : Representation.FunctionTable store inst (inst.module.module.env.func_types.val.map Itasca.Translation.Environment.funcType))
    (globals : GlobalTypeMap store inst.module.module.env.global_types.val inst.globals.val)
    (tables : TableBindings store inst.module.module.env.table_types.val inst.tables.val)
    (memories : MemoryBindings view store inst.module.module.env.mem_types.val inst.memories.val)
    (segments : SegmentTypeBindings store inst) :
    SourceMachine.ModuleBindings (decodeStore view code store) (decodeInstance store inst)
      (Module.Elaboration.moduleContext inst.module.module.env
        (Translation.Environment.elementTypes inst.module.module.env) inst.module.module.tail.data.length) := by
  have decoded : Itasca.Translation.Environment.funcType = Translation.Environment.funcType := funext decode_func_type_source
  have wellformed := decode_store_wf view code store shape sourceSyntax
  have elementMap := segments.element_map instanceShape
  obtain ⟨_, _, _, _, _, _, dataCount, _, _, _, _, _, _, dataIssued⟩ := instanceShape
  constructor
  · simpa only [Module.Elaboration.moduleContext, ← decoded, decodeInstance] using (type_entries_decoded types).symm
  · simpa only [Module.Elaboration.moduleContext, Representation.FunctionsMatch, ← decoded] using functions.source view code
  · exact globals.source view code wellformed
  · exact tables.source view code wellformed shape
  · exact memories.source code wellformed shape
  · exact elementMap.source view code wellformed shape bounds
  · have result := data_addresses_typed view code store inst.datas.val wellformed bounds dataIssued
    change List.Forall₂ _ (inst.datas.val.map UScalar.val) (List.replicate inst.module.module.tail.data.length datatype.OK)
    simpa only [dataCount] using result
  · exact Module.Elaboration.module_context_wf _ _ _

/-- Source uniqueness identifies this same binding context with the independent
module used by generated function typing. -/
theorem module_bindings_source {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (raw : Binary.Module)
    (matched : Module.Elaboration.Matches inst.module.module.env inst.module.module.tail raw)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store)
    (instanceShape : InstanceShape store inst) (bounds : SegmentBounds store)
    (types : TypeEntries store inst.module.module.env.types.val inst.types.val)
    (functions : Representation.FunctionTable store inst (inst.module.module.env.func_types.val.map Itasca.Translation.Environment.funcType))
    (globals : GlobalTypeMap store inst.module.module.env.global_types.val inst.globals.val)
    (tables : TableBindings store inst.module.module.env.table_types.val inst.tables.val)
    (memories : MemoryBindings view store inst.module.module.env.mem_types.val inst.memories.val)
    (segments : SegmentTypeBindings store inst) :
    SourceMachine.ModuleBindings (decodeStore view code store) (decodeInstance store inst) (Module.Elaboration.contextOf raw) := by
  have contextEq : Module.Elaboration.contextOf raw =
      Module.Elaboration.moduleContext inst.module.module.env
        (Translation.Environment.elementTypes inst.module.module.env) inst.module.module.tail.data.length := by
    conv_lhs => rw [matched.1]
    exact Module.Elaboration.context_of_from_env matched.2
  rw [contextEq]
  exact module_bindings_env view code store inst shape sourceSyntax instanceShape bounds types functions globals tables memories segments

end Itasca.Store

end

/-! ## CoreInstantiationSource -/

section

/-!
Source function-instance typing after publication. Published Wasm function bodies establish the core source-typing component of the instantiation code certificate.
-/

/-! ## Core Source Function Instances -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca Itasca.Module.Environment

/-- New defined functions get their source typing from the independently
validated module; old function bodies use checked semantic store extension. -/
theorem core_source_functions_publish_wf {M : Type} (view : M → Slice U8)
    (before after : runtime.store.Store M) (oldCode : CodeInterpretation)
    (raw : Binary.Module)
    (beforeShape : Shape view before)
    (beforeSyntax : StoreSyntax oldCode before)
    (afterWf : wf_store (decodeStore view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) after))
    (retained : StagedPrefix before after)
    (oldTyped : Interp.CoreFunctionsTyped view oldCode before)
    (inst : runtime.store.ModuleInst)
    (found : after.instances.val[before.instances.len.val]? = some inst)
    (elaborated : Module.Elaboration.Elaborates raw (Module.Elaboration.moduleOf raw))
    (typed : Module_ok (Module.Elaboration.moduleOf raw))
    (matched : Module.Elaboration.Matches inst.module.module.env inst.module.module.tail raw)
    (bindings : SourceMachine.ModuleBindings
      (decodeStore view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) after)
      (decodeInstance after inst) (Module.Elaboration.contextOf raw))
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
    have functionsEq := congrArg Binary.Module.functions matched.1
    have typesEq := congrArg Binary.Module.types matched.1
    simp only [Module.Elaboration.fromEnv] at functionsEq typesEq
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
    have actualType : Module.Elaboration.functionType raw.types typeIndex = Itasca.Translation.Environment.funcType defined[index.val] := by
      simp only [Module.Elaboration.functionType, typeFound, Option.map_some, Option.getD_some,
        decode_func_type_source]
    rw [actualType] at sourceTyped
    have contextEq : Module.Elaboration.contextOf raw = Compiler.moduleSourceContext inst.module := by
      conv_lhs => rw [matched.1]
      exact Module.Elaboration.context_of_from_env matched.2
    simp only [Interp.CoreFunctionTyped, encoded]
    refine ⟨inst, .mk_uN typeIndex.val, entry.declared.map (fun ty => local.LOCAL (Translation.valueType ty)), entry.body, found, ?_, ?_, ?_⟩
    · exact install_code_lookup oldCode before.instances.len.val (Compiler.sourceFunctions raw) inst.module index.val _ sourceFound
    · rwa [← contextEq]
    · rw [← contextEq]
      simpa only [decodeFunction, encoded, found, List.getD_eq_getElem?_getD, List.getElem?_map, signature,
        Option.map_some, Option.getD_some, ← alloc.vec.Vec.len_val, Compiler.sourceFunctionCode, CodeEntry.function, defined] using sourceTyped

end Itasca.Store

end

/-! ## Core Instantiation Source -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca

theorem InstantiationCode.core_typed {M : Type} {view : M → Slice U8}
    {before ready : runtime.store.Store M} {inst : runtime.store.ModuleInst}
    (code : InstantiationCode before ready inst) (oldCode : CodeInterpretation)
    (raw : Binary.Module) (shape : Shape view before)
    (oldSyntax : StoreSyntax oldCode before)
    (oldTyped : Interp.CoreFunctionsTyped view oldCode before)
    (freshWf : wf_store (decodeStore view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) ready))
    (found : ready.instances.val[before.instances.len.val]? = some inst)
    (elaborated : Module.Elaboration.Elaborates raw (Module.Elaboration.moduleOf raw))
    (typed : Module_ok (Module.Elaboration.moduleOf raw))
    (matched : Module.Elaboration.Matches inst.module.module.env inst.module.module.tail raw)
    (bindings : SourceMachine.ModuleBindings
      (decodeStore view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) ready)
      (decodeInstance ready inst) (Module.Elaboration.contextOf raw)) :
    Interp.CoreFunctionsTyped view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) ready := by
  obtain ⟨staged, count, rfl, retained, entries, table, signatures⟩ := code
  exact core_source_functions_publish_wf view before staged oldCode raw shape oldSyntax freshWf retained
    oldTyped inst found elaborated typed matched bindings signatures

end Itasca.Store

end

end

end
