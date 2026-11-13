import Itasca.Runtime.Compiler.Local.Source.SourceSegmentPrograms
import Itasca.Runtime.Store.Invariant.CodeAgreement
import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Representation.StoreCapacity
import Itasca.Runtime.SourceMachine.BrTable
import Itasca.Runtime.Store.Api.MemoryBindingLoop
import Itasca.Runtime.Interp.Machine.Functions.CompiledFunctions
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Store.Initialization.InitializerErrors
import Itasca.Runtime.Store.Invariant.PrecommitError

/-!
Sections, each formerly its own module: SourceSyntax, SourceStoreTyping, SupportedFunctionTables, OwnedInitializerErrors.
-/

/-! ## SourceSyntax -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

/-- Canonical source typing supplies the syntax for an installed instance. -/
theorem instance_syntax_source (oldCode : CodeInterpretation) (fresh : Nat)
    (inst : runtime.store.ModuleInst) (raw : ModuleBinary.Module)
    (elaborates : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw))
    (matched : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw) :
    InstanceSyntax (installCode oldCode fresh (Compiler.sourceFunctions raw)) fresh inst := by
  constructor
  · intro entry member
    rw [decode_name_source]
    have exports := congrArg ModuleBinary.Module.exports matched.1
    simp only [ModuleElaboration.fromEnv] at exports
    exact Compiler.source_export_name_wf elaborates typed (ModuleEnv.rawExport entry)
      (by rw [exports]; exact List.mem_map.mpr ⟨entry, member, rfl⟩)
  · intro function bound
    have functions := congrArg ModuleBinary.Module.functions matched.1
    simp only [ModuleElaboration.fromEnv] at functions
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

end Itasca.Runtime.Store

end

/-! ## SourceStoreTyping -/

section

namespace Itasca.Runtime.Store
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
      · simpa only [decodeInstance, List.map_map, Function.comp_def, decodeExport, decode_name_source] using exportBounds.names
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

end Itasca.Runtime.Store

end

/-! ## SupportedFunctionTables -/

section

namespace Itasca.Runtime.Store
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
    Itasca.Runtime.Representation.lookup_prefix _ _ retained.instances found, functionFound,
    Itasca.Runtime.Representation.lookup_prefix _ _ retained.types signatureFound, ?_, function_table_prefix retained table, ?_, certificate⟩
  · rw [agrees instanceIndex.val inst found functionIndex.val]
    exact source
  · rw [decode_instance_prefix before after retained inst (shape.instances inst (List.mem_of_getElem? found))]
    exact types

end Itasca.Runtime.Store

end

/-! ## OwnedInitializerErrors -/

section

namespace Itasca.Runtime.Store
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
        (∀ value, out.1 = .Ok value → ValueInStore store value ∧ Interp.rawType value = ty) ∧
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

end Itasca.Runtime.Store

end
