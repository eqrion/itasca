import Itasca.Runtime.SourceMachine.StoreTyping
import Itasca.Runtime.Store.Api.ExportBounds
import Itasca.Runtime.Representation.NameSource
import Itasca.Runtime.Interp.Machine.Functions.Typing
import Itasca.Runtime.Store.Invariant.Typing

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
    (entry : Itasca.module.Export) (member : entry ∈ inst.module.module.env.exports.val) :
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
