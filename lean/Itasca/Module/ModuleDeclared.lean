import Itasca.Module.ModuleAssembly

open Aeneas Aeneas.Std

namespace Itasca.ModuleReferences

open ModuleElaboration

theorem global_indices (entry : module.Global) :
    DeclaredReferences.globalIndices (ModuleConstants.global entry) =
      (global entry).map (fun index => uN.mk_uN index.val) :=
  initializer_indices entry.init

theorem export_indices (entry : module.Export) :
    DeclaredReferences.exportIndices (exportDecl (ModuleEnv.rawExport entry)) =
      (exportIndices entry).map (fun index => uN.mk_uN index.val) := by
  cases h : entry.desc <;>
    simp [DeclaredReferences.exportIndices, exportDecl, exportIndex,
      ModuleEnv.rawExport, exportIndices, h]

theorem element_member {entry : module.Element} {idx : U32} (h : idx ∈ element entry) :
    uN.mk_uN idx.val ∈ DeclaredReferences.elementIndices
      (ModuleElaboration.element (ModuleEnv.rawElement entry)) := by
  obtain ⟨init, hi, hidx⟩ := List.mem_flatMap.mp h
  simp only [ModuleElaboration.element, ModuleEnv.rawElement, DeclaredReferences.elementIndices]
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨ModuleConstants.expression init, List.mem_map.mpr ⟨init, hi, rfl⟩, ?_⟩
  rw [initializer_indices]
  exact List.mem_map.mpr ⟨idx, hidx, rfl⟩

theorem valid_i32_initializer {env init} (h : ModuleConstants.Valid env init .I32) :
    initializer init = [] := by
  generalize ht : types.ValueType.I32 = ty at h
  cases h <;> try rfl
  cases ht

theorem element_indices {env entry} (h : ModuleSegments.elementValid env entry) :
    DeclaredReferences.elementIndices (ModuleElaboration.element (ModuleEnv.rawElement entry)) =
      (element entry).map (fun index => uN.mk_uN index.val) := by
  have hoffset : DeclaredReferences.elementModeIndices (ModuleSegments.elementMode entry.mode) = [] := by
    cases hm : entry.mode with
    | Passive => rfl
    | Declarative => rfl
    | Active index offset =>
      obtain ⟨hi, ht, ho⟩ := (show ∃ hi : index.val < env.table_types.val.length,
        env.table_types.val[index.val].elem = entry.elem ∧ ModuleConstants.Valid env offset .I32 from by simpa [hm] using h.1)
      simp [ModuleSegments.elementMode, DeclaredReferences.elementModeIndices,
        initializer_indices, valid_i32_initializer ho]
  simp [ModuleElaboration.element, ModuleEnv.rawElement, DeclaredReferences.elementIndices,
    hoffset, List.flatMap_map, initializer_indices, element, List.map_flatMap]

theorem data_indices {env entry} (h : ModuleData.Valid env entry) :
    DeclaredReferences.dataIndices (ModuleData.translate (ModuleData.raw entry)) = [] := by
  cases hm : entry.mode with
  | Passive => simp [ModuleData.translate, ModuleData.raw, hm, ModuleSegments.dataMode, DeclaredReferences.dataIndices]
  | Active index offset =>
    obtain ⟨hi, ho⟩ := (show index.val < env.mem_types.val.length ∧ ModuleConstants.Valid env offset .I32 from by simpa [ModuleData.Valid, hm] using h)
    simp [ModuleData.translate, ModuleData.raw, hm, ModuleSegments.dataMode,
      DeclaredReferences.dataIndices, initializer_indices, valid_i32_initializer ho]

/-- Every runtime reference declaration is a syntactic declaration in the
independently elaborated complete module. Offset declarations can only enlarge
that set, so this implication needs no typing premise. -/
theorem collected_declared {env : module.Env} {tables memories codes segments}
    {idx : U32} (h : idx ∈ collected env) :
    uN.mk_uN idx.val ∈ DeclaredReferences.declarations
      (moduleOf (fromEnv env tables memories codes segments)) := by
  simp only [collected, List.mem_append] at h
  simp only [DeclaredReferences.declarations, moduleOf, fromEnv,
    List.flatMap_map, List.mem_append, List.mem_flatMap]
  rcases h with (hg | he) | hel
  · obtain ⟨entry, hm, hi⟩ := List.mem_flatMap.mp hg
    apply Or.inl
    apply Or.inl
    apply Or.inl
    refine ⟨entry, hm, ?_⟩
    rw [global_indices]
    exact List.mem_map.mpr ⟨idx, hi, rfl⟩
  · obtain ⟨entry, hm, hi⟩ := List.mem_flatMap.mp he
    apply Or.inr
    refine ⟨entry, hm, ?_⟩
    rw [export_indices]
    exact List.mem_map.mpr ⟨idx, hi, rfl⟩
  · obtain ⟨entry, hm, hi⟩ := List.mem_flatMap.mp hel
    exact Or.inl (Or.inl (Or.inr ⟨entry, hm, element_member hi⟩))

theorem coherent_declared {env : module.Env} {tables memories codes segments}
    (h : Coherent env) :
    ∀ index ∈ env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val),
      index ∈ DeclaredReferences.declarations
        (moduleOf (fromEnv env tables memories codes segments)) := by
  intro index hm
  obtain ⟨idx, hi, rfl⟩ := List.mem_map.mp hm
  rw [h] at hi
  exact collected_declared hi

/-- Typing forces every segment offset to be an i32 constant expression, so
all syntactic function declarations are represented in the runtime cache. -/
theorem coherent_declared_iff {env : module.Env} {tables memories codes segments}
    (hc : Coherent env) (he : ∀ entry ∈ env.elements.val, ModuleSegments.elementValid env entry)
    (hd : ∀ entry ∈ segments, ModuleData.Valid env entry) (index : funcidx) :
    index ∈ env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val) ↔
      index ∈ DeclaredReferences.declarations (moduleOf (fromEnv env tables memories codes segments)) := by
  have helem : env.elements.val.flatMap (fun e =>
      DeclaredReferences.elementIndices (ModuleElaboration.element (ModuleEnv.rawElement e))) =
      env.elements.val.flatMap (fun e => (element e).map (fun idx => uN.mk_uN idx.val)) := by
    apply List.flatMap_congr
    intro e hm
    exact element_indices (he e hm)
  have hdata : segments.flatMap (fun d => DeclaredReferences.dataIndices (ModuleData.translate (ModuleData.raw d))) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro d hm
    exact data_indices (hd d hm)
  change env.declared_funcs.val = collected env at hc
  rw [hc]
  simp only [collected, List.map_append, List.map_flatMap,
    DeclaredReferences.declarations, moduleOf, fromEnv, List.flatMap_map,
    global_indices, export_indices, helem, hdata, List.append_nil,
    List.mem_append]
  tauto

end Itasca.ModuleReferences
