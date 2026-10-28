import Itasca.Runtime.Store.Instantiation.LinkedPreparedRun
import Itasca.Runtime.Store.Linking.LinkExternalLoop
import Itasca.Runtime.Store.Linking.LinkLoop
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca.ModuleEnv

theorem LinkedPreparedRun.external_maps {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {imports : Slice runtime.Extern}
    {platform : P} {ready : runtime.store.Store M}
    (trace : LinkedPreparedRun memory hooks floats allocator view before module imports platform ready)
    (laws : Platform.MemoryLaws memory view) (shape : Shape view before)
    {tables memories} (cache : Cache module.module.env tables memories)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external) :
    ExternalMaps imports.val trace.seed := by
  have maps : LinkedMaps view before module (module.module.env.imports.val.take 0) (emptyInstance module) := by
    simpa only [List.take_zero, emptyInstance] using linked_maps_empty view before (emptyInstance module)
      rfl rfl rfl rfl rfl rfl rfl
  have emptyMaps : ExternalMaps (imports.val.take 0) (emptyInstance module) := by
    constructor <;> simp [emptyInstance, externalFunctions, externalTables, externalMemories, externalGlobals]
  have checked := link_external_maps_loop memory view laws before shape module imports trace.importsLength
    handles cache (emptyInstance module) 0#usize (by simp) maps emptyMaps
  rw [trace.linkRun] at checked
  simp only [WP.spec_ok] at checked
  exact (checked.2.2 True.intro).2

theorem ExternalMaps.source (externals : List runtime.Extern) (inst : runtime.store.ModuleInst)
    (maps : ExternalMaps externals inst) :
    fun_funcs (externals.map decodeExternal) (inst.funcs.val.map fun a => a.index.val) ∧
    fun_globals (externals.map decodeExternal) (inst.globals.val.map fun a => a.index.val) ∧
    fun_tables (externals.map decodeExternal) (inst.tables.val.map fun a => a.index.val) ∧
    fun_mems (externals.map decodeExternal) (inst.memories.val.map fun a => a.index.val) := by
  rw [maps.funcs, maps.globals, maps.tables, maps.memories]
  exact ⟨external_functions externals, external_globals externals, external_tables externals,
    external_memories externals⟩
end Itasca.Runtime.Store
