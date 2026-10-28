import Itasca.Runtime.Store.Instantiation.PreparedRun
import Itasca.Runtime.Store.Instantiation.PreparedGlobalTypes
import Itasca.Runtime.Code.Module.SegmentPayloadBounds
import Itasca.Runtime.Code.Module.CompileCache
import Itasca.Runtime.Code.Module.CompileSemantic
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem PreparedRun.global_types {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    {tables memories} (cache : Itasca.ModuleEnv.Cache module.module.env tables memories)
    (valid : Itasca.ModuleEnv.Valid module.module.env module.profile)
    (compiled : Code.InitializerMappings module)
    : ∃ inst, ready.instances.val[before.instances.len.val]? = some inst ∧ inst.module = module ∧
      ready.instances.length = before.instances.length + 1 ∧
      GlobalTypeMap ready module.module.env.global_types.val inst.globals.val ∧
      ElementTypeMap ready module.module.env.elements.val inst.elems.val := by
  obtain ⟨inst, found, source, count, globals, elements⟩ := prepared_commit_global_types memory hooks floats allocator law view laws before trace.seed platform
    shape accounted trace.maps
    (by simpa only [trace.source] using cache) (by simpa only [trace.source] using valid)
    (by simpa only [trace.source] using compiled) trace.instanceRoom trace.elementCapacity trace.dataCapacity
    trace.typed trace.functions trace.tabled trace.prepared trace.typeInst trace.funcInst trace.tableInst trace.inst
    trace.typeRun trace.functionRun trace.tableRun trace.memoryRun trace.publishedInstances trace.publicationRun
    trace.globalStore trace.elementStore trace.dataStore trace.globalRun trace.elementRun trace.dataRun
  rw [trace.committed]
  exact ⟨inst, found, source.trans trace.source, count, by
    simpa only [trace.source] using globals.prefix
      (after := {trace.dataStore with instance_items := trace.charged}) rfl (by simp),
    by simpa only [trace.source, ElementTypeMap] using elements⟩

end Itasca.Runtime.Store
