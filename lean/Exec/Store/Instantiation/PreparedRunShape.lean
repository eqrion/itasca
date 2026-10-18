import Exec.Store.Instantiation.PreparedRun
import Exec.Store.Instantiation.PreparedCommitShape
import Exec.Code.Module.SegmentPayloadBounds
import Exec.Code.Module.CompileCache
import Exec.Code.Module.CompileSemantic
namespace Exec.Store
open Aeneas Aeneas.Std

theorem PreparedRun.shape_data {M P F A : Type}
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
    : ∃ inst, trace.dataStore.instances.val[before.instances.len.val]? = some inst ∧ inst.module = module ∧
      Shape view ready ∧ SegmentTypeBindings trace.dataStore inst ∧
      StagedPrefix before trace.dataStore ∧ SegmentAccounting trace.dataStore ∧
      InstantiationCode before ready inst := by
  obtain ⟨inst, found, source, shaped, segments, retained, segmentAccounting, code⟩ :=
    prepared_commit_shape memory hooks floats allocator law view laws before trace.seed platform
      shape accounted trace.maps (by simpa only [trace.source] using cache)
      (by simpa only [trace.source] using valid) (by simpa only [trace.source] using compiled)
      trace.instanceRoom trace.elementCapacity trace.dataCapacity trace.charged trace.counted trace.limited
      trace.typed trace.functions trace.tabled trace.prepared trace.typeInst trace.funcInst trace.tableInst trace.inst
      trace.typeRun trace.functionRun trace.tableRun trace.memoryRun trace.publishedInstances trace.publicationRun
      trace.globalStore trace.elementStore trace.dataStore trace.globalRun trace.elementRun trace.dataRun
  exact ⟨inst, found, source.trans trace.source, by simpa only [trace.committed] using shaped,
    segments, retained, segmentAccounting, by simpa only [trace.committed] using code⟩
end Exec.Store
