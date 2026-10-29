import Itasca.Runtime.Store.Instantiation.PreparedRun
import Itasca.Runtime.Store.Instantiation.PreparedSegmentBounds
import Itasca.Runtime.Compiler.Module.SegmentPayloadBounds
import Itasca.Runtime.Compiler.Module.CompileCache
import Itasca.Runtime.Compiler.Module.CompileSemantic
import Itasca.Runtime.Store.Instantiation.PreparedGlobalTypes
import Itasca.Runtime.Store.Instantiation.PreparedCommitShape

/-!
Prepared instance segment bounds, global types and store shape from compiler certificates. The PreparedRun relation remains separate for consumers that do not need compiler semantic proofs.
-/

/-! ## Prepared Run Bounds -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem PreparedRun.segment_bounds {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (shape : Shape view before) (accounted : SegmentAccounting before) (bounded : SegmentBounds before)
    {tables memories} (cache : Itasca.ModuleEnv.Cache module.module.env tables memories)
    (valid : Itasca.ModuleEnv.Valid module.module.env module.profile)
    (compiled : Compiler.InitializerMappings module)
    (elementBounds : ∀ element ∈ module.module.env.elements.val, element.init.length < 2^32)
    (dataBounds : ∀ data ∈ module.module.tail.data.val, data.init.length < 2^32) : SegmentBounds ready := by
  have prepared := prepared_commit_segment_bounds memory hooks floats allocator law view laws before trace.seed platform
    shape accounted bounded (by simpa only [trace.source] using elementBounds)
    (by simpa only [trace.source] using dataBounds) trace.maps
    (by simpa only [trace.source] using cache) (by simpa only [trace.source] using valid)
    (by simpa only [trace.source] using compiled) trace.instanceRoom trace.elementCapacity trace.dataCapacity
    trace.typed trace.functions trace.tabled trace.prepared trace.typeInst trace.funcInst trace.tableInst trace.inst
    trace.typeRun trace.functionRun trace.tableRun trace.memoryRun trace.publishedInstances trace.publicationRun
    trace.globalStore trace.elementStore trace.dataStore trace.globalRun trace.elementRun trace.dataRun
  rw [trace.committed]
  exact prepared.same rfl rfl

/-- Actual successful compilation discharges every source-count obligation of
preparation; the retained call trace then transports the old store bounds. -/
theorem PreparedRun.compiled_segment_bounds {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (shape : Shape view before) (accounted : SegmentAccounting before) (bounded : SegmentBounds before)
    (bytes : Slice U8) (profile : Itasca.ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module)) : SegmentBounds ready := by
  obtain ⟨witness⟩ := Compiler.compile_accepted allocator bytes profile limits module accepted
  obtain ⟨tables, memories, cache⟩ := witness.cache law
  have certificates := witness.initializers law
  obtain ⟨valid, _⟩ := witness.semantic law
  have actualValid : Itasca.ModuleEnv.Valid module.module.env module.profile := by
    rw [certificates.2.1]
    exact valid
  obtain ⟨elementBounds, dataBounds⟩ := Compiler.compile_segment_payload_bounds allocator law bytes profile limits module accepted
  exact trace.segment_bounds laws law shape accounted bounded cache actualValid certificates.2.2.2 elementBounds dataBounds
end Itasca.Runtime.Store

end

/-! ## Prepared Run Global Types -/

section

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
    (compiled : Compiler.InitializerMappings module)
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

end

/-! ## Prepared Run Shape -/

section

namespace Itasca.Runtime.Store
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
    (compiled : Compiler.InitializerMappings module)
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
end Itasca.Runtime.Store

end
