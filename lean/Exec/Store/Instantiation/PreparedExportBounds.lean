import Exec.Store.Api.ExportBounds
import Exec.Store.Instantiation.PreparedRunShape
import Exec.Store.Instantiation.PreparedRunGlobalTypes
namespace Exec.Store
open Aeneas Aeneas.Std

/-- The actual publication and initializer staging calls preserve old export
bounds and install the fresh bounds established by module validation. -/
theorem PreparedRun.export_bounds {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    {tables memories} (cache : Itasca.ModuleEnv.Cache module.module.env tables memories)
    (valid : Itasca.ModuleEnv.Valid module.module.env module.profile)
    (compiled : Code.InitializerMappings module) (old : ExportBounds before) : ExportBounds ready := by
  obtain ⟨inst,found,source,_,_,retained,_,_⟩ := trace.shape_data laws law shape accounted cache valid compiled
  obtain ⟨actual,actualFound,_,count,_,_⟩ := trace.global_types laws law shape accounted cache valid compiled
  have bounded : ExportBounds trace.dataStore := by
    apply old.staged retained
    · simpa only [trace.committed] using Nat.le_of_eq count
    · intro selected selectedFound
      have same : selected = inst := Option.some.inj (selectedFound.symm.trans found)
      subst selected
      rw [source]
      exact module_export_bounds valid
  exact bounded.instances_eq (by simp only [trace.committed])
end Exec.Store
