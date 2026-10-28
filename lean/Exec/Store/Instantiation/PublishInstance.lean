import Exec.Store.Preparation.PreparedInitializers
import Exec.Store.Initialization.SegmentAccounting

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The actual vector publication after preparation adds one fresh provisional
instance. It does not yet claim that the incomplete instance has full Shape. -/
theorem publish_prepared_instance {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (room : store.instances.length < Usize.max)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (accounted : SegmentAccounting store)
    (emptyElements : inst.elems.val = []) (emptyData : inst.datas.val = []) :
    alloc.vec.Vec.push store.instances inst ⦃ instances =>
      let after := {store with instances}
      instances.val = store.instances.val ++ [inst] ∧
      after.instances.val[store.instances.len.val]? = some inst ∧ StagedPrefix store after ∧
      InitializerBindings after inst ∧ InitializerImports after inst ∧ InitializerSegmentBindings after inst ∧
      SegmentAccounting after ∧ objectCount after = objectCount store ⦄ := by
  step as ⟨instances, appended⟩
  refine ⟨appended, ?_, ?_, ⟨bindings.funcs, bindings.globals⟩, ⟨imports.funcs, imports.globals⟩,
    ⟨segments.tableCount, segments.memoryCount, segments.tables, segments.memories⟩, ?_, rfl⟩
  · simp [appended]
  · constructor <;> simp [appended]
  · apply accounted.append_instance inst appended
    · simp [emptyElements]
    · simp [emptyData]

end Itasca.Runtime.Store
