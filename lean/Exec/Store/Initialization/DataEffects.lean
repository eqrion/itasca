import Exec.Store.Initialization.Data
import Exec.Store.Api.GlobalStaging
import Exec.Store.Initialization.InitializerCertificates

namespace Exec.Store
open Aeneas Aeneas.Std

inductive DataStageEffect {M : Type} (store : runtime.store.Store M)
    (instIndex : Usize) (inst : runtime.store.Instance) : runtime.store.Store M → Prop where
  | unchanged : DataStageEffect store instIndex inst store
  | appended (datas : alloc.vec.Vec runtime.store.DataInstance)
      (addresses : alloc.vec.Vec Usize) (data : runtime.store.DataInstance)
      (dataValues : datas.val = store.datas.val ++ [data])
      (addressValues : addresses.val = inst.data.val ++ [store.datas.len]) :
      DataStageEffect store instIndex inst
        { store with datas := datas, instances := store.instances.set instIndex { inst with data := addresses } }

theorem add_instance_data_stage_effect {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (instIndex index : Usize) (inst : runtime.store.Instance)
    (found : store.instances.val[instIndex.val]? = some inst)
    (bound : index.val < inst.module.module.tail.data.val.length)
    (room : store.datas.length < Usize.max) (mapRoom : inst.data.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_data memory allocator store instIndex index
      ⦃ out => DataStageEffect store instIndex inst out.2 ⦄ := by
  have instanceBound : instIndex.val < store.instances.length := (List.getElem?_eq_some_iff.mp found).1
  have instanceRead : store.instances.val[instIndex.val] = inst :=
    Option.some.inj ((List.getElem?_eq_getElem instanceBound).symm.trans found)
  apply WP.spec_mono (add_instance_data_effect memory allocator law store instIndex index instanceBound
    (by simpa only [instanceRead] using bound) room (by simpa only [instanceRead] using mapRoom))
  intro out effect
  rcases effect with ⟨error, rfl⟩ | ⟨bytes, datas, addresses, copied, appended, mapped, rfl⟩
  · exact .unchanged
  · simpa only [instanceRead] using DataStageEffect.appended (store := store) (instIndex := instIndex)
      (inst := inst) datas addresses ⟨bytes⟩ appended (by simpa only [instanceRead] using mapped)

theorem DataStageEffect.context {M : Type} {store after : runtime.store.Store M}
    {instIndex : Usize} {inst : runtime.store.Instance}
    (effect : DataStageEffect store instIndex inst after)
    (found : store.instances.val[instIndex.val]? = some inst)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst) :
    ∃ next, after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
      InitializerBindings after next ∧ InitializerImports after next ∧
      InitializerSegmentBindings after next ∧ next.data.length ≤ inst.data.length + 1 ∧
      after.datas.length ≤ store.datas.length + 1 := by
  cases effect with
  | unchanged => exact ⟨inst, found, rfl, bindings, imports, segments, by omega, by omega⟩
  | appended datas addresses data dataValues addressValues =>
    have bound : instIndex.val < store.instances.val.length := (List.getElem?_eq_some_iff.mp found).1
    refine ⟨{inst with data := addresses}, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp [alloc.vec.Vec.set_val_eq, bound]
    · exact ⟨bindings.funcs, bindings.globals⟩
    · exact imports.extend rfl rfl (by simp) (by simp)
    · exact ⟨segments.tableCount, segments.memoryCount, segments.tables, segments.memories⟩
    · simp [addressValues]
    · simp [dataValues]

theorem DataStageEffect.object_count {M : Type} {store after : runtime.store.Store M}
    {instIndex : Usize} {inst : runtime.store.Instance}
    (effect : DataStageEffect store instIndex inst after) : objectCount after = objectCount store := by
  cases effect <;> rfl

theorem DataStageEffect.staged {M : Type} {before store after : runtime.store.Store M}
    {instIndex : Usize} {inst : runtime.store.Instance}
    (effect : DataStageEffect store instIndex inst after)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val) :
    StagedPrefix before after := by
  cases effect with
  | unchanged => exact staged
  | appended datas addresses data dataValues addressValues =>
    have appended : StagedPrefix store {store with datas := datas} := by
      constructor <;> simp [dataValues]
    exact (staged.trans appended).set_fresh_instance instIndex {inst with data := addresses} fresh

end Exec.Store
