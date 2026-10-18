import Exec.Store.Initialization.DataEffects

namespace Exec.Store
open Aeneas Aeneas.Std

inductive DataResultEffect {M : Type} (store : runtime.store.Store M)
    (instIndex : Usize) (inst : runtime.store.Instance) : core.result.Result Unit runtime.ExecError → runtime.store.Store M → Prop where
  | failed (error : runtime.ExecError) : DataResultEffect store instIndex inst (.Err error) store
  | appended (datas : alloc.vec.Vec runtime.store.DataInstance)
      (addresses : alloc.vec.Vec Usize) (data : runtime.store.DataInstance)
      (dataValues : datas.val = store.datas.val ++ [data])
      (addressValues : addresses.val = inst.data.val ++ [store.datas.len]) :
      DataResultEffect store instIndex inst (.Ok ())
        { store with datas := datas, instances := store.instances.set instIndex { inst with data := addresses } }

theorem add_instance_data_result_effect {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (instIndex index : Usize) (inst : runtime.store.Instance)
    (found : store.instances.val[instIndex.val]? = some inst)
    (bound : index.val < inst.module.module.tail.data.val.length)
    (room : store.datas.length < Usize.max) (mapRoom : inst.data.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_data memory allocator store instIndex index
      ⦃ out => DataResultEffect store instIndex inst out.1 out.2 ⦄ := by
  have instanceBound : instIndex.val < store.instances.length := (List.getElem?_eq_some_iff.mp found).1
  have instanceRead : store.instances.val[instIndex.val] = inst :=
    Option.some.inj ((List.getElem?_eq_getElem instanceBound).symm.trans found)
  apply WP.spec_mono (add_instance_data_effect memory allocator law store instIndex index instanceBound
    (by simpa only [instanceRead] using bound) room (by simpa only [instanceRead] using mapRoom))
  intro out effect
  rcases effect with ⟨error, rfl⟩ | ⟨bytes, datas, addresses, copied, appended, mapped, rfl⟩
  · exact .failed error
  · simpa only [instanceRead] using DataResultEffect.appended (store := store) (instIndex := instIndex)
      (inst := inst) datas addresses ⟨bytes⟩ appended (by simpa only [instanceRead] using mapped)

theorem DataResultEffect.effect {M : Type} {store after : runtime.store.Store M}
    {instIndex inst status} (effect : DataResultEffect store instIndex inst status after) :
    DataStageEffect store instIndex inst after := by
  cases effect with
  | failed error => exact .unchanged
  | appended datas addresses data stored mapped => exact .appended datas addresses data stored mapped

theorem DataResultEffect.count {M : Type} {store after : runtime.store.Store M}
    {instIndex inst status} (effect : DataResultEffect store instIndex inst status after)
    (bound : instIndex.val < store.instances.length) {next : runtime.store.Instance}
    (found : after.instances.val[instIndex.val]? = some next) (success : status = .Ok ()) :
    next.data.length = inst.data.length + 1 := by
  cases effect with
  | failed error => simp at success
  | appended datas addresses data stored mapped =>
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at found
    subst next
    simp [mapped]

end Exec.Store
