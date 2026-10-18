import Exec.Store.Initialization.DataResultEffect
namespace Exec.Store
open Aeneas Aeneas.Std

def sourceDataPayload (segment : Itasca.module.Data) : datainst :=
  ⟨segment.init.val.map (fun byte => .mk_byte byte.val)⟩

theorem add_instance_data_payload {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (instIndex index : Usize) (inst : runtime.store.Instance)
    (found : store.instances.val[instIndex.val]? = some inst)
    (bound : index.val < inst.module.module.tail.data.val.length)
    (room : store.datas.length < Usize.max) (mapRoom : inst.data.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_data memory allocator store instIndex index
      ⦃ out => DataResultEffect store instIndex inst out.1 out.2 ∧
        (out.1 = .Ok () → out.2.datas.val.map decodeData =
          store.datas.val.map decodeData ++ [sourceDataPayload inst.module.module.tail.data.val[index.val]]) ⦄ := by
  have instanceBound : instIndex.val < store.instances.length := (List.getElem?_eq_some_iff.mp found).1
  have instanceRead : store.instances.val[instIndex.val] = inst :=
    Option.some.inj ((List.getElem?_eq_getElem instanceBound).symm.trans found)
  apply WP.spec_mono (add_instance_data_effect memory allocator law store instIndex index instanceBound
    (by simpa only [instanceRead] using bound) room (by simpa only [instanceRead] using mapRoom))
  intro out effect
  rcases effect with ⟨error, rfl⟩ | ⟨bytes, datas, addresses, copied, appended, mapped, rfl⟩
  · exact ⟨.failed error, by simp⟩
  · constructor
    · simpa only [instanceRead] using DataResultEffect.appended (store := store) (instIndex := instIndex)
        (inst := inst) datas addresses ⟨bytes⟩ appended (by simpa only [instanceRead] using mapped)
    · intro _
      simp only [List.map_append, List.map_cons, List.map_nil, appended, decodeData,
        copied, instanceRead, sourceDataPayload, decodeBytes]
end Exec.Store
