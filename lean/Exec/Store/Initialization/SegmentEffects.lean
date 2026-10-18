import Exec.Store.Initialization.SegmentAccounting
import Exec.Store.Initialization.ElementEffects
import Exec.Store.Initialization.DataEffects

namespace Exec.Store
open Aeneas Aeneas.Std

theorem GlobalStageEffect.segment_accounting {M : Type} {store after : runtime.store.Store M}
    {index : Usize} {inst : runtime.store.Instance}
    (effect : GlobalStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (accounted : SegmentAccounting store) : SegmentAccounting after := by
  cases effect with
  | unchanged => exact accounted
  | appended globals addresses global globalValues addressValues shape room =>
    apply accounted.update_instance index inst {inst with globals := addresses} found rfl 0 0 <;> simp

theorem ElementStageEffect.segment_accounting {M : Type} {store after : runtime.store.Store M}
    {index : Usize} {inst : runtime.store.Instance}
    (effect : ElementStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (accounted : SegmentAccounting store) : SegmentAccounting after := by
  cases effect with
  | unchanged => exact accounted
  | appended elements addresses element elementValues addressValues =>
    apply accounted.update_instance index inst {inst with elements := addresses} found rfl 1 0
    · simpa using congrArg List.length elementValues
    · simp
    · simpa using congrArg List.length addressValues
    · simp

theorem DataStageEffect.segment_accounting {M : Type} {store after : runtime.store.Store M}
    {index : Usize} {inst : runtime.store.Instance}
    (effect : DataStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (accounted : SegmentAccounting store) : SegmentAccounting after := by
  cases effect with
  | unchanged => exact accounted
  | appended datas addresses data dataValues addressValues =>
    apply accounted.update_instance index inst {inst with data := addresses} found rfl 0 1
    · simp
    · simpa using congrArg List.length dataValues
    · simp
    · simpa using congrArg List.length addressValues

end Exec.Store
