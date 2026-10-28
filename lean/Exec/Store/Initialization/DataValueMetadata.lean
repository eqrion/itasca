import Exec.Store.Initialization.SegmentGlobalMetadata
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem DataStageEffect.elements {M : Type} {store after : runtime.store.Store M}
    {index inst} (effect : DataStageEffect store index inst after) : after.elems = store.elems := by
  cases effect <;> rfl

theorem DataStageEffect.element_map {M : Type} {store after : runtime.store.Store M}
    {index inst next} (effect : DataStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next) : next.elems = inst.elems := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    subst next
    rfl
  | appended datas addresses data stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    rfl
end Itasca.Runtime.Store
