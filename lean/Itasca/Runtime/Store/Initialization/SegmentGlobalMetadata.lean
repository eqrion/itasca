import Itasca.Runtime.Store.Initialization.ElementContentEffect
import Itasca.Runtime.Store.Initialization.DataEffects

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem ElementStageEffect.globals {M : Type} {store after : runtime.store.Store M}
    {index inst} (effect : ElementStageEffect store index inst after) : after.globals = store.globals := by
  cases effect <;> rfl

theorem ElementStageEffect.global_map {M : Type} {store after : runtime.store.Store M}
    {index inst next} (effect : ElementStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next) : next.globals = inst.globals := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    subst next
    rfl
  | appended elements addresses element stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    rfl

theorem DataStageEffect.globals {M : Type} {store after : runtime.store.Store M}
    {index inst} (effect : DataStageEffect store index inst after) : after.globals = store.globals := by
  cases effect <;> rfl

theorem DataStageEffect.global_map {M : Type} {store after : runtime.store.Store M}
    {index inst next} (effect : DataStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next) : next.globals = inst.globals := by
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
