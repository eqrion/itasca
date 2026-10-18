import Exec.Store.Api.GlobalTypeMap
import Exec.Store.Initialization.ElementTypes
namespace Exec.Store
open Aeneas Aeneas.Std

theorem ElementStageEffect.global_types {M : Type} {store after : runtime.store.Store M}
    {inst next : runtime.store.Instance} {index : Usize}
    (effect : ElementStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next)
    {types} (mapping : GlobalTypeMap store types inst.globals.val) :
    GlobalTypeMap after types next.globals.val := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    simpa only [same] using mapping
  | appended elements addresses segment stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    exact mapping

theorem DataStageEffect.global_types {M : Type} {store after : runtime.store.Store M}
    {inst next : runtime.store.Instance} {index : Usize}
    (effect : DataStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next)
    {types} (mapping : GlobalTypeMap store types inst.globals.val) :
    GlobalTypeMap after types next.globals.val := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    simpa only [same] using mapping
  | appended datas addresses segment stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    exact mapping

end Exec.Store
