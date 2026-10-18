import Exec.Store.Api.GlobalTypedEffect
namespace Exec.Store
open Aeneas Aeneas.Std

/-- Source global types agree exactly with the issued instance addresses. -/
def GlobalTypeMap {M : Type} (store : runtime.store.Store M)
    (types : List Itasca.types.GlobalType) (addresses : List runtime.GlobalAddr) : Prop :=
  List.Forall₂ (ImportedGlobal store) types addresses

theorem GlobalTypeMap.prefix {M : Type} {before after : runtime.store.Store M}
    {types addresses} (mapping : GlobalTypeMap before types addresses)
    (identity : after.id = before.id)
    (retained : after.globals.val.take before.globals.length = before.globals.val) :
    GlobalTypeMap after types addresses := by
  apply mapping.imp
  rintro ty address ⟨owner, global, found, typed⟩
  refine ⟨owner.trans identity.symm, global, ?_, typed⟩
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have same := congrArg (fun values : List runtime.store.GlobalInstance => values[address.index.val]?) retained
  simp only [List.getElem?_take, alloc.vec.Vec.length, if_pos bound] at same
  exact same.trans found

theorem GlobalTypedEffect.type_map {M : Type} {store after : runtime.store.Store M}
    {inst next : runtime.store.Instance} {instIndex : Usize} {ty status}
    (effect : GlobalTypedEffect store instIndex inst ty status after)
    (bound : instIndex.val < store.instances.length)
    (found : after.instances.val[instIndex.val]? = some next)
    {types : List Itasca.types.GlobalType} (mapping : GlobalTypeMap store types inst.globals.val)
    (success : status = .Ok ()) : GlobalTypeMap after (types ++ [ty]) next.globals.val := by
  cases effect with
  | failed error => simp at success
  | appended globals addresses lo hi stored mapped canonical room =>
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at found
    subst next
    have old := mapping.prefix
      (after := {store with globals := globals, instances := store.instances.set instIndex {inst with globals := addresses}})
      rfl (by simp [stored])
    change List.Forall₂ _ _ addresses.val
    rw [mapped]
    apply List.rel_append old
    exact .cons ⟨rfl, {ty := ty, lo := lo, hi := hi}, by simp [stored], rfl⟩ .nil

end Exec.Store
