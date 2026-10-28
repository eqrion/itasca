import Exec.Store.Initialization.ElementTypedEffect
import Exec.Store.Initialization.DataEffects

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def ElementTypeMap {M : Type} (store : runtime.store.Store M)
    (source : List Itasca.module.Element) (addresses : List Usize) : Prop :=
  List.Forall₂ (fun entry address => ∃ segment, store.elems.val[address.val]? = some segment ∧ segment.ty = entry.elem) source addresses

theorem ElementTypeMap.prefix {M : Type} {store after : runtime.store.Store M} {source addresses}
    (matching : ElementTypeMap store source addresses) (retained : after.elems.val.take store.elems.length = store.elems.val) :
    ElementTypeMap after source addresses := by
  apply matching.imp
  rintro entry address ⟨segment, found, equal⟩
  refine ⟨segment, ?_, equal⟩
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have lookup := congrArg (fun values : List runtime.store.ElemInst => values[address.val]?) retained
  simp only [List.getElem?_take, alloc.vec.Vec.length, if_pos bound] at lookup
  exact lookup.trans found

theorem ElementTypedEffect.type_map {M : Type} {store after : runtime.store.Store M}
    {inst next : runtime.store.ModuleInst} {instIndex : Usize} {source status}
    (effect : ElementTypedEffect store instIndex inst source status after)
    (bound : instIndex.val < store.instances.length)
    (found : after.instances.val[instIndex.val]? = some next)
    {entries : List Itasca.module.Element} (matching : ElementTypeMap store entries inst.elems.val)
    (success : status = .Ok ()) : ElementTypeMap after (entries ++ [source]) next.elems.val := by
  cases effect with
  | failed error => simp at success
  | appended elements addresses values stored mapped =>
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at found
    subst next
    have old := matching.prefix (after := {store with elems := elements, instances := store.instances.set instIndex {inst with elems := addresses}})
      (by simp [stored])
    change List.Forall₂ _ _ addresses.val
    rw [mapped]
    apply List.rel_append old
    exact .cons ⟨{ty := source.elem, refs := values}, by simp [stored], rfl⟩ .nil

theorem ElementTypeMap.bindings {M : Type} {store : runtime.store.Store M} {inst : runtime.store.ModuleInst}
    (matching : ElementTypeMap store inst.module.module.env.elements.val inst.elems.val) :
    ∀ (index : Nat) (source : Itasca.module.Element) (address : Usize) (segment : runtime.store.ElemInst),
      inst.module.module.env.elements.val[index]? = some source → inst.elems.val[index]? = some address →
      store.elems.val[address.val]? = some segment → segment.ty = source.elem := by
  intro index source address segment sourceFound mapped found
  have left := (List.getElem?_eq_some_iff.mp sourceFound).1
  have right := (List.getElem?_eq_some_iff.mp mapped).1
  have related := matching.get left right
  simp only [List.get_eq_getElem] at related
  have sourceEq := (List.getElem?_eq_some_iff.mp sourceFound).2
  have addressEq := (List.getElem?_eq_some_iff.mp mapped).2
  rw [sourceEq, addressEq] at related
  obtain ⟨actual, actualFound, typed⟩ := related
  have same : actual = segment := Option.some.inj (actualFound.symm.trans found)
  simpa only [same] using typed

/-- Data staging changes no element values or element addresses, including
refusal branches before or after a data append. -/
theorem DataStageEffect.element_types {M : Type} {store after : runtime.store.Store M}
    {inst next : runtime.store.ModuleInst} {instIndex : Usize} {source : List Itasca.module.Element}
    (effect : DataStageEffect store instIndex inst after)
    (found : store.instances.val[instIndex.val]? = some inst)
    (nextFound : after.instances.val[instIndex.val]? = some next)
    (matching : ElementTypeMap store source inst.elems.val) : ElementTypeMap after source next.elems.val := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    simpa only [same] using matching
  | appended datas addresses data stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    exact matching

end Itasca.Runtime.Store
