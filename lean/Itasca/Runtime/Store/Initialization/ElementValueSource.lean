import Itasca.Runtime.Store.Initialization.ElementValueEffect
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def ElementSourceSegments (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (source : List Itasca.module.Element) (values : List runtime.store.ElemInst) : Prop :=
  List.Forall₂ (fun original actual => actual.ty = original.elem ∧
    ElementSourceValues sourceStore sourceInstance original.elem original.init.val actual.refs.val) source values

theorem ElementStageEffect.source_context {M : Type} {store after : runtime.store.Store M}
    {instIndex inst next sourceStore sourceInstance}
    (effect : ElementStageEffect store instIndex inst after)
    (found : store.instances.val[instIndex.val]? = some inst)
    (nextFound : after.instances.val[instIndex.val]? = some next)
    (context : InitializerSourceContext sourceStore sourceInstance store inst) :
    InitializerSourceContext sourceStore sourceInstance after next := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    subst next
    exact context
  | appended elements addresses element stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    exact ⟨context.functions, context.globals⟩

theorem ElementValueEffect.source_values {M : Type} {store after : runtime.store.Store M}
    {instIndex inst sourceStore sourceInstance status}
    {original : Itasca.module.Element}
    (effect : ElementValueEffect sourceStore sourceInstance store instIndex inst original status after)
    {sources : List Itasca.module.Element} {base produced : List runtime.store.ElemInst}
    (stored : store.elems.val = base ++ produced)
    (previous : ElementSourceSegments sourceStore sourceInstance sources produced)
    (success : status = .Ok ()) :
    ∃ values, after.elems.val = base ++ values ∧
      ElementSourceSegments sourceStore sourceInstance (sources ++ [original]) values := by
  cases effect with
  | failed error => simp at success
  | appended elements addresses values entries mapped canonical evaluated =>
    refine ⟨produced ++ [{ty := original.elem, refs := values}], ?_, ?_⟩
    · simpa only [stored, List.append_assoc] using entries
    · exact List.rel_append previous (.cons ⟨rfl, evaluated⟩ .nil)
end Itasca.Runtime.Store
