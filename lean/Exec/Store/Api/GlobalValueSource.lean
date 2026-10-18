import Exec.Store.Api.GlobalValueEffect
import Exec.Store.Initialization.InitializerSourceContext
namespace Exec.Store
open Aeneas Aeneas.Std Itasca

/-- Every appended runtime global has its declared type and its source
initializer's value in the unchanged initial source state. -/
def GlobalSourceValues (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (source : List Itasca.module.Global) (values : List runtime.store.GlobalInstance) : Prop :=
  List.Forall₂ (fun original actual => actual.ty = original.gtype ∧
    Eval_expr ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (ModuleConstants.expression original.init)
      ⟨sourceStore, ⟨[], sourceInstance⟩⟩ [(decodeGlobal actual).VALUE]) source values

theorem GlobalStageEffect.source_context {M : Type} {store after : runtime.store.Store M}
    {instIndex inst next sourceStore sourceInstance}
    (effect : GlobalStageEffect store instIndex inst after)
    (found : store.instances.val[instIndex.val]? = some inst)
    (nextFound : after.instances.val[instIndex.val]? = some next)
    (imports : InitializerImports store inst)
    (context : InitializerSourceContext sourceStore sourceInstance store inst) :
    InitializerSourceContext sourceStore sourceInstance after next := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    subst next
    exact context
  | appended globals addresses global stored mapped canonical room =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    exact context.extend imports rfl rfl (by simp [mapped]) (by simp [stored])

theorem GlobalValueEffect.source_values {M : Type} {store after : runtime.store.Store M}
    {instIndex inst sourceStore sourceInstance status value}
    {original : Itasca.module.Global}
    (effect : GlobalValueEffect store instIndex inst original.gtype value status after)
    (evaluated : Eval_expr ⟨sourceStore, ⟨[], sourceInstance⟩⟩
      (ModuleConstants.expression original.init) ⟨sourceStore, ⟨[], sourceInstance⟩⟩ [value])
    {sources : List Itasca.module.Global} {base produced : List runtime.store.GlobalInstance}
    (stored : store.globals.val = base ++ produced)
    (previous : GlobalSourceValues sourceStore sourceInstance sources produced)
    (success : status = .Ok ()) :
    ∃ values, after.globals.val = base ++ values ∧
      GlobalSourceValues sourceStore sourceInstance (sources ++ [original]) values := by
  cases effect with
  | failed error => simp at success
  | appended globals addresses lo hi entries mapped canonical room decoded =>
    refine ⟨produced ++ [{ty := original.gtype, lo := lo, hi := hi}], ?_, ?_⟩
    · simpa only [stored, List.append_assoc] using entries
    · apply List.rel_append previous
      exact .cons ⟨rfl, by simpa only [decodeGlobal, decoded] using evaluated⟩ .nil
end Exec.Store
