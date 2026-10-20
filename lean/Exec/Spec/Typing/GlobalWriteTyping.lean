import Exec.Spec.Typing.StoreMutationTyping

/-! A mutable global update preserves genuine source store typing from the
existing global declaration and independently typed replacement value. -/

namespace Exec.Spec
open SpecExt

theorem globalinst_typing_wf {s : store} {object : globalinst} {type : globaltype}
    (typed : Globalinst_ok s object type) : wf_globalinst object := by cases typed; assumption

theorem mutable_global_update_extends (object : globalinst) (value : val) (type : valtype)
    (typeEq : object.TYPE=.mk_globaltype (some .MUT) type) (objectWf : wf_globalinst object)
    (valueWf : wf_val value) : Extend_globalinst object {object with VALUE := value} := by
  cases object with
  | MKglobalinst oldType oldValue =>
    cases typeEq
    exact .mk_Extend_globalinst _ _ _ _ (Or.inl rfl) objectWf (.globalinst_case_ _ _ valueWf)

theorem global_value_update_typed {s t : store} (extension : Extend_store s t)
    {object : globalinst} {mutable : «mut»} {type : valtype}
    (typed : Globalinst_ok s object (.mk_globaltype mutable type)) {value : val}
    (valueTyped : Val_ok s value type) : Globalinst_ok t {object with VALUE := value} (.mk_globaltype mutable type) := by
  cases typed with
  | mk_Globalinst_ok _ _ oldValue typeOk _ _ _ =>
    exact .mk_Globalinst_ok _ _ _ _ typeOk (val_ok_extend extension valueTyped)
      (extend_store_wf extension).2 (.globalinst_case_ _ _ (val_ok_wf valueTyped))

def sourceGlobalUpdate (s : store) (index : Nat) (value : val) : store :=
  {s with GLOBALS := s.GLOBALS.set index {s.GLOBALS[index]! with VALUE := value}}

theorem global_update_store_typed {s : store} (typed : Store_ok s) (index : Nat) (bound : index<s.GLOBALS.length)
    (value : val) (type : valtype) (typeEq : s.GLOBALS[index]!.TYPE=.mk_globaltype (some .MUT) type)
    (valueTyped : Val_ok s value type) (postWf : wf_store (sourceGlobalUpdate s index value)) :
    Extend_store s (sourceGlobalUpdate s index value) ∧ Store_ok (sourceGlobalUpdate s index value) := by
  have components := source_store_components typed
  have member : s.GLOBALS[index]! ∈ s.GLOBALS := by
    simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some] using List.getElem_mem bound
  have oldTyped := components.globals _ member
  have oldWf := globalinst_typing_wf oldTyped
  have storeWf : wf_store s := by cases typed; assumption
  have extension : Extend_store s (sourceGlobalUpdate s index value) :=
    extend_store_set_global s index _ storeWf postWf
      (fun _ => mutable_global_update_extends _ _ _ typeEq oldWf (val_ok_wf valueTyped))
  refine ⟨extension,?_⟩
  change Globalinst_ok s s.GLOBALS[index]! s.GLOBALS[index]!.TYPE at oldTyped
  rw [typeEq] at oldTyped
  have fresh := global_value_update_typed extension oldTyped valueTyped
  apply source_store_global_set typed extension index {s.GLOBALS[index]! with VALUE := value} rfl
  change Globalinst_ok (sourceGlobalUpdate s index value) {s.GLOBALS[index]! with VALUE := value} s.GLOBALS[index]!.TYPE
  rw [typeEq]
  exact fresh

end Exec.Spec
