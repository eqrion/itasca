import Itasca.Runtime.SourceMachine.Core.Typing
import Itasca.Runtime.Spec.Globals
import Itasca.Runtime.SourceMachine.Core.ContentExtension

/-!
Global store update contents and mutation certificates, feeding typed source global execution.
-/

/-! ## Global Mutation -/

section

namespace Itasca.Runtime.Abs
open SpecExt Itasca.Runtime.Spec

theorem globalWrite_as_set (s : store) (f : frame) (index address : Nat)
    (object : globalinst) (value : val) (mapped : f.MODULE.GLOBALS[index]? = some address)
    (found : s.GLOBALS[address]? = some object) :
    Spec.globalWrite s f index value =
      {s with GLOBALS := s.GLOBALS.set address {object with VALUE := value}} := by
  simp only [Spec.globalWrite, List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
  rw [List.modify_eq_set_getElem?]
  simp only [found]
  rfl

/-- A typed mutable-global write extends the source store. Unlike raw extension,
this theorem retains the declared value type of the new payload. -/
theorem globalWrite_extends (s : store) (f : frame) (index address : Nat)
    (object : globalinst) (value : val) (ty : valtype)
    (wf : wf_store s) (contents : StoreContentsTyped s)
    (mapped : f.MODULE.GLOBALS[index]? = some address)
    (found : s.GLOBALS[address]? = some object)
    (mutable : object.TYPE = .mk_globaltype (some .MUT) ty)
    (valueTyped : Val_ok s value ty) : Extend_store s (Spec.globalWrite s f index value) := by
  have oldWf : wf_globalinst object := by
    have global := contents.globals object (List.mem_of_getElem? found)
    cases global
    assumption
  have valueWf := val_ok_wf valueTyped
  have freshWf := Spec.globalWrite_wf s f index value wf valueWf
  have same := globalWrite_as_set s f index address object value mapped found
  rw [same] at freshWf ⊢
  apply Spec.extend_store_set_global _ _ _ wf freshWf
  intro bound
  have atAddress : s.GLOBALS[address]! = object := by simp [List.getElem!_eq_getElem?_getD,found]
  rw [atAddress]
  cases object with
  | MKglobalinst type old =>
    dsimp only at mutable
    cases mutable
    exact Spec.extend_global_mutable ty old value oldWf (.globalinst_case_ _ _ valueWf)

end Itasca.Runtime.Abs

end

/-! ## Global Contents -/

section

namespace Itasca.Runtime.Abs
open SpecExt Itasca.Runtime.Spec

theorem StoreContentsTyped.global_write {s : store} (contents : StoreContentsTyped s)
    (wf : wf_store s) (f : frame) (index address : Nat) (object : globalinst) (value : val) (ty : valtype)
    (mapped : f.MODULE.GLOBALS[index]? = some address) (found : s.GLOBALS[address]? = some object)
    (mutable : object.TYPE = .mk_globaltype (some .MUT) ty) (valueTyped : Val_ok s value ty) :
    StoreContentsTyped (Spec.globalWrite s f index value) := by
  have extension := globalWrite_extends s f index address object value ty wf contents mapped found mutable valueTyped
  have valueFresh := val_typed_extend extension valueTyped
  have freshWf := (extend_store_wf extension).2
  have objectFresh : Globalinst_ok (Spec.globalWrite s f index value)
      {object with VALUE := value} {object with VALUE := value}.TYPE := by
    cases object with
    | MKglobalinst type old =>
      dsimp only at mutable
      cases mutable
      exact .mk_Globalinst_ok _ _ _ _ (.mk_Globaltype_ok _ _) valueFresh freshWf
        (.globalinst_case_ _ _ (val_ok_wf valueFresh))
  exact contents.global_replacement extension address {object with VALUE := value}
    (congrArg store.GLOBALS (globalWrite_as_set s f index address object value mapped found))
    rfl rfl rfl rfl objectFresh

end Itasca.Runtime.Abs

end
