import Exec.Spec.Typing.FramePayloadTyping

/-! Element-segment references retain their declared source type through the
actual module address map, including function-reference membership. -/

namespace Exec.Spec
open SpecExt

theorem moduleinst_element_bindings {s : store} {module : moduleinst} {context : _root_.context}
    (typed : Moduleinst_ok s module context) :
    List.Forall₂ (fun address type => Eleminst_ok s s.ELEMS[address]! type) module.ELEMS context.ELEMS := by
  cases typed
  apply forall₂_of_lengths <;> assumption

theorem element_instance_references {s : store} {object : eleminst} {type : reftype}
    (typed : Eleminst_ok s object type) : Forall (fun value => Ref_ok s value type) object.REFS := by
  cases typed
  assumption

theorem FrameEnvironment.element_references {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (index : idx) {type : reftype}
    (bound : proj_uN_0 index<context.ELEMS.length) (same : context.ELEMS[proj_uN_0 index]! = type) :
    Forall (fun value => Ref_ok s value type) (fun_elem ⟨s,frame⟩ index).REFS := by
  have paired := moduleinst_element_bindings environment.moduleTyped
  have addressBound : proj_uN_0 index<frame.MODULE.ELEMS.length := by rw [paired.length_eq]; exact bound
  have relation := paired.get addressBound bound
  have actual : Eleminst_ok s (fun_elem ⟨s,frame⟩ index) context.ELEMS[proj_uN_0 index]! := by
    simpa only [sourceModuleContext,fun_elem,List.get_eq_getElem,List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem bound,List.getElem?_eq_getElem addressBound,Option.getD_some] using relation
  rw [same] at actual
  exact element_instance_references actual

end Exec.Spec
