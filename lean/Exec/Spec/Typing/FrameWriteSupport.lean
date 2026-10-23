import Exec.Spec.Typing.FunctionEntryTyping
import Exec.Spec.Typing.StoreTypingExtension

/-! Frame environments retain control-independent bindings and can reconstruct
canonical frame typing after local/store changes. -/

namespace Exec.Spec
open SpecExt

theorem FrameEnvironment.without_label {s : store} {frame : _root_.frame} {context : _root_.context}
    (types : List valtype)
    (environment : FrameEnvironment s frame ({(default : _root_.context) with LABELS := [.mk_list types]}++context)) :
    FrameEnvironment s frame context := ⟨environment.moduleTyped,environment.locals⟩

theorem FrameEnvironment.without_return {s : store} {frame : _root_.frame} {context : _root_.context}
    (types : List valtype)
    (environment : FrameEnvironment s frame ({(default : _root_.context) with RETURN := some (.mk_list types)}++context)) :
    FrameEnvironment s frame context := ⟨environment.moduleTyped,environment.locals⟩

theorem moduleinst_empty_control {s : store} {module : moduleinst} {context : _root_.context}
    (typed : Moduleinst_ok s module context) : context.LOCALS=[] ∧ context.LABELS=[] ∧ context.RETURN=none := by
  cases typed
  exact ⟨rfl,rfl,rfl⟩

theorem frame_empty_control {s : store} {frame : _root_.frame} {context : _root_.context}
    (typed : Frame_ok s frame context) : context.LABELS=[] ∧ context.RETURN=none := by
  cases typed with
  | mk_Frame_ok values module types moduleContext moduleTyped _ _ _ _ _ _ =>
    have empty := moduleinst_empty_control moduleTyped
    change moduleContext.LABELS=[] ∧ moduleContext.RETURN=none
    exact ⟨empty.2.1,empty.2.2⟩

theorem FrameEnvironment.to_frame_ok {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (storeWf : wf_store s)
    (labels : context.LABELS=[]) (returns : context.RETURN=none) : Frame_ok s frame context := by
  have frameTyped := frame_of_typed_locals environment.moduleTyped storeWf environment.locals
  have same : functionLocalsContext context.LOCALS++sourceModuleContext context=context := by
    change append_context (functionLocalsContext context.LOCALS) (sourceModuleContext context)=context
    cases context
    simp_all [functionLocalsContext,sourceModuleContext,append_context,default]
    decide
  simpa only [same] using frameTyped

theorem resultsTyped_set {s : store} {types : List valtype} {values : List val}
    (typed : ResultsTyped s types values) (index : Nat) (bound : index<types.length) {value : val}
    (valueTyped : Val_ok s value types[index]!) : ResultsTyped s types (values.set index value) := by
  induction typed generalizing index with
  | nil => simp at bound
  | @cons old type values types head tail ih =>
    cases index with
    | zero =>
      have actual : Val_ok s value type := by simpa using valueTyped
      exact .cons actual tail
    | succ index =>
      have nextBound : index<types.length := by simpa using bound
      have actual : Val_ok s value types[index]! := by
        simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_cons_succ] using valueTyped
      exact .cons head (ih index nextBound actual)

end Exec.Spec
