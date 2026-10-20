import Exec.Spec.ListRelations
import Exec.Spec.Typing.ValueOperationTyping

/-! Actual module bindings and typed locals survive administrative control
contexts. These source-only environments support store-dependent reductions. -/

namespace Exec.Spec
open SpecExt

def sourceModuleContext (context : _root_.context) : _root_.context :=
  {context with LOCALS := [], LABELS := [], RETURN := none}

structure FrameEnvironment (s : store) (frame : _root_.frame) (context : _root_.context) : Prop where
  moduleTyped : Moduleinst_ok s frame.MODULE (sourceModuleContext context)
  locals : ResultsTyped s context.LOCALS frame.LOCALS

theorem FrameEnvironment.of_frame_ok {s : store} {frame : _root_.frame} {context : _root_.context}
    (typed : Frame_ok s frame context) : FrameEnvironment s frame context := by
  cases typed with
  | mk_Frame_ok values module types moduleContext moduleTyped count paired _ _ _ _ =>
    have normalized : sourceModuleContext
        ({(default : _root_.context) with LOCALS := types} ++ moduleContext) = moduleContext := by
      cases moduleTyped
      rfl
    constructor
    · change Moduleinst_ok s module (sourceModuleContext ({(default : _root_.context) with LOCALS := types} ++ moduleContext))
      rw [normalized]
      exact moduleTyped
    · have relation : List.Forall₂ (fun type value => Val_ok s value type) types values := by
        exact forall₂_of_lengths count paired
      have localsEmpty : moduleContext.LOCALS=[] := by cases moduleTyped; rfl
      change ResultsTyped s (types++moduleContext.LOCALS) values
      rw [localsEmpty,List.append_nil]
      exact relation.flip

theorem FrameEnvironment.label {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (types : List valtype) :
    FrameEnvironment s frame ({(default : _root_.context) with LABELS := [.mk_list types]} ++ context) := by
  exact ⟨environment.moduleTyped,environment.locals⟩

theorem FrameEnvironment.returns {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (types : List valtype) :
    FrameEnvironment s frame ({(default : _root_.context) with RETURN := some (.mk_list types)} ++ context) := by
  exact ⟨environment.moduleTyped,environment.locals⟩

theorem FrameEnvironment.local_value {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (index : idx) (bound : proj_uN_0 index<context.LOCALS.length) :
    Val_ok s (fun_local ⟨s,frame⟩ index) context.LOCALS[proj_uN_0 index]! := by
  have valueBound : proj_uN_0 index<frame.LOCALS.length := by
    rw [environment.locals.length_eq]
    exact bound
  have selected := environment.locals.get valueBound bound
  simpa only [fun_local,List.get_eq_getElem,List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem valueBound,
    List.getElem?_eq_getElem bound,Option.getD_some] using selected

theorem moduleinst_external_bindings {s : store} {module : moduleinst} {context : _root_.context}
    (typed : Moduleinst_ok s module context) :
    List.Forall₂ (fun address type => Externaddr_ok s (.FUNC address) (.FUNC type)) module.FUNCS context.FUNCS ∧
    List.Forall₂ (fun address type => Externaddr_ok s (.GLOBAL address) (.GLOBAL type)) module.GLOBALS context.GLOBALS ∧
    List.Forall₂ (fun address type => Externaddr_ok s (.TABLE address) (.TABLE type)) module.TABLES context.TABLES ∧
    List.Forall₂ (fun address type => Externaddr_ok s (.MEM address) (.MEM type)) module.MEMS context.MEMS := by
  cases typed
  refine ⟨?_,?_,?_,?_⟩
  all_goals apply forall₂_of_lengths <;> assumption

theorem FrameEnvironment.function_addresses {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) :
    List.Forall₂ (fun address type => Externaddr_ok s (.FUNC address) (.FUNC type)) frame.MODULE.FUNCS context.FUNCS :=
  (moduleinst_external_bindings environment.moduleTyped).1

theorem FrameEnvironment.global_addresses {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) :
    List.Forall₂ (fun address type => Externaddr_ok s (.GLOBAL address) (.GLOBAL type)) frame.MODULE.GLOBALS context.GLOBALS :=
  (moduleinst_external_bindings environment.moduleTyped).2.1

theorem FrameEnvironment.table_addresses {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) :
    List.Forall₂ (fun address type => Externaddr_ok s (.TABLE address) (.TABLE type)) frame.MODULE.TABLES context.TABLES :=
  (moduleinst_external_bindings environment.moduleTyped).2.2.1

theorem FrameEnvironment.memory_addresses {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) :
    List.Forall₂ (fun address type => Externaddr_ok s (.MEM address) (.MEM type)) frame.MODULE.MEMS context.MEMS :=
  (moduleinst_external_bindings environment.moduleTyped).2.2.2

end Exec.Spec
