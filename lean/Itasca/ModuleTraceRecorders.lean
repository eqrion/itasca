import Itasca.ModuleTraceDefs
import Itasca.ModuleDeferred
import Itasca.ModuleCustomObservation
import Itasca.ModuleCodeTotal

open Aeneas Aeneas.Std

namespace Itasca.ModuleTrace

/-- Project the dispatched worker obligations without confusing them with
custom sections or readiness requests. -/
def entries (events : List Event) : List ModuleCodeVisitor.Entry :=
  events.filterMap (fun event => match event with
    | .codeEntry index start _ _ => some (index, start)
    | _ => none)

theorem RecordsCode.entries {V : Type} {visitor : module.CodeVisitor V} {observe : V → List Event}
    (h : RecordsCode visitor observe) :
    ModuleCodeVisitor.Records visitor (fun v => entries (observe v)) := by
  constructor
  · intro v finish reply v' hr
    simp [ModuleTrace.entries, h.need_bytes v finish reply v' hr]
  · intro v data env index start content finish v' hr
    simp [ModuleTrace.entries, h.entry v data env index start content finish v' hr]

theorem RecordsCustom.entries {V : Type} {visitor : module.ModuleVisitor V} {observe : V → List Event}
    (h : RecordsCustom visitor observe) : ModuleTail.Preserves visitor (fun v => entries (observe v)) := by
  intro v chunk v' hr
  simp [ModuleTrace.entries, h v chunk v' hr]

/-- A concrete accepting recorder for all custom-section arguments. -/
def customRecorder : module.ModuleVisitor (List Event) where
  on_custom_section events chunk := .ok (.Ok (), events ++ [.custom chunk])

/-- A dispatch-only recorder, suitable for later worker obligations. -/
def codeRecorder : module.CodeVisitor (List Event) where
  on_need_bytes events finish := .ok (.Ok (), events ++ [.needBytes finish])
  on_code_entry events _ _ index start content finish :=
    .ok (.Ok (), events ++ [.codeEntry index start content finish])

theorem customRecorder_records : RecordsCustom customRecorder id := by
  intro v chunk v' h
  simpa [customRecorder, Eq.comm] using h

theorem codeRecorder_records : RecordsCode codeRecorder id := by
  constructor
  · intro v finish reply v' h
    have he : reply = .Ok () ∧ v' = v ++ [.needBytes finish] := by
      simpa [codeRecorder, Eq.comm] using h
    exact he.2
  · intro v data env index start content finish v' h
    simpa [codeRecorder, Eq.comm] using h

theorem customRecorder_accepts : ModuleTail.HooksAccept customRecorder := by
  intro events chunk
  exact ⟨events ++ [.custom chunk], rfl⟩

theorem codeRecorder_accepts (data : Slice U8) (env : module.Env) :
    ModuleCodeVisitor.Accepts codeRecorder data env := by
  constructor
  · intro events finish; exact ⟨events ++ [.needBytes finish], rfl⟩
  · intro events index start content finish next _
    exact ⟨events ++ [.codeEntry index start content finish], rfl⟩

theorem codeRecorder_total (data : Slice U8) (env : module.Env) :
    ModuleCode.HooksTotal codeRecorder data env := by
  constructor
  · intro events finish; exact ⟨.Ok (), events ++ [.needBytes finish], rfl⟩
  · intro events index start content finish _
    exact ⟨.Ok (), events ++ [.codeEntry index start content finish], rfl⟩

/-- A concrete recorder that also executes the real default entry validator.
Rejected entries return their original error and are not successful handoffs. -/
def validatingRecorder : module.CodeVisitor (List Event) where
  on_need_bytes events finish := .ok (.Ok (), events ++ [.needBytes finish])
  on_code_entry events data env index start content finish := do
    let r ← module.validate_code_entry data start env index
    match r with
    | .Ok _ => .ok (.Ok (), events ++ [.codeEntry index start content finish])
    | .Err e => .ok (.Err e, events)

theorem validatingRecorder_records : RecordsCode validatingRecorder id := by
  constructor
  · intro v finish reply v' h
    have he : reply = .Ok () ∧ v' = v ++ [.needBytes finish] := by
      simpa [validatingRecorder, Eq.comm] using h
    exact he.2
  · intro v data env index start content finish v' h
    unfold validatingRecorder at h
    obtain ⟨r, _, ht⟩ := VisitorErasure.bind_ok_inv _ _ _ h
    cases r with
    | Err e => simp at ht
    | Ok next => simpa [Eq.comm] using ht

theorem validatingRecorder_accepts (data : Slice U8) (env : module.Env) :
    ModuleCodeVisitor.Accepts validatingRecorder data env := by
  constructor
  · intro events finish; exact ⟨events ++ [.needBytes finish], rfl⟩
  · intro events index start content finish next h
    exact ⟨events ++ [.codeEntry index start content finish], by simp [validatingRecorder, h]⟩

theorem validatingRecorder_validates (data : Slice U8) (env : module.Env) :
    ModuleCodeVisitor.Validates validatingRecorder data env := by
  intro v index start content finish v' h
  unfold validatingRecorder at h
  obtain ⟨r, hr, ht⟩ := VisitorErasure.bind_ok_inv _ _ _ h
  cases r with
  | Err e => simp at ht
  | Ok next => exact ⟨next, hr⟩

theorem validatingRecorder_total (data : Slice U8) (env : module.Env) (hb : CodeEntry.Bounds env) :
    ModuleCode.HooksTotal validatingRecorder data env := by
  constructor
  · intro events finish; exact ⟨.Ok (), events ++ [.needBytes finish], rfl⟩
  · intro events index start content finish _
    obtain ⟨r, hr⟩ := module.validate_code_entry.total data start env index hb
    cases r with
    | Err e => exact ⟨.Err e, events, by simp [validatingRecorder, hr]⟩
    | Ok next => exact ⟨.Ok (), events ++ [.codeEntry index start content finish], by simp [validatingRecorder, hr]⟩

end Itasca.ModuleTrace
