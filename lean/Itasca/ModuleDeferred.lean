import Itasca.ModuleCodeVisitor

open Aeneas Aeneas.Std

namespace Itasca.ModuleCodeVisitor

/-- Parallel workers may discharge each obligation with their own operator
visitor run; no common visitor state or callback-totality assumption is needed. -/
theorem EntriesValidate.of_visiting {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (entries : List Entry)
    (h : ∀ index pos, (index, pos) ∈ entries → ∃ v v' finish,
      module.validate_code_entry_with visitor data pos env index v = .ok (.Ok finish, v')) :
    EntriesValidate data env entries := by
  intro index pos hm
  obtain ⟨v, v', finish, he⟩ := h index pos hm
  exact ⟨finish, module.validate_code_entry_with.accepted_erase visitor data pos env index finish v v' he⟩

/-- A consumer records every successful entry handoff in order. Readiness
callbacks leave that observation unchanged, including ordinary rejections. -/
structure Records {V : Type} (visitor : module.CodeVisitor V) (observe : V → List Entry) : Prop where
  need_bytes : ∀ v finish reply v', visitor.on_need_bytes v finish = .ok (reply, v') →
    observe v' = observe v
  entry : ∀ v data env index pos content finish v',
    visitor.on_code_entry v data env index pos content finish = .ok (.Ok (), v') →
    observe v' = observe v ++ [(index, pos)]

theorem EntriesRun.records {V : Type} {visitor : module.CodeVisitor V} {observe : V → List Entry}
    (hr : Records visitor observe) {data env v pos index v' finish entries}
    (h : EntriesRun visitor data env v pos index v' finish entries) :
    observe v' = observe v ++ entries := by
  induction h with
  | done => simp
  | more _ _ hw _ hw2 he _ _ ih =>
    rw [ih, hr.entry _ _ _ _ _ _ _ _ he, hr.need_bytes _ _ _ _ hw2, hr.need_bytes _ _ _ _ hw]
    simp [List.append_assoc]

theorem SectionRun.records {V : Type} {visitor : module.CodeVisitor V} {observe : V → List Entry}
    (hr : Records visitor observe) {data pos env v v' finish entries}
    (h : SectionRun visitor data pos env v v' finish entries) :
    observe v' = observe v ++ entries := by
  cases h with
  | absent _ _ hw _ => simpa using hr.need_bytes _ _ _ _ hw
  | present _ _ hw _ ht => rw [ht.records hr, hr.need_bytes _ _ _ _ hw]

/-- Validation of the final recorded list can be established after the walk,
without strengthening the callback itself into a validating override. -/
theorem SectionRun.deferred {V W : Type} {visitor : module.CodeVisitor V} {observe : V → List Entry}
    (hr : Records visitor observe) {data pos env v v' finish entries}
    (h : SectionRun visitor data pos env v v' finish entries)
    (hv : EntriesValidate data env (observe v'))
    (replacement : module.CodeVisitor W) (ha : Accepts replacement data env) (w : W) :
    ∃ w', SectionRun replacement data pos env w w' finish entries := by
  apply h.transfer replacement ha _ w
  intro index start hm
  apply hv index start
  rw [h.records hr]
  exact List.mem_append.mpr (.inr hm)

/-- A concrete dispatch-only consumer; successful walking does not itself mean
that any body was validated. The final recorded obligations supply that fact. -/
def recorder : module.CodeVisitor (List Entry) where
  on_need_bytes v _ := .ok (.Ok (), v)
  on_code_entry v _ _ index pos _ _ := .ok (.Ok (), v ++ [(index, pos)])

theorem recorder_records : Records recorder id := by
  constructor
  · intro v finish reply v' h
    have he : reply = .Ok () ∧ v' = v := by simpa [recorder, Eq.comm] using h
    exact he.2
  · intro v data env index pos content finish v' h
    simpa [recorder, Eq.comm] using h

theorem recorder_accepts (data : Slice U8) (env : module.Env) : Accepts recorder data env := by
  constructor
  · intro v finish; exact ⟨v, rfl⟩
  · intro v index pos content finish next h
    exact ⟨v ++ [(index, pos)], rfl⟩

end Itasca.ModuleCodeVisitor

namespace Itasca

/-- An accepted recording walk yields the exact ordered entry positions from
its actual framing path. This does not certify the entries' bodies. -/
theorem module.validate_code_with.recorded {V : Type}
    (visitor : module.CodeVisitor V) (observe : V → List ModuleCodeVisitor.Entry)
    (hr : ModuleCodeVisitor.Records visitor observe)
    (data : Slice U8) (pos : Usize) (env : module.Env) (v v' : V) (finish : Usize)
    (h : module.validate_code_with visitor data pos env v = .ok (.Ok finish, v')) :
    ∃ entries, observe v' = observe v ++ entries ∧
      ModuleCodeVisitor.SectionRun visitor data pos env v v' finish entries := by
  obtain ⟨entries, he⟩ := ModuleCodeVisitor.SectionRun.of_accepted visitor data pos env v v' finish h
  exact ⟨entries, he.records hr, he⟩

theorem module.validate_code_with.deferred_transfer {V W : Type}
    (visitor : module.CodeVisitor V) (observe : V → List ModuleCodeVisitor.Entry)
    (hr : ModuleCodeVisitor.Records visitor observe)
    (replacement : module.CodeVisitor W) (data : Slice U8) (pos : Usize) (env : module.Env)
    (ha : ModuleCodeVisitor.Accepts replacement data env) (v v' : V) (w : W) (finish : Usize)
    (h : module.validate_code_with visitor data pos env v = .ok (.Ok finish, v'))
    (hv : ModuleCodeVisitor.EntriesValidate data env (observe v')) :
    ∃ w', module.validate_code_with replacement data pos env w = .ok (.Ok finish, w') := by
  obtain ⟨entries, he⟩ := ModuleCodeVisitor.SectionRun.of_accepted visitor data pos env v v' finish h
  obtain ⟨w', hw⟩ := he.deferred hr hv replacement ha w
  exact ⟨w', hw.accepted⟩

/-- Once every entry actually recorded by the walk has validated, its verdict
is the default code validator's verdict. No immediate hook-validation or
source-hook termination premise is imposed. -/
theorem module.validate_code_with.deferred_erase {V : Type}
    (visitor : module.CodeVisitor V) (observe : V → List ModuleCodeVisitor.Entry)
    (hr : ModuleCodeVisitor.Records visitor observe)
    (data : Slice U8) (pos : Usize) (env : module.Env) (v v' : V) (finish : Usize)
    (h : module.validate_code_with visitor data pos env v = .ok (.Ok finish, v'))
    (hv : ModuleCodeVisitor.EntriesValidate data env (observe v')) :
    module.validate_code data pos env = .ok (.Ok finish) := by
  obtain ⟨w, hw⟩ := module.validate_code_with.deferred_transfer visitor observe hr
    module.ValidatingCodeVisitor.Insts.ItascaModuleCodeVisitor data pos env
    (ModuleCodeVisitor.default_accepts data env) v v' () finish h hv
  simp [module.validate_code, hw]

theorem module.validate_code_with.recorder_validated
    (data : Slice U8) (pos : Usize) (env : module.Env)
    (entries : List ModuleCodeVisitor.Entry) (finish : Usize)
    (h : module.validate_code_with ModuleCodeVisitor.recorder data pos env [] = .ok (.Ok finish, entries))
    (hv : ModuleCodeVisitor.EntriesValidate data env entries) :
    module.validate_code data pos env = .ok (.Ok finish) :=
  module.validate_code_with.deferred_erase ModuleCodeVisitor.recorder id
    ModuleCodeVisitor.recorder_records data pos env [] entries finish h hv

end Itasca
