import Itasca.ModuleCode
import Itasca.ModuleEntryVisitor

open Aeneas Aeneas.Std

namespace Itasca.ModuleCodeVisitor

abbrev Entry := Usize × Usize

/-- A code consumer accepts every entry accepted by the default validator.
Readiness callbacks also accept. This is an acceptance, not a totality, contract. -/
structure Accepts {V : Type} (visitor : module.CodeVisitor V)
    (data : Slice U8) (env : module.Env) : Prop where
  need_bytes : ∀ v finish, ∃ v', visitor.on_need_bytes v finish = .ok (.Ok (), v')
  entry : ∀ v index start content finish next,
    module.validate_code_entry data start env index = .ok (.Ok next) →
    ∃ v', visitor.on_code_entry v data env index start content finish = .ok (.Ok (), v')

/-- An immediate validating override may accept only entries the default
validator accepts. It may reject, and no assumption concerns other executions. -/
def Validates {V : Type} (visitor : module.CodeVisitor V) (data : Slice U8) (env : module.Env) : Prop :=
  ∀ v index start content finish v',
    visitor.on_code_entry v data env index start content finish = .ok (.Ok (), v') →
    ∃ next, module.validate_code_entry data start env index = .ok (.Ok next)

theorem default_accepts (data : Slice U8) (env : module.Env) :
    Accepts module.ValidatingCodeVisitor.Insts.ItascaModuleCodeVisitor data env := by
  constructor
  · intro v finish; exact ⟨v, rfl⟩
  · intro v index start content finish next h
    exact ⟨v, by simp [module.CodeVisitor.on_code_entry.default, h,
      core.result.Result.Insts.CoreOpsTry.branch]⟩

theorem default_validates (data : Slice U8) (env : module.Env) :
    Validates module.ValidatingCodeVisitor.Insts.ItascaModuleCodeVisitor data env := by
  intro v index start content finish v' h
  unfold module.ValidatingCodeVisitor.Insts.ItascaModuleCodeVisitor module.CodeVisitor.on_code_entry.default at h
  obtain ⟨r, hr, h⟩ := VisitorErasure.bind_ok_inv _ _ _ h
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
  | Ok next => exact ⟨next, hr⟩

/-- The exact finite path of an accepted entry walk. This is an execution
certificate used for transfer, not the independent module typing specification. -/
inductive EntriesRun {V : Type} (visitor : module.CodeVisitor V) (data : Slice U8)
    (env : module.Env) : V → Usize → Usize → V → Usize → List Entry → Prop where
  | done (v pos index) (hstop : env.func_type_indices.val.length ≤ index.val) :
      EntriesRun visitor data env v pos index v pos []
  | more {v v1 v2 v3 v' pos content last index j need finish entries}
      (hmore : index.val < env.func_type_indices.val.length)
      (hneed : (pos + limits.MAX_LEB_BYTES : Result Usize) = .ok need)
      (hwait : visitor.on_need_bytes v need = .ok (.Ok (), v1))
      (hframe : module.code_entry_extent data pos = .ok (.Ok (content, last)))
      (hwait2 : visitor.on_need_bytes v1 last = .ok (.Ok (), v2))
      (hentry : visitor.on_code_entry v2 data env index pos content last = .ok (.Ok (), v3))
      (hincr : (index + 1#usize : Result Usize) = .ok j)
      (tail : EntriesRun visitor data env v3 last j v' finish entries) :
      EntriesRun visitor data env v pos index v' finish ((index, pos) :: entries)

/-- One successful framing iteration advances exactly to its declared end. -/
theorem loop_more {V : Type} (visitor : module.CodeVisitor V) (data : Slice U8) (env : module.Env)
    {v v1 v2 v3 : V} {pos content last index j need : Usize}
    (hmore : index.val < env.func_type_indices.val.length)
    (hneed : (pos + limits.MAX_LEB_BYTES : Result Usize) = .ok need)
    (hwait : visitor.on_need_bytes v need = .ok (.Ok (), v1))
    (hframe : module.code_entry_extent data pos = .ok (.Ok (content, last)))
    (hwait2 : visitor.on_need_bytes v1 last = .ok (.Ok (), v2))
    (hentry : visitor.on_code_entry v2 data env index pos content last = .ok (.Ok (), v3))
    (hincr : (index + 1#usize : Result Usize) = .ok j) :
    module.validate_code_entries_with_loop visitor data env v pos index =
      module.validate_code_entries_with_loop visitor data env v3 last j := by
  have hstop : ¬ index ≥ alloc.vec.Vec.len env.func_type_indices := by scalar_tac
  unfold module.validate_code_entries_with_loop
  rw [loop]
  simp [module.validate_code_entries_with_loop.body, hstop, hneed, hwait, hframe, hwait2, hentry, hincr,
    core.result.Result.Insts.CoreOpsTry.branch]

theorem EntriesRun.accepted {V : Type} {visitor : module.CodeVisitor V} {data env v pos index v' finish entries}
    (h : EntriesRun visitor data env v pos index v' finish entries) :
    module.validate_code_entries_with_loop visitor data env v pos index = .ok (.Ok finish, v') := by
  induction h with
  | done v pos index hstop =>
    have hs : index ≥ alloc.vec.Vec.len env.func_type_indices := by scalar_tac
    unfold module.validate_code_entries_with_loop
    rw [loop]
    simp [module.validate_code_entries_with_loop.body, hs]
  | more hm hn hw hf hw2 he hj _ ih =>
    rw [loop_more _ _ _ hm hn hw hf hw2 he hj]
    exact ih

/-- An accepted actual loop has a finite certificate regardless of whether
unvisited callbacks would terminate or accept. -/
theorem EntriesRun.of_accepted {V : Type} (visitor : module.CodeVisitor V) (data : Slice U8)
    (env : module.Env) (v v' : V) (pos index finish : Usize)
    (h : module.validate_code_entries_with_loop visitor data env v pos index = .ok (.Ok finish, v')) :
    ∃ entries, EntriesRun visitor data env v pos index v' finish entries := by
  generalize hn : env.func_type_indices.val.length - index.val = n
  induction n using Nat.strong_induction_on generalizing v pos index with
  | h n ih =>
    have horiginal := h
    unfold module.validate_code_entries_with_loop at h
    rw [loop] at h
    simp only [module.validate_code_entries_with_loop.body] at h
    by_cases hi : index ≥ alloc.vec.Vec.len env.func_type_indices
    · have he : pos = finish ∧ v = v' := by simpa [hi] using h
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨[], .done _ _ _ (by scalar_tac)⟩
    have hmore : index.val < env.func_type_indices.val.length := by scalar_tac
    rw [if_neg hi] at h
    simp only [Std.bind_assoc] at h
    obtain ⟨need, hneed, h⟩ := VisitorErasure.bind_ok_inv _ _ _ h
    obtain ⟨⟨reply, v1⟩, hwait, h⟩ := VisitorErasure.bind_ok_inv _ _ _ h
    cases reply with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok u =>
      cases u
      simp [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_assoc] at h
      obtain ⟨r, hframe, h⟩ := VisitorErasure.bind_ok_inv _ _ _ h
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok pair =>
        obtain ⟨content, last⟩ := pair
        simp [Std.bind_assoc] at h
        obtain ⟨⟨reply, v2⟩, hwait2, h⟩ := VisitorErasure.bind_ok_inv _ _ _ h
        cases reply with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
        | Ok u =>
          cases u
          simp [Std.bind_assoc] at h
          obtain ⟨⟨reply, v3⟩, hentry, h⟩ := VisitorErasure.bind_ok_inv _ _ _ h
          cases reply with
          | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
          | Ok u =>
            cases u
            simp [Std.bind_assoc] at h
            obtain ⟨j, hj, _⟩ := VisitorErasure.bind_ok_inv _ _ _ h
            have hval := UScalar.add_spec (x := index) (y := 1#usize) (by scalar_tac)
            rw [hj, WP.spec_ok] at hval
            have hlt : env.func_type_indices.val.length - j.val < n := by scalar_tac
            have htail := (loop_more visitor data env hmore hneed hwait hframe hwait2 hentry hj).symm.trans horiginal
            obtain ⟨entries, ht⟩ := ih _ hlt v3 last j htail rfl
            exact ⟨_, .more hmore hneed hwait hframe hwait2 hentry hj ht⟩

/-- Deferred obligations are attached to the positions actually handed out. -/
def EntriesValidate (data : Slice U8) (env : module.Env) (entries : List Entry) : Prop :=
  ∀ index pos, (index, pos) ∈ entries →
    ∃ next, module.validate_code_entry data pos env index = .ok (.Ok next)

theorem EntriesRun.validated {V : Type} {visitor : module.CodeVisitor V} {data env v pos index v' finish entries}
    (h : EntriesRun visitor data env v pos index v' finish entries)
    (hv : Validates visitor data env) : EntriesValidate data env entries := by
  induction h with
  | done => intro index pos hm; simp at hm
  | more _ _ _ _ _ he _ _ ih =>
    intro index pos hm
    rcases List.mem_cons.mp hm with hp | hm
    · cases hp
      exact hv _ _ _ _ _ _ he
    · exact ih index pos hm

theorem EntriesRun.transfer {V W : Type} {visitor : module.CodeVisitor V}
    {data env v pos index v' finish entries}
    (h : EntriesRun visitor data env v pos index v' finish entries)
    (replacement : module.CodeVisitor W) (ha : Accepts replacement data env)
    (hv : EntriesValidate data env entries) (w : W) :
    ∃ w', EntriesRun replacement data env w pos index w' finish entries := by
  induction h generalizing w with
  | done _ pos index hs => exact ⟨w, .done _ _ _ hs⟩
  | @more v v1 v2 v3 v' pos content last index j need finish entries hm hn _ hf _ _ hj ht ih =>
    obtain ⟨w1, hw1⟩ := ha.need_bytes w need
    obtain ⟨w2, hw2⟩ := ha.need_bytes w1 last
    obtain ⟨next, hentry⟩ := hv index pos (by simp)
    obtain ⟨w3, hw3⟩ := ha.entry w2 index pos content last next hentry
    obtain ⟨w', hrest⟩ := ih (by intro i p hp; exact hv i p (by simp [hp])) w3
    exact ⟨w', .more hm hn hw1 hf hw2 hw3 hj hrest⟩

/-- An accepted section's exact actual framing path, including the initial
readiness callback and the final section-size check. -/
inductive SectionRun {V : Type} (visitor : module.CodeVisitor V) (data : Slice U8)
    (pos : Usize) (env : module.Env) : V → V → Usize → List Entry → Prop where
  | absent {v v' size need}
      (hsize : limits.MAX_CODE_HEADER_BYTES = .ok size)
      (hneed : (pos + size : Result Usize) = .ok need)
      (hwait : visitor.on_need_bytes v need = .ok (.Ok (), v'))
      (hsection : module.code_section data pos env = .ok (.Ok none)) :
      SectionRun visitor data pos env v v' pos []
  | present {v v1 v' size need cs entries}
      (hsize : limits.MAX_CODE_HEADER_BYTES = .ok size)
      (hneed : (pos + size : Result Usize) = .ok need)
      (hwait : visitor.on_need_bytes v need = .ok (.Ok (), v1))
      (hsection : module.code_section data pos env = .ok (.Ok (some cs)))
      (hentries : EntriesRun visitor data env v1 cs.entries 0#usize v' cs.end entries) :
      SectionRun visitor data pos env v v' cs.end entries

theorem SectionRun.accepted {V : Type} {visitor : module.CodeVisitor V} {data pos env v v' finish entries}
    (h : SectionRun visitor data pos env v v' finish entries) :
    module.validate_code_with visitor data pos env v = .ok (.Ok finish, v') := by
  cases h with
  | absent hs hn hw hc =>
    simp [module.validate_code_with, hs, hn, hw, hc, core.result.Result.Insts.CoreOpsTry.branch]
  | present hs hn hw hc ht =>
    simp [module.validate_code_with, hs, hn, hw, hc, module.validate_code_entries_with,
      ht.accepted, core.result.Result.Insts.CoreOpsTry.branch]

theorem SectionRun.of_accepted {V : Type} (visitor : module.CodeVisitor V)
    (data : Slice U8) (pos : Usize) (env : module.Env) (v v' : V) (finish : Usize)
    (h : module.validate_code_with visitor data pos env v = .ok (.Ok finish, v')) :
    ∃ entries, SectionRun visitor data pos env v v' finish entries := by
  unfold module.validate_code_with at h
  obtain ⟨size, hs, h⟩ := VisitorErasure.bind_ok_inv _ _ _ h
  obtain ⟨need, hn, h⟩ := VisitorErasure.bind_ok_inv _ _ _ h
  obtain ⟨⟨reply, v1⟩, hw, h⟩ := VisitorErasure.bind_ok_inv _ _ _ h
  cases reply with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
  | Ok u =>
    cases u
    simp [core.result.Result.Insts.CoreOpsTry.branch] at h
    obtain ⟨r, hc, h⟩ := VisitorErasure.bind_ok_inv _ _ _ h
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok opt =>
      cases opt with
      | none =>
        have he : pos = finish ∧ v1 = v' := by simpa using h
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨[], .absent hs hn hw hc⟩
      | some cs =>
        simp at h
        obtain ⟨⟨r, v2⟩, hr, h⟩ := VisitorErasure.bind_ok_inv _ _ _ h
        cases r with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
        | Ok next =>
          simp at h
          split at h
          · rename_i hnext
            have hnext' : next = cs.end := UScalar.eq_of_val_eq hnext
            have he : cs.end = finish ∧ v2 = v' := by simpa using h
            obtain ⟨hf, hv⟩ := he
            subst finish
            subst v2
            subst next
            obtain ⟨entries, he⟩ := EntriesRun.of_accepted visitor data env v1 v' cs.entries 0#usize cs.end hr
            exact ⟨entries, .present hs hn hw hc he⟩
          · simp at h

theorem SectionRun.transfer {V W : Type} {visitor : module.CodeVisitor V}
    {data pos env v v' finish entries}
    (h : SectionRun visitor data pos env v v' finish entries)
    (replacement : module.CodeVisitor W) (ha : Accepts replacement data env)
    (hv : EntriesValidate data env entries) (w : W) :
    ∃ w', SectionRun replacement data pos env w w' finish entries := by
  cases h with
  | absent hs hn _ hc =>
    obtain ⟨w', hw⟩ := ha.need_bytes w _
    exact ⟨w', .absent hs hn hw hc⟩
  | present hs hn _ hc ht =>
    obtain ⟨w1, hw⟩ := ha.need_bytes w _
    obtain ⟨w', ht'⟩ := ht.transfer replacement ha hv w1
    exact ⟨w', .present hs hn hw hc ht'⟩

theorem SectionRun.validated {V : Type} {visitor : module.CodeVisitor V}
    {data pos env v v' finish entries}
    (h : SectionRun visitor data pos env v v' finish entries)
    (hv : Validates visitor data env) : EntriesValidate data env entries := by
  cases h with
  | absent => intro i p hm; simp at hm
  | present _ _ _ _ ht => exact ht.validated hv

end Itasca.ModuleCodeVisitor

namespace Itasca

/-- Immediate entry-validation and acceptance contracts transfer any accepted
code-section walk without prevalidated bytes or hook-totality hypotheses. -/
theorem module.validate_code_with.accepted_transfer {V W : Type}
    (visitor : module.CodeVisitor V) (replacement : module.CodeVisitor W)
    (data : Slice U8) (pos : Usize) (env : module.Env) (finish : Usize)
    (hv : ModuleCodeVisitor.Validates visitor data env)
    (ha : ModuleCodeVisitor.Accepts replacement data env) (v v' : V) (w : W)
    (h : module.validate_code_with visitor data pos env v = .ok (.Ok finish, v')) :
    ∃ w', module.validate_code_with replacement data pos env w = .ok (.Ok finish, w') := by
  obtain ⟨entries, hr⟩ := ModuleCodeVisitor.SectionRun.of_accepted visitor data pos env v v' finish h
  obtain ⟨w', hw⟩ := hr.transfer replacement ha (hr.validated hv) w
  exact ⟨w', hw.accepted⟩

theorem module.validate_code_with.accepted_erase {V : Type}
    (visitor : module.CodeVisitor V) (data : Slice U8) (pos : Usize) (env : module.Env)
    (finish : Usize) (hv : ModuleCodeVisitor.Validates visitor data env) (v v' : V)
    (h : module.validate_code_with visitor data pos env v = .ok (.Ok finish, v')) :
    module.validate_code data pos env = .ok (.Ok finish) := by
  obtain ⟨w, hw⟩ := module.validate_code_with.accepted_transfer visitor
    module.ValidatingCodeVisitor.Insts.ItascaModuleCodeVisitor data pos env finish hv
    (ModuleCodeVisitor.default_accepts data env) v v' () h
  simp [module.validate_code, hw]

theorem module.validate_code_with.accepted_lift {V : Type}
    (visitor : module.CodeVisitor V) (data : Slice U8) (pos : Usize) (env : module.Env)
    (finish : Usize) (ha : ModuleCodeVisitor.Accepts visitor data env) (v : V)
    (h : module.validate_code data pos env = .ok (.Ok finish)) :
    ∃ v', module.validate_code_with visitor data pos env v = .ok (.Ok finish, v') := by
  unfold module.validate_code at h
  obtain ⟨⟨r, w⟩, hr, h⟩ := VisitorErasure.bind_ok_inv _ _ _ h
  have he : r = .Ok finish := by simpa using h
  rw [he] at hr
  exact module.validate_code_with.accepted_transfer
    module.ValidatingCodeVisitor.Insts.ItascaModuleCodeVisitor visitor data pos env finish
    (ModuleCodeVisitor.default_validates data env) ha () () v hr

end Itasca
