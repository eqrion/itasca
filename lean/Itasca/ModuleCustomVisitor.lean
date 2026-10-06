import Itasca.ModuleEnvParser
import Itasca.VisitorErasure

open Aeneas Aeneas.Std

namespace Itasca.ModuleTail

/-- Custom-section hooks always return normally and accept. -/
def HooksAccept {V : Type} (visitor : module.ModuleVisitor V) : Prop :=
  ∀ (v : V) (chunk : types.CustomSection),
    ∃ v', visitor.on_custom_section v chunk = .ok (.Ok (), v')

theorem HooksAccept.total {V : Type} {visitor : module.ModuleVisitor V}
    (h : HooksAccept visitor) : HooksTotal visitor := by
  intro v chunk
  obtain ⟨v', hv⟩ := h v chunk
  exact ⟨(.Ok (), v'), hv⟩

theorem empty_hooks_accept : HooksAccept module.EmptyModuleVisitor.Insts.ItascaModuleModuleVisitor := by
  intro v chunk
  exact ⟨v, rfl⟩

end Itasca.ModuleTail

namespace Itasca

theorem module.validate_env_with_loop.accepted_transfer {V W : Type}
    (visitor : module.ModuleVisitor V) (replacement : module.ModuleVisitor W)
    (haccept : ModuleTail.HooksAccept replacement) (data : Slice U8)
    (v : V) (w : W) (env : module.Env) (pos : Usize) (lastId : U8)
    (result : module.Env) (next : Usize) (v' : V)
    (h : module.validate_env_with_loop visitor data v env pos lastId =
      .ok (.Ok (result, next), v')) :
    ∃ w', module.validate_env_with_loop replacement data w env pos lastId =
      .ok (.Ok (result, next), w') := by
  generalize hn : data.length - pos.val = n
  induction n using Nat.strong_induction_on generalizing v w env pos lastId with
  | h n ih =>
    unfold module.validate_env_with_loop at h ⊢
    rw [loop] at h ⊢
    simp only [module.validate_env_with_loop.body] at h ⊢
    by_cases hstop : pos ≥ Slice.len data
    · simp [hstop] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    · simp only [hstop, ↓reduceIte] at h ⊢
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.read_section_header.spec data pos)
      rw [hr] at h ⊢
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok triple =>
        obtain ⟨id, first, last⟩ := triple
        have hspan := hp.span
        have hmeasure : data.length - last.val < n := by scalar_tac
        simp [core.result.Result.Insts.CoreOpsTry.branch] at h ⊢
        by_cases hcustom : id = module.SECTION_CUSTOM
        · simp only [hcustom, ↓reduceIte] at h ⊢
          obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (module.decode_custom_section.spec data first last)
          rw [hr] at h ⊢
          cases r with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
          | Ok chunk =>
            simp [Std.bind_assoc] at h ⊢
            obtain ⟨⟨reply, v1⟩, hv, ht⟩ := VisitorErasure.bind_ok_inv _ _ _ h
            cases reply with
            | Err e => simp at ht
            | Ok u =>
              obtain ⟨w1, hw⟩ := haccept w chunk
              rw [hw]
              simp only [bind_ok]
              obtain ⟨w', hw'⟩ := ih (data.length - last.val) hmeasure v1 w1 env last lastId
                (by simpa [module.validate_env_with_loop, module.validate_env_with_loop.body,
                  core.result.Result.Insts.CoreOpsTry.branch] using ht) rfl
              exact ⟨w', by simpa [module.validate_env_with_loop, module.validate_env_with_loop.body,
                core.result.Result.Insts.CoreOpsTry.branch] using hw'⟩
        · simp only [hcustom, ↓reduceIte] at h ⊢
          by_cases hcode : module.SECTION_CODE.val ≤ id.val
          · simp [hcode] at h ⊢
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact ⟨rfl, rfl⟩
          · simp only [hcode, ↓reduceIte] at h ⊢
            by_cases horder : id.val ≤ lastId.val
            · simp [horder] at h
            · simp only [horder, ↓reduceIte] at h ⊢
              simp only [Std.bind_assoc] at h ⊢
              obtain ⟨⟨read, updated⟩, hr, ht⟩ := VisitorErasure.bind_ok_inv _ _ _ h
              rw [hr]
              simp only [bind_ok]
              cases read with
              | Err e =>
                simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at ht
              | Ok consumed =>
                simp at ht ⊢
                by_cases he : consumed = last
                · simp only [he, ↓reduceIte] at ht ⊢
                  obtain ⟨w', hw'⟩ := ih (data.length - last.val) hmeasure v w updated last id
                    (by simpa [module.validate_env_with_loop, module.validate_env_with_loop.body,
                      core.result.Result.Insts.CoreOpsTry.branch] using ht) rfl
                  exact ⟨w', by simpa [module.validate_env_with_loop, module.validate_env_with_loop.body,
                    core.result.Result.Insts.CoreOpsTry.branch] using hw'⟩
                · have hne : consumed.val ≠ last.val := fun h => he (UScalar.eq_of_val_eq h)
                  simp [hne] at ht

theorem module.validate_env_with.accepted_transfer {V W : Type}
    (visitor : module.ModuleVisitor V) (replacement : module.ModuleVisitor W)
    (haccept : ModuleTail.HooksAccept replacement) (data : Slice U8)
    (v : V) (w : W) (result : module.Env) (next : Usize) (v' : V)
    (h : module.validate_env_with visitor data v = .ok (.Ok (result, next), v')) :
    ∃ w', module.validate_env_with replacement data w = .ok (.Ok (result, next), w') := by
  unfold module.validate_env_with at h ⊢
  obtain ⟨initial, hi, ht⟩ := VisitorErasure.bind_ok_inv _ _ _ h
  rw [hi]
  simp only [bind_ok]
  obtain ⟨read, hr, ht⟩ := VisitorErasure.bind_ok_inv _ _ _ ht
  rw [hr]
  simp only [bind_ok]
  cases read with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at ht
  | Ok start =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at ht ⊢
    exact module.validate_env_with_loop.accepted_transfer visitor replacement haccept data
      v w initial start 0#u8 result next v' ht

/-- Successful visiting parsing has exactly the default parser's environment
and cursor, with no assumption about any other callback execution. -/
theorem module.validate_env_with.accepted_erase {V : Type}
    (visitor : module.ModuleVisitor V) (data : Slice U8) (v : V)
    (result : module.Env) (next : Usize) (v' : V)
    (h : module.validate_env_with visitor data v = .ok (.Ok (result, next), v')) :
    module.validate_env data = .ok (.Ok (result, next)) := by
  obtain ⟨w', hw⟩ := module.validate_env_with.accepted_transfer visitor
    module.EmptyModuleVisitor.Insts.ItascaModuleModuleVisitor ModuleTail.empty_hooks_accept
    data v () result next v' h
  simp [module.validate_env, hw]

theorem module.validate_env_with.accepted_lift {V : Type}
    (visitor : module.ModuleVisitor V) (haccept : ModuleTail.HooksAccept visitor)
    (data : Slice U8) (v : V) (result : module.Env) (next : Usize)
    (h : module.validate_env data = .ok (.Ok (result, next))) :
    ∃ v', module.validate_env_with visitor data v = .ok (.Ok (result, next), v') := by
  unfold module.validate_env at h
  obtain ⟨⟨read, w⟩, hr, ht⟩ := VisitorErasure.bind_ok_inv _ _ _ h
  have ht : read = .Ok (result, next) := by simpa using ht
  subst read
  exact module.validate_env_with.accepted_transfer
    module.EmptyModuleVisitor.Insts.ItascaModuleModuleVisitor visitor haccept data
    () v result next w hr

theorem module.validate_tail_with_loop.accepted_transfer {V W : Type}
    (visitor : module.ModuleVisitor V) (replacement : module.ModuleVisitor W)
    (haccept : ModuleTail.HooksAccept replacement) (data : Slice U8) (env : module.Env)
    (v : V) (w : W) (segments : alloc.vec.Vec module.Data) (pos : Usize) (seen : Bool)
    (result : module.Tail) (v' : V)
    (h : module.validate_tail_with_loop visitor data env v segments pos seen =
      .ok (.Ok result, v')) :
    ∃ w', module.validate_tail_with_loop replacement data env w segments pos seen =
      .ok (.Ok result, w') := by
  generalize hn : data.length - pos.val = n
  induction n using Nat.strong_induction_on generalizing v w segments pos seen with
  | h n ih =>
    unfold module.validate_tail_with_loop at h ⊢
    rw [loop] at h ⊢
    simp only [module.validate_tail_with_loop.body] at h ⊢
    by_cases hstop : pos ≥ Slice.len data
    · simp [hstop] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · simp only [hstop, ↓reduceIte] at h ⊢
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.read_section_header.spec data pos)
      rw [hr] at h ⊢
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok triple =>
        obtain ⟨id, first, last⟩ := triple
        have hspan := hp.span
        have hmeasure : data.length - last.val < n := by scalar_tac
        simp [core.result.Result.Insts.CoreOpsTry.branch] at h ⊢
        by_cases hcustom : id = module.SECTION_CUSTOM
        · simp only [hcustom, ↓reduceIte] at h ⊢
          obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (module.decode_custom_section.spec data first last)
          rw [hr] at h ⊢
          cases r with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
          | Ok chunk =>
            simp [Std.bind_assoc] at h ⊢
            obtain ⟨⟨reply, v1⟩, hv, ht⟩ := VisitorErasure.bind_ok_inv _ _ _ h
            cases reply with
            | Err e => simp at ht
            | Ok u =>
              obtain ⟨w1, hw⟩ := haccept w chunk
              rw [hw]
              simp only [bind_ok]
              obtain ⟨w', hw'⟩ := ih (data.length - last.val) hmeasure v1 w1 segments last seen
                (by simpa [module.validate_tail_with_loop, module.validate_tail_with_loop.body,
                  core.result.Result.Insts.CoreOpsTry.branch] using ht) rfl
              exact ⟨w', by simpa [module.validate_tail_with_loop, module.validate_tail_with_loop.body,
                core.result.Result.Insts.CoreOpsTry.branch] using hw'⟩
        · simp only [hcustom, ↓reduceIte] at h ⊢
          by_cases hdata : id.val = module.SECTION_DATA.val
          · simp only [hdata, ↓reduceIte] at h ⊢
            cases seen with
            | true => simp at h
            | false =>
              simp [Std.bind_assoc] at h ⊢
              obtain ⟨read, hr, ht⟩ := VisitorErasure.bind_ok_inv _ _ _ h
              rw [hr]
              simp only [bind_ok]
              cases read with
              | Err e =>
                simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at ht
              | Ok pair =>
                obtain ⟨decoded, consumed⟩ := pair
                simp at ht ⊢
                by_cases he : consumed.val = last.val
                · simp only [he, ↓reduceIte] at ht ⊢
                  obtain ⟨w', hw'⟩ := ih (data.length - last.val) hmeasure v w decoded last true
                    (by simpa [module.validate_tail_with_loop, module.validate_tail_with_loop.body,
                      core.result.Result.Insts.CoreOpsTry.branch] using ht) rfl
                  exact ⟨w', by simpa [module.validate_tail_with_loop, module.validate_tail_with_loop.body,
                    core.result.Result.Insts.CoreOpsTry.branch] using hw'⟩
                · simp [he] at ht
          · simp [hdata] at h

theorem module.validate_tail_with.accepted_transfer {V W : Type}
    (visitor : module.ModuleVisitor V) (replacement : module.ModuleVisitor W)
    (haccept : ModuleTail.HooksAccept replacement) (data : Slice U8) (start : Usize)
    (env : module.Env) (v : V) (w : W) (result : module.Tail) (v' : V)
    (h : module.validate_tail_with visitor data start env v = .ok (.Ok result, v')) :
    ∃ w', module.validate_tail_with replacement data start env w = .ok (.Ok result, w') :=
  module.validate_tail_with_loop.accepted_transfer visitor replacement haccept data env
    v w (alloc.vec.Vec.new _) start false result v' h

/-- Custom hooks cannot change an accepted data tail, and erasing them needs
no termination premise for the source visitor. -/
theorem module.validate_tail_with.accepted_erase {V : Type}
    (visitor : module.ModuleVisitor V) (data : Slice U8) (start : Usize) (env : module.Env)
    (v : V) (result : module.Tail) (v' : V)
    (h : module.validate_tail_with visitor data start env v = .ok (.Ok result, v')) :
    module.validate_tail data start env = .ok (.Ok result) := by
  obtain ⟨w', hw⟩ := module.validate_tail_with.accepted_transfer visitor
    module.EmptyModuleVisitor.Insts.ItascaModuleModuleVisitor ModuleTail.empty_hooks_accept
    data start env v () result v' h
  simp [module.validate_tail, hw]

theorem module.validate_tail_with.accepted_lift {V : Type}
    (visitor : module.ModuleVisitor V) (haccept : ModuleTail.HooksAccept visitor)
    (data : Slice U8) (start : Usize) (env : module.Env) (v : V) (result : module.Tail)
    (h : module.validate_tail data start env = .ok (.Ok result)) :
    ∃ v', module.validate_tail_with visitor data start env v = .ok (.Ok result, v') := by
  unfold module.validate_tail at h
  obtain ⟨⟨read, w⟩, hr, ht⟩ := VisitorErasure.bind_ok_inv _ _ _ h
  have ht : read = .Ok result := by simpa using ht
  subst read
  exact module.validate_tail_with.accepted_transfer
    module.EmptyModuleVisitor.Insts.ItascaModuleModuleVisitor visitor haccept data start env
    () v result w hr

end Itasca
