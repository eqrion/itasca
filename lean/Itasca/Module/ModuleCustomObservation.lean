import Itasca.Support.Result
import Itasca.Module.ModuleCustomVisitor

open Aeneas Aeneas.Std

namespace Itasca.ModuleTail

/-- A custom-section consumer may change its own state while preserving an
observation, such as the work list handed to deferred compilation threads. -/
def Preserves {V A : Type} (visitor : module.ModuleVisitor V) (observe : V → A) : Prop :=
  ∀ v chunk v', visitor.on_custom_section v chunk = .ok (.Ok (), v') → observe v' = observe v

end Itasca.ModuleTail

namespace Itasca

theorem module.validate_tail_with_loop.accepted_preserves {V A : Type}
    (visitor : module.ModuleVisitor V) (observe : V → A) (hp : ModuleTail.Preserves visitor observe)
    (data : Slice U8) (env : module.Env) (v : V)
    (segments : alloc.vec.Vec module.Data) (pos : Usize) (seen : Bool)
    (result : module.Tail) (v' : V)
    (h : module.validate_tail_with_loop visitor data env v segments pos seen = .ok (.Ok result, v')) :
    observe v' = observe v := by
  generalize hn : data.length - pos.val = n
  induction n using Nat.strong_induction_on generalizing v segments pos seen with
  | h n ih =>
    unfold module.validate_tail_with_loop at h
    rw [loop] at h
    simp only [module.validate_tail_with_loop.body] at h
    by_cases hstop : pos ≥ Slice.len data
    · simp [hstop] at h
      obtain ⟨_, rfl⟩ := h
      rfl
    · simp only [hstop, ↓reduceIte] at h
      obtain ⟨r, hr, hh⟩ := WP.spec_imp_exists (module.read_section_header.spec data pos)
      rw [hr] at h
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok triple =>
        obtain ⟨id, first, last⟩ := triple
        have hspan := hh.span
        have hmeasure : data.length - last.val < n := by scalar_tac
        simp [core.result.Result.Insts.CoreOpsTry.branch] at h
        by_cases hcustom : id = module.SECTION_CUSTOM
        · simp only [hcustom, ↓reduceIte] at h
          obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (module.decode_custom_section.spec data first last)
          rw [hr] at h
          cases r with
          | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
          | Ok chunk =>
            simp [Std.bind_assoc] at h
            obtain ⟨⟨reply, v1⟩, hv, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
            cases reply with
            | Err e => simp at ht
            | Ok u =>
              cases u
              have hobs := hp v chunk v1 hv
              have hrest := ih (data.length - last.val) hmeasure v1 segments last seen
                (by simpa [module.validate_tail_with_loop, module.validate_tail_with_loop.body,
                  core.result.Result.Insts.CoreOpsTry.branch] using ht) rfl
              exact hrest.trans hobs
        · simp only [hcustom, ↓reduceIte] at h
          by_cases hdata : id.val = module.SECTION_DATA.val
          · simp only [hdata, ↓reduceIte] at h
            cases seen with
            | true => simp at h
            | false =>
              simp [Std.bind_assoc] at h
              obtain ⟨read, _, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
              cases read with
              | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at ht
              | Ok pair =>
                obtain ⟨decoded, consumed⟩ := pair
                simp at ht
                by_cases he : consumed.val = last.val
                · simp only [he, ↓reduceIte] at ht
                  exact ih (data.length - last.val) hmeasure v decoded last true
                    (by simpa [module.validate_tail_with_loop, module.validate_tail_with_loop.body,
                      core.result.Result.Insts.CoreOpsTry.branch] using ht) rfl
                · simp [he] at ht
          · simp [hdata] at h

/-- Accepted tail validation preserves deferred work observations when custom
callbacks do. This speaks only about the actual successful run. -/
theorem module.validate_tail_with.accepted_preserves {V A : Type}
    (visitor : module.ModuleVisitor V) (observe : V → A) (hp : ModuleTail.Preserves visitor observe)
    (data : Slice U8) (pos : Usize) (env : module.Env) (v : V) (result : module.Tail) (v' : V)
    (h : module.validate_tail_with visitor data pos env v = .ok (.Ok result, v')) :
    observe v' = observe v :=
  module.validate_tail_with_loop.accepted_preserves visitor observe hp data env v
    (alloc.vec.Vec.new _) pos false result v' h

end Itasca
