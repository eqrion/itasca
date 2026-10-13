import Itasca.Support.Result
import Itasca.Module.Custom.Visitor

open Aeneas Aeneas.Std

namespace Itasca.ModuleTail

/-- A custom-section consumer may advance workers while preserving a
provenance invariant; no fixed work observation is required. -/
def PreservesInvariant {V : Type} (visitor : module.ModuleVisitor V) (P : V → Prop) : Prop :=
  ∀ v chunk v', visitor.on_custom_section v chunk = .ok (.Ok (), v') → P v → P v'

end Itasca.ModuleTail

namespace Itasca

variable {profile : ValidationProfile}

theorem module.validate_tail_with_loop.accepted_invariant {V : Type}
    (visitor : module.ModuleVisitor V) (P : V → Prop) (hp : ModuleTail.PreservesInvariant visitor P)
    (data : Slice U8) (env : module.Env) (v : V)
    (segments : alloc.vec.Vec module.Data) (pos : Usize) (seen : Bool)
    (result : module.Tail) (v' : V)
    (h : module.validate_tail_with_loop visitor data env profile v segments pos seen = .ok (.Ok result, v')) :
    P v → P v' := by
  generalize hn : data.length - pos.val = n
  induction n using Nat.strong_induction_on generalizing v segments pos seen with
  | h n ih =>
    unfold module.validate_tail_with_loop at h
    rw [loop] at h
    simp only [module.validate_tail_with_loop.body] at h
    by_cases hstop : pos ≥ Slice.len data
    · simp only [hstop, ↓reduceIte] at h
      cases hc : env.data_count with
      | none =>
        simp [hc] at h
        obtain ⟨_, rfl⟩ := h
        exact id
      | some count =>
        simp only [hc, Std.bind_assoc] at h
        obtain ⟨size, _, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
        by_cases he : size.val = segments.val.length
        · simp [he] at ht
          obtain ⟨_, rfl⟩ := ht
          exact id
        · simp [he] at ht
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
              exact fun hv => hrest (hobs hv)
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

/-- Accepted tail validation preserves a scheduler invariant when custom
callbacks do. This speaks only about the actual successful run. -/
theorem module.validate_tail_with.accepted_invariant {V : Type}
    (visitor : module.ModuleVisitor V) (P : V → Prop) (hp : ModuleTail.PreservesInvariant visitor P)
    (data : Slice U8) (pos : Usize) (env : module.Env) (v : V) (result : module.Tail) (v' : V)
    (h : module.validate_tail_with visitor data pos env profile v = .ok (.Ok result, v')) :
    P v → P v' :=
  module.validate_tail_with_loop.accepted_invariant visitor P hp data env v
    (alloc.vec.Vec.new _) pos false result v' h

/-- Environment custom callbacks preserve arbitrary scheduler provenance. -/
theorem module.validate_env_with_loop.accepted_invariant {V : Type}
    (visitor : module.ModuleVisitor V) (P : V → Prop)
    (hp : ModuleTail.PreservesInvariant visitor P) (data : Slice U8)
    (v : V) (env : module.Env) (pos : Usize) (lastId : U8)
    (result : module.Env) (next : Usize) (v' : V)
    (h : module.validate_env_with_loop visitor data profile v env pos lastId =
      .ok (.Ok (result, next), v')) : P v → P v' := by
  generalize hn : data.length - pos.val = n
  induction n using Nat.strong_induction_on generalizing v env pos lastId with
  | h n ih =>
    unfold module.validate_env_with_loop at h
    rw [loop] at h
    simp only [module.validate_env_with_loop.body] at h
    by_cases hstop : pos ≥ Slice.len data
    · simp [hstop] at h
      obtain ⟨_, _, rfl⟩ := h
      exact id
    · simp only [hstop, ↓reduceIte] at h
      obtain ⟨r, hr, hpRead⟩ := WP.spec_imp_exists (module.read_section_header.spec data pos)
      rw [hr] at h
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok triple =>
        obtain ⟨id, first, last⟩ := triple
        have hspan := hpRead.span
        have hmeasure : data.length - last.val < n := by scalar_tac
        simp [core.result.Result.Insts.CoreOpsTry.branch] at h
        by_cases hcustom : id = module.SECTION_CUSTOM
        · simp only [hcustom, ↓reduceIte] at h
          obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (module.decode_custom_section.spec data first last)
          rw [hr] at h
          cases r with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
          | Ok chunk =>
            simp [Std.bind_assoc] at h
            obtain ⟨⟨reply, v1⟩, hv, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
            cases reply with
            | Err e => simp at ht
            | Ok u =>
              cases u
              have hrest := ih (data.length - last.val) hmeasure v1 env last lastId
                (by simpa [module.validate_env_with_loop, module.validate_env_with_loop.body,
                  core.result.Result.Insts.CoreOpsTry.branch] using ht) rfl
              exact fun hv0 => hrest (hp v chunk v1 hv hv0)
        · simp only [hcustom, ↓reduceIte] at h
          by_cases hcode : id = module.SECTION_CODE
          · simp [hcode] at h
            obtain ⟨_, _, rfl⟩ := h
            exact fun hv => hv
          · simp only [hcode, ↓reduceIte] at h
            by_cases hdata : id = module.SECTION_DATA
            · simp [hdata] at h
              obtain ⟨_, _, rfl⟩ := h
              exact fun hv => hv
            · simp only [hdata, ↓reduceIte] at h
              obtain ⟨ordered, hord, _⟩ := WP.spec_imp_exists (module.section_order.spec id)
              rw [hord] at h
              cases ordered with
              | Err e =>
                simp [
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
              | Ok rank =>
                simp only [bind_ok] at h
                by_cases horder : rank.val ≤ lastId.val
                · simp [horder] at h
                · simp only [horder, ↓reduceIte, Std.bind_assoc] at h
                  obtain ⟨⟨read, updated⟩, _, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
                  cases read with
                  | Err e =>
                    simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at ht
                  | Ok consumed =>
                    simp at ht
                    by_cases he : consumed = last
                    · simp only [he, ↓reduceIte] at ht
                      exact ih (data.length - last.val) hmeasure v updated last rank
                        (by simpa [module.validate_env_with_loop, module.validate_env_with_loop.body,
                          core.result.Result.Insts.CoreOpsTry.branch] using ht) rfl
                    · have hne : consumed.val ≠ last.val := fun h => he (UScalar.eq_of_val_eq h)
                      simp [hne] at ht

theorem module.validate_env_with.accepted_invariant {V : Type}
    (visitor : module.ModuleVisitor V) (P : V → Prop)
    (hp : ModuleTail.PreservesInvariant visitor P) (data : Slice U8)
    (v : V) (result : module.Env) (next : Usize) (v' : V)
    (h : module.validate_env_with visitor data profile v = .ok (.Ok (result, next), v')) :
    P v → P v' := by
  unfold module.validate_env_with at h
  obtain ⟨initial, _, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
  obtain ⟨read, _, ht⟩ := ResultFacts.bind_ok_inv _ _ _ ht
  cases read with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at ht
  | Ok start =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at ht
    exact module.validate_env_with_loop.accepted_invariant visitor P hp data
      v initial start 0#u8 result next v' ht

end Itasca

open Aeneas Aeneas.Std

namespace Itasca.ModuleTail

/-- A custom-section consumer may change its own state while preserving an
observation, such as the work list handed to deferred compilation threads. -/
def Preserves {V A : Type} (visitor : module.ModuleVisitor V) (observe : V → A) : Prop :=
  ∀ v chunk v', visitor.on_custom_section v chunk = .ok (.Ok (), v') → observe v' = observe v

end Itasca.ModuleTail

namespace Itasca

variable {profile : ValidationProfile}

theorem module.validate_tail_with_loop.accepted_preserves {V A : Type}
    (visitor : module.ModuleVisitor V) (observe : V → A) (hp : ModuleTail.Preserves visitor observe)
    (data : Slice U8) (env : module.Env) (v : V)
    (segments : alloc.vec.Vec module.Data) (pos : Usize) (seen : Bool)
    (result : module.Tail) (v' : V)
    (h : module.validate_tail_with_loop visitor data env profile v segments pos seen = .ok (.Ok result, v')) :
    observe v' = observe v := by
  have hinvariant : ModuleTail.PreservesInvariant visitor (fun state => observe state = observe v) := by
    intro before chunk after hcallback hbefore
    exact (hp before chunk after hcallback).trans hbefore
  exact module.validate_tail_with_loop.accepted_invariant visitor _ hinvariant
    data env v segments pos seen result v' h rfl

/-- Accepted tail validation preserves deferred work observations when custom
callbacks do. This speaks only about the actual successful run. -/
theorem module.validate_tail_with.accepted_preserves {V A : Type}
    (visitor : module.ModuleVisitor V) (observe : V → A) (hp : ModuleTail.Preserves visitor observe)
    (data : Slice U8) (pos : Usize) (env : module.Env) (v : V) (result : module.Tail) (v' : V)
    (h : module.validate_tail_with visitor data pos env profile v = .ok (.Ok result, v')) :
    observe v' = observe v :=
  module.validate_tail_with_loop.accepted_preserves visitor observe hp data env v
    (alloc.vec.Vec.new _) pos false result v' h

end Itasca
