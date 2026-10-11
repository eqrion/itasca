import Itasca.Support.Result
import Itasca.Module.ModuleCustomVisitor

open Aeneas Aeneas.Std

namespace Itasca.ModuleTail

/-- A custom-section consumer may advance workers while preserving a
provenance invariant; no fixed work observation is required. -/
def PreservesInvariant {V : Type} (visitor : module.ModuleVisitor V) (P : V → Prop) : Prop :=
  ∀ v chunk v', visitor.on_custom_section v chunk = .ok (.Ok (), v') → P v → P v'

end Itasca.ModuleTail

namespace Itasca

theorem module.validate_tail_with_loop.accepted_invariant {V : Type}
    (visitor : module.ModuleVisitor V) (P : V → Prop) (hp : ModuleTail.PreservesInvariant visitor P)
    (data : Slice U8) (env : module.Env) (v : V)
    (segments : alloc.vec.Vec module.Data) (pos : Usize) (seen : Bool)
    (result : module.Tail) (v' : V)
    (h : module.validate_tail_with_loop visitor data env v segments pos seen = .ok (.Ok result, v')) :
    P v → P v' := by
  generalize hn : data.length - pos.val = n
  induction n using Nat.strong_induction_on generalizing v segments pos seen with
  | h n ih =>
    unfold module.validate_tail_with_loop at h
    rw [loop] at h
    simp only [module.validate_tail_with_loop.body] at h
    by_cases hstop : pos ≥ Slice.len data
    · simp [hstop] at h
      obtain ⟨_, rfl⟩ := h
      exact id
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
    (h : module.validate_tail_with visitor data pos env v = .ok (.Ok result, v')) :
    P v → P v' :=
  module.validate_tail_with_loop.accepted_invariant visitor P hp data env v
    (alloc.vec.Vec.new _) pos false result v' h

/-- Environment custom callbacks preserve arbitrary scheduler provenance. -/
theorem module.validate_env_with_loop.accepted_invariant {V : Type}
    (visitor : module.ModuleVisitor V) (P : V → Prop)
    (hp : ModuleTail.PreservesInvariant visitor P) (data : Slice U8)
    (v : V) (env : module.Env) (pos : Usize) (lastId : U8)
    (result : module.Env) (next : Usize) (v' : V)
    (h : module.validate_env_with_loop visitor data v env pos lastId =
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
          by_cases hcode : module.SECTION_CODE.val ≤ id.val
          · simp [hcode] at h
            obtain ⟨_, _, rfl⟩ := h
            exact fun hv => hv
          · simp only [hcode, ↓reduceIte] at h
            by_cases horder : id.val ≤ lastId.val
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
                  exact ih (data.length - last.val) hmeasure v updated last id
                    (by simpa [module.validate_env_with_loop, module.validate_env_with_loop.body,
                      core.result.Result.Insts.CoreOpsTry.branch] using ht) rfl
                · have hne : consumed.val ≠ last.val := fun h => he (UScalar.eq_of_val_eq h)
                  simp [hne] at ht

theorem module.validate_env_with.accepted_invariant {V : Type}
    (visitor : module.ModuleVisitor V) (P : V → Prop)
    (hp : ModuleTail.PreservesInvariant visitor P) (data : Slice U8)
    (v : V) (result : module.Env) (next : Usize) (v' : V)
    (h : module.validate_env_with visitor data v = .ok (.Ok (result, next), v')) :
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
