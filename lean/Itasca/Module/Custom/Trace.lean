import Itasca.Support.Result
import Itasca.Module.Custom.TraceDefs
import Itasca.Module.Custom.Visitor

open Aeneas Aeneas.Std

namespace Itasca

variable {profile : ValidationProfile}

open ModuleTrace

/-- An accepted environment walk reports each custom section exactly where
its independently decoded header and UTF-8 name place its payload. -/
theorem module.validate_env_with_loop.accepted_trace {V : Type}
    (visitor : module.ModuleVisitor V) (observe : V → List Event)
    (hrecords : RecordsCustom visitor observe) (data : Slice U8)
    (v : V) (env : module.Env) (pos : Usize) (lastId : U8)
    (result : module.Env) (next : Usize) (v' : V)
    (hpos : pos.val ≤ data.length)
    (h : module.validate_env_with_loop visitor data profile v env pos lastId =
      .ok (.Ok (result, next), v')) :
    ∃ events, observe v' = observe v ++ events ∧
      SectionTrace data (fun id => (1 ≤ id.val ∧ id.val < 10) ∨ id.val = 12) pos next events := by
  generalize hn : data.length - pos.val = n
  induction n using Nat.strong_induction_on generalizing v env pos lastId with
  | h n ih =>
    unfold module.validate_env_with_loop at h
    rw [loop] at h
    simp only [module.validate_env_with_loop.body] at h
    by_cases hstop : pos ≥ Slice.len data
    · simp [hstop] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨[], by simp, .done _ hpos⟩
    · simp only [hstop, ↓reduceIte] at h
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.read_section_header.spec data pos)
      rw [hr] at h
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok triple =>
        obtain ⟨id, first, last⟩ := triple
        have hspan := hp.span
        have hmeasure : data.length - last.val < n := by scalar_tac
        simp [core.result.Result.Insts.CoreOpsTry.branch] at h
        by_cases hcustom : id = module.SECTION_CUSTOM
        · simp only [hcustom, ↓reduceIte] at h
          obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (module.decode_custom_section.spec data first last)
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
              obtain ⟨events, hlog, htrace⟩ := ih (data.length - last.val) hmeasure v1 env last lastId hspan.2.2
                (by simpa [module.validate_env_with_loop, module.validate_env_with_loop.body,
                  core.result.Result.Insts.CoreOpsTry.branch] using ht) rfl
              obtain ⟨nm, hname, hbefore, hend, hlen⟩ := hc
              refine ⟨.custom chunk :: events, ?_, .custom ?_ htrace⟩
              · simpa [hrecords v chunk v1 hv, List.append_assoc] using hlog
              · exact ⟨first, nm, by simpa [hcustom, module.SECTION_CUSTOM] using hp,
                  hname, hbefore, hend, hlen⟩
        · simp only [hcustom, ↓reduceIte] at h
          by_cases hcode : id = module.SECTION_CODE
          · simp [hcode] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact ⟨[], by simp, .done _ hpos⟩
          · simp only [hcode, ↓reduceIte] at h
            by_cases hdata : id = module.SECTION_DATA
            · simp [hdata] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact ⟨[], by simp, .done _ hpos⟩
            · simp only [hdata, ↓reduceIte] at h
              obtain ⟨ordered, hord, hrank⟩ := WP.spec_imp_exists (module.section_order.spec id)
              rw [hord] at h
              cases ordered with
              | Err e =>
                simp [core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
              | Ok rank =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at h
                by_cases horder : rank.val ≤ lastId.val
                · simp [horder] at h
                · simp only [horder, ↓reduceIte, Std.bind_assoc] at h
                  obtain ⟨⟨read, updated⟩, _, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
                  cases read with
                  | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at ht
                  | Ok consumed =>
                    simp at ht
                    by_cases he : consumed = last
                    · simp only [he, ↓reduceIte] at ht
                      obtain ⟨events, hlog, htrace⟩ := ih (data.length - last.val) hmeasure v updated last rank hspan.2.2
                        (by simpa [module.validate_env_with_loop, module.validate_env_with_loop.body,
                          core.result.Result.Insts.CoreOpsTry.branch] using ht) rfl
                      have hid : id ≠ 0#u8 := by simpa [module.SECTION_CUSTOM] using hcustom
                      have h10 : id.val ≠ 10 := fun hv => hcode
                        (UScalar.eq_of_val_eq (by simpa [module.SECTION_CODE] using hv))
                      have h11 : id.val ≠ 11 := fun hv => hdata
                        (UScalar.eq_of_val_eq (by simpa [module.SECTION_DATA] using hv))
                      exact ⟨events, hlog, .ordinary (by omega) hid hp htrace⟩
                    · have hne : consumed.val ≠ last.val := fun h => he (UScalar.eq_of_val_eq h)
                      simp [hne] at ht

/-- Accepted public environment parsing has an exact custom callback stream
from the checked magic/version header to its first code/data boundary. -/
theorem module.validate_env_with.accepted_trace {V : Type}
    (visitor : module.ModuleVisitor V) (observe : V → List Event)
    (hrecords : RecordsCustom visitor observe) (data : Slice U8)
    (v : V) (result : module.Env) (next : Usize) (v' : V)
    (h : module.validate_env_with visitor data profile v = .ok (.Ok (result, next), v')) :
    ∃ events, observe v' = observe v ++ events ∧ EnvTrace data next events := by
  unfold module.validate_env_with at h
  obtain ⟨initial, _, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.read_header.spec data)
  rw [hr] at ht
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at ht
  | Ok start =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at ht
    obtain ⟨events, hlog, htrace⟩ := module.validate_env_with_loop.accepted_trace visitor observe hrecords data
      v initial start 0#u8 result next v' hp.bound ht
    exact ⟨events, hlog, start, hp, htrace⟩

/-- Custom callbacks in the tail are separated by the exact intervening data
section, and the successful walk reaches the input's end. -/
theorem module.validate_tail_with_loop.accepted_trace {V : Type}
    (visitor : module.ModuleVisitor V) (observe : V → List Event)
    (hrecords : RecordsCustom visitor observe) (data : Slice U8) (env : module.Env)
    (v : V) (segments : alloc.vec.Vec module.Data) (pos : Usize) (seen : Bool)
    (result : module.Tail) (v' : V) (hpos : pos.val ≤ data.length)
    (h : module.validate_tail_with_loop visitor data env profile v segments pos seen = .ok (.Ok result, v')) :
    ∃ events, observe v' = observe v ++ events ∧ TailTrace data pos events := by
  generalize hn : data.length - pos.val = n
  induction n using Nat.strong_induction_on generalizing v segments pos seen with
  | h n ih =>
    unfold module.validate_tail_with_loop at h
    rw [loop] at h
    simp only [module.validate_tail_with_loop.body] at h
    by_cases hstop : pos ≥ Slice.len data
    · simp only [hstop, ↓reduceIte] at h
      have hv : v' = v := by
        cases hc : env.data_count with
        | none =>
          simp [hc] at h
          exact h.2.symm
        | some count =>
          simp only [hc, Std.bind_assoc] at h
          obtain ⟨size, _, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
          by_cases he : size.val = segments.val.length
          · simp [he] at ht
            exact ht.2.symm
          · simp [he] at ht
      subst v'
      have he : pos = Slice.len data := UScalar.eq_of_val_eq (by scalar_tac)
      exact ⟨[], by simp, by simpa only [he, TailTrace] using SectionTrace.done (data := data) (allowed := fun id => id = 11#u8) pos hpos⟩
    · simp only [hstop, ↓reduceIte] at h
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.read_section_header.spec data pos)
      rw [hr] at h
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok triple =>
        obtain ⟨id, first, last⟩ := triple
        have hspan := hp.span
        have hmeasure : data.length - last.val < n := by scalar_tac
        simp [core.result.Result.Insts.CoreOpsTry.branch] at h
        by_cases hcustom : id = module.SECTION_CUSTOM
        · simp only [hcustom, ↓reduceIte] at h
          obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (module.decode_custom_section.spec data first last)
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
              obtain ⟨events, hlog, htrace⟩ := ih (data.length - last.val) hmeasure v1 segments last seen hspan.2.2
                (by simpa [module.validate_tail_with_loop, module.validate_tail_with_loop.body,
                  core.result.Result.Insts.CoreOpsTry.branch] using ht) rfl
              obtain ⟨nm, hname, hbefore, hend, hlen⟩ := hc
              refine ⟨.custom chunk :: events, ?_, .custom ?_ htrace⟩
              · simpa [hrecords v chunk v1 hv, List.append_assoc] using hlog
              · exact ⟨first, nm, by simpa [hcustom, module.SECTION_CUSTOM] using hp,
                  hname, hbefore, hend, hlen⟩
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
                  obtain ⟨events, hlog, htrace⟩ := ih (data.length - last.val) hmeasure v decoded last true hspan.2.2
                    (by simpa [module.validate_tail_with_loop, module.validate_tail_with_loop.body,
                      core.result.Result.Insts.CoreOpsTry.branch] using ht) rfl
                  have hid : id = 11#u8 := UScalar.eq_of_val_eq (by simpa [module.SECTION_DATA] using hdata)
                  exact ⟨events, hlog, .ordinary hid (by simp [hid]) hp htrace⟩
                · simp [he] at ht
          · simp [hdata] at h

/-- Exact accepted custom callbacks for the public tail API. The bound excludes
the API's deliberate immediate-success behavior for an out-of-range start. -/
theorem module.validate_tail_with.accepted_trace {V : Type}
    (visitor : module.ModuleVisitor V) (observe : V → List Event)
    (hrecords : RecordsCustom visitor observe) (data : Slice U8) (pos : Usize) (env : module.Env)
    (v : V) (result : module.Tail) (v' : V) (hpos : pos.val ≤ data.length)
    (h : module.validate_tail_with visitor data pos env profile v = .ok (.Ok result, v')) :
    ∃ events, observe v' = observe v ++ events ∧ TailTrace data pos events :=
  module.validate_tail_with_loop.accepted_trace visitor observe hrecords data env v (alloc.vec.Vec.new _)
    pos false result v' hpos h

end Itasca
