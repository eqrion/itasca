import Itasca.Support.Result
import Itasca.Module.Code.Entry
import Itasca.Wasm1.Visitor.Lift

open Aeneas Aeneas.Std

namespace Itasca

/-- Successful entry validation transfers to any always-accepting operator
visitor, including the function-start callback before the body. No environment,
size, syntax, or termination premise is imposed on the source visitor. -/
theorem module.validate_code_entry_with.accepted_transfer {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (haccept : FullVisitor.Accepts replacement)
    (data : Slice U8) (pos : Usize) (env : module.Env) (index finish : Usize)
    (v v' : V) (w : W)
    (h : module.validate_code_entry_with visitor data pos env index .Wasm1 v = .ok (.Ok finish, v')) :
    ∃ w', module.validate_code_entry_with replacement data pos env index .Wasm1 w = .ok (.Ok finish, w') := by
  unfold module.validate_code_entry_with at h ⊢
  try dsimp only at h ⊢
  by_cases hi : index ≥ alloc.vec.Vec.len env.func_type_indices
  · simp [hi] at h
  rw [if_neg hi] at h ⊢
  obtain ⟨r, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  rw [hr]
  simp at h ⊢
  try dsimp only at h ⊢
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from] at h
  | Ok pair =>
    obtain ⟨size, p⟩ := pair
    simp [core.result.Result.Insts.CoreOpsTry.branch] at h ⊢
    obtain ⟨n, hn, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    rw [hn]
    simp at h ⊢
    obtain ⟨r, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    rw [hr]
    simp at h ⊢
    cases r with
    | Err e =>
      simp [
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok u =>
      cases u
      simp at h ⊢
      obtain ⟨last, hlast, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      rw [hlast]
      simp at h ⊢
      obtain ⟨r, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      rw [hr]
      simp at h ⊢
      cases r with
      | Err e =>
        simp [
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok pair =>
        obtain ⟨declared, first⟩ := pair
        simp at h ⊢
        by_cases hf : first.val > last.val
        · simp [hf] at h
        rw [if_neg hf] at h ⊢
        obtain ⟨typeidx, htypeidx, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
        rw [htypeidx]
        simp at h ⊢
        obtain ⟨t, ht, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
        rw [ht]
        simp at h ⊢
        by_cases hti : t.val ≥ env.types.val.length
        · simp [hti] at h
        rw [if_neg hti] at h ⊢
        obtain ⟨ft, hft, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
        rw [hft]
        simp at h ⊢
        obtain ⟨locals, hlocals, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
        rw [hlocals]
        simp at h ⊢
        obtain ⟨results, hresults, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
        rw [hresults]
        simp at h ⊢
        obtain ⟨⟨reply, started⟩, hstart, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
        cases reply with
        | Err e => simp at h
        | Ok u =>
          cases u
          obtain ⟨started', hstart'⟩ := haccept.on_function_start w ⟨locals, results⟩ typeidx first last
          rw [hstart']
          simp at h ⊢
          obtain ⟨body, hbody, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
          rw [hbody]
          simp at h ⊢
          obtain ⟨⟨reply, ended⟩, hrun, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
          cases reply with
          | Err e => simp at h
          | Ok u =>
            cases u
            have he : last = finish ∧ ended = v' := by simpa using h
            obtain ⟨ended', hrun'⟩ := code.validate_body_with.accepted_lift replacement haccept
              body env ⟨locals, results⟩ started'
              (code.validate_body_with.accepted_erase visitor body env ⟨locals, results⟩ started ended hrun)
            exact ⟨ended', by simp [hrun', he.1]⟩

/-- A compiler's accepted visiting entry certifies the default entry validator,
without requiring its other callback runs to terminate. -/
theorem module.validate_code_entry_with.accepted_erase {V : Type}
    (visitor : code.OpVisitor V) (data : Slice U8) (pos : Usize) (env : module.Env)
    (index finish : Usize) (v v' : V)
    (h : module.validate_code_entry_with visitor data pos env index .Wasm1 v = .ok (.Ok finish, v')) :
    module.validate_code_entry data pos env index .Wasm1 = .ok (.Ok finish) := by
  obtain ⟨w, hw⟩ := module.validate_code_entry_with.accepted_transfer visitor
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts data pos env index finish v v' () h
  simp [module.validate_code_entry, hw]

/-- Accepting callbacks preserve every successful default entry validation. -/
theorem module.validate_code_entry_with.accepted_lift {V : Type}
    (visitor : code.OpVisitor V) (haccept : FullVisitor.Accepts visitor)
    (data : Slice U8) (pos : Usize) (env : module.Env) (index finish : Usize) (v : V)
    (h : module.validate_code_entry data pos env index .Wasm1 = .ok (.Ok finish)) :
    ∃ v', module.validate_code_entry_with visitor data pos env index .Wasm1 v = .ok (.Ok finish, v') := by
  unfold module.validate_code_entry at h
  obtain ⟨⟨r, w⟩, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  have he : r = .Ok finish := by simpa using h
  rw [he] at hr
  exact module.validate_code_entry_with.accepted_transfer
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor visitor haccept data pos env index finish () () v hr

theorem module.validate_code_entry_with.accepted_iff {V : Type}
    (visitor : code.OpVisitor V) (haccept : FullVisitor.Accepts visitor)
    (data : Slice U8) (pos : Usize) (env : module.Env) (index finish : Usize) (v : V) :
    (∃ v', module.validate_code_entry_with visitor data pos env index .Wasm1 v = .ok (.Ok finish, v')) ↔
      module.validate_code_entry data pos env index .Wasm1 = .ok (.Ok finish) := by
  constructor
  · rintro ⟨v', h⟩
    exact module.validate_code_entry_with.accepted_erase visitor data pos env index finish v v' h
  · exact module.validate_code_entry_with.accepted_lift visitor haccept data pos env index finish v

/-- Accepted visiting entries carry the same independent binary and Wasm 1.0
body certificate as default entries, without a visitor-totality premise. -/
theorem module.validate_code_entry_with.wasm_sound {V : Type}
    (visitor : code.OpVisitor V) (data : Slice U8) (pos : Usize) (env : module.Env)
    (index finish : Usize) (v v' : V) (hbound : CodeEntry.Bounds env)
    (hresults : ∀ ft ∈ env.types.val, ft.results.val.length ≤ 1)
    (h : module.validate_code_entry_with visitor data pos env index .Wasm1 v = .ok (.Ok finish, v')) :
    CodeEntry.Validated data env index pos finish := by
  have he := module.validate_code_entry_with.accepted_erase visitor data pos env index finish v v' h
  have hs := module.validate_code_entry.spec data pos env index hbound hresults
  rw [he, WP.spec_ok] at hs
  exact hs finish rfl

end Itasca
