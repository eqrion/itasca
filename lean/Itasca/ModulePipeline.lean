import Itasca.Generated.Funs

open Aeneas Aeneas.Std

namespace Itasca.ModulePipeline

private theorem bind_ok_inv {A B : Type} (read : Result A) (next : A → Result B)
    (b : B) (h : (read >>= next) = .ok b) :
    ∃ a, read = .ok a ∧ next a = .ok b := by
  induction read using Result.cases with
  | ret a => exact ⟨a, rfl, by simpa using h⟩
  | vis e k => simp at h
  | div => simp at h

/-- The public entry point exposes the same environment, code, and tail runs.
This is a composition lemma; typing and binary provenance come from the
separate decoder theorems, not from this statement alone. -/
theorem accepted_parts (data : Slice U8) (decoded : module.Module)
    (h : module.validate_module data = .ok (.Ok decoded)) :
    data.length ≤ limits.MAX_MODULE_BYTES.val ∧
    ∃ codePos tailPos,
      module.validate_env data = .ok (.Ok (decoded.env, codePos)) ∧
      module.validate_code data codePos decoded.env = .ok (.Ok tailPos) ∧
      module.validate_tail data tailPos decoded.env = .ok (.Ok decoded.tail) := by
  unfold module.validate_module at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i hsize
    obtain ⟨envResult, henv, h⟩ := bind_ok_inv _ _ _ h
    cases envResult with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok pair =>
      rcases pair with ⟨env, codePos⟩
      simp [core.result.Result.Insts.CoreOpsTry.branch] at h
      obtain ⟨codeResult, hcode, h⟩ := bind_ok_inv _ _ _ h
      cases codeResult with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok tailPos =>
        simp [core.result.Result.Insts.CoreOpsTry.branch] at h
        obtain ⟨tailResult, htail, h⟩ := bind_ok_inv _ _ _ h
        cases tailResult with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
        | Ok tail =>
          have he : ({ env := env, tail := tail } : module.Module) = decoded := by
            simpa [core.result.Result.Insts.CoreOpsTry.branch] using h
          subst decoded
          exact ⟨by scalar_tac, codePos, tailPos, henv, hcode, htail⟩

theorem accepted_of_parts (data : Slice U8) (env : module.Env) (tail : module.Tail)
    (codePos tailPos : Usize) (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : module.validate_env data = .ok (.Ok (env, codePos)))
    (hcode : module.validate_code data codePos env = .ok (.Ok tailPos))
    (htail : module.validate_tail data tailPos env = .ok (.Ok tail)) :
    module.validate_module data = .ok (.Ok ⟨env, tail⟩) := by
  have hs : ¬ Slice.len data > limits.MAX_MODULE_BYTES := by scalar_tac
  simp [module.validate_module, hs, henv, hcode, htail,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- Successful visiting composition retains both intermediate visitor states.
No hook-termination or hook-validation premise is needed to expose the calls. -/
theorem accepted_parts_with {V : Type} (mv : module.ModuleVisitor V)
    (cv : module.CodeVisitor V) (data : Slice U8) (v v' : V) (decoded : module.Module)
    (h : module.validate_module_with mv cv data v = .ok (.Ok decoded, v')) :
    data.length ≤ limits.MAX_MODULE_BYTES.val ∧
    ∃ codePos tailPos v1 v2,
      module.validate_env_with mv data v = .ok (.Ok (decoded.env, codePos), v1) ∧
      module.validate_code_with cv data codePos decoded.env v1 = .ok (.Ok tailPos, v2) ∧
      module.validate_tail_with mv data tailPos decoded.env v2 = .ok (.Ok decoded.tail, v') := by
  unfold module.validate_module_with at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i hsize
    obtain ⟨⟨envResult, v1⟩, henv, h⟩ := bind_ok_inv _ _ _ h
    try dsimp only at h
    cases envResult with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok pair =>
      rcases pair with ⟨env, codePos⟩
      simp [core.result.Result.Insts.CoreOpsTry.branch] at h
      obtain ⟨⟨codeResult, v2⟩, hcode, h⟩ := bind_ok_inv _ _ _ h
      try dsimp only at h
      cases codeResult with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok tailPos =>
        simp [core.result.Result.Insts.CoreOpsTry.branch] at h
        obtain ⟨⟨tailResult, v3⟩, htail, h⟩ := bind_ok_inv _ _ _ h
        try dsimp only at h
        cases tailResult with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
        | Ok tail =>
          have he : ({ env := env, tail := tail } : module.Module) = decoded ∧ v3 = v' := by
            simpa [core.result.Result.Insts.CoreOpsTry.branch] using h
          rcases he with ⟨rfl, rfl⟩
          exact ⟨by scalar_tac, codePos, tailPos, v1, v2, henv, hcode, htail⟩

theorem accepted_of_parts_with {V : Type} (mv : module.ModuleVisitor V)
    (cv : module.CodeVisitor V) (data : Slice U8) (env : module.Env) (tail : module.Tail)
    (codePos tailPos : Usize) (v v1 v2 v3 : V)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : module.validate_env_with mv data v = .ok (.Ok (env, codePos), v1))
    (hcode : module.validate_code_with cv data codePos env v1 = .ok (.Ok tailPos, v2))
    (htail : module.validate_tail_with mv data tailPos env v2 = .ok (.Ok tail, v3)) :
    module.validate_module_with mv cv data v = .ok (.Ok ⟨env, tail⟩, v3) := by
  have hs : ¬ Slice.len data > limits.MAX_MODULE_BYTES := by scalar_tac
  simp [module.validate_module_with, hs, henv, hcode, htail,
    core.result.Result.Insts.CoreOpsTry.branch]

end Itasca.ModulePipeline
