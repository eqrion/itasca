import Exec.Code.Body.Reader.Control.ReaderBranchWasm1
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxHeartbeats 2000000

/-- The Wasm 1 branch callback reports the depth and target read from the actual control stack. -/
theorem reader_branch_label_wasm1 (st out : code.OpIterState) (data : Slice U8)
    (conditional : Bool) (depth : U32) (bt : code.BlockType)
    (accepted : (if conditional then code.read_br_if st data else code.read_br st data) =
      .ok (.Ok (depth, bt), out)) :
    ∃ middle target, code.read_label st data = .ok (.Ok (depth, target), middle) ∧
      bt = Control.targetBlockType target := by
  cases conditional <;> simp only [Bool.false_eq_true, ↓reduceIte, code.read_br, code.read_br_if] at accepted
  all_goals
    obtain ⟨⟨result, middle⟩, read, accepted⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
    simp only [Std.uncurry] at accepted
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
    | Ok pair =>
      obtain ⟨selected, target⟩ := pair
      have same : selected = depth ∧ Control.targetBlockType target = bt := by
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, code.branch_target_bt.eq] at accepted
        repeat' first
          | (solve | simp at accepted | simpa using accepted)
          | (split at accepted <;> try simp only [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              Std.uncurry, bind_ok] at accepted)
          | (obtain ⟨value, equation, accepted⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
             try simp only [core.result.Result.Insts.CoreOpsTry.branch,
               core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
               Std.uncurry, bind_ok] at accepted)
        all_goals simp_all
      obtain ⟨rfl, rfl⟩ := same
      exact ⟨middle, target, read, rfl⟩
end Exec.Code
