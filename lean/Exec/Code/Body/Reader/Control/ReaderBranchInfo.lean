import Exec.Code.Body.Reader.Calls.ReaderWasm2Call
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2
set_option maxHeartbeats 2000000

/-- Branch stack processing cannot change the label metadata produced by its actual reader. -/
theorem reader_branch_info_label (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (conditional : Bool) (depth : U32) (view : signature.ResultType)
    (out : code.BodyState)
    (accepted : code.branch_info st data env conditional = .ok (.Ok (depth, view), out)) :
    ∃ middle, code.read_label_info st data = .ok (.Ok (depth, view), middle) := by
  unfold code.branch_info at accepted
  obtain ⟨⟨result, middle⟩, read, accepted⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
  simp only [Std.uncurry] at accepted
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨selected, label⟩ := pair
    have same : selected = depth ∧ label = view := by
      cases conditional <;> simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        Bool.false_eq_true, ↓reduceIte] at accepted
      all_goals
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
    exact ⟨middle, read⟩

/-- A successful branch's actual callback depth selects exactly its reported label view. -/
theorem reader_branch_info_selected (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (conditional : Bool) (depth : U32) (view : signature.ResultType)
    (out : code.BodyState)
    (aligned : st.blocks.val.length = st.core.ctrls.val.length)
    (accepted : code.branch_info st data env conditional = .ok (.Ok (depth, view), out)) :
    labelAt st depth.val = some view := by
  obtain ⟨middle, read⟩ := reader_branch_info_label st data env conditional depth view out accepted
  have erased : code.read_multi_value_label st data = .ok (.Ok view, middle) := by
    simp [code.read_multi_value_label, read, core.result.Result.Insts.CoreOpsTry.branch]
  have effect := code.read_multi_value_label.spec st data aligned
  rw [erased, WP.spec_ok] at effect
  obtain ⟨_, _, _, _, post⟩ := effect
  obtain ⟨selected, decoded, label⟩ := post view rfl
  dsimp only at decoded label
  have bytes := code.read_label_info.bytes st data aligned
  rw [read, WP.spec_ok] at bytes
  obtain ⟨rfl, _⟩ := Leb128.Decoded.deterministic data st.core.pos depth selected middle.core.pos middle.core.pos
    (bytes.2.2 depth view rfl) decoded
  exact label
end Itasca.Runtime.Code
