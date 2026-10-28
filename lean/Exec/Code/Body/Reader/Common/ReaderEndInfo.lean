import Exec.Code.Body.Reader.Common.ReaderEnterWasm2
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2
set_option maxHeartbeats 2000000
/-- Successful END/ELSE metadata belongs to the frame actually removed or switched. -/
theorem reader_end_info_metadata (st : code.BodyState) (env : module.Env) (isElse : Bool)
    (parents : List code.Ctrl) (frame : code.Ctrl)
    (controls : st.core.ctrls.val = parents ++ [frame])
    (kind : code.LabelKind) (bt : signature.BlockType) (out : code.BodyState)
    (accepted : code.end_frame_info st env isElse = .ok (.Ok (kind, bt), out)) :
    kind = frame.kind ∧ bt = frame.signature := by
  have nonempty : alloc.vec.Vec.len st.core.ctrls ≠ 0#usize := by
    intro empty
    have := congrArg UScalar.val empty
    simp [controls] at this
  obtain ⟨index, indexEq, indexVal⟩ := WP.spec_imp_exists
    (UScalar.sub_spec (x := alloc.vec.Vec.len st.core.ctrls) (y := 1#usize) (by simp [controls]))
  have indexVal' : index.val = parents.length := by simp [controls] at indexVal; omega
  have bound : index.val < st.core.ctrls.val.length := by simp [indexVal', controls]
  obtain ⟨actual, lookup, actualEq⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec st.core.ctrls index bound)
  have same : actual = frame := by simpa [controls, indexVal'] using actualEq
  subst actual
  have indexed : st.core.ctrls.val[index.val] = frame := same
  simp only [code.end_frame_info, nonempty, ↓reduceIte, indexEq, bind_ok,
    alloc.vec.Vec.index_slice_index, lookup, indexed] at accepted
  cases isElse <;> cases kindEq : frame.kind <;>
    simp only [Bool.false_eq_true, ↓reduceIte, kindEq] at accepted
  all_goals
    repeat' first
      | (solve | simp at accepted | simpa [kindEq] using accepted)
      | (split at accepted <;> try simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          Std.uncurry, bind_ok] at accepted)
      | (obtain ⟨value, equation, accepted⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
         try simp only [core.result.Result.Insts.CoreOpsTry.branch,
           core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
           Std.uncurry, bind_ok] at accepted)
  all_goals simp_all
end Itasca.Runtime.Code
