import Exec.Code.Body.Relations.Common.KnownEntryStack
import Exec.Code.Body.Reader.Common.ReaderEnterWasm1
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Wasm 1 IF pops its condition but never introduces an unknown operand;
this also holds in a polymorphic segment that will not emit bytecode. -/
@[step] theorem read_if_known (st : code.OpIterState) (data : Slice U8)
    (outer segment : List code.StackType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length) (known : ConcreteStack st.vals.val)
    (capacity : st.ctrls.val.length < Usize.max) :
    code.read_if st data ⦃ out => ∀ bt, out.1 = .Ok bt → ConcreteStack out.2.vals.val ⦄ := by
  have both := concreteStack_append.mp (values ▸ known)
  unfold code.read_if
  step with code.read_block_type.raw_spec data st.pos as ⟨result, decoded⟩
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨bt, next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with pop_with_type_concrete {st with pos := next} outer segment .I32 values base both.2
      as ⟨reply, middle, controls, position, rest, afterValues, restKnown⟩
    cases reply with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with code.push_ctrl.spec middle .Then bt (by simpa [controls] using capacity)
        as ⟨after, frames, operands, cursor⟩
      intro _ _
      rw [operands, afterValues]
      exact concreteStack_append.mpr ⟨both.1, restKnown⟩

theorem reader_if_known_wasm1 {data env ctx bodyBt st out bt}
    (p : Wasm1.Pending data env ctx bodyBt st) (known : ConcreteStack st.vals.val)
    (accepted : code.read_if st data = .ok (.Ok bt, out)) : ConcreteStack out.vals.val := by
  obtain ⟨C, outer, spine, header, position, typed, controls, values⟩ := p.opened
  have base : (Control.base st).val = outer.length := by simp [Control.base, controls, position]
  have effect := read_if_known st data outer p.current.vals values base known p.ctrl_capacity
  rw [accepted, WP.spec_ok] at effect
  exact effect bt rfl

end Exec.Code
