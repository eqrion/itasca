import Exec.Code.Local.Source.TypedStepsWasm1
import Exec.Code.Local.Source.TypedStepsWasm2
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Once the root END closes the canonical control stack, an accepted typed
run contains no more callbacks and its cursor must be the end of the body. -/
theorem TypedRunWasm1.closed {V : Type} {visitor : code.OpVisitor V}
    {data env ctx bt st before after}
    (run : TypedRunWasm1 visitor data env ctx bt st before after)
    (closed : st.ctrls.val = []) : after = before ∧ st.pos = Slice.len data := by
  cases run with
  | done typed empty finished => exact ⟨rfl, finished⟩
  | step typed pending start advance called rest =>
    obtain ⟨_, _, _, _, _, _, controls, _⟩ := pending.opened
    simp only at controls
    rw [closed] at controls
    simp at controls

theorem TypedRunWasm2.closed {V : Type} {visitor : code.OpVisitor V}
    {data env ctx index st before after}
    (run : TypedRunWasm2 visitor data env ctx index st before after)
    (closed : st.blocks.val = []) : after = before ∧ st.core.pos = Slice.len data := by
  cases run with
  | done typed empty finished => exact ⟨rfl, finished⟩
  | step typed pending start advance called rest =>
    obtain ⟨_, _, _, _, _, _, _, blocks, _⟩ := pending.opened
    simp only [code.BodyState.blocks] at closed blocks
    rw [closed] at blocks
    simp at blocks
end Exec.Code
