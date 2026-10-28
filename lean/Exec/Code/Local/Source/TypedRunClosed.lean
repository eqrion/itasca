import Exec.Code.Local.Source.TypedStepsWasm2
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

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
end Itasca.Runtime.Code
