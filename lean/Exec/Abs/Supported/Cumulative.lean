import Exec.Abs.CumulativeState
import Exec.Abs.Supported.Language
namespace Exec.Abs

theorem cumulative_language : Supported.Language CumulativeInstr where
  cumulative := id
  block := .block
  loop := .loop
  block_body := CumulativeInstr.block_body
  loop_body := CumulativeInstr.loop_body
  if_bodies := CumulativeInstr.if_bodies
  head := .cumulative

theorem CumulativeState.supported {s : AState} (covered : CumulativeState s) :
    SupportedState CumulativeInstr s := ⟨covered.active,covered.functions⟩

theorem SupportedState.cumulative {s : AState} (covered : SupportedState CumulativeInstr s) :
    CumulativeState s := ⟨covered.active,covered.functions⟩
theorem supported_cumulative_eq : SupportedState CumulativeInstr = CumulativeState := by
  funext s
  exact propext ⟨SupportedState.cumulative,CumulativeState.supported⟩
end Exec.Abs
