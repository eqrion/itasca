import Exec.Abs.SimdCumulativeState
import Exec.Abs.Supported.Language
namespace Exec.Abs

/-- SIMD heads are handled by their relational semantics and cannot silently
    take a deterministic scalar Core step. -/
theorem SimdInstr.core_stuck {op : instr} (supported : SimdInstr op)
    (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame) (after : List instr) :
    Core.instruction s ambient f rest op after = .stuck := by
  cases supported with
  | pure signature => cases signature <;> rfl
  | constant => rfl
  | memory signature => cases signature <;> rfl

theorem simd_cumulative_language : Supported.Language SimdCumulativeInstr where
  cumulative := .cumulative
  block := .block
  loop := .loop
  block_body := SimdCumulativeInstr.block_body
  loop_body := SimdCumulativeInstr.loop_body
  if_bodies := SimdCumulativeInstr.if_bodies
  head allowed := by
    cases allowed with
    | cumulative old => exact .cumulative old
    | simd supported => exact .external supported.core_stuck
    | block ty body _ => exact .block ty body
    | loop ty body _ => exact .loop ty body
    | ifelse ty yes no _ _ => exact .ifelse ty yes no
end Exec.Abs
