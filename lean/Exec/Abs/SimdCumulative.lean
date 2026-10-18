import Exec.Abs.Cumulative
import Exec.Abs.Simd.Source

namespace Exec.Abs

/-- Supported source syntax with SIMD, retaining the existing cumulative
instruction family and allowing mixed nested bodies. -/
inductive SimdCumulativeInstr : instr → Prop where
  | cumulative {source} : CumulativeInstr source → SimdCumulativeInstr source
  | simd {source} : SimdInstr source → SimdCumulativeInstr source
  | block (type : blocktype) (body : List instr) :
      Forall SimdCumulativeInstr body → SimdCumulativeInstr (.BLOCK type body)
  | loop (type : blocktype) (body : List instr) :
      Forall SimdCumulativeInstr body → SimdCumulativeInstr (.LOOP type body)
  | ifelse (type : blocktype) (yes no : List instr) :
      Forall SimdCumulativeInstr yes → Forall SimdCumulativeInstr no → SimdCumulativeInstr (.IFELSE type yes no)

theorem SimdCumulativeInstr.block_body {type body} (allowed : SimdCumulativeInstr (.BLOCK type body)) :
    Forall SimdCumulativeInstr body := by
  cases allowed with
  | cumulative old => exact fun i member => .cumulative (old.block_body i member)
  | simd impossible => exact False.elim (SimdInstr.not_block impossible)
  | block _ _ body => exact body

theorem SimdCumulativeInstr.loop_body {type body} (allowed : SimdCumulativeInstr (.LOOP type body)) :
    Forall SimdCumulativeInstr body := by
  cases allowed with
  | cumulative old => exact fun i member => .cumulative (old.loop_body i member)
  | simd impossible => exact False.elim (SimdInstr.not_loop impossible)
  | loop _ _ body => exact body

theorem SimdCumulativeInstr.if_bodies {type yes no} (allowed : SimdCumulativeInstr (.IFELSE type yes no)) :
    Forall SimdCumulativeInstr yes ∧ Forall SimdCumulativeInstr no := by
  cases allowed with
  | cumulative old => exact ⟨fun i member => .cumulative (old.if_bodies.1 i member),
      fun i member => .cumulative (old.if_bodies.2 i member)⟩
  | simd impossible => exact False.elim (SimdInstr.not_if impossible)
  | ifelse _ _ _ yes no => exact ⟨yes,no⟩

end Exec.Abs
