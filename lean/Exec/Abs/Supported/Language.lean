import Exec.Abs.Core.Step
import Exec.Abs.Cumulative
import Exec.Abs.SupportedState

namespace Exec.Abs.Supported

/-- Classification of a source head for the deterministic core. Structured
bodies may contain instructions handled by other transition relations. -/
inductive CoreHead : instr → Prop where
  | cumulative {op} : CumulativeInstr op → CoreHead op
  | block (ty : blocktype) (body : List instr) : CoreHead (.BLOCK ty body)
  | loop (ty : blocktype) (body : List instr) : CoreHead (.LOOP ty body)
  | ifelse (ty : blocktype) (yes no : List instr) : CoreHead (.IFELSE ty yes no)
  | external {op} : (∀ s ambient f rest after, Core.instruction s ambient f rest op after = .stuck) → CoreHead op

/-- Syntactic closure requirements used by source support preservation. -/
structure Language (allowed : instr → Prop) : Prop where
  cumulative : ∀ {op}, CumulativeInstr op → allowed op
  block : ∀ ty body, Forall allowed body → allowed (.BLOCK ty body)
  loop : ∀ ty body, Forall allowed body → allowed (.LOOP ty body)
  block_body : ∀ {ty body}, allowed (.BLOCK ty body) → Forall allowed body
  loop_body : ∀ {ty body}, allowed (.LOOP ty body) → Forall allowed body
  if_bodies : ∀ {ty yes no}, allowed (.IFELSE ty yes no) → Forall allowed yes ∧ Forall allowed no
  head : ∀ {op}, allowed op → CoreHead op

end Exec.Abs.Supported
