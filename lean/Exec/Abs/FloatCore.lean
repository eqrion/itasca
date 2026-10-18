import Exec.Abs.Core
import Exec.Abs.Float.Decode
namespace Exec.Abs

/-- Isolated source grammar for scalar float instructions inside the mutable
core. Its inclusion constructors assert syntax, not execution correctness. -/
inductive FloatCoreInstr : instr → Prop where
  | core {instruction} : CoreInstr instruction → FloatCoreInstr instruction
  | scalar (op : Float.Instruction) : FloatCoreInstr op.source
  | block (ty : blocktype) (body : List instr) :
      Forall FloatCoreInstr body → FloatCoreInstr (.BLOCK ty body)
  | loop (ty : blocktype) (body : List instr) :
      Forall FloatCoreInstr body → FloatCoreInstr (.LOOP ty body)
  | ifelse (ty : blocktype) (yes no : List instr) :
      Forall FloatCoreInstr yes → Forall FloatCoreInstr no → FloatCoreInstr (.IFELSE ty yes no)

theorem FloatCoreInstr.block_body {ty body} (covered : FloatCoreInstr (.BLOCK ty body)) :
    Forall FloatCoreInstr body := by
  generalize equal : instr.BLOCK ty body = instruction at covered
  cases covered with
  | core h => rw [← equal] at h; exact fun i member => .core (h.block_body i member)
  | scalar op =>
    have impossible := congrArg Float.decodeInstruction equal
    rw [Float.decodeInstruction_source] at impossible
    contradiction
  | block _ _ body => cases equal; exact body
  | loop => cases equal
  | ifelse => cases equal

theorem FloatCoreInstr.loop_body {ty body} (covered : FloatCoreInstr (.LOOP ty body)) :
    Forall FloatCoreInstr body := by
  generalize equal : instr.LOOP ty body = instruction at covered
  cases covered with
  | core h => rw [← equal] at h; exact fun i member => .core (h.loop_body i member)
  | scalar op =>
    have impossible := congrArg Float.decodeInstruction equal
    rw [Float.decodeInstruction_source] at impossible
    contradiction
  | block => cases equal
  | loop _ _ body => cases equal; exact body
  | ifelse => cases equal

theorem FloatCoreInstr.if_bodies {ty yes no} (covered : FloatCoreInstr (.IFELSE ty yes no)) :
    Forall FloatCoreInstr yes ∧ Forall FloatCoreInstr no := by
  generalize equal : instr.IFELSE ty yes no = instruction at covered
  cases covered with
  | core h => rw [← equal] at h; exact ⟨fun i member => .core (h.if_bodies.1 i member),fun i member => .core (h.if_bodies.2 i member)⟩
  | scalar op =>
    have impossible := congrArg Float.decodeInstruction equal
    rw [Float.decodeInstruction_source] at impossible
    contradiction
  | block => cases equal
  | loop => cases equal
  | ifelse _ _ _ yes no => cases equal; exact ⟨yes,no⟩
end Exec.Abs
