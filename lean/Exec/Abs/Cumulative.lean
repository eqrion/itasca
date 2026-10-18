import Exec.Abs.FloatCore
import Exec.Abs.Stateful.Descriptor
namespace Exec.Abs

/-- Cumulative source grammar for references, tables and bulk operations alongside
the mutable scalar and float core. Its inclusion constructors assert syntax, not execution correctness. -/
inductive CumulativeInstr : instr → Prop where
  | core {instruction} : FloatCoreInstr instruction → CumulativeInstr instruction
  | stateful (op : Stateful.Instruction) : CumulativeInstr op.source
  | indirect_call (table : tableidx) (type : typeidx) : CumulativeInstr (.CALL_INDIRECT table type)
  | block (ty : blocktype) (body : List instr) :
      Forall CumulativeInstr body → CumulativeInstr (.BLOCK ty body)
  | loop (ty : blocktype) (body : List instr) :
      Forall CumulativeInstr body → CumulativeInstr (.LOOP ty body)
  | ifelse (ty : blocktype) (yes no : List instr) :
      Forall CumulativeInstr yes → Forall CumulativeInstr no → CumulativeInstr (.IFELSE ty yes no)

theorem CumulativeInstr.block_body {ty body} (covered : CumulativeInstr (.BLOCK ty body)) :
    Forall CumulativeInstr body := by
  generalize equal : instr.BLOCK ty body = instruction at covered
  cases covered with
  | core h => rw [← equal] at h; exact fun i member => .core (h.block_body i member)
  | stateful op =>
    have impossible := congrArg Stateful.decodeInstruction equal
    rw [Stateful.decode_source] at impossible
    contradiction
  | indirect_call => cases equal
  | block _ _ body => cases equal; exact body
  | loop => cases equal
  | ifelse => cases equal

theorem CumulativeInstr.loop_body {ty body} (covered : CumulativeInstr (.LOOP ty body)) :
    Forall CumulativeInstr body := by
  generalize equal : instr.LOOP ty body = instruction at covered
  cases covered with
  | core h => rw [← equal] at h; exact fun i member => .core (h.loop_body i member)
  | stateful op =>
    have impossible := congrArg Stateful.decodeInstruction equal
    rw [Stateful.decode_source] at impossible
    contradiction
  | indirect_call => cases equal
  | block => cases equal
  | loop _ _ body => cases equal; exact body
  | ifelse => cases equal

theorem CumulativeInstr.if_bodies {ty yes no} (covered : CumulativeInstr (.IFELSE ty yes no)) :
    Forall CumulativeInstr yes ∧ Forall CumulativeInstr no := by
  generalize equal : instr.IFELSE ty yes no = instruction at covered
  cases covered with
  | core h => rw [← equal] at h; exact ⟨fun i member => .core (h.if_bodies.1 i member),fun i member => .core (h.if_bodies.2 i member)⟩
  | stateful op =>
    have impossible := congrArg Stateful.decodeInstruction equal
    rw [Stateful.decode_source] at impossible
    contradiction
  | indirect_call => cases equal
  | block => cases equal
  | loop => cases equal
  | ifelse _ _ _ yes no => cases equal; exact ⟨yes,no⟩
end Exec.Abs
