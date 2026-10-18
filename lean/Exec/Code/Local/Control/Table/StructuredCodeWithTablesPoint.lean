import Exec.Code.Local.Control.Table.StructuredCodeWithTables
import Exec.Code.Local.Control.Common.StructuredComposition
namespace Exec.Code
open Aeneas.Std

def StructuredCodeWithTables.Targets (emission : List valtype → instr → List Bytecode → List valtype → Prop)
    (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (jumpTables : List U32) (labels : List LabelTarget) : Prop :=
  ∀ depth label, labels[depth]? = some label → label.branchLive = true →
    ∃ next after, StructuredCodeWithTables emission types functions returns locals code jumpTables (labels.drop (depth + 1))
      (label.front ++ label.branchTypes) (label.cont ++ label.after) label.target.val next after ∧
      ExitAligned (labels.drop (depth + 1)) next ∧
      RootAligned code returns (labels.drop (depth + 1)) next after

/-- Normal label exits retain their own continuation; for an IF then arm this
starts at the skip instruction rather than the branch target after the else. -/
def StructuredCodeWithTables.Normals (emission : List valtype → instr → List Bytecode → List valtype → Prop)
    (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (jumpTables : List U32) (labels : List LabelTarget) : Prop :=
  ∀ depth label, labels[depth]? = some label → label.normalLive = true →
    ∃ next after, StructuredCodeWithTables emission types functions returns locals code jumpTables (labels.drop (depth + 1))
      (label.front ++ label.resultTypes) label.after label.normalExit next after ∧
      ExitAligned (labels.drop (depth + 1)) next ∧
      RootAligned code returns (labels.drop (depth + 1)) next after

/-- Static source position, branch and fallthrough continuations, and scope
endpoint alignment. Empty source code therefore identifies a normal exit. -/
structure StructuredCodeWithTables.Point (emission : List valtype → instr → List Bytecode → List valtype → Prop)
    (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (jumpTables : List U32) (labels : List LabelTarget) (stack : List valtype)
    (source : List instr) (pc next : Nat) (after : List valtype) : Prop where
  current : StructuredCodeWithTables emission types functions returns locals code jumpTables labels stack source pc next after
  targets : StructuredCodeWithTables.Targets emission types functions returns locals code jumpTables labels
  normal : StructuredCodeWithTables.Normals emission types functions returns locals code jumpTables labels
  exit : ExitAligned labels next
  root : RootAligned code returns labels next after

theorem StructuredCodeWithTables.Targets.tail {emission types functions returns locals code jumpTables label labels}
    (targets : StructuredCodeWithTables.Targets emission types functions returns locals code jumpTables (label :: labels)) :
    StructuredCodeWithTables.Targets emission types functions returns locals code jumpTables labels := by
  intro depth target lookup live
  simpa using targets (depth + 1) target (by simpa using lookup) live

theorem StructuredCodeWithTables.Targets.drop {emission types functions returns locals code jumpTables labels}
    (targets : StructuredCodeWithTables.Targets emission types functions returns locals code jumpTables labels) (count : Nat) :
    StructuredCodeWithTables.Targets emission types functions returns locals code jumpTables (labels.drop count) := by
  intro depth label lookup live
  have original : labels[count + depth]? = some label := by simpa using lookup
  obtain ⟨next, after, relation, aligned, root⟩ := targets (count + depth) label original live
  refine ⟨next, after, ?_, ?_, ?_⟩
  · simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using relation
  · simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using aligned
  · simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using root

theorem StructuredCodeWithTables.Normals.drop {emission types functions returns locals code jumpTables labels}
    (targets : StructuredCodeWithTables.Normals emission types functions returns locals code jumpTables labels) (count : Nat) :
    StructuredCodeWithTables.Normals emission types functions returns locals code jumpTables (labels.drop count) := by
  intro depth label lookup live
  have original : labels[count + depth]? = some label := by simpa using lookup
  obtain ⟨next, after, relation, aligned, root⟩ := targets (count + depth) label original live
  refine ⟨next, after, ?_, ?_, ?_⟩
  · simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using relation
  · simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using aligned
  · simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using root

theorem StructuredCodeWithTables.pc_le_next {emission types functions returns locals code jumpTables labels stack source pc next after}
    (relation : StructuredCodeWithTables emission types functions returns locals code jumpTables labels stack source pc next after) : pc ≤ next := by
  induction relation using StructuredCodeWithTables.rec with
  | nil => omega
  | linear head ordinary fragment rest ih => exact fragment.pc_le_next.trans ih
  | skip forward instruction rest ih => omega
  | block signature bodyCode rest targetRest bounds bodyBound restBound targetBound => exact bounds.1
  | loop signature head bodyCode rest bounds bodyBound restBound => exact bounds.1
  | ifElse signature condition guard yesCode skip noCode rest bounds yesBound noBound restBound => omega
  | branch lookup live layout fragment remaining scope => exact fragment.pc_le_next.trans remaining
  | branchIf lookup live layout condition fragment rest ih => exact fragment.pc_le_next.trans ih
  | call signature arguments instruction rest ih => omega
  | unreachable instruction remaining scope => omega
  | return_ source size instruction remaining scope => omega
  | branchTable gate table bounds => omega

theorem StructuredCodeWithTables.next_le_length {emission types functions returns locals code jumpTables labels stack source pc next after}
    (relation : StructuredCodeWithTables emission types functions returns locals code jumpTables labels stack source pc next after) : next ≤ code.length := by
  induction relation using StructuredCodeWithTables.rec with
  | nil labels stack pc bound live => exact bound
  | linear _ _ _ _ ih => exact ih
  | skip _ _ _ ih => exact ih
  | block _ _ _ _ bounds _ _ _ => exact bounds.2
  | loop _ _ _ _ bounds _ _ => exact bounds.2
  | ifElse _ _ _ _ _ _ _ bounds _ _ _ => exact bounds.2.2
  | branch _ _ _ _ _ scope => exact scope
  | branchIf _ _ _ _ _ _ ih => exact ih
  | call _ _ _ _ ih => exact ih
  | unreachable _ _ scope => exact scope
  | return_ _ _ _ _ scope => exact scope
  | branchTable _ _ bounds => exact bounds.2

theorem StructuredCodeWithTables.entry_bound {emission types functions returns locals code jumpTables labels stack source pc next after}
    (relation : StructuredCodeWithTables emission types functions returns locals code jumpTables labels stack source pc next after) :
    pc ≤ code.length := relation.pc_le_next.trans relation.next_le_length


end Exec.Code
