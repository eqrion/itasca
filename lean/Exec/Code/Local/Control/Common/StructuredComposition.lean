import Exec.Code.Local.Control.Common.Structured
import Exec.Code.Local.Lowering.Common.Lowering
namespace Exec.Code
open Aeneas.Std

theorem Segment.split {code pc emitted next} (segment : Segment code pc emitted next)
    {first second} (parts : emitted = first ++ second) :
    Segment code pc first (pc + first.length) ∧
    Segment code (pc + first.length) second next := by
  obtain ⟨pre, suffix, rfl, rfl, rfl⟩ := segment
  subst emitted
  constructor
  · exact ⟨pre, second ++ suffix, by simp [List.append_assoc], rfl, rfl⟩
  · refine ⟨pre ++ first, suffix, by simp [List.append_assoc], by simp, ?_⟩
    simp [List.length_append, Nat.add_assoc]

theorem Segment.next_bound {code pc emitted next} (segment : Segment code pc emitted next) :
    next ≤ code.length := by
  obtain ⟨pre, suffix, rfl, rfl, rfl⟩ := segment
  simp

/-- Existing straight-line certificates embed without weakening slot operands
or replacing exact instruction fragments with semantic assumptions. -/
theorem LinearRel.structured {types functions returns locals code labels before source emitted after pc next}
    (relation : LinearRel locals before source emitted after)
    (segment : Segment code pc emitted next) (live : NormalLive labels) :
    CodeRel types functions returns locals code labels before source pc next after := by
  induction relation generalizing pc with
  | nil stack =>
    have same : next = pc := by obtain ⟨_, _, _, _, h⟩ := segment; simpa using h
    subst next
    exact CodeRel.nil labels stack pc segment.next_bound live
  | cons head tail ih =>
    obtain ⟨first, rest⟩ := segment.split rfl
    exact CodeRel.linear head first (ih rest)

theorem LinearCodeRel.structured {types functions returns locals code labels before source after pc next}
    (relation : LinearCodeRel locals before source code pc next after) (live : NormalLive labels) :
    CodeRel types functions returns locals code labels before source pc next after := by
  obtain ⟨pre, emitted, suffix, hc, hp, hn, relation⟩ := relation
  exact relation.structured ⟨pre, suffix, hc, hp, hn⟩ live

/-- A source prefix can precede a structured continuation; each recursive
constructor carries the intermediate static stack and actual instruction span. -/
theorem LinearRel.prepend_structured {types functions returns locals code labels before middle after
    source emitted rest pc boundary next}
    (relation : LinearRel locals before source emitted middle)
    (segment : Segment code pc emitted boundary)
    (continuation : CodeRel types functions returns locals code labels middle rest boundary next after) :
    CodeRel types functions returns locals code labels before (source ++ rest) pc next after := by
  induction relation generalizing pc with
  | nil stack =>
    have same : boundary = pc := by obtain ⟨_, _, _, _, h⟩ := segment; simpa using h
    simpa [same] using continuation
  | cons head tail ih =>
    obtain ⟨first, remaining⟩ := segment.split rfl
    exact CodeRel.linear head first (ih remaining continuation)

/-- A retained scope's logical fallthrough endpoint agrees with its top label. -/
def ExitAligned (labels : List LabelTarget) (next : Nat) : Prop :=
  ∀ label, labels.head? = some label → next = label.normalExit

/-- An outermost continuation ends immediately before the function's retained
Return epilogue and produces exactly its declared results. -/
def RootAligned (code : List Bytecode) (returns : List valtype)
    (labels : List LabelTarget) (next : Nat) (output : List valtype) : Prop :=
  labels = [] → next + 1 = code.length ∧ output = returns ∧
    ∃ src count, count.val = slots returns ∧ code[next]? = some (.Return src count)

theorem RootAligned.cons (code : List Bytecode) (returns : List valtype)
    (label : LabelTarget) (labels : List LabelTarget) (next : Nat) (output : List valtype) :
    RootAligned code returns (label :: labels) next output := by
  intro impossible
  simp at impossible

/-- Every branch target carries its source continuation under the enclosing
labels and retains the enclosing scope's logical endpoint. -/
def LabelContinuations (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (labels : List LabelTarget) : Prop :=
  ∀ depth label, labels[depth]? = some label → label.branchLive = true →
    ∃ next after, CodeRel types functions returns locals code (labels.drop (depth + 1))
      (label.front ++ label.branchTypes) (label.cont ++ label.after) label.target.val next after ∧
      ExitAligned (labels.drop (depth + 1)) next ∧
      RootAligned code returns (labels.drop (depth + 1)) next after

/-- Normal label exits retain their own continuation; for an IF then arm this
starts at the skip instruction rather than the branch target after the else. -/
def NormalContinuations (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (labels : List LabelTarget) : Prop :=
  ∀ depth label, labels[depth]? = some label → label.normalLive = true →
    ∃ next after, CodeRel types functions returns locals code (labels.drop (depth + 1))
      (label.front ++ label.resultTypes) label.after label.normalExit next after ∧
      ExitAligned (labels.drop (depth + 1)) next ∧
      RootAligned code returns (labels.drop (depth + 1)) next after

/-- Static source position, branch and fallthrough continuations, and scope
endpoint alignment. Empty source code therefore identifies a normal exit. -/
structure StructuredPoint (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (labels : List LabelTarget) (stack : List valtype)
    (source : List instr) (pc next : Nat) (after : List valtype) : Prop where
  current : CodeRel types functions returns locals code labels stack source pc next after
  targets : LabelContinuations types functions returns locals code labels
  normal : NormalContinuations types functions returns locals code labels
  exit : ExitAligned labels next
  root : RootAligned code returns labels next after

theorem LabelContinuations.tail {types functions returns locals code label labels}
    (targets : LabelContinuations types functions returns locals code (label :: labels)) :
    LabelContinuations types functions returns locals code labels := by
  intro depth target lookup live
  simpa using targets (depth + 1) target (by simpa using lookup) live

theorem LabelContinuations.drop {types functions returns locals code labels}
    (targets : LabelContinuations types functions returns locals code labels) (count : Nat) :
    LabelContinuations types functions returns locals code (labels.drop count) := by
  intro depth label lookup live
  have original : labels[count + depth]? = some label := by simpa using lookup
  obtain ⟨next, after, relation, aligned, root⟩ := targets (count + depth) label original live
  refine ⟨next, after, ?_, ?_, ?_⟩
  · simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using relation
  · simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using aligned
  · simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using root

theorem NormalContinuations.drop {types functions returns locals code labels}
    (targets : NormalContinuations types functions returns locals code labels) (count : Nat) :
    NormalContinuations types functions returns locals code (labels.drop count) := by
  intro depth label lookup live
  have original : labels[count + depth]? = some label := by simpa using lookup
  obtain ⟨next, after, relation, aligned, root⟩ := targets (count + depth) label original live
  refine ⟨next, after, ?_, ?_, ?_⟩
  · simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using relation
  · simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using aligned
  · simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using root

theorem Segment.pc_le_next {code pc emitted next} (segment : Segment code pc emitted next) : pc ≤ next := by
  obtain ⟨_, _, _, _, rfl⟩ := segment
  omega

theorem CodeRel.pc_le_next {types functions returns locals code labels stack source pc next after}
    (relation : CodeRel types functions returns locals code labels stack source pc next after) : pc ≤ next := by
  induction relation with
  | nil => omega
  | linear head fragment rest ih => exact fragment.pc_le_next.trans ih
  | skip forward instruction rest ih => omega
  | block signature bodyCode rest targetRest bounds bodyBound restBound targetBound => exact bounds.1
  | loop signature head bodyCode rest bounds bodyBound restBound => exact bounds.1
  | ifElse signature condition guard yesCode skip noCode rest bounds yesBound noBound restBound => omega
  | branch lookup live layout fragment remaining scope => exact fragment.pc_le_next.trans remaining
  | branchIf lookup live layout condition fragment rest ih => exact fragment.pc_le_next.trans ih
  | call signature arguments instruction rest ih => omega
  | unreachable instruction remaining scope => omega
  | return_ source size instruction remaining scope => omega

theorem CodeRel.next_le_length {types functions returns locals code labels stack source pc next after}
    (relation : CodeRel types functions returns locals code labels stack source pc next after) : next ≤ code.length := by
  induction relation with
  | nil labels stack pc bound live => exact bound
  | linear _ _ _ ih => exact ih
  | skip _ _ _ ih => exact ih
  | block _ _ _ _ bounds _ _ _ => exact bounds.2
  | loop _ _ _ _ bounds _ _ => exact bounds.2
  | ifElse _ _ _ _ _ _ _ bounds _ _ _ => exact bounds.2.2
  | branch _ _ _ _ _ scope => exact scope
  | branchIf _ _ _ _ _ _ ih => exact ih
  | call _ _ _ _ ih => exact ih
  | unreachable _ _ scope => exact scope
  | return_ _ _ _ _ scope => exact scope

theorem CodeRel.entry_bound {types functions returns locals code labels stack source pc next after}
    (relation : CodeRel types functions returns locals code labels stack source pc next after) :
    pc ≤ code.length := relation.pc_le_next.trans relation.next_le_length

end Exec.Code
