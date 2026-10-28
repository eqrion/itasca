import Itasca.Runtime.Code.Local.Control.Common.Structured
import Itasca.Runtime.Code.Local.Lowering.Common.Lowering
namespace Itasca.Runtime.Code
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

theorem Segment.pc_le_next {code pc emitted next} (segment : Segment code pc emitted next) : pc ≤ next := by
  obtain ⟨_, _, _, _, rfl⟩ := segment
  omega

end Itasca.Runtime.Code
