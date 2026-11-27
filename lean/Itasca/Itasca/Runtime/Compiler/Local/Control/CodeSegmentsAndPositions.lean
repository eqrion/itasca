import Itasca.Runtime.Compiler.Local.Definitions
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty

open WebAssembly

/-!
Proofs for Runtime / Compiler / Local / Control.

This module collects Positions, CodeSegments.
Each section documents its contracts and consumers.
-/

/-! ## Positions -/

section

/-!
# Internal source positions in compiled code

Branch and fallthrough continuations reconstruct the current execution point
from structured emission. Public compilation certificates describe the complete
function; these intermediate positions belong to the execution proof.
-/
namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Representation

/-- A retained scope's logical fallthrough endpoint agrees with its top label. -/
def ExitAligned (labels : List LabelTarget) (next : Nat) : Prop :=
  ∀ label, labels.head? = some label → next = label.normalExit

/-- An outermost continuation ends immediately before the function's retained
Return epilogue and produces exactly its declared results. -/
def RootAligned (code : List Bytecode) (returns : List valtype)
    (labels : List LabelTarget) (next : Nat) (output : List valtype) : Prop :=
  labels = [] → next + 1 = code.length ∧ output = returns ∧
    ∃ src count, count.val = slots returns ∧ code[next]? = some (.Return src count)


def StructuredCode.Targets (emission : List valtype → instr → List Bytecode → List valtype → Prop)
    (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (jumpTables : List U32) (labels : List LabelTarget) : Prop :=
  ∀ depth label, labels[depth]? = some label → label.branchLive = true →
    ∃ next after, StructuredCode emission types functions returns locals code jumpTables (labels.drop (depth + 1))
      (label.front ++ label.branchTypes) (label.cont ++ label.after) label.target.val next after ∧
      ExitAligned (labels.drop (depth + 1)) next ∧
      RootAligned code returns (labels.drop (depth + 1)) next after

/-- Normal label exits retain their own continuation; for an IF then arm this
starts at the skip instruction rather than the branch target after the else. -/
def StructuredCode.Normals (emission : List valtype → instr → List Bytecode → List valtype → Prop)
    (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (jumpTables : List U32) (labels : List LabelTarget) : Prop :=
  ∀ depth label, labels[depth]? = some label → label.normalLive = true →
    ∃ next after, StructuredCode emission types functions returns locals code jumpTables (labels.drop (depth + 1))
      (label.front ++ label.resultTypes) label.after label.normalExit next after ∧
      ExitAligned (labels.drop (depth + 1)) next ∧
      RootAligned code returns (labels.drop (depth + 1)) next after

/-- Static source position, branch and fallthrough continuations, and scope
endpoint alignment. Empty source code therefore identifies a normal exit. -/
structure StructuredCode.Point (emission : List valtype → instr → List Bytecode → List valtype → Prop)
    (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (jumpTables : List U32) (labels : List LabelTarget) (stack : List valtype)
    (source : List instr) (pc next : Nat) (after : List valtype) : Prop where
  current : StructuredCode emission types functions returns locals code jumpTables labels stack source pc next after
  targets : StructuredCode.Targets emission types functions returns locals code jumpTables labels
  normal : StructuredCode.Normals emission types functions returns locals code jumpTables labels
  exit : ExitAligned labels next
  root : RootAligned code returns labels next after


end Itasca.Compiler

end

/-! ## CodeSegments -/

section

open Itasca.Representation

/-!
# Code Segments

Structured code segments compose while retaining their labels, source boundaries and control correspondence.
-/

/-! ## Structured -/

section

/-!
Concrete copy specialization shared by compiler and execution certificates.

Main declarations: `transferInstruction` and `Segment`.
-/

namespace Itasca.Compiler
open Aeneas.Std

theorem Segment.fetch {code instructions pc next} (segment : Segment code pc instructions next)
    {index instruction} (found : instructions[index]? = some instruction) :
    code[pc + index]? = some instruction := by
  obtain ⟨front, suffix, rfl, rfl, rfl⟩ := segment
  rw [List.append_assoc, List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found

theorem NormalLive.nil : NormalLive [] := by intro label impossible; simp at impossible

theorem NormalLive.cons {label : LabelTarget} {labels} (live : label.normalLive = true) :
    NormalLive (label :: labels) := by intro other eq; simp only [List.head?_cons, Option.some.injEq] at eq; subst other; exact live

theorem IfSkip.pc_le_next {code yesExit noEntry exit yesNormal}
    (skip : IfSkip code yesExit noEntry exit yesNormal) : yesExit ≤ noEntry.val := by
  cases skip with
  | emitted fragment => obtain ⟨_, _, _, _, endpoint⟩ := fragment; omega
  | direct normal otherwise => simp [normal, otherwise]

/-- Retained structured source-to-code evidence. Constructors contain only
syntax, static types, slot coordinates, and exact bytecode fragments. They do
not assume execution correctness or a compiler-success theorem. Live-exit
flags retain only source continuations that the compiler actually emits. -/
inductive CodeRel (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) : List LabelTarget → List valtype → List instr → Nat → Nat → List valtype → Prop where
  | nil (labels stack pc) (bound : pc ≤ code.length) (live : NormalLive labels) :
      CodeRel types functions returns locals code labels stack [] pc pc stack
  | linear {labels before middle after instruction source emitted pc tail next}
      (head : LinearEmission locals before instruction emitted middle)
      (fragment : Segment code pc emitted tail)
      (rest : CodeRel types functions returns locals code labels middle source tail next after) :
      CodeRel types functions returns locals code labels before (instruction :: source) pc next after
  | skip {labels stack source pc target next final}
      (forward : pc < target.val)
      (instruction : code[pc]? = some (.Jump target))
      (rest : CodeRel types functions returns locals code labels stack source target.val next final) :
      CodeRel types functions returns locals code labels stack source pc next final
  | block {labels front params results after body bt pc normalExit branchExit next final normalLive branchLive}
      (signature : BlockSignature types bt params results)
      (bodyCode : CodeRel types functions returns locals code
        (⟨front, results, results, branchExit, normalExit, [], after, normalLive, branchLive⟩ :: labels)
        (front ++ params) body pc normalExit (front ++ results))
      (rest : normalLive = true → CodeRel types functions returns locals code labels (front ++ results) after normalExit next final)
      (targetRest : branchLive = true → CodeRel types functions returns locals code labels (front ++ results) after branchExit.val next final)
      (bounds : pc ≤ next ∧ next ≤ code.length) :
      CodeRel types functions returns locals code labels (front ++ params) (.BLOCK bt body :: after) pc next final
  | loop {labels front params results after body bt entry exit next final normalLive}
      (signature : BlockSignature types bt params results)
      (head : code[entry.val]? = some .LoopHead)
      (bodyCode : CodeRel types functions returns locals code
        (⟨front, params, results, entry, exit, [.LOOP bt body], after, normalLive, true⟩ :: labels)
        (front ++ params) body (entry.val + 1) exit (front ++ results))
      (rest : normalLive = true → CodeRel types functions returns locals code labels (front ++ results) after exit next final)
      (bounds : entry.val ≤ next ∧ next ≤ code.length) :
      CodeRel types functions returns locals code labels (front ++ params) (.LOOP bt body :: after) entry.val next final
  | ifElse {labels front params results after yes no bt pc yesExit noEntry exit next final cond yesNormal yesBranch noNormal noBranch}
      (signature : BlockSignature types bt params results)
      (condition : cond.val = slots locals + slots (front ++ params))
      (guard : code[pc]? = some (.JumpIfZero cond noEntry))
      (yesCode : CodeRel types functions returns locals code
        (⟨front, results, results, exit, yesExit, [], after, yesNormal, yesBranch⟩ :: labels)
        (front ++ params) yes (pc + 1) yesExit (front ++ results))
      (skip : IfSkip code yesExit noEntry exit yesNormal)
      (noCode : CodeRel types functions returns locals code
        (⟨front, results, results, exit, exit.val, [], after, noNormal, noBranch⟩ :: labels)
        (front ++ params) no noEntry.val exit.val (front ++ results))
      (rest : yesNormal = true ∨ yesBranch = true ∨ noNormal = true ∨ noBranch = true →
        CodeRel types functions returns locals code labels (front ++ results) after exit.val next final)
      (bounds : pc + 1 ≤ next ∧ noEntry.val ≤ next ∧ next ≤ code.length) :
      CodeRel types functions returns locals code labels (front ++ params ++ [.I32])
        (.IFELSE bt yes no :: after) pc next final
  | branch {labels stack after depth label dst src count pc fragmentEnd next final}
      (lookup : labels[depth]? = some label)
      (live : label.branchLive = true)
      (layout : BranchLayout locals stack label dst src count)
      (fragment : Segment code pc (branchInstructions dst src count label.target) fragmentEnd)
      (remaining : fragmentEnd ≤ next) (scope : next ≤ code.length) :
      CodeRel types functions returns locals code labels stack (.BR (.mk_uN depth) :: after) pc next final
  | branchIf {labels stack after depth label dst src count cond resume pc next final}
      (lookup : labels[depth]? = some label)
      (live : label.branchLive = true)
      (layout : BranchLayout locals stack label dst src count)
      (condition : cond.val = slots locals + slots stack)
      (fragment : Segment code pc (branchIfInstructions dst src count label.target cond resume) resume.val)
      (rest : CodeRel types functions returns locals code labels stack after resume.val next final) :
      CodeRel types functions returns locals code labels (stack ++ [.I32])
        (.BR_IF (.mk_uN depth) :: after) pc next final
  | call {labels front params results after index base pc next final}
      (signature : functions[index.val]? = some ⟨.mk_list params, .mk_list results⟩)
      (arguments : base.val = slots locals + slots front)
      (instruction : code[pc]? = some (.Call index base))
      (rest : CodeRel types functions returns locals code labels (front ++ results) after (pc + 1) next final) :
      CodeRel types functions returns locals code labels (front ++ params) (.CALL (.mk_uN index.val) :: after) pc next final
  | unreachable {labels stack after pc next final}
      (instruction : code[pc]? = some .Unreachable)
      (remaining : pc + 1 ≤ next) (scope : next ≤ code.length) :
      CodeRel types functions returns locals code labels stack (.UNREACHABLE :: after) pc next final
  | return_ {labels front after src count pc next final}
      (source : src.val = slots locals + slots front)
      (size : count.val = slots returns)
      (instruction : code[pc]? = some (.Return src count))
      (remaining : pc + 1 ≤ next) (scope : next ≤ code.length) :
      CodeRel types functions returns locals code labels (front ++ returns) (.RETURN :: after) pc next final

end Itasca.Compiler

end

/-! ## StructuredComposition -/

section

/-!
A retained scope's logical fallthrough endpoint agrees with its top label.

Main declarations: `ExitAligned` and `RootAligned`.
-/

namespace Itasca.Compiler
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

theorem RootAligned.cons (code : List Bytecode) (returns : List valtype)
    (label : LabelTarget) (labels : List LabelTarget) (next : Nat) (output : List valtype) :
    RootAligned code returns (label :: labels) next output := by
  intro impossible
  simp at impossible

theorem Segment.pc_le_next {code pc emitted next} (segment : Segment code pc emitted next) : pc ≤ next := by
  obtain ⟨_, _, _, _, rfl⟩ := segment
  omega

end Itasca.Compiler

end

/-! ## StructuredLabels -/

section

/-!
Extending an aligned structured label sequence.

Main declarations: `ExitAligned.cons`.
-/

namespace Itasca.Compiler
open Aeneas.Std

theorem ExitAligned.cons (label : LabelTarget) (labels : List LabelTarget) :
    ExitAligned (label :: labels) label.normalExit := by
  intro found lookup
  have same : found = label := by simpa using lookup.symm
  subst found
  rfl

end Itasca.Compiler

end

end
