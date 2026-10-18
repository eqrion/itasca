import Exec.Code.Local.Relations.Common.Rel

namespace Exec.Code
open Aeneas.Std

/-- Concrete copy specialization shared by compiler and execution certificates. -/
def transferInstruction (dst src count : U32) : Bytecode :=
  if count.val = 1 then .Copy dst src else if count.val = 2 then .Copy2 dst src else .CopyN dst src count

/-- An exact bytecode fragment with absolute entry and continuation coordinates. -/
def Segment (code : List Bytecode) (pc : Nat) (instructions : List Bytecode) (next : Nat) : Prop :=
  ∃ front suffix, code = front ++ instructions ++ suffix ∧ front.length = pc ∧
    next = pc + instructions.length

theorem Segment.fetch {code instructions pc next} (segment : Segment code pc instructions next)
    {index instruction} (found : instructions[index]? = some instruction) :
    code[pc + index]? = some instruction := by
  obtain ⟨front, suffix, rfl, rfl, rfl⟩ := segment
  rw [List.append_assoc, List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found

theorem Segment.append {code pc middle next first second}
    (left : Segment code pc first middle) (right : Segment code middle second next) :
    Segment code pc (first ++ second) next := by
  obtain ⟨pre, suffix, hc, hp, hm⟩ := left
  obtain ⟨pre', suffix', hc', hp', hn⟩ := right
  have same : pre ++ first = pre' := by
    have eq := congrArg (List.take middle) (hc.symm.trans hc')
    have size : (pre ++ first).length = middle := by simp [hp, hm]
    have takeLeft : (pre ++ first ++ suffix).take middle = pre ++ first := by
      rw [← size, List.take_left]
    have takeRight : (pre' ++ second ++ suffix').take middle = pre' := by
      rw [List.append_assoc, ← hp', List.take_left]
    exact takeLeft.symm.trans (eq.trans takeRight)
  refine ⟨pre, suffix', ?_, hp, ?_⟩
  · simpa only [List.append_assoc, ← same] using hc'
  · simp only [List.length_append]
    omega

/-- Static label information retained from structured source control. Branch
operands replace everything above `front`; a loop continuation re-enters its
source LOOP instruction and its bytecode LoopHead. -/
structure LabelTarget where
  front : List valtype
  branchTypes : List valtype
  resultTypes : List valtype
  target : U32
  /-- Fallthrough leaves the label here; an IF then arm may execute a skip. -/
  normalExit : Nat
  cont : List instr
  after : List instr
  normalLive : Bool
  branchLive : Bool

/-- Only a live normal exit can be reached by an empty source continuation. -/
def NormalLive (labels : List LabelTarget) : Prop :=
  ∀ label, labels.head? = some label → label.normalLive = true

theorem NormalLive.nil : NormalLive [] := by intro label impossible; simp at impossible

theorem NormalLive.cons {label : LabelTarget} {labels} (live : label.normalLive = true) :
    NormalLive (label :: labels) := by intro other eq; simp only [List.head?_cons, Option.some.injEq] at eq; subst other; exact live

/-- Source block signatures, including module-local type-index resolution. -/
inductive BlockSignature (types : List functype) : blocktype → List valtype → List valtype → Prop where
  | empty : BlockSignature types (._RESULT none) [] []
  | value (ty) : BlockSignature types (._RESULT (some ty)) [] [ty]
  | index (i : Nat) (params results)
      (lookup : types[i]? = some ⟨.mk_list params, .mk_list results⟩) :
      BlockSignature types (._IDX (.mk_uN i)) params results

/-- Transfer layout is independent of operand values and runtime state. -/
def BranchLayout (locals stack : List valtype) (label : LabelTarget)
    (dst src count : U32) : Prop :=
  ∃ discarded, stack = label.front ++ discarded ++ label.branchTypes ∧
    dst.val = slots locals + slots label.front ∧
    src.val = slots locals + slots (label.front ++ discarded) ∧
    count.val = slots label.branchTypes

/-- Exactly the branch instruction sequence emitted after fixups resolve. -/
def branchInstructions (dst src count target : U32) : List Bytecode :=
  if count = 0#u32 ∨ src = dst then [.Jump target]
  else [transferInstruction dst src count, .Jump target]

/-- Conditional branches either test directly, or guard a transfer/jump pair. -/
def branchIfInstructions (dst src count target cond resume : U32) : List Bytecode :=
  if count = 0#u32 ∨ src = dst then [.JumpIfNonZero cond target]
  else [.JumpIfZero cond resume, transferInstruction dst src count, .Jump target]

/-- A then arm either skips an explicit else arm or meets the shared exit
without emitting a jump (the binary IF-without-ELSE form). -/
inductive IfSkip (code : List Bytecode) (yesExit : Nat) (noEntry exit : U32) (yesNormal : Bool) : Prop where
  | emitted (fragment : Segment code yesExit (if yesNormal then [.Jump exit] else []) noEntry.val) :
      IfSkip code yesExit noEntry exit yesNormal
  | direct (normal : yesExit = exit.val) (otherwise : noEntry = exit) :
      IfSkip code yesExit noEntry exit yesNormal

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

end Exec.Code
