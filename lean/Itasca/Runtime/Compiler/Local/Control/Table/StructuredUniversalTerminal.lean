import Itasca.Runtime.Compiler.Local.Relations.Table.TableDepths
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant

/-!
Sections, each formerly its own module: StructuredCode, StructuredCodePoint, StructuredCodeTableExclusion, StructuredCodeAlgebra, StructuredPrefix, StructuredPrefixEmission, StructuredSuspendedPrefix, StructuredPrefixZipper, StructuredUniversalPrefix, StructuredElseEvidence, StructuredParentPrefixPop, StructuredUniversalTerminal.
-/

/-! ## StructuredCode -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std
/-- Structured compiler evidence parameterized only by its syntactic emitted-head relation. -/
inductive StructuredCode (emission : List valtype → instr → List Bytecode → List valtype → Prop)
    (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) : List U32 → List LabelTarget → List valtype → List instr → Nat → Nat → List valtype → Prop where
  | nil (labels stack pc) (bound : pc ≤ code.length) (live : NormalLive labels) :
      StructuredCode emission types functions returns locals code jumpTables labels stack [] pc pc stack
  | linear {labels before middle after instruction source emitted pc tail next}
      (head : emission before instruction emitted middle)
      (ordinary : ∀ depths fallback, instruction ≠ .BR_TABLE depths fallback)
      (fragment : Segment code pc emitted tail)
      (rest : StructuredCode emission types functions returns locals code jumpTables labels middle source tail next after) :
      StructuredCode emission types functions returns locals code jumpTables labels before (instruction :: source) pc next after
  | skip {labels stack source pc target next final}
      (forward : pc < target.val)
      (instruction : code[pc]? = some (.Jump target))
      (rest : StructuredCode emission types functions returns locals code jumpTables labels stack source target.val next final) :
      StructuredCode emission types functions returns locals code jumpTables labels stack source pc next final
  | block {labels front params results after body bt pc normalExit branchExit next final normalLive branchLive}
      (signature : BlockSignature types bt params results)
      (bodyCode : StructuredCode emission types functions returns locals code jumpTables
        (⟨front, results, results, branchExit, normalExit, [], after, normalLive, branchLive⟩ :: labels)
        (front ++ params) body pc normalExit (front ++ results))
      (rest : normalLive = true → StructuredCode emission types functions returns locals code jumpTables labels (front ++ results) after normalExit next final)
      (targetRest : branchLive = true → StructuredCode emission types functions returns locals code jumpTables labels (front ++ results) after branchExit.val next final)
      (bounds : pc ≤ next ∧ next ≤ code.length) :
      StructuredCode emission types functions returns locals code jumpTables labels (front ++ params) (.BLOCK bt body :: after) pc next final
  | loop {labels front params results after body bt entry exit next final normalLive}
      (signature : BlockSignature types bt params results)
      (head : code[entry.val]? = some .LoopHead)
      (bodyCode : StructuredCode emission types functions returns locals code jumpTables
        (⟨front, params, results, entry, exit, [.LOOP bt body], after, normalLive, true⟩ :: labels)
        (front ++ params) body (entry.val + 1) exit (front ++ results))
      (rest : normalLive = true → StructuredCode emission types functions returns locals code jumpTables labels (front ++ results) after exit next final)
      (bounds : entry.val ≤ next ∧ next ≤ code.length) :
      StructuredCode emission types functions returns locals code jumpTables labels (front ++ params) (.LOOP bt body :: after) entry.val next final
  | ifElse {labels front params results after yes no bt pc yesExit noEntry exit next final cond yesNormal yesBranch noNormal noBranch}
      (signature : BlockSignature types bt params results)
      (condition : cond.val = slots locals + slots (front ++ params))
      (guard : code[pc]? = some (.JumpIfZero cond noEntry))
      (yesCode : StructuredCode emission types functions returns locals code jumpTables
        (⟨front, results, results, exit, yesExit, [], after, yesNormal, yesBranch⟩ :: labels)
        (front ++ params) yes (pc + 1) yesExit (front ++ results))
      (skip : IfSkip code yesExit noEntry exit yesNormal)
      (noCode : StructuredCode emission types functions returns locals code jumpTables
        (⟨front, results, results, exit, exit.val, [], after, noNormal, noBranch⟩ :: labels)
        (front ++ params) no noEntry.val exit.val (front ++ results))
      (rest : yesNormal = true ∨ yesBranch = true ∨ noNormal = true ∨ noBranch = true →
        StructuredCode emission types functions returns locals code jumpTables labels (front ++ results) after exit.val next final)
      (bounds : pc + 1 ≤ next ∧ noEntry.val ≤ next ∧ next ≤ code.length) :
      StructuredCode emission types functions returns locals code jumpTables labels (front ++ params ++ [.I32])
        (.IFELSE bt yes no :: after) pc next final
  | branch {labels stack after depth label dst src count pc fragmentEnd next final}
      (lookup : labels[depth]? = some label)
      (live : label.branchLive = true)
      (layout : BranchLayout locals stack label dst src count)
      (fragment : Segment code pc (branchInstructions dst src count label.target) fragmentEnd)
      (remaining : fragmentEnd ≤ next) (scope : next ≤ code.length) :
      StructuredCode emission types functions returns locals code jumpTables labels stack (.BR (.mk_uN depth) :: after) pc next final
  | branchIf {labels stack after depth label dst src count cond resume pc next final}
      (lookup : labels[depth]? = some label)
      (live : label.branchLive = true)
      (layout : BranchLayout locals stack label dst src count)
      (condition : cond.val = slots locals + slots stack)
      (fragment : Segment code pc (branchIfInstructions dst src count label.target cond resume) resume.val)
      (rest : StructuredCode emission types functions returns locals code jumpTables labels stack after resume.val next final) :
      StructuredCode emission types functions returns locals code jumpTables labels (stack ++ [.I32])
        (.BR_IF (.mk_uN depth) :: after) pc next final
  | call {labels front params results after index base pc next final}
      (signature : functions[index.val]? = some ⟨.mk_list params, .mk_list results⟩)
      (arguments : base.val = slots locals + slots front)
      (instruction : code[pc]? = some (.Call index base))
      (rest : StructuredCode emission types functions returns locals code jumpTables labels (front ++ results) after (pc + 1) next final) :
      StructuredCode emission types functions returns locals code jumpTables labels (front ++ params) (.CALL (.mk_uN index.val) :: after) pc next final
  | unreachable {labels stack after pc next final}
      (instruction : code[pc]? = some .Unreachable)
      (remaining : pc + 1 ≤ next) (scope : next ≤ code.length) :
      StructuredCode emission types functions returns locals code jumpTables labels stack (.UNREACHABLE :: after) pc next final
  | return_ {labels front after src count pc next final}
      (source : src.val = slots locals + slots front)
      (size : count.val = slots returns)
      (instruction : code[pc]? = some (.Return src count))
      (remaining : pc + 1 ≤ next) (scope : next ≤ code.length) :
      StructuredCode emission types functions returns locals code jumpTables labels (front ++ returns) (.RETURN :: after) pc next final

  | branchTable {first rest labels stack after depths fallback pc next final selector start len}
      (gate : emission (stack ++ [.I32]) (.BR_TABLE depths fallback) [.JumpTable selector start len] stack)
      (table : BranchTableLayout (first :: rest) locals labels stack code depths fallback pc next selector start len)
      (bounds : pc + 1 ≤ next ∧ next ≤ code.length) :
      StructuredCode emission types functions returns locals code (first :: rest) labels
        (stack ++ [.I32]) (.BR_TABLE depths fallback :: after) pc next final

theorem StructuredCode.map_emission {first second types functions returns locals code jumpTables labels stack source pc next final}
    (relation : StructuredCode first types functions returns locals code jumpTables labels stack source pc next final)
    (map : ∀ before instruction emitted after, first before instruction emitted after → second before instruction emitted after) :
    StructuredCode second types functions returns locals code jumpTables labels stack source pc next final := by
  induction relation using StructuredCode.rec with
  | nil labels stack pc bound live => exact .nil labels stack pc bound live
  | linear head ordinary fragment rest ih => exact .linear (map _ _ _ _ head) ordinary fragment ih
  | skip forward fetched rest ih => exact .skip forward fetched ih
  | block signature bodyCode rest targetRest bounds bodyIH restIH targetIH =>
    exact .block signature bodyIH restIH targetIH bounds
  | loop signature head bodyCode rest bounds bodyIH restIH =>
    exact .loop signature head bodyIH restIH bounds
  | ifElse signature condition guard yesCode skip noCode rest bounds yesIH noIH restIH =>
    exact .ifElse signature condition guard yesIH skip noIH restIH bounds
  | branch lookup live layout fragment remaining scope =>
    exact .branch lookup live layout fragment remaining scope
  | branchIf lookup live layout condition fragment rest ih =>
    exact .branchIf lookup live layout condition fragment ih
  | call signature arguments fetched rest ih => exact .call signature arguments fetched ih
  | unreachable fetched remaining scope => exact .unreachable fetched remaining scope
  | return_ source size fetched remaining scope => exact .return_ source size fetched remaining scope
  | branchTable gate table bounds => exact .branchTable (map _ _ _ _ gate) table bounds

end Itasca.Runtime.Compiler

end

/-! ## StructuredCodePoint -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

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

theorem StructuredCode.Targets.drop {emission types functions returns locals code jumpTables labels}
    (targets : StructuredCode.Targets emission types functions returns locals code jumpTables labels) (count : Nat) :
    StructuredCode.Targets emission types functions returns locals code jumpTables (labels.drop count) := by
  intro depth label lookup live
  have original : labels[count + depth]? = some label := by simpa using lookup
  obtain ⟨next, after, relation, aligned, root⟩ := targets (count + depth) label original live
  refine ⟨next, after, ?_, ?_, ?_⟩
  · simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using relation
  · simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using aligned
  · simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using root

theorem StructuredCode.Normals.drop {emission types functions returns locals code jumpTables labels}
    (targets : StructuredCode.Normals emission types functions returns locals code jumpTables labels) (count : Nat) :
    StructuredCode.Normals emission types functions returns locals code jumpTables (labels.drop count) := by
  intro depth label lookup live
  have original : labels[count + depth]? = some label := by simpa using lookup
  obtain ⟨next, after, relation, aligned, root⟩ := targets (count + depth) label original live
  refine ⟨next, after, ?_, ?_, ?_⟩
  · simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using relation
  · simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using aligned
  · simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using root

theorem StructuredCode.pc_le_next {emission types functions returns locals code jumpTables labels stack source pc next after}
    (relation : StructuredCode emission types functions returns locals code jumpTables labels stack source pc next after) : pc ≤ next := by
  induction relation using StructuredCode.rec with
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

theorem StructuredCode.next_le_length {emission types functions returns locals code jumpTables labels stack source pc next after}
    (relation : StructuredCode emission types functions returns locals code jumpTables labels stack source pc next after) : next ≤ code.length := by
  induction relation using StructuredCode.rec with
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

theorem StructuredCode.entry_bound {emission types functions returns locals code jumpTables labels stack source pc next after}
    (relation : StructuredCode emission types functions returns locals code jumpTables labels stack source pc next after) :
    pc ≤ code.length := relation.pc_le_next.trans relation.next_le_length

end Itasca.Runtime.Compiler

end

/-! ## StructuredCodeTableExclusion -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

private theorem numeric_not_branch_table (op : SourceMachine.Numeric.Instruction) (depths fallback) :
    op.source ≠ .BR_TABLE depths fallback := by
  cases op with
  | conversion op => cases op <;> simp [SourceMachine.Numeric.Instruction.source,SourceMachine.Numeric.Conversion.source]
  | _ => simp [SourceMachine.Numeric.Instruction.source]

theorem LinearEmission.not_branch_table {locals before instruction emitted after}
    (h : LinearEmission locals before instruction emitted after) (depths fallback) :
    instruction ≠ .BR_TABLE depths fallback := by
  cases h with
  | binary stack ty op => cases op <;> simp [IntegerBinary.source]
  | numeric stack op => exact numeric_not_branch_table op depths fallback
  | _ => simp

theorem ScalarEmission.not_branch_table {C before instruction emitted after}
    (h : ScalarEmission C before instruction emitted after) (depths fallback) :
    instruction ≠ .BR_TABLE depths fallback := by
  cases h with
  | linear h => exact h.not_branch_table depths fallback
  | float stack op => cases op <;> simp [SourceMachine.Float.Instruction.source]
  | load => simp [SourceMachine.Memory.Load.source]
  | store => simp [SourceMachine.Memory.Store.source]
  | _ => simp

end Itasca.Runtime.Compiler

end

/-! ## StructuredCodeAlgebra -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std
theorem StructuredCode.extend {emission types functions returns locals code jumpTables labels stack source pc next final}
    (relation : StructuredCode emission types functions returns locals code jumpTables labels stack source pc next final)
    (suffix : List Bytecode) :
    StructuredCode emission types functions returns locals (code ++ suffix) jumpTables labels stack source pc next final := by
  induction relation using StructuredCode.rec with
  | nil labels stack pc bound live => exact .nil labels stack pc (by simp; omega) live
  | linear head ordinary fragment rest ih => exact .linear head ordinary (fragment.extend suffix) ih
  | skip forward fetched rest ih => exact .skip forward (fetch_extend fetched suffix) ih
  | block signature bodyCode rest targetRest bounds bodyIH restIH targetIH =>
    exact .block signature bodyIH restIH targetIH ⟨bounds.1, by simp; omega⟩
  | loop signature head bodyCode rest bounds bodyIH restIH =>
    exact .loop signature (fetch_extend head suffix) bodyIH restIH ⟨bounds.1, by simp; omega⟩
  | ifElse signature condition guard yesCode skip noCode rest bounds yesIH noIH restIH =>
    exact .ifElse signature condition (fetch_extend guard suffix) yesIH (skip.extend suffix) noIH restIH
      ⟨bounds.1, bounds.2.1, by simp; omega⟩
  | branch lookup live layout fragment remaining scope =>
    exact .branch lookup live layout (fragment.extend suffix) remaining (by simp; omega)
  | branchIf lookup live layout condition fragment rest ih =>
    exact .branchIf lookup live layout condition (fragment.extend suffix) ih
  | call signature arguments fetched rest ih => exact .call signature arguments (fetch_extend fetched suffix) ih
  | unreachable fetched remaining scope => exact .unreachable (fetch_extend fetched suffix) remaining (by simp; omega)
  | return_ source size fetched remaining scope =>
    exact .return_ source size (fetch_extend fetched suffix) remaining (by simp; omega)
  | branchTable gate table bounds => exact .branchTable gate (table.extend suffix) ⟨bounds.1,by simp; omega⟩

theorem StructuredCode.relabel {emission types functions returns locals code jumpTables labels stack source pc next after}
    (relation : StructuredCode emission types functions returns locals code jumpTables labels stack source pc next after)
    {other} (shape : LabelsShape labels other) :
    StructuredCode emission types functions returns locals code jumpTables other stack source pc next after := by
  induction relation using StructuredCode.rec generalizing other with
  | nil labels stack pc bound live => exact .nil other stack pc bound (shape.normal live)
  | linear head ordinary fragment rest ih => exact .linear head ordinary fragment (ih shape)
  | skip forward instruction rest ih => exact .skip forward instruction (ih shape)
  | block signature body rest target bounds bodyIH restIH targetIH =>
    exact .block signature (bodyIH (.cons (LabelShape.refl _) shape))
      (fun live => restIH live shape) (fun live => targetIH live shape) bounds
  | loop signature head body rest bounds bodyIH restIH =>
    exact .loop signature head (bodyIH (.cons (LabelShape.refl _) shape))
      (fun live => restIH live shape) bounds
  | ifElse signature condition guard yes skip no rest bounds yesIH noIH restIH =>
    exact .ifElse signature condition guard (yesIH (.cons (LabelShape.refl _) shape)) skip
      (noIH (.cons (LabelShape.refl _) shape)) (fun live => restIH live shape) bounds
  | @branch jumpTables labels stack after depth label dst src count pc fragmentEnd next final lookup live layout fragment remaining scope =>
    obtain ⟨otherLabel, otherAt, same⟩ := LabelsShape.lookup shape lookup
    apply StructuredCode.branch (dst := dst) (src := src) (count := count) otherAt (same.branchLive.symm.trans live) ?_ ?_ remaining scope
    · simpa only [BranchLayout, ← same.front, ← same.branchTypes] using layout
    · simpa only [← same.target] using fragment
  | @branchIf jumpTables labels stack after depth label dst src count cond resume pc next final lookup live layout condition fragment rest ih =>
    obtain ⟨otherLabel, otherAt, same⟩ := LabelsShape.lookup shape lookup
    apply StructuredCode.branchIf (dst := dst) (src := src) (count := count) otherAt (same.branchLive.symm.trans live) ?_ condition ?_ (ih shape)
    · simpa only [BranchLayout, ← same.front, ← same.branchTypes] using layout
    · simpa only [← same.target] using fragment
  | call signature arguments instruction rest ih => exact .call signature arguments instruction (ih shape)
  | unreachable instruction remaining scope => exact .unreachable instruction remaining scope
  | return_ source size instruction remaining scope => exact .return_ source size instruction remaining scope

  | branchTable gate table bounds => exact .branchTable gate (table.relabel shape) bounds

end Itasca.Runtime.Compiler

end

/-! ## StructuredPrefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- A builder invariant for a still-open source prefix. Its hole is another
syntactic StructuredCode emission certificate, never an execution or simulation premise. Unlike
a completed StructuredCode emission, an unfinished hole does not assert a live normal exit;
a later RETURN or branch can close it without certifying unreachable suffixes. -/
def StructuredPrefix (emission : List valtype → instr → List Bytecode → List valtype → Prop) (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (labels : List LabelTarget)
    (before : List valtype) (source : List instr) (pc cursor : Nat) (stack : List valtype) (jumpTables : List U32 := []) : Prop :=
  ∀ suffix tail next final, StructuredCode emission types functions returns locals (code ++ suffix) jumpTables labels stack tail cursor next final →
    StructuredCode emission types functions returns locals (code ++ suffix) jumpTables labels before (source ++ tail) pc next final

theorem StructuredPrefix.empty {jumpTables : List U32} (emission types functions returns locals code labels stack pc) :
    StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals code labels stack [] pc pc stack := by
  intro suffix tail next final rest
  simpa using rest

theorem StructuredPrefix.append {jumpTables : List U32} {emission types functions returns locals code labels before source pc cursor stack
    more finish output}
    (first : StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before source pc cursor stack)
    (second : StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals code labels stack more cursor finish output) :
    StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before (source ++ more) pc finish output := by
  intro suffix tail next final rest
  simpa [List.append_assoc] using first suffix _ _ _ (second suffix _ _ _ rest)

theorem StructuredPrefix.linear {jumpTables : List U32} {emission types functions returns locals code labels before middle instruction emitted pc cursor}
    (head : emission before instruction emitted middle)
    (ordinary : ∀ depths fallback, instruction ≠ .BR_TABLE depths fallback)
    (fragment : Segment code pc emitted cursor) :
    StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before [instruction] pc cursor middle := by
  intro suffix tail next final rest
  exact .linear head ordinary (fragment.extend suffix) rest

theorem StructuredPrefix.call {jumpTables : List U32} {emission types functions returns locals code labels front params results index base pc}
    (signature : functions[index.val]? = some ⟨.mk_list params, .mk_list results⟩)
    (arguments : base.val = slots locals + slots front)
    (instruction : code[pc]? = some (.Call index base)) :
    StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals code labels (front ++ params) [.CALL (.mk_uN index.val)]
      pc (pc + 1) (front ++ results) := by
  intro suffix tail next final rest
  exact .call signature arguments (fetch_extend instruction suffix) rest

theorem StructuredPrefix.branch_if {jumpTables : List U32} {emission types functions returns locals code labels stack depth label dst src count cond resume pc}
    (lookup : labels[depth]? = some label) (live : label.branchLive = true)
    (layout : BranchLayout locals stack label dst src count)
    (condition : cond.val = slots locals + slots stack)
    (fragment : Segment code pc (branchIfInstructions dst src count label.target cond resume) resume.val) :
    StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals code labels (stack ++ [.I32]) [.BR_IF (.mk_uN depth)]
      pc resume.val stack := by
  intro suffix tail next final rest
  exact .branchIf lookup live layout condition (fragment.extend suffix) rest

/-- A terminal prefix gives a certificate even for arbitrary uncompiled source
suffixes. The proof is obtained from a literal terminal bytecode constructor. -/
def StructuredDeadPrefix (emission : List valtype → instr → List Bytecode → List valtype → Prop) (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (labels : List LabelTarget)
    (before : List valtype) (source : List instr) (pc cursor : Nat) (jumpTables : List U32 := []) : Prop :=
  ∀ suffix tail next final, cursor ≤ next → next ≤ (code ++ suffix).length →
    StructuredCode emission types functions returns locals (code ++ suffix) jumpTables labels before (source ++ tail) pc next final

theorem StructuredDeadPrefix.unreachable {jumpTables : List U32} {emission types functions returns locals code labels stack pc}
    (found : code[pc]? = some .Unreachable) :
    StructuredDeadPrefix (jumpTables := jumpTables) emission types functions returns locals code labels stack [.UNREACHABLE] pc (pc + 1) := by
  intro suffix tail next final order bound
  exact .unreachable (fetch_extend found suffix) order bound

theorem StructuredDeadPrefix.return_ {jumpTables : List U32} {emission types functions returns locals code labels front src count pc}
    (source : src.val = slots locals + slots front) (size : count.val = slots returns)
    (found : code[pc]? = some (.Return src count)) :
    StructuredDeadPrefix (jumpTables := jumpTables) emission types functions returns locals code labels (front ++ returns) [.RETURN] pc (pc + 1) := by
  intro suffix tail next final order bound
  exact .return_ source size (fetch_extend found suffix) order bound

theorem StructuredDeadPrefix.branch {jumpTables : List U32} {emission types functions returns locals code labels stack depth label dst src count pc cursor}
    (lookup : labels[depth]? = some label) (live : label.branchLive = true)
    (layout : BranchLayout locals stack label dst src count)
    (fragment : Segment code pc (branchInstructions dst src count label.target) cursor) :
    StructuredDeadPrefix (jumpTables := jumpTables) emission types functions returns locals code labels stack [.BR (.mk_uN depth)] pc cursor := by
  intro suffix tail next final order bound
  exact .branch lookup live layout (fragment.extend suffix) order bound

theorem StructuredPrefix.terminal {jumpTables : List U32} {emission types functions returns locals code labels before source pc cursor stack more finish}
    (first : StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before source pc cursor stack)
    (terminal : StructuredDeadPrefix (jumpTables := jumpTables) emission types functions returns locals code labels stack more cursor finish) :
    StructuredDeadPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before (source ++ more) pc finish := by
  intro suffix tail next final order bound
  simpa [List.append_assoc] using first suffix _ _ _ (terminal suffix _ _ _ order bound)

theorem StructuredDeadPrefix.skip_source {jumpTables : List U32} {emission types functions returns locals code labels before source pc cursor}
    (dead : StructuredDeadPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before source pc cursor)
    (skipped : List instr) :
    StructuredDeadPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before (source ++ skipped) pc cursor := by
  intro suffix tail next final order bound
  simpa [List.append_assoc] using dead suffix (skipped ++ tail) next final order bound

/-- Prefix evidence survives later bytecode emission without assuming that the
old end-of-code already admitted a valid continuation. -/
theorem StructuredPrefix.extend {jumpTables : List U32} {emission types functions returns locals code labels before source pc cursor stack}
    (evidence : StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before source pc cursor stack)
    (emitted : List Bytecode) :
    StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals (code ++ emitted) labels before source pc cursor stack := by
  intro suffix tail next final rest
  simpa only [List.append_assoc] using evidence (emitted ++ suffix) tail next final
    (by simpa only [List.append_assoc] using rest)

theorem StructuredDeadPrefix.extend {jumpTables : List U32} {emission types functions returns locals code labels before source pc cursor}
    (evidence : StructuredDeadPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before source pc cursor)
    (emitted : List Bytecode) :
    StructuredDeadPrefix (jumpTables := jumpTables) emission types functions returns locals (code ++ emitted) labels before source pc cursor := by
  intro suffix tail next final order bound
  simpa only [List.append_assoc] using evidence (emitted ++ suffix) tail next final order
    (by simpa only [List.append_assoc] using bound)

/-- A completed branch-table header closes one source instruction after all of
its independently certified target fragments have been emitted. -/
theorem StructuredDeadPrefix.branch_table
    {emission types functions returns locals code tables labels stack depths fallback pc cursor selector start len}
    (gate : emission (stack ++ [.I32]) (.BR_TABLE depths fallback) [.JumpTable selector start len] stack)
    (table : BranchTableLayout tables locals labels stack code depths fallback pc cursor selector start len)
    (header : pc + 1 ≤ cursor) :
    StructuredDeadPrefix (jumpTables := tables) emission types functions returns locals code labels
      (stack ++ [.I32]) [.BR_TABLE depths fallback] pc cursor := by
  cases tables with
  | nil =>
    obtain ⟨entry,found,_⟩ := table.entries depths.length fallback (by simp)
    simp at found
  | cons first rest =>
    intro suffix tail next final order bound
    exact .branchTable gate ((table.extend suffix).weaken_next order bound) ⟨header.trans order,bound⟩
end Itasca.Runtime.Compiler

end

/-! ## StructuredPrefixEmission -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

theorem StructuredPrefix.emit {jumpTables : List U32} {emission types functions returns locals code labels initial source start stack instruction emitted output}
    (prior : StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals code labels initial source start code.length stack)
    (head : emission stack instruction emitted output)
    (ordinary : ∀ depths fallback, instruction ≠ .BR_TABLE depths fallback) :
    StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals (code ++ emitted) labels initial (source ++ [instruction])
      start (code ++ emitted).length output := by
  have fragment : Segment (code ++ emitted) code.length emitted (code ++ emitted).length :=
    ⟨code, [], by simp, rfl, by simp⟩
  exact (prior.extend emitted).append (StructuredPrefix.linear head ordinary fragment)

/-- The prefix component of the compiler invariant, with physical open fixups
resolved through explicit future static targets. Control-frame/source-zipper
alignment is a separate component, not assumed by this record. -/
structure StructuredResolvedInv (jumpTables : List U32) (emission : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (labels : List LabelTarget) (groups : List FixupTarget)
    (initial : List valtype) (source : List instr) (start : Nat) (stack : List valtype) : Prop where
  localsEq : compilerLocals compiler = locals
  layout : CompilerLayout compiler stack
  inside : FixupsInside groups compiler.function.code.val.length
  code : StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals (resolvedCode compiler.function.code.val groups)
    labels initial source start compiler.function.code.val.length stack

/-- Every checked ordinary callback extends the resolved structured prefix.
This consumes its literal emission theorem and typed slot operands. -/
theorem Lowered.structured_resolved_advance {jumpTables : List U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emission types functions returns locals labels groups initial source start stack instruction emitted output}
    (lowered : Lowered before after emitted output)
    (invariant : StructuredResolvedInv jumpTables emission before types functions returns locals labels groups initial source start stack)
    (head : emission stack instruction [emitted] output)
    (ordinary : ∀ depths fallback, instruction ≠ .BR_TABLE depths fallback) :
    StructuredResolvedInv jumpTables emission after types functions returns locals labels groups initial (source ++ [instruction]) start output := by
  refine ⟨lowered.2.2.1.trans invariant.localsEq, lowered.2.1, ?_, ?_⟩
  · intro group member site atSite
    have old := invariant.inside group member site atSite
    simp only [lowered.1, List.length_append, List.length_singleton]
    omega
  · have resolved := resolved_code_append_code before.function.code.val [emitted] groups invariant.inside
    have sourceCode : StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals (resolvedCode before.function.code.val groups)
        labels initial source start (resolvedCode before.function.code.val groups).length stack := by
      simpa only [resolved_code_length] using invariant.code
    have advanced := sourceCode.emit head ordinary
    simpa only [lowered.1, resolved, List.length_append, resolved_code_length] using advanced

end Itasca.Runtime.Compiler

end

/-! ## StructuredSuspendedPrefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- A suspended parent owns only the bytecode before its child-entry cursor.
Later child emission and fixups may freely change the remaining suffix. -/
def StructuredSuspendedPrefix (jumpTables : List U32) (emission : List valtype → instr → List Bytecode → List valtype → Prop) (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (labels : List LabelTarget) (before : List valtype)
    (source : List instr) (start cursor : Nat) (stack : List valtype) : Prop :=
  cursor ≤ code.length ∧
    StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals (code.take cursor) labels before source start cursor stack

theorem StructuredSuspendedPrefix.full {jumpTables : List U32} {emission types functions returns locals code labels before source start cursor stack}
    (suspended : StructuredSuspendedPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before source start cursor stack) :
    StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before source start cursor stack := by
  simpa only [List.take_append_drop] using suspended.2.extend (code.drop cursor)

theorem StructuredSuspendedPrefix.stable {jumpTables : List U32} {emission types functions returns locals code labels before source start cursor stack}
    (suspended : StructuredSuspendedPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before source start cursor stack)
    (changed : List Bytecode) (bound : cursor ≤ changed.length)
    (same : changed.take cursor = code.take cursor) :
    StructuredSuspendedPrefix (jumpTables := jumpTables) emission types functions returns locals changed labels before source start cursor stack :=
  ⟨bound, same ▸ suspended.2⟩

theorem StructuredSuspendedPrefix.extend {jumpTables : List U32} {emission types functions returns locals code labels before source start cursor stack}
    (suspended : StructuredSuspendedPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before source start cursor stack)
    (emitted : List Bytecode) :
    StructuredSuspendedPrefix (jumpTables := jumpTables) emission types functions returns locals (code ++ emitted) labels before source start cursor stack := by
  have bound := suspended.1
  apply suspended.stable (code ++ emitted) (by simp; omega)
  exact List.take_append_of_le_length suspended.1

theorem StructuredPrefix.suspend {jumpTables : List U32} {emission types functions returns locals code labels before source start stack}
    (current : StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before source start code.length stack) :
    StructuredSuspendedPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before source start code.length stack :=
  ⟨Nat.le_refl _, by simpa using current⟩

/-- Once the child is closed, its syntactic certificate is appended to the
saved parent prefix at the exact retained entry cursor. -/
theorem StructuredSuspendedPrefix.resume {jumpTables : List U32} {emission types functions returns locals code labels before source start cursor stack
    more finish output}
    (suspended : StructuredSuspendedPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before source start cursor stack)
    (child : StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals code labels stack more cursor finish output) :
    StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before (source ++ more) start finish output :=
  suspended.full.append child

theorem StructuredSuspendedPrefix.resume_dead {jumpTables : List U32} {emission types functions returns locals code labels before source start cursor stack
    more finish}
    (suspended : StructuredSuspendedPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before source start cursor stack)
    (child : StructuredDeadPrefix (jumpTables := jumpTables) emission types functions returns locals code labels stack more cursor finish) :
    StructuredDeadPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before (source ++ more) start finish :=
  suspended.full.terminal child

end Itasca.Runtime.Compiler

end

/-! ## StructuredPrefixZipper -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std
/-- A terminal suspended parent owns just the code before its child, exactly
as a live suspended parent does. No instruction in an unentered child is needed. -/
def StructuredSuspendedTerminal (jumpTables : List U32) (emission : List valtype → instr → List Bytecode → List valtype → Prop) (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (labels : List LabelTarget) (before : List valtype)
    (source : List instr) (start cursor : Nat) : Prop :=
  cursor ≤ code.length ∧ StructuredDeadPrefix (jumpTables := jumpTables) emission types functions returns locals (code.take cursor)
    labels before source start cursor

theorem StructuredSuspendedTerminal.full {jumpTables : List U32} {emission types functions returns locals code labels before source start cursor}
    (saved : StructuredSuspendedTerminal (jumpTables := jumpTables) emission types functions returns locals code labels before source start cursor) :
    StructuredDeadPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before source start cursor := by
  simpa only [List.take_append_drop] using saved.2.extend (code.drop cursor)

theorem StructuredSuspendedTerminal.stable {jumpTables : List U32} {emission types functions returns locals code labels before source start cursor}
    (saved : StructuredSuspendedTerminal (jumpTables := jumpTables) emission types functions returns locals code labels before source start cursor)
    (changed : List Bytecode) (bound : cursor ≤ changed.length)
    (same : changed.take cursor = code.take cursor) :
    StructuredSuspendedTerminal (jumpTables := jumpTables) emission types functions returns locals changed labels before source start cursor :=
  ⟨bound, same ▸ saved.2⟩

theorem StructuredSuspendedTerminal.extend {jumpTables : List U32} {emission types functions returns locals code labels before source start cursor}
    (saved : StructuredSuspendedTerminal (jumpTables := jumpTables) emission types functions returns locals code labels before source start cursor)
    (emitted : List Bytecode) :
    StructuredSuspendedTerminal (jumpTables := jumpTables) emission types functions returns locals (code ++ emitted) labels before source start cursor := by
  have bound := saved.1
  exact saved.stable (code ++ emitted) (by simp; omega) (List.take_append_of_le_length bound)

theorem StructuredDeadPrefix.suspend {jumpTables : List U32} {emission types functions returns locals code labels before source start}
    (current : StructuredDeadPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before source start code.length) :
    StructuredSuspendedTerminal (jumpTables := jumpTables) emission types functions returns locals code labels before source start code.length :=
  ⟨Nat.le_refl _, by simpa using current⟩

/-- A parent either waits for an entered child's typed result, already has a
terminal prefix, or itself belongs to an unentered source subtree. -/
def StructuredParentPrefix (jumpTables : List U32) (emission : List valtype → instr → List Bytecode → List valtype → Prop) (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (labels : List LabelTarget) (parent child : SourceScope) : Prop :=
  if parent.entered then
    if child.entered then
      StructuredSuspendedPrefix (jumpTables := jumpTables) emission types functions returns locals code labels parent.input parent.source
        parent.bodyPc child.entry child.arguments
    else StructuredSuspendedTerminal (jumpTables := jumpTables) emission types functions returns locals code labels parent.input parent.source
        parent.bodyPc child.entry
  else True

theorem StructuredParentPrefix.extend {jumpTables : List U32} {emission types functions returns locals code labels parent child}
    (saved : StructuredParentPrefix (jumpTables := jumpTables) emission types functions returns locals code labels parent child)
    (emitted : List Bytecode) :
    StructuredParentPrefix (jumpTables := jumpTables) emission types functions returns locals (code ++ emitted) labels parent child := by
  unfold StructuredParentPrefix at *
  split at saved
  · split at saved
    · simpa only [‹parent.entered = true›, ‹child.entered = true›, ite_true] using saved.extend emitted
    · simpa only [‹parent.entered = true›, ‹¬child.entered = true›, ite_true, ite_false, Bool.false_eq_true] using saved.extend emitted
  · simp_all

/-- The saved parent chain mirrors the source validator zipper. Each parent
owns its prefix before the next child's opening instruction. -/
inductive StructuredParentPrefixes (jumpTables : List U32) (emission : List valtype → instr → List Bytecode → List valtype → Prop) (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) : List SourceScope → List LabelTarget → SourceScope → Prop where
  | root (current) : StructuredParentPrefixes (jumpTables := jumpTables) emission types functions returns locals code [] [] current
  | push {parents labels parent} (prior : StructuredParentPrefixes (jumpTables := jumpTables) emission types functions returns locals code parents labels parent)
      (label child) (shape : ScopeLabel parent label)
      (bound : child.entry ≤ code.length)
      (saved : StructuredParentPrefix (jumpTables := jumpTables) emission types functions returns locals code (label :: labels) parent child) :
      StructuredParentPrefixes (jumpTables := jumpTables) emission types functions returns locals code (parents ++ [parent]) (label :: labels) child

theorem StructuredParentPrefixes.extend {jumpTables : List U32} {emission types functions returns locals code parents labels current}
    (saved : StructuredParentPrefixes (jumpTables := jumpTables) emission types functions returns locals code parents labels current)
    (emitted : List Bytecode) :
    StructuredParentPrefixes (jumpTables := jumpTables) emission types functions returns locals (code ++ emitted) parents labels current := by
  induction saved with
  | root current => exact .root current
  | push prior label child shape bound saved ih =>
    exact .push ih label child shape (by simp; omega) (saved.extend emitted)


/-- Terminal evidence remains valid when the physical builder advances past
an unentered source subtree. The logical continuation cannot precede it. -/
theorem StructuredDeadPrefix.delay {jumpTables : List U32} {emission types functions returns locals code labels before source start cursor}
    (current : StructuredDeadPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before source start cursor)
    {later : Nat} (order : cursor ≤ later) :
    StructuredDeadPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before source start later := by
  intro suffix tail next final nextOrder bound
  exact current suffix tail next final (order.trans nextOrder) bound

theorem StructuredSuspendedTerminal.close_child {jumpTables : List U32} {emission types functions returns locals code labels before source start cursor}
    (saved : StructuredSuspendedTerminal (jumpTables := jumpTables) emission types functions returns locals code labels before source start cursor)
    (instruction : instr) :
    StructuredDeadPrefix (jumpTables := jumpTables) emission types functions returns locals code labels before (source ++ [instruction]) start code.length :=
  (saved.full.skip_source [instruction]).delay saved.1

theorem StructuredParentPrefix.resume {jumpTables : List U32} {emission types functions returns locals code labels parent child}
    (saved : StructuredParentPrefix (jumpTables := jumpTables) emission types functions returns locals code labels parent child)
    (parentEntered : parent.entered = true) (childEntered : child.entered = true)
    {source next stack}
    (closed : StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals code labels child.arguments source child.entry next stack) :
    StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals code labels parent.input (parent.source ++ source)
      parent.bodyPc next stack := by
  simp only [StructuredParentPrefix, parentEntered, childEntered, ite_true] at saved
  exact saved.resume closed

theorem StructuredParentPrefix.resume_dead {jumpTables : List U32} {emission types functions returns locals code labels parent child}
    (saved : StructuredParentPrefix (jumpTables := jumpTables) emission types functions returns locals code labels parent child)
    (parentEntered : parent.entered = true) (childEntered : child.entered = true)
    {source next}
    (closed : StructuredDeadPrefix (jumpTables := jumpTables) emission types functions returns locals code labels child.arguments source child.entry next) :
    StructuredDeadPrefix (jumpTables := jumpTables) emission types functions returns locals code labels parent.input (parent.source ++ source)
      parent.bodyPc next := by
  simp only [StructuredParentPrefix, parentEntered, childEntered, ite_true] at saved
  exact saved.resume_dead closed

theorem StructuredParentPrefix.close_unentered {jumpTables : List U32} {emission types functions returns locals code labels parent child}
    (saved : StructuredParentPrefix (jumpTables := jumpTables) emission types functions returns locals code labels parent child)
    (parentEntered : parent.entered = true) (childEntered : child.entered = false)
    (instruction : instr) :
    StructuredDeadPrefix (jumpTables := jumpTables) emission types functions returns locals code labels parent.input (parent.source ++ [instruction])
      parent.bodyPc code.length := by
  simp only [StructuredParentPrefix, parentEntered, childEntered, Bool.false_eq_true, ite_true, ite_false] at saved
  exact saved.close_child instruction

end Itasca.Runtime.Compiler

end

/-! ## StructuredUniversalPrefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std
theorem StructuredParentPrefixes.advance_current {jumpTables : List U32} {emission types functions returns locals code parents labels current}
    (saved : StructuredParentPrefixes (jumpTables := jumpTables) emission types functions returns locals code parents labels current)
    (instruction : instr) :
    StructuredParentPrefixes (jumpTables := jumpTables) emission types functions returns locals code parents labels (current.advance instruction) := by
  induction saved with
  | root current => exact .root _
  | push prior label child shape bound saved ih =>
    exact .push prior label (child.advance instruction) shape bound saved

/-- The live prefix invariant is uniform over every admissible future layout.
The source zipper fixes exact label types; the plans supply only future PCs and
exit liveness. This component retains no execution-correctness premise. -/
structure StructuredUniversalPrefix (jumpTables : List U32) (emission : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) (stack : List valtype) : Prop where
  localsEq : compilerLocals compiler = locals
  layout : CompilerLayout compiler stack
  sites : ∀ frame ∈ compiler.frames.val, FrameSites compiler.function.code.val frame
  prefixes : ∀ label labels groups,
    FramePlans compiler.function.code.val.length locals compiler.frames.val (label :: labels) groups →
    ScopeLabel current label → List.Forall₂ ScopeLabel parents.reverse labels →
    StructuredParentPrefixes (jumpTables := jumpTables) emission types functions returns locals (resolvedCode compiler.function.code.val groups)
      parents labels current ∧
    StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals (resolvedCode compiler.function.code.val groups)
      (label :: labels) current.input current.source current.bodyPc compiler.function.code.val.length stack

theorem StructuredUniversalPrefix.resolved {jumpTables : List U32} {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {emission types functions returns locals parents current stack}
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emission compiler types functions returns locals parents current stack)
    {label labels groups}
    (plans : FramePlans compiler.function.code.val.length locals compiler.frames.val (label :: labels) groups)
    (shape : ScopeLabel current label) (parentShapes : List.Forall₂ ScopeLabel parents.reverse labels) :
    StructuredResolvedInv (jumpTables := jumpTables) emission compiler types functions returns locals (label :: labels) groups
      current.input current.source current.bodyPc stack :=
  ⟨invariant.localsEq, invariant.layout, plans.inside invariant.sites,
    (invariant.prefixes label labels groups plans shape parentShapes).2⟩

/-- Actual ordinary emission preserves all possible control completions at
once. A later branch may strengthen liveness or add a fixup without requiring
any earlier ordinary callback to know that future decision. -/
theorem Lowered.structured_universal_advance {jumpTables : List U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emission types functions returns locals parents current stack instruction emitted output}
    (lowered : Lowered before after emitted output)
    (frames : after.frames = before.frames)
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emission before types functions returns locals parents current stack)
    (head : emission stack instruction [emitted] output)
    (ordinary : ∀ depths fallback, instruction ≠ .BR_TABLE depths fallback) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emission after types functions returns locals parents (current.advance instruction) output := by
  have codeEq := lowered.1
  have lengthOrder : before.function.code.val.length ≤ after.function.code.val.length := by
    simp [codeEq]
  refine ⟨lowered.2.2.1.trans invariant.localsEq, lowered.2.1, ?_, ?_⟩
  · intro frame member
    rw [frames] at member
    simpa only [codeEq] using (invariant.sites frame member).extend [emitted]
  · intro label labels groups plans shape parentShapes
    have oldPlans : FramePlans before.function.code.val.length locals before.frames.val
        (label :: labels) groups := by
      rw [← frames]
      exact plans.before lengthOrder
    have oldShape : ScopeLabel current label :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    have old := invariant.resolved oldPlans oldShape parentShapes
    have next := lowered.structured_resolved_advance old head ordinary
    have saved := (invariant.prefixes label labels groups oldPlans oldShape parentShapes).1
    have resolved := resolved_code_append_code before.function.code.val [emitted] groups old.inside
    refine ⟨?_, next.code⟩
    simpa only [codeEq, resolved] using (saved.extend [emitted]).advance_current instruction

end Itasca.Runtime.Compiler

end

/-! ## StructuredElseEvidence -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- An ELSE scope retains its completed then arm, resolved guard, and literal
skip shape. Future branch liveness may overapproximate branches in the then arm;
normal liveness remains the actual decision recorded when ELSE was entered. -/
def StructuredElseEvidence (jumpTables : List Aeneas.Std.U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (outer : List LabelTarget) (scope : SourceScope) (label : LabelTarget) : Prop :=
  if scope.entered then
    match scope.form with
    | .else_ _ condition yes yesExit noEntry yesNormal =>
      condition.val = slots locals + slots scope.input ∧
      code[scope.entry]? = some (.JumpIfZero condition noEntry) ∧
      StructuredCode emit types functions returns locals code jumpTables
        (⟨scope.front, scope.results, scope.results, label.target, yesExit, [], [], yesNormal, label.branchLive⟩ :: outer)
        scope.input yes (scope.entry + 1) yesExit (scope.front ++ scope.results) ∧
      IfSkip code yesExit noEntry label.target yesNormal ∧ scope.bodyPc = noEntry.val
    | _ => True
  else True

theorem StructuredElseEvidence.extend {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code outer scope label}
    (evidence : StructuredElseEvidence (jumpTables := jumpTables) emit types functions returns locals code outer scope label)
    (emitted : List Bytecode) :
    StructuredElseEvidence (jumpTables := jumpTables) emit types functions returns locals (code ++ emitted) outer scope label := by
  unfold StructuredElseEvidence at *
  split at evidence
  · rename_i entered
    simp only [entered, ite_true]
    cases form : scope.form <;> simp only [form] at evidence ⊢
    all_goals try trivial
    obtain ⟨condition, guard, body, skip, begin⟩ := evidence
    exact ⟨condition, fetch_extend guard emitted, body.extend emitted, skip.extend emitted, begin⟩
  · simp_all

theorem StructuredElseEvidence.advance {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code outer scope label}
    (evidence : StructuredElseEvidence (jumpTables := jumpTables) emit types functions returns locals code outer scope label)
    (instruction : instr) :
    StructuredElseEvidence (jumpTables := jumpTables) emit types functions returns locals code outer (scope.advance instruction) label := by
  simpa only [StructuredElseEvidence, SourceScope.advance, SourceScope.input] using evidence

/-- Completed arms are stored at every active ELSE frame, including suspended
parents. The source and label lists are ordered from innermost to outermost. -/
inductive StructuredElseFrames (jumpTables : List Aeneas.Std.U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) : List SourceScope → List LabelTarget → Prop where
  | nil : StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals code [] []
  | cons {scopes labels} (scope label)
      (current : StructuredElseEvidence (jumpTables := jumpTables) emit types functions returns locals code labels scope label)
      (outer : StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals code scopes labels) :
      StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals code (scope :: scopes) (label :: labels)

theorem StructuredElseFrames.extend {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code scopes labels}
    (evidence : StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals code scopes labels) (emitted : List Bytecode) :
    StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals (code ++ emitted) scopes labels := by
  induction evidence with
  | nil => exact .nil
  | cons scope label current outer ih => exact .cons scope label (current.extend emitted) ih

theorem StructuredElseFrames.advance {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code scopes labels scope label}
    (evidence : StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals code (scope :: scopes) (label :: labels))
    (instruction : instr) :
    StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals code (scope.advance instruction :: scopes) (label :: labels) := by
  cases evidence with
  | cons scope label current outer => exact .cons _ label (current.advance instruction) outer

/-- Completed-arm evidence is uniform over the same future plans as live and
terminal source prefixes. It is a separate syntactic component of the zipper. -/
def StructuredUniversalElse (jumpTables : List Aeneas.Std.U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) : Prop :=
  ∀ label labels groups,
    FramePlans compiler.function.code.val.length locals compiler.frames.val (label :: labels) groups →
    ScopeLabel current label → List.Forall₂ ScopeLabel parents.reverse labels →
    StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals (resolvedCode compiler.function.code.val groups)
      (current :: parents.reverse) (label :: labels)

theorem StructuredUniversalElse.append {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current}
    (invariant : StructuredUniversalElse (jumpTables := jumpTables) emit before types functions returns locals parents current)
    (sites : ∀ frame ∈ before.frames.val, FrameSites before.function.code.val frame)
    (emitted : List Bytecode) (instruction : instr)
    (codeEq : after.function.code.val = before.function.code.val ++ emitted)
    (framesEq : after.frames = before.frames) :
    StructuredUniversalElse (jumpTables := jumpTables) emit after types functions returns locals parents (current.advance instruction) := by
  intro label labels groups plans shape parentShapes
  have order : before.function.code.val.length ≤ after.function.code.val.length := by simp [codeEq]
  have oldPlans : FramePlans before.function.code.val.length locals before.frames.val (label :: labels) groups := by
    rw [← framesEq]
    exact plans.before order
  have oldShape : ScopeLabel current label :=
    ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
  have prior := invariant label labels groups oldPlans oldShape parentShapes
  rw [codeEq, resolved_code_append_code _ _ _ (oldPlans.inside sites)]
  exact (prior.extend emitted).advance instruction

end Itasca.Runtime.Compiler

end

/-! ## StructuredParentPrefixPop -/

section

namespace Itasca.Runtime.Compiler

/-- Closing the current source scope exposes exactly its suspended parent and
the unchanged remainder of the source zipper. -/
theorem StructuredParentPrefixes.pop {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code parents parent label labels child}
    (saved : StructuredParentPrefixes (jumpTables := jumpTables) emit types functions returns locals code (parents ++ [parent]) (label :: labels) child) :
    StructuredParentPrefixes (jumpTables := jumpTables) emit types functions returns locals code parents labels parent ∧
      ScopeLabel parent label ∧ child.entry ≤ code.length ∧
      StructuredParentPrefix (jumpTables := jumpTables) emit types functions returns locals code (label :: labels) parent child := by
  generalize physical : parents ++ [parent] = scopes at saved
  cases saved with
  | @push earlier outer previous prior inner current shape bound held =>
    have size : parents.length = earlier.length := by
      have lengths := congrArg List.length physical
      simp only [List.length_append, List.length_singleton] at lengths
      omega
    obtain ⟨sameParents, sameParent⟩ := List.append_inj physical size
    simp only [List.cons.injEq, and_true] at sameParent
    subst earlier previous
    exact ⟨prior, shape, bound, held⟩

end Itasca.Runtime.Compiler

end

/-! ## StructuredUniversalTerminal -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std
theorem TerminalEmission.structured_prefix {jumpTables : List Aeneas.Std.U32} {locals returns stack instruction emitted}
    (emission : TerminalEmission locals returns stack instruction emitted)
    {emit types functions code labels pc} (fetched : code[pc]? = some emitted) :
    StructuredDeadPrefix (jumpTables := jumpTables) emit types functions returns locals code labels stack [instruction] pc (pc + 1) := by
  cases emission with
  | unreachable => exact .unreachable fetched
  | return_ front source count position width => exact .return_ position width fetched

/-- Dead source prefixes retain their parent chain but do not assert a live
operand layout. Source suffixes are admitted only through a checked terminal
instruction already retained in the prefix. -/
structure StructuredUniversalTerminal (jumpTables : List Aeneas.Std.U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) : Prop where
  localsEq : compilerLocals compiler = locals
  sites : ∀ frame ∈ compiler.frames.val, FrameSites compiler.function.code.val frame
  prefixes : ∀ label labels groups,
    FramePlans compiler.function.code.val.length locals compiler.frames.val (label :: labels) groups →
    ScopeLabel current label → List.Forall₂ ScopeLabel parents.reverse labels →
    StructuredParentPrefixes (jumpTables := jumpTables) emit types functions returns locals (resolvedCode compiler.function.code.val groups)
      parents labels current ∧
    StructuredDeadPrefix (jumpTables := jumpTables) emit types functions returns locals (resolvedCode compiler.function.code.val groups)
      (label :: labels) current.input current.source current.bodyPc compiler.function.code.val.length

/-- Exact emission of UNREACHABLE or RETURN changes a live prefix into a
terminal one for every future control completion. -/
theorem StructuredUniversalPrefix.terminate {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current stack instruction emitted}
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emit before types functions returns locals parents current stack)
    (emission : TerminalEmission locals returns stack instruction emitted)
    (codeEq : after.function.code.val = before.function.code.val ++ [emitted])
    (framesEq : after.frames = before.frames) (localsEq : compilerLocals after = locals) :
    StructuredUniversalTerminal (jumpTables := jumpTables) emit after types functions returns locals parents (current.advance instruction) := by
  have lengthOrder : before.function.code.val.length ≤ after.function.code.val.length := by simp [codeEq]
  refine ⟨localsEq, ?_, ?_⟩
  · intro frame member
    rw [framesEq] at member
    simpa only [codeEq] using (invariant.sites frame member).extend [emitted]
  · intro label labels groups plans shape parentShapes
    have oldPlans : FramePlans before.function.code.val.length locals before.frames.val (label :: labels) groups := by
      rw [← framesEq]
      exact plans.before lengthOrder
    have oldShape : ScopeLabel current label :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    have old := invariant.resolved oldPlans oldShape parentShapes
    have saved := (invariant.prefixes label labels groups oldPlans oldShape parentShapes).1
    have resolved := resolved_code_append_code before.function.code.val [emitted] groups old.inside
    refine ⟨?_, ?_⟩
    · simpa only [codeEq, resolved] using (saved.extend [emitted]).advance_current instruction
    · have fetched : (resolvedCode before.function.code.val groups ++ [emitted])[before.function.code.val.length]? = some emitted := by simp [← resolved_code_length before.function.code.val groups]
      have terminal := (old.code.extend [emitted]).terminal (emission.structured_prefix fetched)
      simpa only [codeEq, resolved, List.length_append, List.length_singleton, SourceScope.advance, SourceScope.input] using terminal

/-- An omitted ordinary instruction in an unreachable source suffix extends
only the source prefix. This consumes exact unchanged-code/frame equations. -/
theorem StructuredUniversalTerminal.skip {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current}
    (invariant : StructuredUniversalTerminal (jumpTables := jumpTables) emit before types functions returns locals parents current)
    (instruction : instr)
    (codeEq : after.function.code.val = before.function.code.val)
    (framesEq : after.frames = before.frames) (localsEq : compilerLocals after = locals) :
    StructuredUniversalTerminal (jumpTables := jumpTables) emit after types functions returns locals parents (current.advance instruction) := by
  refine ⟨localsEq, ?_, ?_⟩
  · simpa only [codeEq, framesEq] using invariant.sites
  · intro label labels groups plans shape parentShapes
    have oldPlans : FramePlans before.function.code.val.length locals before.frames.val (label :: labels) groups := by
      simpa only [codeEq, framesEq] using plans
    have oldShape : ScopeLabel current label :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    obtain ⟨saved, terminal⟩ := invariant.prefixes label labels groups oldPlans oldShape parentShapes
    exact ⟨by simpa only [codeEq] using saved.advance_current instruction,
      by simpa only [codeEq, SourceScope.advance, SourceScope.input] using terminal.skip_source [instruction]⟩

end Itasca.Runtime.Compiler

end
