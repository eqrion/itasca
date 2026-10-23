import Exec.Code.Local.Control.Table.StructuredCodeAlgebra
namespace Exec.Code
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

theorem StructuredPrefix.branchIf {jumpTables : List U32} {emission types functions returns locals code labels stack depth label dst src count cond resume pc}
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
theorem StructuredDeadPrefix.branchTable
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
end Exec.Code

