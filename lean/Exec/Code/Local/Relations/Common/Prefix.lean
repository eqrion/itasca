import Exec.Code.Local.Relations.Common.Concatenation
import Exec.Code.Local.Relations.Common.Extension
namespace Exec.Code
open Aeneas.Std

/-- A builder invariant for a still-open source prefix. Its hole is another
syntactic CodeRel certificate, never an execution or simulation premise. Unlike
a completed CodeRel, an unfinished hole does not assert a live normal exit;
a later RETURN or branch can close it without certifying unreachable suffixes. -/
def CodePrefix (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (labels : List LabelTarget)
    (before : List valtype) (source : List instr) (pc cursor : Nat) (stack : List valtype) : Prop :=
  ∀ suffix tail next final, CodeRel types functions returns locals (code ++ suffix) labels stack tail cursor next final →
    CodeRel types functions returns locals (code ++ suffix) labels before (source ++ tail) pc next final

theorem CodePrefix.empty (types functions returns locals code labels stack pc) :
    CodePrefix types functions returns locals code labels stack [] pc pc stack := by
  intro suffix tail next final rest
  simpa using rest

theorem CodePrefix.of_relation {types functions returns locals code labels before source pc cursor stack}
    (relation : CodeRel types functions returns locals code labels before source pc cursor stack) :
    CodePrefix types functions returns locals code labels before source pc cursor stack := by
  intro suffix tail next final rest
  exact (relation.extend suffix).append rest

theorem CodePrefix.append {types functions returns locals code labels before source pc cursor stack
    more finish output}
    (first : CodePrefix types functions returns locals code labels before source pc cursor stack)
    (second : CodePrefix types functions returns locals code labels stack more cursor finish output) :
    CodePrefix types functions returns locals code labels before (source ++ more) pc finish output := by
  intro suffix tail next final rest
  simpa [List.append_assoc] using first suffix _ _ _ (second suffix _ _ _ rest)

theorem CodePrefix.linear {types functions returns locals code labels before middle instruction emitted pc cursor}
    (head : LinearEmission locals before instruction emitted middle)
    (fragment : Segment code pc emitted cursor) :
    CodePrefix types functions returns locals code labels before [instruction] pc cursor middle := by
  intro suffix tail next final rest
  exact .linear head (fragment.extend suffix) rest

theorem CodePrefix.call {types functions returns locals code labels front params results index base pc}
    (signature : functions[index.val]? = some ⟨.mk_list params, .mk_list results⟩)
    (arguments : base.val = slots locals + slots front)
    (instruction : code[pc]? = some (.Call index base)) :
    CodePrefix types functions returns locals code labels (front ++ params) [.CALL (.mk_uN index.val)]
      pc (pc + 1) (front ++ results) := by
  intro suffix tail next final rest
  exact .call signature arguments (fetch_extend instruction suffix) rest

theorem CodePrefix.branchIf {types functions returns locals code labels stack depth label dst src count cond resume pc}
    (lookup : labels[depth]? = some label) (live : label.branchLive = true)
    (layout : BranchLayout locals stack label dst src count)
    (condition : cond.val = slots locals + slots stack)
    (fragment : Segment code pc (branchIfInstructions dst src count label.target cond resume) resume.val) :
    CodePrefix types functions returns locals code labels (stack ++ [.I32]) [.BR_IF (.mk_uN depth)]
      pc resume.val stack := by
  intro suffix tail next final rest
  exact .branchIf lookup live layout condition (fragment.extend suffix) rest

/-- A terminal prefix gives a certificate even for arbitrary uncompiled source
suffixes. The proof is obtained from a literal terminal bytecode constructor. -/
def DeadCodePrefix (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (labels : List LabelTarget)
    (before : List valtype) (source : List instr) (pc cursor : Nat) : Prop :=
  ∀ suffix tail next final, cursor ≤ next → next ≤ (code ++ suffix).length →
    CodeRel types functions returns locals (code ++ suffix) labels before (source ++ tail) pc next final

theorem DeadCodePrefix.unreachable {types functions returns locals code labels stack pc}
    (found : code[pc]? = some .Unreachable) :
    DeadCodePrefix types functions returns locals code labels stack [.UNREACHABLE] pc (pc + 1) := by
  intro suffix tail next final order bound
  exact .unreachable (fetch_extend found suffix) order bound

theorem DeadCodePrefix.return_ {types functions returns locals code labels front src count pc}
    (source : src.val = slots locals + slots front) (size : count.val = slots returns)
    (found : code[pc]? = some (.Return src count)) :
    DeadCodePrefix types functions returns locals code labels (front ++ returns) [.RETURN] pc (pc + 1) := by
  intro suffix tail next final order bound
  exact .return_ source size (fetch_extend found suffix) order bound

theorem DeadCodePrefix.branch {types functions returns locals code labels stack depth label dst src count pc cursor}
    (lookup : labels[depth]? = some label) (live : label.branchLive = true)
    (layout : BranchLayout locals stack label dst src count)
    (fragment : Segment code pc (branchInstructions dst src count label.target) cursor) :
    DeadCodePrefix types functions returns locals code labels stack [.BR (.mk_uN depth)] pc cursor := by
  intro suffix tail next final order bound
  exact .branch lookup live layout (fragment.extend suffix) order bound

theorem CodePrefix.terminal {types functions returns locals code labels before source pc cursor stack more finish}
    (first : CodePrefix types functions returns locals code labels before source pc cursor stack)
    (terminal : DeadCodePrefix types functions returns locals code labels stack more cursor finish) :
    DeadCodePrefix types functions returns locals code labels before (source ++ more) pc finish := by
  intro suffix tail next final order bound
  simpa [List.append_assoc] using first suffix _ _ _ (terminal suffix _ _ _ order bound)

theorem DeadCodePrefix.skip_source {types functions returns locals code labels before source pc cursor}
    (dead : DeadCodePrefix types functions returns locals code labels before source pc cursor)
    (skipped : List instr) :
    DeadCodePrefix types functions returns locals code labels before (source ++ skipped) pc cursor := by
  intro suffix tail next final order bound
  simpa [List.append_assoc] using dead suffix (skipped ++ tail) next final order bound

/-- Prefix evidence survives later bytecode emission without assuming that the
old end-of-code already admitted a valid continuation. -/
theorem CodePrefix.extend {types functions returns locals code labels before source pc cursor stack}
    (evidence : CodePrefix types functions returns locals code labels before source pc cursor stack)
    (emitted : List Bytecode) :
    CodePrefix types functions returns locals (code ++ emitted) labels before source pc cursor stack := by
  intro suffix tail next final rest
  simpa only [List.append_assoc] using evidence (emitted ++ suffix) tail next final
    (by simpa only [List.append_assoc] using rest)

theorem DeadCodePrefix.extend {types functions returns locals code labels before source pc cursor}
    (evidence : DeadCodePrefix types functions returns locals code labels before source pc cursor)
    (emitted : List Bytecode) :
    DeadCodePrefix types functions returns locals (code ++ emitted) labels before source pc cursor := by
  intro suffix tail next final order bound
  simpa only [List.append_assoc] using evidence (emitted ++ suffix) tail next final order
    (by simpa only [List.append_assoc] using bound)

end Exec.Code
