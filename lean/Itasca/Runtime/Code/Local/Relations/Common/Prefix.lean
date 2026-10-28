import Itasca.Runtime.Code.Local.Relations.Common.Concatenation
import Itasca.Runtime.Code.Local.Relations.Common.Extension
namespace Itasca.Runtime.Code
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

/-- A terminal prefix gives a certificate even for arbitrary uncompiled source
suffixes. The proof is obtained from a literal terminal bytecode constructor. -/
def DeadCodePrefix (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (labels : List LabelTarget)
    (before : List valtype) (source : List instr) (pc cursor : Nat) : Prop :=
  ∀ suffix tail next final, cursor ≤ next → next ≤ (code ++ suffix).length →
    CodeRel types functions returns locals (code ++ suffix) labels before (source ++ tail) pc next final

end Itasca.Runtime.Code
