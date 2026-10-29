import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition

/-!
Extension of source/code segment and guarded-skip certificates.

Main declarations: `Segment.extend` and `IfSkip.extend`. A direct consumer is `Compiler.Local.Relations.Prefix.Prefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

theorem Segment.extend {code pc instructions next} (segment : Segment code pc instructions next)
    (suffix : List Bytecode) : Segment (code ++ suffix) pc instructions next := by
  obtain ⟨front, back, rfl, position, endpoint⟩ := segment
  exact ⟨front, back ++ suffix, by simp only [List.append_assoc], position, endpoint⟩

theorem fetch_extend {code : List Bytecode} {pc : Nat} {instruction : Bytecode}
    (found : code[pc]? = some instruction) (suffix : List Bytecode) :
    (code ++ suffix)[pc]? = some instruction :=
  (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found

theorem IfSkip.extend {code yesExit noEntry exit yesNormal}
    (skip : IfSkip code yesExit noEntry exit yesNormal) (suffix : List Bytecode) :
    IfSkip (code ++ suffix) yesExit noEntry exit yesNormal := by
  cases skip with
  | emitted fragment => exact .emitted (fragment.extend suffix)
  | direct normal otherwise => exact .direct normal otherwise

end Itasca.Runtime.Compiler
