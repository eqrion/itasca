import Exec.Code.Local.Control.Common.StructuredParentPrefixPop
namespace Exec.Code

open Aeneas.Std
theorem StructuredPrefix.suspend_after {emit types functions returns locals labels initial source start stack}
    {code : List Bytecode}
    (prior : StructuredPrefix emit types functions returns locals code labels initial source start code.length stack)
    (emitted : List Bytecode) :
    StructuredSuspendedPrefix emit types functions returns locals (code ++ emitted) labels initial source start code.length stack :=
  prior.suspend.extend emitted


/-- ELSE changes a child's source form and current instruction list while
leaving the suspended parent's entry hole and argument vector unchanged. -/
theorem StructuredParentPrefix.change_child {emit types functions returns locals code labels parent before after}
    (saved : StructuredParentPrefix emit types functions returns locals code labels parent before)
    (entered : after.entered = before.entered) (entry : after.entry = before.entry)
    (arguments : after.arguments = before.arguments) :
    StructuredParentPrefix emit types functions returns locals code labels parent after := by
  simpa only [StructuredParentPrefix, entered, entry, arguments] using saved

theorem StructuredParentPrefixes.change_current {emit types functions returns locals code parents labels before after}
    (saved : StructuredParentPrefixes emit types functions returns locals code parents labels before)
    (entered : after.entered = before.entered) (entry : after.entry = before.entry)
    (arguments : after.arguments = before.arguments) :
    StructuredParentPrefixes emit types functions returns locals code parents labels after := by
  induction saved with
  | root current => exact .root after
  | push prior label child shape bound held ih =>
    exact .push prior label after shape (by simpa only [entry] using bound)
      (held.change_child entered entry arguments)

end Exec.Code

