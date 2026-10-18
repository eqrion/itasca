import Exec.Code.Local.Callbacks.Common.ParentPrefixPop
namespace Exec.Code

/-- ELSE changes a child's source form and current instruction list while
leaving the suspended parent's entry hole and argument vector unchanged. -/
theorem ParentPrefix.change_child {types functions returns locals code labels parent before after}
    (saved : ParentPrefix types functions returns locals code labels parent before)
    (entered : after.entered = before.entered) (entry : after.entry = before.entry)
    (arguments : after.arguments = before.arguments) :
    ParentPrefix types functions returns locals code labels parent after := by
  simpa only [ParentPrefix, entered, entry, arguments] using saved

theorem ParentPrefixes.change_current {types functions returns locals code parents labels before after}
    (saved : ParentPrefixes types functions returns locals code parents labels before)
    (entered : after.entered = before.entered) (entry : after.entry = before.entry)
    (arguments : after.arguments = before.arguments) :
    ParentPrefixes types functions returns locals code parents labels after := by
  induction saved with
  | root current => exact .root after
  | push prior label child shape bound held ih =>
    exact .push prior label after shape (by simpa only [entry] using bound)
      (held.change_child entered entry arguments)

end Exec.Code
