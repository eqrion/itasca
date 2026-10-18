import Exec.Abs.ControlSafety

namespace Exec.Abs

/-- Generated source typing exposes the nesting bound below every active
label. This ensures downward branch transfers preserve saved outer prefixes. -/
theorem codeStack_outer_heights {C : context} {labels : List Label}
    {stack results : List valtype} {code : List instr}
    (h : CodeStackTyped C labels stack code results)
    (depth : Nat) (target : Label) (lookup : labels[depth]? = some target) :
    ∀ label ∈ labels.drop (depth + 1), label.height ≤ target.height := by
  induction h generalizing depth target with
  | outer _ => simp at lookup
  | @label label labels saved operands code results height nesting hc cont after ih =>
    cases depth with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
      subst target
      simpa only [List.drop_succ_cons, List.drop_zero] using nesting
    | succ depth =>
      simp only [List.getElem?_cons_succ] at lookup
      simpa only [List.drop_succ_cons] using ih depth target lookup

theorem FrameTyped.outer_heights {s : store} {frame : AFrame} {incoming : List valtype}
    (typed : FrameTyped s frame incoming)
    (depth : Nat) (target : Label) (lookup : frame.labels[depth]? = some target) :
    ∀ label ∈ frame.labels.drop (depth + 1), label.height ≤ target.height := by
  cases typed with
  | mk C bindings localTypes locals values returns code wf =>
    exact codeStack_outer_heights code depth target lookup

end Exec.Abs
