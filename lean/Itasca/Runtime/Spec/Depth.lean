import SpecExt.Host

/-!
Administrative frame depth, excluding the ambient frame. Source invocation resource arguments use this nesting measure independently of runtime slots.
-/

namespace Itasca.Runtime.Spec

mutual
  /-- Number of nested administrative frames in an instruction. -/
  def instrDepth : admininstr → Nat
    | .FRAME_ _ _ body => instrsDepth body + 1
    | .LABEL_ _ _ body => instrsDepth body
    | _ => 0

  /-- Maximum frame nesting in an administrative instruction sequence. -/
  def instrsDepth : List admininstr → Nat
    | [] => 0
    | ai :: rest => max (instrDepth ai) (instrsDepth rest)
end

/-- FRAME_ nesting of a decoded configuration, excluding its ambient frame. -/
def frameDepth : config → Nat
  | .mk_config _ body => instrsDepth body

@[simp] theorem instrs_depth_nil : instrsDepth [] = 0 := rfl

@[simp] theorem instrs_depth_append (xs ys : List admininstr) :
    instrsDepth (xs ++ ys) = max (instrsDepth xs) (instrsDepth ys) := by
  induction xs with
  | nil => simp [instrsDepth]
  | cons ai rest ih => simp [instrsDepth, ih, Nat.max_assoc]

@[simp] theorem instrs_depth_singleton (ai : admininstr) :
    instrsDepth [ai] = instrDepth ai := by simp [instrsDepth]

end Itasca.Runtime.Spec
