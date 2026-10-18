import SpecExt.Host

namespace Exec.Spec

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

@[simp] theorem instrsDepth_nil : instrsDepth [] = 0 := rfl

@[simp] theorem instrsDepth_append (xs ys : List admininstr) :
    instrsDepth (xs ++ ys) = max (instrsDepth xs) (instrsDepth ys) := by
  induction xs with
  | nil => simp [instrsDepth]
  | cons ai rest ih => simp [instrsDepth, ih, Nat.max_assoc]

@[simp] theorem instrsDepth_singleton (ai : admininstr) :
    instrsDepth [ai] = instrDepth ai := by simp [instrsDepth]

@[simp] theorem frameDepth_frame (z : state) (arity : Nat) (f : frame) (body : List admininstr) :
    frameDepth (.mk_config z [.FRAME_ arity f body]) = instrsDepth body + 1 := by
  simp [frameDepth, instrDepth]

@[simp] theorem frameDepth_label (z : state) (arity : Nat) (cont : List instr) (body : List admininstr) :
    frameDepth (.mk_config z [.LABEL_ arity cont body]) = instrsDepth body := by
  simp [frameDepth, instrDepth]

end Exec.Spec
