import Itasca.Runtime.Interp.Relations.ScalarDispatch

/-! Exact state effects of the extracted copy, constant, and jump handlers.
Bounds are slot/frame bounds, independent of compiler correctness. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (platform : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (alloc : runtime.platform.Alloc A)

@[step] theorem const32_effect (exec : runtime.interp.Execution)
    (base : Usize) (dst value : U32)
    (hd : base.val + dst.val < exec.slots.length) :
    runtime.interp.execute_const32 exec base dst value
      ⦃ out => out.1 = .Ok () ∧ SlotsEffect exec out.2
        (exec.slots.val.set (base.val + dst.val) (UScalar.cast .U64 value)) ⦄ := by
  unfold runtime.interp.execute_const32
  step* <;> simp_all [SlotsEffect]

@[step] theorem const64_effect (exec : runtime.interp.Execution)
    (base : Usize) (dst : U32) (value : U64)
    (hd : base.val + dst.val < exec.slots.length) :
    runtime.interp.execute_const64 exec base dst value
      ⦃ out => out.1 = .Ok () ∧ SlotsEffect exec out.2
        (exec.slots.val.set (base.val + dst.val) value) ⦄ := by
  unfold runtime.interp.execute_const64
  step* <;> simp_all [SlotsEffect]

@[step] theorem copy_effect (exec : runtime.interp.Execution)
    (base : Usize) (dst src : U32)
    (hs : base.val + src.val < exec.slots.length)
    (hd : base.val + dst.val < exec.slots.length) :
    runtime.interp.execute_copy exec base dst src
      ⦃ out => out.1 = .Ok () ∧ SlotsEffect exec out.2
        (exec.slots.val.set (base.val + dst.val)
          exec.slots.val[base.val + src.val]!) ⦄ := by
  unfold runtime.interp.execute_copy
  step* <;> simp_all [SlotsEffect, _root_.getElem!_pos]

/-- A jump changes only the selected frame's program counter. -/
def JumpEffect (before after : runtime.interp.Execution) (index : Nat) (target : U32) : Prop :=
  ∃ frame, before.frames.val[index]? = some frame ∧
    after.frames.val = before.frames.val.set index { frame with pc := target } ∧
    { after with frames := before.frames } = before

@[step] theorem jump_effect (exec : runtime.interp.Execution)
    (index : Usize) (target : U32) (hi : index.val < exec.frames.length) :
    runtime.interp.execute_jump exec index target
      ⦃ out => out.1 = .Ok () ∧ JumpEffect exec out.2 index.val target ⦄ := by
  unfold runtime.interp.execute_jump
  step* <;> simp_all [JumpEffect, _root_.getElem!_pos]

@[step] theorem jump_if_zero_effect (exec : runtime.interp.Execution)
    (index base : Usize) (cond target : U32)
    (hi : index.val < exec.frames.length)
    (hc : base.val + cond.val < exec.slots.length) :
    runtime.interp.execute_jump_if_zero exec index base cond target
      ⦃ out => out.1 = .Ok () ∧
        if UScalar.cast .U32 exec.slots.val[base.val + cond.val]! = 0#u32
        then JumpEffect exec out.2 index.val target else out.2 = exec ⦄ := by
  unfold runtime.interp.execute_jump_if_zero
  step* <;> simp_all [JumpEffect, _root_.getElem!_pos]

@[step] theorem jump_if_non_zero_effect (exec : runtime.interp.Execution)
    (index base : Usize) (cond target : U32)
    (hi : index.val < exec.frames.length)
    (hc : base.val + cond.val < exec.slots.length) :
    runtime.interp.execute_jump_if_non_zero exec index base cond target
      ⦃ out => out.1 = .Ok () ∧
        if UScalar.cast .U32 exec.slots.val[base.val + cond.val]! = 0#u32
        then out.2 = exec else JumpEffect exec out.2 index.val target ⦄ := by
  unfold runtime.interp.execute_jump_if_non_zero
  step* <;> simp_all [JumpEffect, _root_.getElem!_pos]

end Itasca.Runtime.Interp
