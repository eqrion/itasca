import Itasca.Runtime.Interp.Relations.CopyRel
import Itasca.Runtime.Interp.Relations.PrefixEffect
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

@[step] theorem select_effect (exec : runtime.interp.Execution) (base : Usize) (left right condition : U32)
    (hc : base.val+condition.val < exec.slots.length)
    (hl : base.val+left.val < exec.slots.length)
    (hr : base.val+right.val < exec.slots.length) :
    runtime.interp.execute_select exec base left right condition ⦃ out =>
      out.1 = .Ok () ∧ SlotsEffect exec out.2
        (if UScalar.cast .U32 exec.slots.val[base.val+condition.val]! = 0#u32
         then copyWords exec.slots.val (base.val+left.val) (base.val+right.val) 1
         else exec.slots.val) ⦄ := by
  unfold runtime.interp.execute_select
  step* <;> simp_all [SlotsEffect,copyWords,_root_.getElem!_pos]

@[step] theorem select2_effect (exec : runtime.interp.Execution) (base : Usize) (left right condition : U32)
    (hc : base.val+condition.val < exec.slots.length)
    (hl : base.val+left.val+2 ≤ exec.slots.length)
    (hr : base.val+right.val+2 ≤ exec.slots.length) :
    runtime.interp.execute_select2 exec base left right condition ⦃ out =>
      out.1 = .Ok () ∧ SlotsEffect exec out.2
        (if UScalar.cast .U32 exec.slots.val[base.val+condition.val]! = 0#u32
         then copyWords exec.slots.val (base.val+left.val) (base.val+right.val) 2
         else exec.slots.val) ⦄ := by
  unfold runtime.interp.execute_select2
  simp only [lift,bind_ok,alloc.vec.Vec.deref_mut]
  step* <;> simp_all [SlotsEffect,_root_.getElem!_pos] <;> first | assumption | omega
end Itasca.Runtime.Interp
