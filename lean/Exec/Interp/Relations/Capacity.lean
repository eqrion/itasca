import Exec.Interp.Relations.FrameBindings
import Exec.Code.Local.Capacity.OperandBounds

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- A represented region ends within storage, including an empty region at a
known valid base. -/
theorem WordsAt.end_le {words : List U64} {base : Nat} {bits : List Nat}
    (represented : WordsAt words base bits) (start : base ≤ words.length) :
    base + bits.length ≤ words.length := by
  by_cases empty : bits.length = 0
  · omega
  · have last := (represented (bits.length - 1) (by omega)).1
    omega

/-- The allocated capacity is for the function actually selected by the frame. -/
theorem FrameBinding.capacity {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame} {source : Abs.AFrame}
    (binding : FrameBinding store exec raw source)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (instanceLookup : store.instances.val[raw.instance.val]? = some inst)
    (functionLookup : inst.module.functions.val[raw.function.val]? = some compiled) :
    raw.base.val + compiled.slot_count.val ≤ exec.slots.length := by
  obtain ⟨actual, fn, actualCode, signature, _, _, hi, _, _, hc, _, _, _, _, capacity⟩ := binding
  have same : actual = inst := Option.some.inj (hi.symm.trans instanceLookup)
  subst actual
  have sameCode : actualCode = compiled := Option.some.inj (hc.symm.trans functionLookup)
  exact sameCode ▸ capacity

theorem FrameBinding.base_bound {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame} {source : Abs.AFrame}
    (binding : FrameBinding store exec raw source) : raw.base.val ≤ exec.slots.val.length := by
  obtain ⟨_, _, compiled, _, _, _, _, _, _, _, _, _, _, _, capacity⟩ := binding
  change raw.base.val + compiled.slot_count.val ≤ exec.slots.val.length at capacity
  omega

/-- Live-value capacity follows from representation and frame allocation. -/
theorem FrameSlots.capacity {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame} {source : Abs.AFrame}
    (represented : FrameSlots exec raw source) (binding : FrameBinding store exec raw source) :
    raw.base.val + Code.slots ((source.locals ++ source.vals).map Code.valueType) ≤ exec.slots.length := by
  have bound := represented.end_le binding.base_bound
  simpa only [Code.encodeValues_length] using bound

end Exec.Interp
