import Exec.Interp.Numeric.Integer.NumericValues
import Exec.Interp.Numeric.Integer.NumericDispatch

namespace Exec.Interp
open Aeneas Aeneas.Std Abs.Numeric

theorem step_integer_values {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (op : Instruction) (left right : U32) (front : List val)
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetched : compiled.code.val[raw.pc.val]? = some (Code.integerInstruction op left left right))
    (pcBound : raw.pc.val < U32.max)
    (values : ValuesAt exec.slots.val raw.base.val (front ++ op.operands a b))
    (hl : left.val = Code.slots (front.map Code.valueType))
    (hr : right.val = left.val + (op.arity - 1)) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ pc : U32, pc.val = raw.pc.val + 1 ∧
        NumericValuesEffect op a b
          { exec with frames := exec.frames.set index { raw with pc := pc } }
          raw.base.val front (out.1, out.2.1) ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
    (Code.integerInstruction op left left right) last hf hi hc fetched pcBound
  intro pc position
  rw [dispatch_integer_eq]
  obtain ⟨out, equation, effect⟩ := WP.spec_imp_exists (integer_values floats
    { exec with frames := exec.frames.set index { raw with pc := pc } } raw.base op left right front a b values hl hr)
  rw [equation]
  rcases out with ⟨status, changed⟩
  simp only [bind_ok]
  with_unfolding_all apply WP.spec.ret
  exact ⟨rfl, rfl, pc, position, effect⟩
end Exec.Interp
