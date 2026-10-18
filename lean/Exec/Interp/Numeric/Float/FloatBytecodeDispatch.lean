import Exec.Interp.Numeric.Float.FloatDispatch
import Exec.Interp.Relations.Fetch
import Exec.Code.Local.Lowering.Float.FloatOpcode
namespace Exec.Interp
open Aeneas Aeneas.Std Platform
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

set_option maxHeartbeats 2000000 in
theorem dispatch_float_eq (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (index inst function base : Usize)
    (op : Abs.Float.Instruction) (dst left right : U32) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (Code.floatInstruction op dst left right) = (do
        let (r, next) ← runtime.interp.execute_scalar floats exec base
          (floatOpcode op) dst left right
        Result.ok (r, next, store, platform)) := by
  cases op with
  | unary ty operation => cases ty <;> cases operation <;> simp [Code.floatInstruction, floatOpcode, Abs.Float.Instruction.opcode,
    Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex, Abs.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | binary ty operation => cases ty <;> cases operation <;> simp [Code.floatInstruction, floatOpcode, Abs.Float.Instruction.opcode,
    Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex, Abs.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | compare ty operation => cases ty <;> cases operation <;> simp [Code.floatInstruction, floatOpcode, Abs.Float.Instruction.opcode,
    Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex, Abs.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | convert source target sign => cases source <;> cases target <;> cases sign <;> simp [Code.floatInstruction, floatOpcode, Abs.Float.Instruction.opcode,
    Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex, Abs.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | truncate source target sign sat => cases source <;> cases target <;> cases sign <;> cases sat <;> simp [Code.floatInstruction, floatOpcode, Abs.Float.Instruction.opcode,
    Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex, Abs.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | reinterpretFloat source => cases source <;> simp [Code.floatInstruction, floatOpcode, Abs.Float.Instruction.opcode,
    Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex, Abs.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | reinterpretInt source => cases source <;> simp [Code.floatInstruction, floatOpcode, Abs.Float.Instruction.opcode,
    Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex, Abs.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | promote | demote => skip <;> simp [Code.floatInstruction, floatOpcode, Abs.Float.Instruction.opcode,
    Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex, Abs.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]


theorem dispatch_float_effect (correct : FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index inst function base : Usize) (op : Abs.Float.Instruction) (dst left right : U32)
    (hl : base.val + left.val < exec.slots.length)
    (hr : base.val + right.val < exec.slots.length)
    (hd : base.val + dst.val < exec.slots.length) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (Code.floatInstruction op dst left right) ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ numeric, FloatScalarOutcome op exec.slots.val[base.val + left.val]! exec.slots.val[base.val + right.val]! numeric ∧
        ScalarEffect exec (base.val + dst.val) numeric (out.1, out.2.1) ⦄ := by
  rw [dispatch_float_eq]
  obtain ⟨out, equation, property⟩ := WP.spec_imp_exists
    (execute_float_effect floats correct exec base op dst left right hl hr hd)
  rw [equation]
  rcases out with ⟨r, next⟩
  simp only [bind_ok]
  with_unfolding_all apply WP.spec.ret
  exact ⟨rfl, rfl, property⟩
end Exec.Interp
