import Exec.Interp.Numeric.Float.FloatDispatch
import Exec.Interp.Numeric.Float.FloatChosenInstruction
namespace Exec.Interp
open Aeneas Aeneas.Std Exec.Spec Platform

/-- Concrete slot reads and writes retain the fixed scalar numeric policy. -/
theorem execute_float_chosen_effect {F : Type} (floats : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect floats)
    {choices : SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric = firstNumericChoice) (occurrence : Nat)
    (exec : runtime.interp.Execution) (base : Usize) (op : Abs.Float.Instruction) (dst left right : U32)
    (hl : base.val + left.val < exec.slots.length)
    (hr : base.val + right.val < exec.slots.length)
    (hd : base.val + dst.val < exec.slots.length) :
    runtime.interp.execute_scalar floats exec base (floatOpcode op) dst left right ⦃ out =>
      ∃ numeric, FloatChosenScalarOutcome choices occurrence op exec.slots.val[base.val + left.val]! exec.slots.val[base.val + right.val]! numeric ∧
        ScalarEffect exec (base.val + dst.val) numeric out ⦄ := by
  obtain ⟨numeric, equation, exactResult⟩ := WP.spec_imp_exists
    (scalar_float_chosen_instruction floats correct admissible numericChoice occurrence op exec.slots.val[base.val + left.val]! exec.slots.val[base.val + right.val]!)
  rw [← scalar_float_dispatch] at equation
  apply WP.spec_mono (execute_scalar_effect floats exec base (floatOpcode op) dst left right hl hr hd numeric equation)
  exact fun _ effect => ⟨numeric, exactResult, effect⟩
end Exec.Interp
