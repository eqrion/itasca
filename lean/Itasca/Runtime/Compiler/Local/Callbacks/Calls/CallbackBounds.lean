import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackSafety
import Itasca.Runtime.Compiler.Local.Source.SourceControlBudget
import Itasca.Runtime.Compiler.Local.Source.SourceLengths
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Observation bounds every prefix, including bottom-valued dormant stacks. -/
theorem ObservedStack.prefix_bound {A} {compiler : runtime.compiler.FunctionCompiler A}
    {values : List Itasca.code.StackType} (observed : ObservedStack compiler values) (count : Nat) :
    compiler.function.local_slots.val + stackWords (values.take count) ≤ U32.max := by
  have max : compiler.height.val ≤ U32.max := by scalar_tac
  rw [observed.height] at max
  by_cases small : count ≤ values.length
  · have mono := stack_words_take_mono values small
    simp only [List.take_length] at mono
    omega
  · simpa [List.take_of_length_le (by omega : values.length ≤ count)] using max

/-- The byte cap leaves room for the largest ordinary callback (three code
and coordinate entries), not merely its first append. -/
theorem SourceCodeBudget.callback_headroom {A} {compiler : runtime.compiler.FunctionCompiler A}
    {position : Nat} (budget : SourceCodeBudget compiler position)
    (bounded : position ≤ Itasca.limits.MAX_MODULE_BYTES.val)
    (aligned : SourceAligned compiler) :
    compiler.function.code.val.length + 3 < 2^32 ∧
    compiler.function.code.val.length + 3 ≤ Usize.max ∧
    compiler.function.source_offsets.val.length + 3 ≤ Usize.max := by
  have words : 2^32 - 1 ≤ Usize.max := by scalar_tac
  unfold SourceCodeBudget SourceAligned at *
  norm_num [Itasca.limits.MAX_MODULE_BYTES] at bounded
  omega

end Itasca.Runtime.Compiler
