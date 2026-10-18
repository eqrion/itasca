import Exec.Code.Local.Capacity.BranchTableSourceGrowth
import Exec.Code.Local.Callbacks.Calls.CallbackBounds
namespace Exec.Code
open Aeneas Aeneas.Std

/-- The actual immediate span pays for every table arm, including its default.
No valid encoding of the remaining function body is required. -/
theorem SourceCodeBudget.table_callback_headroom {A}
    {compiler : runtime.compiler.FunctionCompiler A} {sourceStart : Nat}
    {data start depths fallback next}
    (budget : SourceCodeBudget compiler sourceStart)
    (decoded : Itasca.BrTable.Decoded data start depths fallback next)
    (position : start.val = sourceStart+1)
    (bounded : next.val ≤ Itasca.limits.MAX_MODULE_BYTES.val)
    (buffer : compiler.table_depths.val = depths) :
    compiler.function.code.val.length + 1 + 2*(compiler.table_depths.val.length+1) ≤ Usize.max := by
  have growth := table_instruction_growth_bound decoded sourceStart compiler.function.code.val.length position
  have words : 2^32-1 ≤ Usize.max := by scalar_tac
  unfold SourceCodeBudget at budget
  norm_num [Itasca.limits.MAX_MODULE_BYTES] at bounded
  rw [buffer]
  have consumed := table_immediate_byte_bound decoded
  omega

/-- Label collection itself is safe at every reached decoding prefix. -/
theorem table_label_buffer_headroom {data start depths next}
    (decoded : Itasca.BrTable.LabelsDecoded data start depths next)
    (bounded : next.val ≤ Itasca.limits.MAX_MODULE_BYTES.val) : depths.length < Usize.max := by
  have consumed := table_labels_byte_bound decoded
  have words : 2^32-1 ≤ Usize.max := by scalar_tac
  norm_num [Itasca.limits.MAX_MODULE_BYTES] at bounded
  omega
end Exec.Code
