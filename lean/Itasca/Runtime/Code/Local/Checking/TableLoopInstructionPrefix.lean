import Itasca.Runtime.Code.Local.Checking.TableBranchInstructionEffect

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- The finite table builder preserves all stored checks except the dispatch
word whose rows are still being constructed. -/
theorem TableBranchRun.instruction_prefix_except {A : Type} {ops : runtime.platform.Alloc A}
    (law : Platform.AllocCorrect ops) {before after : runtime.compiler.FunctionCompiler A}
    {index limit omitted : Nat} (run : TableBranchRun ops before index after)
    (safe : TableLoopSafe before index limit) (limitFits : limit ≤ Usize.max)
    (transfers : TableTransferBounds before)
    (heightFits : before.height.val ≤ before.function.slot_count.val)
    (held : CompilerInstructionPrefixExcept before omitted) :
    CompilerInstructionPrefixExcept after omitted := by
  induction run with
  | done => exact held
  | @cons before middle after index inside called rest ih =>
    let depth := before.table_depths.val[index.val]
    have lookup : before.table_depths.val[index.val]? = some depth := List.getElem?_eq_getElem inside
    have effect := compiler_table_branch_instruction_effect ops law before middle index depth limit
      lookup safe limitFits transfers heightFits called
    obtain ⟨_,_,_,height,code⟩ := compiler_table_target_code ops law before middle index depth lookup called
    have depths := compiler_table_branch_depths ops before middle index (.Ok ()) called
    have capacity := (compiler_table_branch_fixed ops law before middle index depth lookup called).stable.capacity
    apply ih (safe.advance ops law inside called) (transfers.advance code depths height)
    · rw [height]
      exact heightFits.trans capacity
    · exact effect.apply_except omitted held

end Itasca.Runtime.Code
