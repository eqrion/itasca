import Exec.Code.Body.Reader.Publication.NonScopeCallbackPublication
import Exec.Code.Local.Coordinates.LoweringTargetBounds
import Exec.Code.Local.Coordinates.TableCallbackTargetBounds
import Exec.Code.Local.Callbacks.Table.CallbackTables
import Exec.Code.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Every non-scope-boundary event retains valid jump-table targets. Tables
append only actual branch-stub positions; all other callbacks retain the table. -/
theorem compiler_non_scope_hook_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) {action : Action} (supported : NonScopePublicationAction action)
    (held : JumpTableBounds before)
    (called : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before (.op state action) =
      .ok (.Ok (),after)) : JumpTableBounds after := by
  cases supported with
  | scalar supported =>
    obtain ⟨opcode,a,b,bits,member,dispatch⟩ := scalar_hook_publication_dispatch ops before state supported
    rw [dispatch] at called
    exact compiler_scalar_target_bounds ops law before after state opcode a b bits member held called
  | numeric hook =>
    rcases numeric_hook_publication_dispatch ops before state hook with ⟨op,dispatch⟩ | ⟨op,dispatch⟩
    · rw [dispatch] at called
      exact compiler_numeric_target_bounds ops law before after state op held called
    · rw [dispatch] at called
      exact compiler_float_target_bounds ops law before after state op held called
  | extendedNumeric hook =>
    rcases extended_numeric_hook_publication_dispatch ops before state hook with ⟨op,dispatch⟩ | ⟨op,dispatch⟩
    · rw [dispatch] at called
      exact compiler_numeric_target_bounds ops law before after state op held called
    · rw [dispatch] at called
      exact compiler_float_target_bounds ops law before after state op held called
  | memory hook arg =>
    have range : 40 ≤ hook.opcode.val ∧ hook.opcode.val ≤ 62 := by cases hook <;> decide
    have visited := (MemoryHook.dispatch (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before state hook arg).trans called
    rcases source_memory_byte_partition hook.opcode range.1 range.2 with ⟨op,byte⟩ | ⟨op,byte⟩
    · have dispatch := (memory_load_reader_facts ops before state op arg).2.2.2.2.1
      rw [← byte,dispatch] at visited
      exact compiler_core_target_bounds ops law before after state (.load op arg.offset arg.align) held visited
    · have dispatch := (memory_store_reader_facts ops before state op arg).2.2.2.2.1
      rw [← byte,dispatch] at visited
      exact compiler_core_target_bounds ops law before after state (.store op arg.offset arg.align) held visited
  | simd supported =>
    obtain ⟨opcode,a,b,bits,lower,upper,dispatch⟩ := simd_hook_publication_dispatch ops before state supported
    rw [dispatch] at called
    exact compiler_simd_target_bounds ops law before after state opcode a b bits lower upper held called
  | unreachable =>
    exact held.retained (after := after)
      (congrArg CompilerTables.jumpTables (compiler_unreachable_tables ops law before after state called))
      (compiler_unreachable_code_mono ops law before after state called)
  | return_ =>
    exact held.retained (after := after)
      (congrArg CompilerTables.jumpTables (compiler_return_tables ops law before after state called))
      (compiler_return_code_mono ops law before after state called)
  | br depth types =>
    exact held.retained (after := after)
      (congrArg CompilerTables.jumpTables (compiler_br_tables ops law before after state depth types called))
      (compiler_br_code_mono ops law before after state depth types called)
  | br_if depth types =>
    exact held.retained (after := after)
      (congrArg CompilerTables.jumpTables (compiler_br_if_tables ops law before after state depth types called))
      (compiler_br_if_code_mono ops law before after state depth types called)
  | label depth => exact compiler_table_label_target_bounds ops law before after state depth held called
  | table fallback types => exact compiler_br_table_target_bounds ops law before after state fallback types held called
  | else_ bt =>
    exact held.retained (after := after)
      (congrArg CompilerTables.jumpTables (compiler_else_tables ops law before after state bt called))
      (compiler_else_code_mono ops law before after state bt called)

end Itasca.Runtime.Code
