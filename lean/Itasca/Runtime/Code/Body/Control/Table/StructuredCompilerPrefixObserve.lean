import Itasca.Runtime.Code.Body.Control.Table.StructuredPrefixDead
import Itasca.Runtime.Code.Local.Source.SourceCursor
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- The real dead-opcode path observes the validator without emitting code.
The source instruction may still extend its typed omitted suffix. -/
theorem StructuredCompilerPrefix.dead_op {jumpTables : List Aeneas.Std.U32} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (state : code.OpIterState) (instruction : instr) (opcode : U16) (a b : U32) (bits : U128)
    (dead : before.reachable = false)
    (consumed : position < state.pos.val)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance instruction) state.vals.val state.pos.val := by
  unfold runtime.compiler.lower.FunctionCompiler.op at accepted
  rw [if_neg (by simp only [dead, Bool.false_eq_true, not_false_eq_true])] at accepted
  have frame := compiler_observe_frame ops law before state
  rw [accepted, WP.spec_ok] at frame
  change ObserveFrame before after at frame
  have ordinary := compiler_observe_ordinary_result ops law before after state (.Ok ()) accepted
  have sources := compiler_observe_sources ops law before after state (.Ok ()) accepted
  have cursor := compiler_observe_cursor ops law before after state (.Ok ()) accepted rfl
  have unchanged : after.function.code = before.function.code := by rw [frame]
  have deadAfter : after.reachable = false := by rw [frame]; exact dead
  exact invariant.skip instruction dead deadAfter ordinary unchanged sources consumed (by rw [cursor])

end Itasca.Runtime.Code
