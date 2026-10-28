import Exec.Code.Local.Callbacks.Table.CompilerTablePreservation
import Exec.Code.Local.Callbacks.Common.CompilerCodeMonotone

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Every stored jump-table target is inside the currently emitted code. -/
def JumpTableBounds (compiler : runtime.compiler.FunctionCompiler A) : Prop :=
  ∀ target ∈ compiler.function.jump_tables.val, target.val < compiler.function.code.val.length

/-- Table preservation and code growth retain all existing target bounds. -/
theorem JumpTableBounds.retained {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : JumpTableBounds before)
    (tables : after.function.jump_tables.val = before.function.jump_tables.val)
    (code : before.function.code.val.length ≤ after.function.code.val.length) : JumpTableBounds after := by
  intro target member
  rw [tables] at member
  exact (held target member).trans_le code

/-- Successful emission retains side-table targets while extending code. -/
theorem Emitted.jumpTableBounds {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction : runtime.bytecode.Instr} (emitted : Emitted before after instruction)
    (held : JumpTableBounds before) : JumpTableBounds after := by
  obtain ⟨budget,code,sources,rfl,appended,_⟩ := emitted
  intro target member
  have bounded := held target member
  change target.val < code.val.length
  rw [appended]
  simp only [List.length_append,List.length_singleton]
  omega

/-- Actual observation leaves both code and jump-table targets fixed. -/
theorem compiler_observe_jump_table_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (held : JumpTableBounds before)
    (called : runtime.compiler.FunctionCompiler.observe ops before state = .ok (.Ok (),after)) :
    JumpTableBounds after := by
  apply held.retained (after := after) (congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called))
    (compiler_observe_code_mono ops law before after state (.Ok ()) called)

end Itasca.Runtime.Code
