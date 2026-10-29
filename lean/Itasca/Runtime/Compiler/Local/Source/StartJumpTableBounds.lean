import Itasca.Runtime.Compiler.Local.Relations.Function.FunctionStartRaw
import Itasca.Runtime.Compiler.Local.Relations.Function.FunctionEntry
import Itasca.Runtime.Compiler.Local.Source.JumpTableBounds

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Actual construction and function-start leave the jump table empty, so no
completed function or source-body execution premise is needed for its bounds. -/
theorem compiler_start_jump_table_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (signatures : Slice runtime.compiler.Signature)
    (functionSlots : Slice U32) (budget : runtime.compiler.Budget A) (batchStart : Usize)
    (initial started : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (signature : runtime.compiler.Signature)
    (bodyBegin bodyEnd : Usize)
    (lookup : signatures.val[typeIndex.val]? = some signature)
    (beginFits : batchStart.val+bodyBegin.val ≤ Usize.max)
    (endFits : batchStart.val+bodyEnd.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (begun : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial ctx typeIndex bodyBegin bodyEnd = .ok (.Ok (),started)) : JumpTableBounds started := by
  have newPost := compiler_new ops signatures functionSlots budget batchStart
  rw [created,WP.spec_ok] at newPost
  obtain ⟨layout,emptyLocals,emptyOperands,emptyMaps,emptyFrames,emptyCode,reachable,sigs,widths,coordinate⟩ := newPost
  have startPost := compiler_function_start_raw ops law initial ctx typeIndex signature bodyBegin bodyEnd
    (by simpa only [sigs] using lookup) (by simpa only [coordinate] using beginFits)
    (by simpa only [coordinate] using endFits) emptyLocals layout emptyOperands
    (by simp [emptyMaps]; scalar_tac) (by simp [emptyFrames]; scalar_tac)
  rw [begun,WP.spec_ok] at startPost
  obtain ⟨_,_,_,tables⟩ := startPost rfl
  have jumpTables := congrArg CompilerTables.jumpTables tables
  change started.function.jump_tables.val = initial.function.jump_tables.val at jumpTables
  have initialEmpty : initial.function.jump_tables.val = [] := by
    simp only [runtime.compiler.FunctionCompiler.new,Result.ok.injEq] at created
    subst initial
    rfl
  intro target member
  rw [jumpTables,initialEmpty] at member
  cases member

end Itasca.Runtime.Compiler
