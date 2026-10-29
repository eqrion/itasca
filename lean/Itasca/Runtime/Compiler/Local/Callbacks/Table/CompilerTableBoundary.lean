import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTables
namespace Itasca.Runtime.Code
open Aeneas.Std

/-- Scratch-buffer and side-table bounds at complete source-instruction
boundaries. Parsed BR_TABLE labels are consumed before the next boundary. -/
structure CompilerTableBoundary {A : Type} (compiler : runtime.compiler.FunctionCompiler A) : Prop where
  depths : compiler.table_depths.val = []
  targets : compiler.function.jump_tables.val.length ≤ compiler.function.code.val.length

theorem CompilerTableBoundary.empty {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    (depths : compiler.table_depths.val = []) (targets : compiler.function.jump_tables.val = []) :
    CompilerTableBoundary compiler := ⟨depths,by simp only [targets,List.length_nil]; omega⟩

theorem CompilerTableBoundary.preserved {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (boundary : CompilerTableBoundary before)
    (depths : after.table_depths = before.table_depths)
    (targets : after.function.jump_tables = before.function.jump_tables)
    (code : before.function.code.val.length ≤ after.function.code.val.length) :
    CompilerTableBoundary after :=
  ⟨by simpa only [depths] using boundary.depths,
    by simpa only [targets] using boundary.targets.trans code⟩

end Itasca.Runtime.Code
