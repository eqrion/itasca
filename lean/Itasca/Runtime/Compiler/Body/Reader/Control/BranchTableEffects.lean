import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableEffects
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTableSource
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTableSuffix
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableOperands

/-!
Complete instruction effects at reader boundaries, after the private label buffer has been consumed. Applies to live and unreachable paths.

Main declarations: `TableReaderEffect`. A direct consumer is `Compiler.Body.Reader.Control.BranchTableIndexed`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Complete instruction effects at reader boundaries, after the private label
buffer has been consumed. Applies to live and unreachable paths. -/
def TableReaderEffect {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (position : Usize) (depths : List U32) : Prop :=
  TableFixed before after ∧ SourceProgress before after ∧ after.next_source=position ∧
  CompilerTableBoundary after ∧ after.reachable=false ∧
  after.function.code.val.length≤before.function.code.val.length+1+2*(depths.length+1)

theorem compiler_reader_table_effect_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (shape : Control.Shape st.core) (depths : List U32) (fallback : U32) (next : Usize)
    (encoded : BrTable.Decoded data st.core.pos depths fallback next)
    (boundary : CompilerTableBoundary before)
    (accepted : code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env .Wasm2 before=.ok (.Ok (),final,after)) :
    TableReaderEffect before after final.core.pos depths := by
  obtain ⟨budget,buffer,types,bufferEq,callback⟩ := compiler_table_source_wasm2 ops law before after st final data env
    shape depths fallback next encoded accepted
  obtain ⟨fixed,source,cursor,afterBoundary,dead,growth⟩ := compiler_br_table_effects ops law
    {before with budget,table_depths := buffer} after final.core fallback types boundary.targets callback
  refine ⟨⟨⟨fixed.stable.metadata,fixed.stable.capacity⟩,fixed.controls,fixed.indirect,fixed.simd,fixed.constants⟩,
    source,cursor,afterBoundary,dead,?_⟩
  simpa only [bufferEq,boundary.depths,List.nil_append] using growth

end Itasca.Runtime.Compiler
