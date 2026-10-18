import Exec.Code.Local.Relations.Table.BranchTableEffects
import Exec.Code.Body.Reader.Table.ReaderTableDispatchWasm1
import Exec.Code.Body.Reader.Table.ReaderTableSource
namespace Exec.Code
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
    (st final : code.BodyState) (data : Slice U8) (env : module.Env)
    (shape : Control.Shape st.core) (depths : List U32) (fallback : U32) (next : Usize)
    (encoded : BrTable.Decoded data st.core.pos depths fallback next)
    (boundary : CompilerTableBoundary before)
    (accepted : code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env before=.ok (.Ok (),final,after)) :
    TableReaderEffect before after final.core.pos depths := by
  obtain ⟨budget,buffer,types,bufferEq,callback⟩ := compiler_table_source_wasm2 ops law before after st final data env
    shape depths fallback next encoded accepted
  obtain ⟨fixed,source,cursor,afterBoundary,dead,growth⟩ := compiler_br_table_effects ops law
    {before with budget,table_depths := buffer} after final.core fallback types boundary.targets callback
  refine ⟨⟨⟨fixed.stable.metadata,fixed.stable.capacity⟩,fixed.controls,fixed.indirect,fixed.simd,fixed.constants⟩,
    source,cursor,afterBoundary,dead,?_⟩
  simpa only [bufferEq,boundary.depths,List.nil_append] using growth

theorem compiler_reader_table_effect_wasm1 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (depths : List U32) (fallback : U32) (next : Usize)
    (encoded : BrTable.Decoded data st.pos depths fallback next)
    (boundary : CompilerTableBoundary before)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_BR_TABLE before=.ok (.Ok (),final,after)) :
    TableReaderEffect before after final.pos depths := by
  obtain ⟨actual,common,collected,read,callback⟩ := reader_table_dispatch_wasm1
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st final data env ctx before after accepted
  obtain ⟨rfl,budget,buffer,collectedEq,bufferEq⟩ := compiler_table_source_wasm1 ops law before collected st final data
    actual common depths fallback next encoded read
  subst collected
  obtain ⟨fixed,source,cursor,afterBoundary,dead,growth⟩ := compiler_br_table_effects ops law
    {before with budget,table_depths := buffer} after final actual (Control.resultView common) boundary.targets callback
  refine ⟨⟨⟨fixed.stable.metadata,fixed.stable.capacity⟩,fixed.controls,fixed.indirect,fixed.simd,fixed.constants⟩,
    source,cursor,afterBoundary,dead,?_⟩
  simpa only [bufferEq,boundary.depths,List.nil_append] using growth
end Exec.Code
