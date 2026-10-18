import Exec.Code.Body.Reader.Table.ReaderTableDispatchWasm1
import Exec.Code.Local.Relations.Table.BranchTableCallbackLayout
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Actual accepted live Wasm 1 reading and compiler callbacks produce the
retained jump-table certificate without any per-target input assumption. -/
theorem compiler_reader_table_layout_wasm1 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {data env ctx bt st} (p : Wasm1.Pending data env ctx bt st)
    {parents current}
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm1.Frames.Saved.vals))
    (chain : SourceEntryChain parents current) (entered : current.entered=true)
    (known : ConcreteStack st.vals.val) (monomorphic : p.current.ctrl.polymorphic_base=false)
    (before after : runtime.compiler.FunctionCompiler A) (final : code.OpIterState)
    (locals : List valtype) (labels : List LabelTarget) (groups : List FixupTarget)
    (depths : List U32) (fallback : U32) (next : Usize)
    (encoded : BrTable.Decoded data st.pos depths fallback next)
    (layout : CompilerLayout before (Sequence.stackTypes st.vals.val))
    (localTypes : compilerLocals before=locals)
    (paired : List.Forall₂ (ScopeFrameShape locals) (parents++[current]) before.frames.val)
    (labelShapes : List.Forall₂ ScopeLabel (parents++[current]).reverse labels)
    (boundary : CompilerTableBoundary before)
    (sites : ∀ frame ∈ before.frames.val, FrameSites before.function.code.val frame)
    (plans : FramePlans after.function.code.val.length locals after.frames.val labels groups)
    (live : before.reachable=true)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_BR_TABLE before=.ok (.Ok (),final,after)) :
    ∃ stack previous start len selector,
      Sequence.stackTypes st.vals.val=stack++[.I32] ∧
      FramePlans before.function.code.val.length locals before.frames.val labels previous ∧
      BranchTableLayout after.function.jump_tables.val locals labels stack
        (resolvedCode after.function.code.val groups) (depths.map (fun d => .mk_uN d.val)) (.mk_uN fallback.val)
        before.function.code.val.length after.function.code.val.length selector start len ∧
      before.function.code.val.length+1≤after.function.code.val.length ∧
      CompilerTableBoundary after ∧ after.reachable=false ∧
      ∃ extra, resolvedCode after.function.code.val groups =
        resolvedCode before.function.code.val previous ++ (.JumpTable selector start len :: extra) := by
  obtain ⟨actual,common,collected,read,callback⟩ := reader_table_dispatch_wasm1
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st final data env ctx before after accepted
  obtain ⟨stack,stackEq,inputs⟩ := reader_table_inputs_wasm1
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) p same fronts chain entered known monomorphic
    before collected final actual common depths fallback next encoded read
  obtain ⟨rfl,budget,buffer,collectedEq,bufferEq⟩ := compiler_table_source_wasm1 ops law before collected st final data
    actual common depths fallback next encoded read
  subst collected
  have bufferSource : buffer.val=depths := by simpa only [boundary.depths,List.nil_append] using bufferEq
  have stagedLayout : CompilerLayout {before with budget,table_depths := buffer} (stack++[.I32]) := by
    rw [stackEq] at layout
    exact ⟨layout.localSlots,layout.localOffsets,layout.operandOffsets,layout.height,layout.capacity⟩
  obtain ⟨previous,start,len,selector,prior,certificate,header,afterBoundary,dead,extra,resolved⟩ :=
    compiler_br_table_layout_prefix ops law {before with budget,table_depths := buffer} after final actual (Control.resultView common)
      locals stack (parents++[current]) labels depths groups bufferSource stagedLayout localTypes paired labelShapes inputs
      boundary.targets sites plans live callback
  exact ⟨stack,previous,start,len,selector,stackEq,prior,certificate,header,afterBoundary,dead,extra,resolved⟩
end Exec.Code
