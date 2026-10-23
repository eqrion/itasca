import Exec.Code.Local.Relations.Table.BranchTableLayoutProduction
import Exec.Code.Local.Relations.Table.BranchTableCallback
import Exec.Code.Local.Callbacks.Table.CompilerTableBoundary
namespace Exec.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- The actual terminal callback retains every resolved branch-table arm and
restores the scratch-buffer/dominance boundary for the following instruction. -/
theorem compiler_br_table_layout_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (locals stack : List valtype) (scopes : List SourceScope) (labels : List LabelTarget)
    (depths : List U32) (groups : List FixupTarget)
    (buffer : before.table_depths.val = depths)
    (layout : CompilerLayout before (stack++[.I32])) (localTypes : compilerLocals before=locals)
    (paired : List.Forall₂ (ScopeFrameShape locals) scopes before.frames.val)
    (labelShapes : List.Forall₂ ScopeLabel scopes.reverse labels)
    (inputs : TableOperandScopes scopes stack (depths++[fallback]))
    (dominance : before.function.jump_tables.val.length ≤ before.function.code.val.length)
    (sites : ∀ frame ∈ before.frames.val, FrameSites before.function.code.val frame)
    (plans : FramePlans after.function.code.val.length locals after.frames.val labels groups)
    (live : before.reachable=true)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types=.ok (.Ok (),after)) :
    ∃ previous start len selector,
      FramePlans before.function.code.val.length locals before.frames.val labels previous ∧
      BranchTableLayout after.function.jump_tables.val locals labels stack
        (resolvedCode after.function.code.val groups) (depths.map (fun d => .mk_uN d.val)) (.mk_uN fallback.val)
        before.function.code.val.length after.function.code.val.length selector start len ∧
      before.function.code.val.length+1≤after.function.code.val.length ∧
      CompilerTableBoundary after ∧ after.reachable=false ∧
      ∃ extra, resolvedCode after.function.code.val groups =
        resolvedCode before.function.code.val previous ++ (.JumpTable selector start len :: extra) := by
  obtain ⟨budget,collected,lowered,cleared,collectedEq,loweredCall,clearedEq,observeCall⟩ :=
    compiler_br_table_success ops law before after state fallback types live accepted
  have observation := compiler_observe_frame ops law {lowered with reachable := false,table_depths := cleared} state
  rw [observeCall,WP.spec_ok] at observation
  dsimp only [ObserveFrame] at observation
  have codeEq : after.function.code = lowered.function.code := by rw [observation]
  have framesEq : after.frames = lowered.frames := by rw [observation]
  have tablesEq : after.function.jump_tables = lowered.function.jump_tables := by rw [observation]
  have depthsEq : after.table_depths = cleared := by rw [observation]
  have dead : after.reachable=false := by rw [observation]
  have plansLowered : FramePlans lowered.function.code.val.length locals lowered.frames.val labels groups := by
    simpa only [codeEq,framesEq] using plans
  have collectedLayout : CompilerLayout {before with budget,table_depths := collected} (stack++[.I32]) :=
    ⟨layout.localSlots,layout.localOffsets,layout.operandOffsets,layout.height,layout.capacity⟩
  obtain ⟨previous,start,len,selector,previousPlans,certificate,header,targets,extra,resolved⟩ :=
    compiler_lower_table_layout_prefix ops law {before with budget,table_depths := collected} lowered
      locals stack scopes labels depths fallback groups (by simpa only [buffer] using collectedEq)
      collectedLayout localTypes paired labelShapes inputs dominance sites plansLowered loweredCall
  refine ⟨previous,start,len,selector,previousPlans,?_,?_,?_,dead,extra,?_⟩
  · simpa only [codeEq,tablesEq] using certificate
  · simpa only [codeEq] using header
  · constructor
    · simpa only [depthsEq] using clearedEq
    · simpa only [codeEq,tablesEq] using targets
  · simpa only [codeEq] using resolved
end Exec.Code
