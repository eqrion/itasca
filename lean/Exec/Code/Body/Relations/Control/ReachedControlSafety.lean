import Exec.Code.Body.Control.Table.StructuredPrefixDeadWithTables
import Exec.Code.Local.Callbacks.Calls.CallbackBounds
import Exec.Code.Local.Relations.Common.EndSafety
import Exec.Code.Local.Callbacks.Control.ElseSafety
import Exec.Code.Local.Relations.Control.BranchSafety
import Exec.Code.Local.Callbacks.Common.FixupBudget
namespace Exec.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

 theorem ScopeFrameShape.body_guard {locals scope frame}
    (shape : ScopeFrameShape locals scope frame) (body : frame.kind = .Body) : frame.if_pc = none := by
  have kind := shape.kind.symm.trans body
  have guard := shape.guard
  cases form : scope.form <;> simp [form,ScopeForm.kind] at kind
  simp [SourceScope.guardPosition,form] at guard
  exact guard

/-- Every reached END uses the retained physical frame, map and fixup sites.
The validator may already have closed its own frame before invoking the hook. -/
theorem StructuredCompilerPrefixWithTables.end_total {jumpTables : List U32} {A}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial compiler types functions returns locals parents current raw position)
    (bounded : position ≤ Itasca.limits.MAX_MODULE_BYTES.val)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (coordinate : compiler.function.body_start.val + state.pos.val ≤ Usize.max)
    (emitCoordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state kind bt ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  obtain ⟨prior,frame,frames,paired,shape⟩ := invariant.frames.split
  let rest := alloc.vec.Vec.from prior (by have := compiler.frames.property; simp only [frames,List.length_append,List.length_singleton] at this; omega)
  have room := invariant.codeBudget.callback_headroom bounded invariant.sources
  exact compiler_end_total ops law compiler state frame rest kind bt (by simpa [rest] using frames)
    (invariant.mode.sites frame (by simp [frames])) shape.toScopeFrameShape.body_guard shape.mapBound
    (by omega) coordinate (by omega) (by omega) emitCoordinate

 theorem StructuredCompilerPrefixWithTables.else_total {jumpTables : List U32} {A}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial compiler types functions returns locals parents current raw position)
    (bounded : position ≤ Itasca.limits.MAX_MODULE_BYTES.val)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (coordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  obtain ⟨prior,frame,frames,paired,shape⟩ := invariant.frames.split
  have member : frame ∈ compiler.frames.val := by simp [frames]
  have room := invariant.codeBudget.callback_headroom bounded invariant.sources
  exact compiler_else_total ops law compiler state bt frame prior frames (invariant.mode.sites frame member)
    ((fixups frame member).trans_lt (by omega)) (by omega) (by omega) (by omega) coordinate
end Exec.Code
