import Exec.Code.Body.Control.Table.StructuredPrefixDeadWithTables
import Exec.Code.Local.Publication.RootMapPublication
import Exec.Code.Local.Publication.FinalControlMapBounds

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- A reached root prefix supplies its sole body frame and branch sites. The
actual final END emits RETURN and establishes every strict map range checked
at publication, rather than assuming those ranges in a completed certificate. -/
theorem structured_root_map_publication {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals current raw position}
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial before types functions returns locals [] current raw position)
    (rootForm : current.form = .body) (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (maps : ControlMapPublication before) (consumed : position < state.pos.val)
    (endBound : before.function.body_start.val+state.pos.val ≤ before.function.body_end.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (),after)) :
    FinalControlMapBounds after.function := by
  obtain ⟨prior,frame,frames,paired,shape⟩ := invariant.frames.split
  have empty : prior = [] := by cases paired; rfl
  let rest := alloc.vec.Vec.new runtime.compiler.Frame
  have restEmpty : rest.val = [] := by simp [rest,alloc.vec.Vec.new]
  have physical : before.frames.val = rest.val ++ [frame] := by simpa only [restEmpty,empty] using frames
  have root : frame.kind = .Body := by simpa only [rootForm,ScopeForm.kind] using shape.kind
  have noIf : frame.if_pc = none := by
    have guard := shape.guard
    simpa only [rootForm,SourceScope.guardPosition,Option.map_eq_none_iff] using guard
  have codeBound := invariant.codeBudget.fetch_bound sourceBound
  let target : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  have sites := (invariant.mode.sites frame (by simp [frames])).branches.branches
  obtain ⟨codeFits,offsetsFit,_,_⟩ := invariant.capacities sourceBound
  have progress : before.next_source.val < state.pos.val := lt_of_le_of_lt invariant.cursor consumed
  have endFits : before.function.body_end.val ≤ Usize.max := by scalar_tac
  have coordinateFits : before.function.body_start.val+state.pos.val ≤ Usize.max := by omega
  have emitFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by omega
  exact compiler_root_map_publication ops law before after state frame rest target maps physical restEmpty root noIf
    rfl sites shape.mapBound coordinateFits codeFits offsetsFit emitFits progress endBound called

end Exec.Code
