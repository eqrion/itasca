import Exec.Code.Local.Publication.CloseMapPublication
import Exec.Code.Local.Coordinates.ControlSourceCoordinates

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Closing geometry comes from the current physical scope and its branch
sites, independently of any completed publication certificate. -/
structure ScopeCloseGeometry {A : Type} (before : runtime.compiler.FunctionCompiler A) where
  frame : runtime.compiler.Frame
  rest : alloc.vec.Vec runtime.compiler.Frame
  target : U32
  frames : before.frames.val = rest.val ++ [frame]
  position : target.val = before.function.code.val.length
  branches : BranchSites before.function.code.val frame.fixups.val

/-- A conditional frame patches its pending guard; other closes require only
room for the root epilogue when the closing frame is the function body. -/
inductive ScopeCloseMode {A : Type} {before : runtime.compiler.FunctionCompiler A}
    (geometry : ScopeCloseGeometry before) : Prop where
  | unguarded (noIf : geometry.frame.if_pc = none)
      (codeFits : before.function.code.val.length < Usize.max)
      (sourceFits : before.function.source_offsets.val.length < Usize.max)
      (emitCoordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max) :
      ScopeCloseMode geometry
  | guarded (guard : Usize) (condition old : U32)
      (nonBody : geometry.frame.kind ≠ .Body) (hasIf : geometry.frame.if_pc = some guard)
      (guardCode : before.function.code.val[guard.val]? = some (.JumpIfZero condition old)) :
      ScopeCloseMode geometry

/-- The actual END event retains both invariants. The map index is bounded by
its active owner, and reader progress supplies the positive source interval. -/
theorem compiler_scope_close_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (geometry : ScopeCloseGeometry before) (mode : ScopeCloseMode geometry)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (progress : before.next_source.val < state.pos.val)
    (endBound : before.function.body_start.val+state.pos.val ≤ before.function.body_end.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (),after)) :
    SourceCoordinates after ∧ ControlMapPublication after := by
  refine ⟨compiler_end_source_coordinates ops law before after state kind bt coordinates inside (by omega) called,?_⟩
  have mapFits : geometry.frame.map.val < before.function.controls.val.length := by
    apply maps.owners
    simp [activeControlMaps,geometry.frames]
  have coordinateFits : before.function.body_start.val+state.pos.val ≤ Usize.max := by
    have bound : before.function.body_end.val ≤ Usize.max := by scalar_tac
    omega
  have canonical : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state .Block .Empty =
      .ok (.Ok (),after) := called
  cases mode with
  | unguarded noIf codeFits sourceFits emitCoordinateFits =>
    exact compiler_unguarded_map_publication ops law before after state geometry.frame geometry.rest geometry.target
      maps geometry.frames noIf geometry.position geometry.branches mapFits coordinateFits codeFits sourceFits emitCoordinateFits
      progress endBound canonical
  | guarded guard condition old nonBody hasIf guardCode =>
    exact compiler_guarded_map_publication ops law before after state geometry.frame geometry.rest geometry.target
      maps geometry.frames guard condition old nonBody hasIf guardCode geometry.position geometry.branches mapFits coordinateFits
      progress endBound canonical

end Itasca.Runtime.Code
