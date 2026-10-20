import Exec.Code.Local.Checking.ScopeCloseInstructionPrefix
import Exec.Code.Local.Checking.FrameExitSlotBounds

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Actual nested END removes its frame while retaining slot bounds of every
outer forward exit, including guarded scope closure. -/
theorem compiler_scope_close_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (geometry : ScopeCloseGeometry before) (mode : ScopeCloseMode geometry)
    (nonBody : geometry.frame.kind ≠ .Body) (maps : ControlMapPublication before)
    (coordinateFits : before.function.body_start.val+state.pos.val ≤ Usize.max)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  have capacity := (compiler_end_stable_result ops law before after state kind bt (.Ok ()) called).capacity
  have mapFits : geometry.frame.map.val < before.function.controls.val.length := by
    apply maps.owners
    simp [activeControlMaps,geometry.frames]
  have canonical : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state .Block .Empty =
      .ok (.Ok (),after) := called
  cases mode with
  | unguarded noIf codeFits sourceFits emitCoordinateFits =>
    have effect := close_scope_effect ops law before state geometry.frame geometry.rest geometry.target
      geometry.frames nonBody noIf geometry.position geometry.branches mapFits coordinateFits
    rw [canonical,WP.spec_ok] at effect
    obtain ⟨frames,_,code,_⟩ := effect rfl
    exact held.pop geometry.frame (by rw [frames]; exact geometry.frames) capacity
  | guarded guard condition old _ hasIf guardCode =>
    have effect := close_guarded_map_effect ops law before state geometry.frame geometry.rest geometry.target geometry.frames
      guard condition old nonBody hasIf guardCode geometry.position geometry.branches mapFits coordinateFits
    rw [canonical,WP.spec_ok] at effect
    obtain ⟨frames,code,_⟩ := effect rfl
    exact held.pop geometry.frame (by rw [frames]; exact geometry.frames) capacity

end Exec.Code
