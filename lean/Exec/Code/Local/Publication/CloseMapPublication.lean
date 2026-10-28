import Exec.Code.Local.Callbacks.Control.CloseGuardedMapEffect
import Exec.Code.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Exec.Code.Local.Relations.Control.ControlCursor
import Exec.Code.Local.Callbacks.Common.CompilerCloseMetadata
import Exec.Code.Local.Publication.ControlMapCloseEffect

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- An actual unguarded END retains control-map publication bounds. -/
theorem compiler_unguarded_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (held : ControlMapPublication before)
    (frames : before.frames.val = rest.val ++ [frame])
    (noIf : frame.if_pc = none)
    (position : target.val = before.function.code.val.length)
    (branches : BranchSites before.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < before.function.controls.val.length)
    (coordinateFits : before.function.body_start.val+state.pos.val ≤ Usize.max)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (emitCoordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (progress : before.next_source.val < state.pos.val)
    (endBound : before.function.body_start.val+state.pos.val ≤ before.function.body_end.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
      ops before state .Block .Empty = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  have effect := close_unguarded_map_effect ops law before state frame rest target frames noIf
    position branches mapFits coordinateFits codeFits sourceFits emitCoordinateFits
  rw [called,WP.spec_ok] at effect
  obtain ⟨remaining,_,entry,closed,found,controls,startPc,startSource,endPc,endSource⟩ := effect rfl
  have cursor := compiler_end_cursor ops law before after state .Block .Empty called
  apply held.close_effect (compiler_end_stable_result ops law before after state .Block .Empty (.Ok ()) called)
    frame rest frames remaining entry closed found controls startPc startSource (endPc.trans position)
    endSource progress endBound (compiler_end_code_mono ops law before after state .Block .Empty called)
  rw [cursor]
  omega

/-- An actual guarded END retains control-map publication bounds. -/
theorem compiler_guarded_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (held : ControlMapPublication before)
    (frames : before.frames.val = rest.val ++ [frame])
    (guard : Usize) (condition old : U32)
    (nonBody : frame.kind ≠ .Body) (hasIf : frame.if_pc = some guard)
    (guardCode : before.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (position : target.val = before.function.code.val.length)
    (branches : BranchSites before.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < before.function.controls.val.length)
    (coordinateFits : before.function.body_start.val+state.pos.val ≤ Usize.max)
    (progress : before.next_source.val < state.pos.val)
    (endBound : before.function.body_start.val+state.pos.val ≤ before.function.body_end.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
      ops before state .Block .Empty = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  have effect := close_guarded_map_effect ops law before state frame rest target frames guard condition old
    nonBody hasIf guardCode position branches mapFits coordinateFits
  rw [called,WP.spec_ok] at effect
  obtain ⟨remaining,_,entry,closed,found,controls,startPc,startSource,endPc,endSource⟩ := effect rfl
  have cursor := compiler_end_cursor ops law before after state .Block .Empty called
  apply held.close_effect (compiler_end_stable_result ops law before after state .Block .Empty (.Ok ()) called)
    frame rest frames remaining entry closed found controls startPc startSource (endPc.trans position)
    endSource progress endBound (compiler_end_code_mono ops law before after state .Block .Empty called)
  rw [cursor]
  omega

end Itasca.Runtime.Code
