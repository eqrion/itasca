import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseMapEffect
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerCloseMetadata
import Itasca.Runtime.Compiler.Local.Publication.ControlMapPublication

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The actual final END callback establishes every control-map range checked
at publication. Its return instruction puts all closing targets inside code. -/
theorem compiler_root_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (held : ControlMapPublication before)
    (frames : before.frames.val = rest.val ++ [frame]) (empty : rest.val = [])
    (root : frame.kind = .Body) (noIf : frame.if_pc = none)
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
    ∀ map ∈ after.function.controls.val,
      map.start_pc.val ≤ map.end_pc.val ∧ map.end_pc.val < after.function.code.length ∧
      after.function.body_start.val ≤ map.source_start.val ∧ map.source_end.val ≤ after.function.body_end.val ∧
      map.source_start.val < map.source_end.val := by
  have effect := close_unguarded_map_effect ops law before state frame rest target frames noIf
    position branches mapFits coordinateFits codeFits sourceFits emitCoordinateFits
  rw [called,WP.spec_ok] at effect
  obtain ⟨_,code,entry,closed,found,controls,startPc,startSource,endPc,endSource⟩ := effect rfl
  have bounded := (held.entries frame.map.val entry found).close_fields startPc startSource
    (endPc.trans position) endSource progress endBound
  have growth : before.function.code.length < after.function.code.length := by
    change before.function.code.val.length < after.function.code.val.length
    rw [code]
    simp only [List.length_append,patch_code_length,closeMapEpilogue,root,List.length_singleton]
    omega
  have owners : activeControlMaps before = [frame.map.val] := by
    simp [activeControlMaps,frames,empty]
  exact held.close_last_publish (compiler_end_stable_result ops law before after state .Block .Empty (.Ok ()) called)
    frame.map.val entry closed found controls owners bounded growth

end Itasca.Runtime.Compiler
