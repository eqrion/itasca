import Itasca.Runtime.Code.Local.Publication.BranchMapOwners
import Itasca.Runtime.Code.Local.Callbacks.Common.CompilerCloseMetadata
import Itasca.Runtime.Code.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Code.Local.Relations.Control.ControlCursor

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- ELSE changes the current frame's arm and fixups, preserving its map owner. -/
theorem compiler_else_map_owners {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (status,after)) :
    activeControlMaps after = activeControlMaps before := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else at accepted
  simp only [core.option.Option.take] at accepted
  repeat' owners_step accepted using ops, law

/-- ELSE leaves the complete control-map vector unchanged. -/
theorem compiler_else_controls_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (status,after)) :
    after.function.controls = before.function.controls := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else at accepted
  simp only [core.option.Option.take] at accepted
  repeat' maps_step accepted using ops, law

/-- The actual ELSE callback retains open and already closed map ranges. -/
theorem compiler_else_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  apply held.retained (compiler_else_stable_result ops law before after state bt (.Ok ()) called)
    (compiler_else_controls_result ops law before after state bt (.Ok ()) called)
    (compiler_else_map_owners ops law before after state bt (.Ok ()) called)
    (compiler_else_code_mono ops law before after state bt called)
  rw [compiler_else_cursor ops law before after state bt called]
  exact forward

end Itasca.Runtime.Code
