import Exec.Code.Local.Checking.PendingInstructionClose
import Exec.Code.Local.Publication.ScopeClosePublication
import Exec.Code.Local.Relations.Table.ControlTablePreservation

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Actual nested END patches all sites of its closing frame, removes that
owner, and preserves every instruction's local check. Function-root END also
emits an epilogue and is treated separately. -/
theorem compiler_scope_close_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (geometry : ScopeCloseGeometry before) (mode : ScopeCloseMode geometry)
    (nonBody : geometry.frame.kind ≠ .Body) (maps : ControlMapPublication before)
    (coordinateFits : before.function.body_start.val+state.pos.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_end_tables ops law before after state kind bt called)
    (compiler_end_stable_result ops law before after state kind bt (.Ok ()) called).capacity
    (compiler_end_code_mono ops law before after state kind bt called)
  have inside : geometry.target.val ≤ after.function.code.length := by
    change geometry.target.val ≤ after.function.code.val.length
    rw [geometry.position]
    exact growth.code
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
    apply compiler_instruction_prefix_close held geometry.frame geometry.rest geometry.target geometry.frames frames growth _ inside
    simpa only [frameInstructionSites,noIf,Option.toList_none,List.nil_append] using code
  | guarded guard condition old _ hasIf guardCode =>
    have effect := close_guarded_map_effect ops law before state geometry.frame geometry.rest geometry.target geometry.frames
      guard condition old nonBody hasIf guardCode geometry.position geometry.branches mapFits coordinateFits
    rw [canonical,WP.spec_ok] at effect
    obtain ⟨frames,code,_⟩ := effect rfl
    have patched : patchCode before.function.code.val [guard] geometry.target =
        before.function.code.val.set guard.val (.JumpIfZero condition geometry.target) := by
      simp [patchCode,guardCode,retarget]
    apply compiler_instruction_prefix_close held geometry.frame geometry.rest geometry.target geometry.frames frames growth _ inside
    rw [frameInstructionSites,hasIf]
    simp only [Option.toList_some]
    rw [patchCode_append_sites,patched]
    exact code

end Exec.Code
