import Itasca.Runtime.Code.Local.Checking.RootInstructionPublication
import Itasca.Runtime.Code.Local.Publication.ScopeClosePublication
import Itasca.Runtime.Code.Local.Relations.Table.ControlTablePreservation

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- The actual final END patches the root frame and emits a checked return.
Source result layout bounds the epilogue. No final checker success or completed
function instruction certificate is assumed. -/
theorem compiler_root_close_checked_instructions_of_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (geometry : ScopeCloseGeometry before) (body : geometry.frame.kind = .Body)
    (closed : geometry.rest.val = []) (noIf : geometry.frame.if_pc = none)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (emitCoordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (coordinateFits : before.function.body_start.val+state.pos.val ≤ Usize.max)
    (maps : ControlMapPublication before) (held : CompilerInstructionPrefix before)
    (returnFits : geometry.frame.height.val+
      (if scopeExitLive before.reachable geometry.frame then geometry.frame.results else 0#u32).val ≤ after.function.slot_count.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (),after)) :
    CheckedInstructionPrefix after.function := by
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_end_tables ops law before after state kind bt called)
    (compiler_end_stable_result ops law before after state kind bt (.Ok ()) called).capacity
    (compiler_end_code_mono ops law before after state kind bt called)
  have mapFits : geometry.frame.map.val < before.function.controls.val.length := by
    apply maps.owners
    simp [activeControlMaps,geometry.frames]
  have canonical : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state .Block .Empty =
      .ok (.Ok (),after) := called
  have effect := close_function_effect ops law before state geometry.frame geometry.rest geometry.target geometry.frames body noIf
    geometry.position geometry.branches mapFits coordinateFits codeFits sourceFits emitCoordinateFits
  rw [canonical,WP.spec_ok] at effect
  obtain ⟨frames,reachable,code,_⟩ := effect rfl
  apply compiler_instruction_root_publish held geometry.frame geometry.rest geometry.target geometry.frames frames closed growth
    [.Return geometry.frame.height (if scopeExitLive before.reachable geometry.frame then geometry.frame.results else 0#u32)]
    (by simpa only [frameInstructionSites,noIf,Option.toList_none,List.nil_append] using code) (by simp)
  · change geometry.target.val < after.function.code.val.length
    rw [code,List.length_append,patchCode_length,List.length_singleton,geometry.position]
    omega
  · intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    exact (CoreInstructionBounds.return_ returnFits).accepts

end Itasca.Runtime.Code
