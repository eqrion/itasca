import Exec.Code.Body.Callbacks.Common.CompilerPrefixOpenDormant
import Exec.Code.Local.Callbacks.Calls.ScopeCallbackDead
import Exec.Code.Local.Relations.Control.ControlEntrySuccess
import Exec.Code.Local.Callbacks.Common.CompilerEnterMetadata
import Exec.Code.Local.Relations.Control.ControlCursor
import Exec.Code.Local.Relations.Control.ControlSources
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem callback_block_dead_prefix {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : CompilerPrefix initial before types functions returns locals parents current raw position)
    (dead : before.reachable = false)
    (state : code.OpIterState) (ctrl : code.Ctrl) (prior : List code.Ctrl)
    (bt : signature.BlockType) (signature : runtime.compiler.Signature)
    (front params results : List valtype)
    (selected : SignatureAt before.signatures bt signature) (matched : SignatureMatches signature params results)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (known : ConcreteStack state.vals.val)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_block ops before state bt = .ok (.Ok (), after)) :
    CompilerPrefix initial after types functions returns locals (parents ++ [current])
      (SourceScope.enterBlock (Wasm2.blockType bt) front params results before.function.code.val.length false) state.vals.val state.pos.val := by
  obtain ⟨_, _, mapsFit, framesFit⟩ := invariant.capacities sourceBound
  obtain ⟨_, parentFrame, _, _, parentShape⟩ := invariant.frames.split
  have bound := invariant.codeBudget.fetch_bound sourceBound
  let pc : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  have positionPc : pc.val = before.function.code.val.length := rfl
  have coordinates := control_entry_coordinates ops before after state ctrl prior .Block bt controls valuesFit accepted
  obtain ⟨codeEq, deadAfter, height, source, sourceEq, framesEq, mapsEq, fresh, nested, preserve⟩ :=
    callback_block_dead_scope ops law before after state ctrl prior bt signature pc locals front params results
      parents current parentFrame invariant.frames.nested parentShape matched.paramWords matched.resultWords
      controls selected valuesFit coordinates.1 coordinates.2 positionPc mapsFit framesFit dead accepted
  let child := SourceScope.enterBlock (Wasm2.blockType bt) front params results before.function.code.val.length false
  let frame : runtime.compiler.Frame := ⟨alloc.vec.Vec.len before.function.controls, .Block, height,
    signature.param_slots, signature.result_slots, pc, none, false, false, alloc.vec.Vec.new Usize⟩
  have aligned : ScopeFrameStack locals after (parents ++ [current]) child :=
    invariant.frames.push child frame framesEq preserve fresh parentShape.bodyBound (by simp [child, SourceScope.enterBlock])
  have stable := compiler_enter_stable_result ops law before after state .Block bt (.Ok ()) accepted
  have sources := compiler_enter_sources ops law before after state .Block bt accepted
  have cursor := compiler_enter_cursor ops law before after state .Block bt accepted
  exact invariant.open_dormant dead deadAfter child frame stable aligned codeEq framesEq
    (by simp [mapsEq]) rfl rfl (DormantFrame.fresh rfl rfl) rfl known rfl rfl sources consumed (by rw [cursor])

end Exec.Code
