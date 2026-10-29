import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixOpen
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.ScopeCallbackEnter
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlEntrySuccess
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerEnterMetadata
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlCursor
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlSources
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout

/-!
A literal successful BLOCK callback lifts its exact emitted frame to the whole source-prefix invariant. Reader wrappers below supply the type/base facts.

Main declarations: `structured_callback_block_prefix`. A direct consumer is `Compiler.Body.Reader.Control.BlockWasm2Prefix`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- A literal successful BLOCK callback lifts its exact emitted frame to the
whole source-prefix invariant. Reader wrappers below supply the type/base facts. -/
theorem structured_callback_block_prefix {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true)
    (state : code.OpIterState) (ctrl : code.Ctrl) (prior : List code.Ctrl)
    (bt : signature.BlockType) (signature : runtime.compiler.Signature)
    (front params results : List valtype)
    (selected : SignatureAt before.signatures bt signature) (matched : SignatureMatches signature params results)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (words : stackWords (state.vals.val.take ctrl.value_stack_base.val) = slots front)
    (oldTypes : Sequence.stackTypes raw = front ++ params)
    (newTypes : SourceStack state.vals.val (front ++ params))
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_block ops before state bt = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals (parents ++ [current])
      (SourceScope.enterBlock (Wasm2.blockType bt) front params results before.function.code.val.length true)
      state.vals.val state.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨_, _, mapsFit, framesFit⟩ := invariant.capacities sourceBound
  obtain ⟨_, parentFrame, _, _, parentShape⟩ := invariant.frames.split
  have bound := invariant.codeBudget.fetch_bound sourceBound
  let pc : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  have positionPc : pc.val = before.function.code.val.length := rfl
  have localWidth : before.function.local_slots.val = slots locals := by
    rw [retained.layout.localSlots, retained.localsEq]
  have coordinates := control_entry_coordinates ops before after state ctrl prior .Block bt controls valuesFit accepted
  obtain ⟨codeEq, live, height, source, sourceEq, framesEq, mapsEq, fresh, nested, preserve⟩ :=
    callback_block_scope ops law before after state ctrl prior bt signature pc locals front params results
      parents current parentFrame invariant.frames.nested parentShape localWidth words matched.paramWords matched.resultWords
      controls selected valuesFit coordinates.1 coordinates.2 positionPc mapsFit framesFit reachable accepted
  let child := SourceScope.enterBlock (Wasm2.blockType bt) front params results before.function.code.val.length true
  let frame : runtime.compiler.Frame := ⟨alloc.vec.Vec.len before.function.controls, .Block, height,
    signature.param_slots, signature.result_slots, pc, none, true, false, alloc.vec.Vec.new Usize⟩
  have aligned : ScopeFrameStack locals after (parents ++ [current]) child :=
    invariant.frames.push child frame framesEq preserve fresh parentShape.bodyBound (Nat.le_refl _)
  have stable := compiler_enter_stable_result ops law before after state .Block bt (.Ok ()) accepted
  have observed : CompilerLayout after (front ++ params) := by
    have localBefore : LocalLayout before := ⟨retained.layout.localSlots, retained.layout.localOffsets⟩
    simpa only [newTypes.decoded] using compiler_enter_layout_success ops law before after state .Block bt
      newTypes.concrete (stable.local_layout localBefore) accepted
  have sources := compiler_enter_sources ops law before after state .Block bt accepted
  have cursor := compiler_enter_cursor ops law before after state .Block bt accepted
  apply invariant.open_plain reachable live child frame [] stable aligned
    (by simp [codeEq]) framesEq (by simp [mapsEq]) rfl rfl (DormantFrame.entered rfl) rfl (by trivial)
    (by simpa only [oldTypes] using observed)
    ⟨newTypes.concrete, newTypes.decoded.trans oldTypes.symm⟩ rfl rfl
    (by simp [child, SourceScope.enterBlock, codeEq]) rfl
    (by simpa [child, SourceScope.enterBlock, SourceScope.input] using oldTypes.symm)
    (by simpa [child, SourceScope.enterBlock, SourceScope.arguments, SourceScope.input] using oldTypes.symm)
    sources (by simp) consumed (by rw [cursor])

end Itasca.Runtime.Code
