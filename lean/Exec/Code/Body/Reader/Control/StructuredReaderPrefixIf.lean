import Exec.Code.Body.Reader.Control.StructuredReaderPrefixBlock
import Exec.Code.Local.Callbacks.Calls.ScopeCallbackIf
import Exec.Code.Local.Relations.Control.ControlObservedLayout
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem structured_callback_if_prefix {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : StructuredCompilerPrefix emit initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true)
    (state : code.OpIterState) (ctrl : code.Ctrl) (prior : List code.Ctrl)
    (bt : signature.BlockType) (signature : runtime.compiler.Signature)
    (front params results : List valtype)
    (selected : SignatureAt before.signatures bt signature) (matched : SignatureMatches signature params results)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (words : stackWords (state.vals.val.take ctrl.value_stack_base.val) = slots front)
    (oldTypes : Sequence.stackTypes raw = (front ++ params) ++ [.I32])
    (newTypes : SourceStack state.vals.val (front ++ params))
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_if ops before state bt = .ok (.Ok (), after)) :
    ∃ condition,
      condition.val = slots locals + slots (front ++ params) ∧
      StructuredCompilerPrefix emit initial after types functions returns locals (parents ++ [current])
        (SourceScope.enterIf (Wasm2.blockType bt) condition front params results before.function.code.val.length true)
        state.vals.val state.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨codeFits, offsetsFit, mapsFit, framesFit⟩ := invariant.capacities sourceBound
  obtain ⟨_, parentFrame, _, _, parentShape⟩ := invariant.frames.split
  have bound := invariant.codeBudget.fetch_bound sourceBound
  let pc : U32 := UScalar.ofNatCore (before.function.code.val.length + 1) (by scalar_tac)
  have positionPc : pc.val = before.function.code.val.length + 1 := rfl
  have localWidth : before.function.local_slots.val = slots locals := by
    rw [retained.layout.localSlots, retained.localsEq]
  have coordinates := control_entry_coordinates ops before after state ctrl prior .Then bt controls valuesFit accepted
  obtain ⟨live, condition, height, source, conditionEq, sourceEq, codeEq, framesEq, mapsEq, fresh, nested, preserve⟩ :=
    callback_if_scope ops law before after state ctrl prior bt signature pc locals front params results
      (front ++ params) parents current parentFrame invariant.frames.nested parentShape localWidth words
      matched.paramWords matched.resultWords (by simpa only [oldTypes] using retained.layout)
      codeFits offsetsFit controls selected valuesFit coordinates.1 coordinates.2 positionPc mapsFit framesFit reachable accepted
  let child := SourceScope.enterIf (Wasm2.blockType bt) condition front params results before.function.code.val.length true
  let frame : runtime.compiler.Frame := ⟨alloc.vec.Vec.len before.function.controls, .Then, height,
    signature.param_slots, signature.result_slots, pc, some (alloc.vec.Vec.len before.function.code), true, false, alloc.vec.Vec.new Usize⟩
  have aligned : ScopeFrameStack locals after (parents ++ [current]) child :=
    invariant.frames.push child frame framesEq preserve fresh parentShape.bodyBound (by simp [child, SourceScope.enterIf])
  have stable := compiler_enter_stable_result ops law before after state .Then bt (.Ok ()) accepted
  have observed : CompilerLayout after (front ++ params) := by
    have localBefore : LocalLayout before := ⟨retained.layout.localSlots, retained.layout.localOffsets⟩
    simpa only [newTypes.decoded] using compiler_enter_layout_success ops law before after state .Then bt
      newTypes.concrete (stable.local_layout localBefore) accepted
  have sources := compiler_enter_sources ops law before after state .Then bt accepted
  have cursor := compiler_enter_cursor ops law before after state .Then bt accepted
  refine ⟨condition, by simpa only [retained.localsEq] using conditionEq, ?_⟩
  exact invariant.open_if reachable live child frame condition (alloc.vec.Vec.len before.function.code) rfl oldTypes
    stable aligned codeEq framesEq (by simp [mapsEq]) rfl rfl (DormantFrame.entered rfl) rfl
    (by intro _; simpa only [retained.localsEq, child, SourceScope.enterIf, SourceScope.input] using conditionEq) observed
    newTypes rfl rfl (by simp [child, SourceScope.enterIf, codeEq]) rfl rfl rfl sources consumed (by rw [cursor])

end Exec.Code
