import Itasca.Runtime.Compiler.Body.Reader.Control.BlockPrefix
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.ScopeCallbackIf
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Body.Callbacks.Calls.ScopeCallbackInputs
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Reader.Control.FrontTransitions

/-!
Structured if reader prefixes and their complete-profile transport. These are control-map proofs, not Wasm table operations.
-/

/-! ## Structured Reader Prefix If -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem structured_callback_if_prefix {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
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
    (oldTypes : Sequence.stackTypes raw = (front ++ params) ++ [.I32])
    (newTypes : SourceStack state.vals.val (front ++ params))
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_if ops before state bt = .ok (.Ok (), after)) :
    ∃ condition,
      condition.val = slots locals + slots (front ++ params) ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals (parents ++ [current])
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

end Itasca.Runtime.Code

end

/-! ## Structured Reader Prefix If Wasm2 -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- An accepted canonical IF reader constructs the complete live child
compiler prefix, its source zipper, and validator reachability correspondence. -/
theorem structured_reader_prefix_if_wasm2 {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env localTypes index st}
    (p : Wasm2.Pending data env .Wasm2 localTypes index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (reach : ReaderReachabilityWasm2 before.reachable parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (reachable : before.reachable = true)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_IF)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_IF before = .ok (.Ok (), out, after)) :
    ∃ bt ins outs remaining base front condition,
      let child := SourceScope.enterIf (Wasm2.blockType bt) condition front (ins.map Translate.valueType)
        (outs.map Translate.valueType) before.function.code.val.length true
      ReaderEnterPostWasm2 p out .then_ bt ins outs remaining base ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals (parents ++ [current]) child out.core.vals.val out.core.pos.val ∧
      ReaderScopeZipperWasm2 (parents ++ [current]) child
        (p.parents ++ [{p.current with vals := remaining}]) (Wasm2.Frames.Saved.fresh base .then_ bt ins outs) ∧
      ReaderReachabilityWasm2 after.reachable (parents ++ [current]) child
        (p.parents ++ [{p.current with vals := remaining}]) (Wasm2.Frames.Saved.fresh base .then_ bt ins outs) ∧
      ReaderScopeFronts (parents ++ [current]) child
        ((p.parents ++ [{p.current with vals := remaining}]).map Wasm2.Frames.Saved.vals) := by
  obtain ⟨bt, ins, outs, remaining, base, callback, read, post⟩ := reader_enter_wasm2 p .then_ (.inr (.inr rfl))
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx
      (by simpa [Wasm2.Frames.Form.opcode, global_simps] using byte)
      (by simpa [Wasm2.Frames.Form.opcode, global_simps] using accepted)
  have liveLayout := (invariant.live reachable).2.layout
  obtain ⟨front, signature, oldTypes, newTypes, known, selected, matched, controls, valuesFit, words, height⟩ :=
    post.callback_inputs (.inr (.inr rfl)) (reach.current reachable) (invariant.known reachable) liveLayout signatures
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES, limits.MAX_MODULE_BYTES] at size ⊢
    omega
  have consumed : p.start.val < out.core.pos.val := by
    have position := p.pos
    have advanced := post.after.2.1
    omega
  obtain ⟨condition, conditionEq, certified⟩ := structured_callback_if_prefix ops law initial before after types functions returns locals parents current
    st.core.vals.val p.start.val invariant reachable out.core (Wasm2.Frames.Saved.fresh base .then_ bt ins outs).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Wasm2.Frames.Saved.ctrl) bt signature front
    (ins.map Translate.valueType) (outs.map Translate.valueType) selected matched controls valuesFit words
    (by simpa [Wasm2.Frames.Form.args, List.append_assoc] using oldTypes) ⟨known, newTypes⟩ sourceBound consumed callback
  refine ⟨bt, ins, outs, remaining, base, front, condition, post, certified, ?_, ?_, ?_⟩
  · apply same.enter _ _ _ remaining
    exact SourceScopeMatchesWasm2.fresh bt .then_ _ (.then_ condition) base ins outs front _ _ true
  · apply reach.push after.reachable _ {p.current with vals := remaining} _ rfl (fun _ => reachable)
    intro _
    rfl
  · exact post.scope_fronts (.inr (.inr rfl)) fronts _ (by simpa [SourceScope.enterIf] using newTypes)

end Itasca.Runtime.Code

end
