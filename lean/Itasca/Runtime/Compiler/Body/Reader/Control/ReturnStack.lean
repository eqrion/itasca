import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixOpen
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchCertificates
import Itasca.Runtime.Compiler.Body.Callbacks.Calls.ScopeCallbackInputs
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Reader.Control.FrontTransitions
import Itasca.Runtime.Compiler.Body.Reader.Control.Return
import Itasca.Runtime.Compiler.Body.Reader.Stacks.Stacks

/-!
Sections, each formerly its own module: LoopPrefix, ReturnStack.
-/

/-! ## LoopPrefix -/

section

/-!
Structured loop reader prefixes and their complete-profile transport. These are control-map proofs, not Wasm table operations.
-/

/-! ## Structured Reader Prefix Loop -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- A literal successful LOOP callback lifts its exact emitted frame to the
whole source-prefix invariant. Reader wrappers below supply the type/base facts. -/
theorem structured_callback_loop_prefix {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
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
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_loop ops before state bt = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals (parents ++ [current])
      (SourceScope.enterLoop (Wasm2.blockType bt) front params results before.function.code.val.length true)
      state.vals.val state.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨codeFits, offsetsFit, mapsFit, framesFit⟩ := invariant.capacities sourceBound
  obtain ⟨_, parentFrame, _, _, parentShape⟩ := invariant.frames.split
  have bound := invariant.codeBudget.fetch_bound sourceBound
  let pc : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  have positionPc : pc.val = before.function.code.val.length := rfl
  have localWidth : before.function.local_slots.val = slots locals := by
    rw [retained.layout.localSlots, retained.localsEq]
  have coordinates := control_entry_coordinates ops before after state ctrl prior .Loop bt controls valuesFit accepted
  obtain ⟨codeEq, live, height, source, sourceEq, framesEq, mapsEq, fresh, nested, preserve⟩ :=
    callback_loop_scope ops law before after state ctrl prior bt signature pc locals front params results
      parents current parentFrame invariant.frames.nested parentShape localWidth words matched.paramWords matched.resultWords
      controls selected valuesFit coordinates.1 coordinates.2 positionPc codeFits offsetsFit mapsFit framesFit reachable accepted
  let child := SourceScope.enterLoop (Wasm2.blockType bt) front params results before.function.code.val.length true
  let frame : runtime.compiler.Frame := ⟨alloc.vec.Vec.len before.function.controls, .Loop, height,
    signature.param_slots, signature.result_slots, pc, none, true, false, alloc.vec.Vec.new Usize⟩
  have aligned : ScopeFrameStack locals after (parents ++ [current]) child :=
    invariant.frames.push child frame framesEq preserve fresh parentShape.bodyBound (by simp [child, SourceScope.enterLoop])
  have stable := compiler_enter_stable_result ops law before after state .Loop bt (.Ok ()) accepted
  have observed : CompilerLayout after (front ++ params) := by
    have localBefore : LocalLayout before := ⟨retained.layout.localSlots, retained.layout.localOffsets⟩
    simpa only [newTypes.decoded] using compiler_enter_layout_success ops law before after state .Loop bt
      newTypes.concrete (stable.local_layout localBefore) accepted
  have sources := compiler_enter_sources ops law before after state .Loop bt accepted
  have cursor := compiler_enter_cursor ops law before after state .Loop bt accepted
  apply invariant.open_plain reachable live child frame [.LoopHead] stable aligned
    codeEq framesEq (by simp [mapsEq]) rfl rfl (DormantFrame.entered rfl) rfl (by trivial)
    (by simpa only [oldTypes] using observed)
    ⟨newTypes.concrete, newTypes.decoded.trans oldTypes.symm⟩ rfl rfl
    (by simp [child, SourceScope.enterLoop, codeEq]) rfl
    (by simpa [child, SourceScope.enterLoop, SourceScope.input] using oldTypes.symm)
    (by simpa [child, SourceScope.enterLoop, SourceScope.arguments, SourceScope.input] using oldTypes.symm)
    sources (by simp) consumed (by rw [cursor])

end Itasca.Runtime.Compiler

end

/-! ## Structured Reader Prefix Loop Wasm2 -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- An accepted canonical LOOP reader constructs the complete live child
compiler prefix, its source zipper, and validator reachability correspondence. -/
theorem structured_reader_prefix_loop_wasm2 {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env localTypes index st}
    (p : Wasm2.Pending data env localTypes index st) {A : Type}
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
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOOP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_LOOP before = .ok (.Ok (), out, after)) :
    ∃ bt ins outs remaining base front,
      let child := SourceScope.enterLoop (Wasm2.blockType bt) front (ins.map Translate.valueType)
        (outs.map Translate.valueType) before.function.code.val.length true
      Wasm2.ReaderEnterPost p out .loop bt ins outs remaining base ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals (parents ++ [current]) child out.core.vals.val out.core.pos.val ∧
      ReaderScopeZipperWasm2 (parents ++ [current]) child
        (p.parents ++ [{p.current with vals := remaining}]) (Wasm2.Frames.Saved.fresh base .loop bt ins outs) ∧
      ReaderReachabilityWasm2 after.reachable (parents ++ [current]) child
        (p.parents ++ [{p.current with vals := remaining}]) (Wasm2.Frames.Saved.fresh base .loop bt ins outs) ∧
      ReaderScopeFronts (parents ++ [current]) child
        ((p.parents ++ [{p.current with vals := remaining}]).map Wasm2.Frames.Saved.vals) := by
  obtain ⟨bt, ins, outs, remaining, base, callback, read, post⟩ := reader_enter_wasm2 p .loop (.inr (.inl rfl))
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx
      (by simpa [Wasm2.Frames.Form.opcode, global_simps] using byte)
      (by simpa [Wasm2.Frames.Form.opcode, global_simps] using accepted)
  have liveLayout := (invariant.live reachable).2.layout
  obtain ⟨front, signature, oldTypes, newTypes, known, selected, matched, controls, valuesFit, words, height⟩ :=
    post.callback_inputs (.inr (.inl rfl)) (reach.current reachable) (invariant.known reachable) liveLayout signatures
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
  have certified := structured_callback_loop_prefix ops law initial before after types functions returns locals parents current
    st.core.vals.val p.start.val invariant reachable out.core (Wasm2.Frames.Saved.fresh base .loop bt ins outs).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Wasm2.Frames.Saved.ctrl) bt signature front
    (ins.map Translate.valueType) (outs.map Translate.valueType) selected matched controls valuesFit words
    (by simpa [Wasm2.Frames.Form.args] using oldTypes) ⟨known, newTypes⟩ sourceBound consumed callback
  refine ⟨bt, ins, outs, remaining, base, front, post, certified, ?_, ?_, ?_⟩
  · apply same.enter _ _ _ remaining
    exact SourceScopeMatchesWasm2.fresh bt .loop _ .loop base ins outs front _ _ true
  · apply reach.push after.reachable _ {p.current with vals := remaining} _ rfl (fun _ => reachable)
    intro _
    rfl
  · exact post.scope_fronts (.inr (.inl rfl)) fronts _ (by simpa [SourceScope.enterLoop] using newTypes)

end Itasca.Runtime.Compiler

end

end

/-! ## ReturnStack -/

section

/-!
Operand-stack facts at a return reader step.

Main declarations: `reader_return_stack_wasm2`. A direct consumer is `Compiler.Body.Reader.Control.ReachedReturnAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

private theorem return_stack_suffix {before outer segment rest : List code.StackType} {results : List valtype}
    (values : before = outer ++ segment) (known : ConcreteStack before)
    (transfer : ∀ ts, Sequence.Realizes false rest ts → Sequence.Realizes false segment (ts ++ results)) :
    ∃ front, Sequence.stackTypes before = front ++ results := by
  have segmentKnown := (concrete_stack_append.mp (values ▸ known)).2
  have types := realized_concrete_types segmentKnown (transfer _ (Sequence.realizes_default false rest))
  refine ⟨Sequence.stackTypes outer ++ Sequence.stackTypes rest, ?_⟩
  simpa [Sequence.stackTypes, values, List.map_append, List.append_assoc] using
    congrArg (Sequence.stackTypes outer ++ ·) types.symm

theorem reader_return_stack_wasm2 (st out : code.BodyState) (env : metadata.Env) (index : U32)
    (results : List wasm_types.ValueType) (outer segment : List code.StackType)
    (resolved : Wasm2.resolve env (.Type index .Results) = some results)
    (values : st.core.vals.val = outer ++ segment) (base : (Control.base st.core).val = outer.length)
    (known : ConcreteStack st.core.vals.val) (mono : Control.polymorphic st.core = false)
    (accepted : Wasm2.returnStep st env index = .ok (.Ok (), out)) :
    ∃ front, Sequence.stackTypes st.core.vals.val = front ++ results.map Translate.valueType := by
  obtain ⟨⟨result, middle⟩, popped, _, _, rest, _, _, transfer⟩ := WP.spec_imp_exists
    (code.pop_results.realizes st.core env (.Type index .Results) results outer segment resolved values base)
  cases result with
  | Err error => simp [Wasm2.returnStep, popped] at accepted
  | Ok unit =>
    have effect := transfer rfl
    try dsimp only at effect
    rw [mono] at effect
    exact return_stack_suffix values known effect

end Itasca.Runtime.Compiler

end
