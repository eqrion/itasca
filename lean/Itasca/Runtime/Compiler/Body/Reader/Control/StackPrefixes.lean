import Itasca.Runtime.Compiler.Body.Control.CompiledBody
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CallbackRetention
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Local.Callbacks.MetadataPreservation
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlCoordinates
import Itasca.Runtime.Compiler.Body.Callbacks.ScopeInputs
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Reader.Control.EndCompilation
import Itasca.Runtime.Compiler.Body.Reader.StackValues

/-!
Proofs for Runtime / Compiler / Body / Reader / Control.

This module collects ReturnStack, BlockPrefix.
Each section documents its contracts and consumers.
-/

/-! ## ReturnStack -/

section

open Itasca.Representation

/-! ## LoopPrefix -/

section

/-!
Structured loop reader prefixes and their complete transport. These are control-map proofs, not Wasm table operations.
-/

/-! ## Structured Reader Prefix Loop -/

section

namespace Itasca.Compiler
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
    (oldTypes : Body.Stack.stackTypes raw = front ++ params)
    (newTypes : SourceStack state.vals.val (front ++ params))
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_loop ops before state bt = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals (parents ++ [current])
      (SourceScope.enterLoop (Body.blockType bt) front params results before.function.code.val.length true)
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
  let child := SourceScope.enterLoop (Body.blockType bt) front params results before.function.code.val.length true
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

end Itasca.Compiler

end

/-! ## Structured Reader Prefix Loop Body -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- An accepted canonical LOOP reader constructs the complete live child
compiler prefix, its source zipper, and validator reachability correspondence. -/
theorem structured_reader_prefix_loop {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env localTypes index st}
    (p : Body.Pending data env localTypes index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (reach : BodyReaderReachability before.reachable parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (reachable : before.reachable = true)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOOP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_LOOP before = .ok (.Ok (), out, after)) :
    ∃ bt ins outs remaining base front,
      let child := SourceScope.enterLoop (Body.blockType bt) front (ins.map Translation.valueType)
        (outs.map Translation.valueType) before.function.code.val.length true
      Body.ReaderEnterPost p out .loop bt ins outs remaining base ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals (parents ++ [current]) child out.core.vals.val out.core.pos.val ∧
      ReaderScopeZipper (parents ++ [current]) child
        (p.parents ++ [{p.current with vals := remaining}]) (Body.Frames.Saved.fresh base .loop bt ins outs) ∧
      BodyReaderReachability after.reachable (parents ++ [current]) child
        (p.parents ++ [{p.current with vals := remaining}]) (Body.Frames.Saved.fresh base .loop bt ins outs) ∧
      ReaderScopeFronts (parents ++ [current]) child
        ((p.parents ++ [{p.current with vals := remaining}]).map Body.Frames.Saved.vals) := by
  obtain ⟨bt, ins, outs, remaining, base, callback, read, post⟩ := reader_enter p .loop (.inr (.inl rfl))
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx
      (by simpa [Body.Frames.Form.opcode, global_simps] using byte)
      (by simpa [Body.Frames.Form.opcode, global_simps] using accepted)
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
    st.core.vals.val p.start.val invariant reachable out.core (Body.Frames.Saved.fresh base .loop bt ins outs).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Body.Frames.Saved.ctrl) bt signature front
    (ins.map Translation.valueType) (outs.map Translation.valueType) selected matched controls valuesFit words
    (by simpa [Body.Frames.Form.args] using oldTypes) ⟨known, newTypes⟩ sourceBound consumed callback
  refine ⟨bt, ins, outs, remaining, base, front, post, certified, ?_, ?_, ?_⟩
  · apply same.enter _ _ _ remaining
    exact SourceScopeMatches.fresh bt .loop _ .loop base ins outs front _ _ true
  · apply reach.push after.reachable _ {p.current with vals := remaining} _ rfl (fun _ => reachable)
    intro _
    rfl
  · exact post.scope_fronts (.inr (.inl rfl)) fronts _ (by simpa [SourceScope.enterLoop] using newTypes)

end Itasca.Compiler

end

end

/-! ## ReturnStack -/

section

/-!
Operand-stack facts at a return reader step.

Main declarations: `reader_return_stack`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

private theorem return_stack_suffix {before outer segment rest : List code.StackType} {results : List valtype}
    (values : before = outer ++ segment) (known : ConcreteStack before)
    (transfer : ∀ ts, Body.Stack.Realizes false rest ts → Body.Stack.Realizes false segment (ts ++ results)) :
    ∃ front, Body.Stack.stackTypes before = front ++ results := by
  have segmentKnown := (concrete_stack_append.mp (values ▸ known)).2
  have types := realized_concrete_types segmentKnown (transfer _ (Body.Stack.realizes_default false rest))
  refine ⟨Body.Stack.stackTypes outer ++ Body.Stack.stackTypes rest, ?_⟩
  simpa [Body.Stack.stackTypes, values, List.map_append, List.append_assoc] using
    congrArg (Body.Stack.stackTypes outer ++ ·) types.symm

theorem reader_return_stack (st out : code.BodyState) (env : metadata.Env) (index : U32)
    (results : List wasm_types.ValueType) (outer segment : List code.StackType)
    (resolved : Body.resolve env (.Type index .Results) = some results)
    (values : st.core.vals.val = outer ++ segment) (base : (Body.Control.base st.core).val = outer.length)
    (known : ConcreteStack st.core.vals.val) (mono : Body.Control.polymorphic st.core = false)
    (accepted : Body.returnStep st env index = .ok (.Ok (), out)) :
    ∃ front, Body.Stack.stackTypes st.core.vals.val = front ++ results.map Translation.valueType := by
  obtain ⟨⟨result, middle⟩, popped, _, _, rest, _, _, transfer⟩ := WP.spec_imp_exists
    (code.pop_results.realizes st.core env (.Type index .Results) results outer segment resolved values base)
  cases result with
  | Err error => simp [Body.returnStep, popped] at accepted
  | Ok unit =>
    have effect := transfer rfl
    try dsimp only at effect
    rw [mono] at effect
    exact return_stack_suffix values known effect

end Itasca.Compiler

end

end

/-! ## BlockPrefix -/

section

open Itasca.Representation

/-!
A literal successful BLOCK callback lifts its exact emitted frame to the whole source-prefix invariant. Reader wrappers below supply the type/base facts.

Main declarations: `structured_callback_block_prefix`.
-/

namespace Itasca.Compiler
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
    (oldTypes : Body.Stack.stackTypes raw = front ++ params)
    (newTypes : SourceStack state.vals.val (front ++ params))
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_block ops before state bt = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals (parents ++ [current])
      (SourceScope.enterBlock (Body.blockType bt) front params results before.function.code.val.length true)
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
  let child := SourceScope.enterBlock (Body.blockType bt) front params results before.function.code.val.length true
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

end Itasca.Compiler

end
