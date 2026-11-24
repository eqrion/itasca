import Itasca.Runtime.Compiler.Body.Reader.Control.StackPrefixes
import Itasca.Runtime.Compiler.Body.Callbacks.ScopeInputs
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Reader.Control.EndCompilation
import Itasca.Runtime.Compiler.Body.Control.BranchesAndDormantEntry
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CallbackRetention
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Local.Callbacks.MetadataPreservation
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlCoordinates
import Itasca.Runtime.Compiler.Local.Relations.Stacks.ConcretePops
import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Runtime.Compiler.Local.Capacity.AuxiliaryGrowth
import Itasca.Runtime.Compiler.Local.Capacity.SimdAuxiliaryGrowth
import Itasca.Runtime.Compiler.Body.Reader.Replay.OrdinaryEffects
import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedCapacity
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchAndCallMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupPreservation
import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth
import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Runtime.Compiler.Body.Reader.References.TypedSelectEmission
import Itasca.Runtime.Compiler.Body.Reader.Simd.Dispatch
import Itasca.Runtime.Compiler.Local.Relations.Syntax.ReaderOpcode
import Itasca.Runtime.Compiler.Local.Lowering.Integer.Lowering
import Itasca.Runtime.Compiler.Body.Callbacks.CompilerPrefixStart
import Itasca.Runtime.Compiler.Body.Reader.Scalar.ScalarEffects
import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.Compiler.Local.Source.SourceTactics
import Itasca.Runtime.Compiler.Local.Relations.Operations.CoreBasicEmissions
import Itasca.Runtime.Compiler.Local.Lowering.Literal.SourceEffects
import Itasca.Runtime.Compiler.Local.Lowering.LoweringLocal
import Itasca.Runtime.Compiler.Body.CapacityTrace
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEffects
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Body.Reader.Calls.Acceptance
import Itasca.Support.Translation
import Itasca.Runtime.Compiler.Local.Capacity.EmissionGrowth
import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchAndTerminalEffects
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchAndScopeEffects
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EntryAndElseFrames
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalRoot
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Local.Source.TypedRunClosed
import Itasca.Runtime.Compiler.Body.Relations.Control.ReachedControlSafety
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchAndElseCompilation

/-!
Proofs for Runtime / Compiler / Body / Reader / Replay.

This module collects EnterCompilation, OrdinaryLedger.
Each section documents its contracts and consumers.
-/

/-! ## EnterCompilation -/

section

open Itasca.Representation

/-!
# Structured control entry compilation

Live and dormant BLOCK, LOOP and IF prefixes supply the entered compiler invariant and compose into the source-bound entry construction.
-/

/-! ## BlockReaderPrefix -/

section BlockReaderPrefix

/-!
An accepted canonical BLOCK reader constructs the complete live child compiler prefix, its source zipper, and validator reachability correspondence.

Main declarations: `structured_reader_prefix_block`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- An accepted canonical BLOCK reader constructs the complete live child
compiler prefix, its source zipper, and validator reachability correspondence. -/
theorem structured_reader_prefix_block {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env localTypes index st}
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
    (byte : data.val[p.start.val]'p.inbounds = code.OP_BLOCK)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_BLOCK before = .ok (.Ok (), out, after)) :
    ∃ bt ins outs remaining base front,
      let child := SourceScope.enterBlock (Body.blockType bt) front (ins.map Translation.valueType)
        (outs.map Translation.valueType) before.function.code.val.length true
      Body.ReaderEnterPost p out .block bt ins outs remaining base ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals (parents ++ [current]) child out.core.vals.val out.core.pos.val ∧
      ReaderScopeZipper (parents ++ [current]) child
        (p.parents ++ [{p.current with vals := remaining}]) (Body.Frames.Saved.fresh base .block bt ins outs) ∧
      BodyReaderReachability after.reachable (parents ++ [current]) child
        (p.parents ++ [{p.current with vals := remaining}]) (Body.Frames.Saved.fresh base .block bt ins outs) ∧
      ReaderScopeFronts (parents ++ [current]) child
        ((p.parents ++ [{p.current with vals := remaining}]).map Body.Frames.Saved.vals) := by
  obtain ⟨bt, ins, outs, remaining, base, callback, read, post⟩ := reader_enter p .block (.inl rfl)
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx
      (by simpa [Body.Frames.Form.opcode, global_simps] using byte)
      (by simpa [Body.Frames.Form.opcode, global_simps] using accepted)
  have liveLayout := (invariant.live reachable).2.layout
  obtain ⟨front, signature, oldTypes, newTypes, known, selected, matched, controls, valuesFit, words, height⟩ :=
    post.callback_inputs (.inl rfl) (reach.current reachable) (invariant.known reachable) liveLayout signatures
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
  have certified := structured_callback_block_prefix ops law initial before after types functions returns locals parents current
    st.core.vals.val p.start.val invariant reachable out.core (Body.Frames.Saved.fresh base .block bt ins outs).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Body.Frames.Saved.ctrl) bt signature front
    (ins.map Translation.valueType) (outs.map Translation.valueType) selected matched controls valuesFit words
    (by simpa [Body.Frames.Form.args] using oldTypes) ⟨known, newTypes⟩ sourceBound consumed callback
  refine ⟨bt, ins, outs, remaining, base, front, post, certified, ?_, ?_, ?_⟩
  · apply same.enter _ _ _ remaining
    exact SourceScopeMatches.fresh bt .block _ .block base ins outs front _ _ true
  · apply reach.push after.reachable _ {p.current with vals := remaining} _ rfl (fun _ => reachable)
    intro _
    rfl
  · exact post.scope_fronts (.inl rfl) fronts _ (by simpa [SourceScope.enterBlock] using newTypes)

end Itasca.Compiler

end BlockReaderPrefix

/-! ## BlockDormantPrefix -/

section BlockDormantPrefix

/-!
Dormant block reader prefixes and source-prefix transport, retaining omitted-code and control-map obligations.
-/

/-! ## Structured Reader Prefix Block Dormant -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_callback_block_dead_prefix {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (dead : before.reachable = false)
    (state : code.OpIterState) (ctrl : code.Ctrl) (prior : List code.Ctrl)
    (bt : signature.BlockType) (signature : runtime.compiler.Signature)
    (front params results : List valtype)
    (selected : SignatureAt before.signatures bt signature) (matched : SignatureMatches signature params results)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_block ops before state bt = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals (parents ++ [current])
      (SourceScope.enterBlock (Body.blockType bt) front params results before.function.code.val.length false) state.vals.val state.pos.val := by
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
  let child := SourceScope.enterBlock (Body.blockType bt) front params results before.function.code.val.length false
  let frame : runtime.compiler.Frame := ⟨alloc.vec.Vec.len before.function.controls, .Block, height,
    signature.param_slots, signature.result_slots, pc, none, false, false, alloc.vec.Vec.new Usize⟩
  have aligned : ScopeFrameStack locals after (parents ++ [current]) child :=
    invariant.frames.push child frame framesEq preserve fresh parentShape.bodyBound (by simp [child, SourceScope.enterBlock])
  have stable := compiler_enter_stable_result ops law before after state .Block bt (.Ok ()) accepted
  have sources := compiler_enter_sources ops law before after state .Block bt accepted
  have cursor := compiler_enter_cursor ops law before after state .Block bt accepted
  exact invariant.open_dormant dead deadAfter child frame stable aligned codeEq framesEq
    (by simp [mapsEq]) rfl rfl (DormantFrame.fresh rfl rfl) rfl rfl rfl sources consumed (by rw [cursor])

end Itasca.Compiler

end

/-! ## Structured Reader Prefix Block Dormant Body -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

theorem structured_reader_prefix_block_dead {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env localTypes index st}
    (p : Body.Pending data env localTypes index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (reach : BodyReaderReachability before.reachable parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (dead : before.reachable = false)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_BLOCK)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_BLOCK before = .ok (.Ok (), out, after)) :
    ∃ bt ins outs remaining base front,
      let child := SourceScope.enterBlock (Body.blockType bt) front (ins.map Translation.valueType) (outs.map Translation.valueType) before.function.code.val.length false
      Body.ReaderEnterPost p out .block bt ins outs remaining base ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals (parents ++ [current]) child out.core.vals.val out.core.pos.val ∧
      ReaderScopeZipper (parents ++ [current]) child
        (p.parents ++ [{p.current with vals := remaining}]) (Body.Frames.Saved.fresh base .block bt ins outs) ∧
      BodyReaderReachability after.reachable (parents ++ [current]) child
        (p.parents ++ [{p.current with vals := remaining}]) (Body.Frames.Saved.fresh base .block bt ins outs) ∧
      ReaderScopeFronts (parents ++ [current]) child
        ((p.parents ++ [{p.current with vals := remaining}]).map Body.Frames.Saved.vals) := by
  obtain ⟨bt, ins, outs, remaining, base, callback, read, post⟩ := reader_enter p .block (.inl rfl)
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx
      (by simpa [Body.Frames.Form.opcode, global_simps] using byte)
      (by simpa [Body.Frames.Form.opcode, global_simps] using accepted)
  obtain ⟨signature, selected, matched⟩ := signatures.select post.inputs post.outputs
  obtain ⟨controls, valuesFit, _, _⟩ := post.front (.inl rfl)
  let front := Body.Stack.stackTypes (out.core.vals.val.take base.val)
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
  have certified := structured_callback_block_dead_prefix ops law initial before after types functions returns locals parents current
    st.core.vals.val p.start.val invariant dead out.core (Body.Frames.Saved.fresh base .block bt ins outs).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Body.Frames.Saved.ctrl) bt signature front
    (ins.map Translation.valueType) (outs.map Translation.valueType) selected matched controls valuesFit
    sourceBound consumed callback
  refine ⟨bt, ins, outs, remaining, base, front, post, certified, ?_, ?_, ?_⟩
  · apply same.enter _ _ _ remaining
    exact SourceScopeMatches.fresh bt .block _ .block base ins outs front _ _ false
  · apply reach.push after.reachable _ {p.current with vals := remaining} _ rfl
      (by simp [SourceScope.enterBlock])
    intro _
    rfl
  · exact post.scope_fronts_dormant (.inl rfl) fronts _ rfl

end Itasca.Compiler

end

end BlockDormantPrefix

/-! ## IfPrefix -/

section IfPrefix

/-!
Structured if reader prefixes and their complete transport. These are control-map proofs, not Wasm table operations.
-/

/-! ## Structured Reader Prefix If -/

section

namespace Itasca.Compiler
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
    (oldTypes : Body.Stack.stackTypes raw = (front ++ params) ++ [.I32])
    (newTypes : SourceStack state.vals.val (front ++ params))
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_if ops before state bt = .ok (.Ok (), after)) :
    ∃ condition,
      condition.val = slots locals + slots (front ++ params) ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals (parents ++ [current])
        (SourceScope.enterIf (Body.blockType bt) condition front params results before.function.code.val.length true)
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
  let child := SourceScope.enterIf (Body.blockType bt) condition front params results before.function.code.val.length true
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

end Itasca.Compiler

end

/-! ## Structured Reader Prefix If Body -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- An accepted canonical IF reader constructs the complete live child
compiler prefix, its source zipper, and validator reachability correspondence. -/
theorem structured_reader_prefix_if {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env localTypes index st}
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
    (byte : data.val[p.start.val]'p.inbounds = code.OP_IF)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_IF before = .ok (.Ok (), out, after)) :
    ∃ bt ins outs remaining base front condition,
      let child := SourceScope.enterIf (Body.blockType bt) condition front (ins.map Translation.valueType)
        (outs.map Translation.valueType) before.function.code.val.length true
      Body.ReaderEnterPost p out .then_ bt ins outs remaining base ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals (parents ++ [current]) child out.core.vals.val out.core.pos.val ∧
      ReaderScopeZipper (parents ++ [current]) child
        (p.parents ++ [{p.current with vals := remaining}]) (Body.Frames.Saved.fresh base .then_ bt ins outs) ∧
      BodyReaderReachability after.reachable (parents ++ [current]) child
        (p.parents ++ [{p.current with vals := remaining}]) (Body.Frames.Saved.fresh base .then_ bt ins outs) ∧
      ReaderScopeFronts (parents ++ [current]) child
        ((p.parents ++ [{p.current with vals := remaining}]).map Body.Frames.Saved.vals) := by
  obtain ⟨bt, ins, outs, remaining, base, callback, read, post⟩ := reader_enter p .then_ (.inr (.inr rfl))
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx
      (by simpa [Body.Frames.Form.opcode, global_simps] using byte)
      (by simpa [Body.Frames.Form.opcode, global_simps] using accepted)
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
    st.core.vals.val p.start.val invariant reachable out.core (Body.Frames.Saved.fresh base .then_ bt ins outs).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Body.Frames.Saved.ctrl) bt signature front
    (ins.map Translation.valueType) (outs.map Translation.valueType) selected matched controls valuesFit words
    (by simpa [Body.Frames.Form.args, List.append_assoc] using oldTypes) ⟨known, newTypes⟩ sourceBound consumed callback
  refine ⟨bt, ins, outs, remaining, base, front, condition, post, certified, ?_, ?_, ?_⟩
  · apply same.enter _ _ _ remaining
    exact SourceScopeMatches.fresh bt .then_ _ (.then_ condition) base ins outs front _ _ true
  · apply reach.push after.reachable _ {p.current with vals := remaining} _ rfl (fun _ => reachable)
    intro _
    rfl
  · exact post.scope_fronts (.inr (.inr rfl)) fronts _ (by simpa [SourceScope.enterIf] using newTypes)

end Itasca.Compiler

end

end IfPrefix

/-! ## IfDormantPrefix -/

section IfDormantPrefix

/-!
Dormant if reader prefixes and source-prefix transport, retaining omitted-code and control-map obligations.
-/

/-! ## Structured Reader Prefix If Dormant -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_callback_if_dead_prefix {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (dead : before.reachable = false)
    (state : code.OpIterState) (ctrl : code.Ctrl) (prior : List code.Ctrl)
    (bt : signature.BlockType) (signature : runtime.compiler.Signature)
    (front params results : List valtype)
    (selected : SignatureAt before.signatures bt signature) (matched : SignatureMatches signature params results)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_if ops before state bt = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals (parents ++ [current])
      (SourceScope.enterIf (Body.blockType bt) 0#u32 front params results before.function.code.val.length false) state.vals.val state.pos.val := by
  obtain ⟨_, _, mapsFit, framesFit⟩ := invariant.capacities sourceBound
  obtain ⟨_, parentFrame, _, _, parentShape⟩ := invariant.frames.split
  have bound := invariant.codeBudget.fetch_bound sourceBound
  let pc : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  have positionPc : pc.val = before.function.code.val.length := rfl
  have coordinates := control_entry_coordinates ops before after state ctrl prior .Then bt controls valuesFit accepted
  obtain ⟨codeEq, deadAfter, height, source, sourceEq, framesEq, mapsEq, fresh, nested, preserve⟩ :=
    callback_if_dead_scope ops law before after state ctrl prior bt signature pc locals front params results
      parents current parentFrame invariant.frames.nested parentShape matched.paramWords matched.resultWords
      controls selected valuesFit coordinates.1 coordinates.2 positionPc mapsFit framesFit dead accepted
  let child := SourceScope.enterIf (Body.blockType bt) 0#u32 front params results before.function.code.val.length false
  let frame : runtime.compiler.Frame := ⟨alloc.vec.Vec.len before.function.controls, .Then, height,
    signature.param_slots, signature.result_slots, pc, none, false, false, alloc.vec.Vec.new Usize⟩
  have aligned : ScopeFrameStack locals after (parents ++ [current]) child :=
    invariant.frames.push child frame framesEq preserve fresh parentShape.bodyBound (by simp [child, SourceScope.enterIf])
  have stable := compiler_enter_stable_result ops law before after state .Then bt (.Ok ()) accepted
  have sources := compiler_enter_sources ops law before after state .Then bt accepted
  have cursor := compiler_enter_cursor ops law before after state .Then bt accepted
  exact invariant.open_dormant dead deadAfter child frame stable aligned codeEq framesEq
    (by simp [mapsEq]) rfl rfl (DormantFrame.fresh rfl rfl) rfl rfl rfl sources consumed (by rw [cursor])

end Itasca.Compiler

end

/-! ## Structured Reader Prefix If Dormant Body -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

theorem structured_reader_prefix_if_dead {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env localTypes index st}
    (p : Body.Pending data env localTypes index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (reach : BodyReaderReachability before.reachable parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (dead : before.reachable = false)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_IF)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_IF before = .ok (.Ok (), out, after)) :
    ∃ bt ins outs remaining base front,
      let child := SourceScope.enterIf (Body.blockType bt) 0#u32 front (ins.map Translation.valueType) (outs.map Translation.valueType) before.function.code.val.length false
      Body.ReaderEnterPost p out .then_ bt ins outs remaining base ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals (parents ++ [current]) child out.core.vals.val out.core.pos.val ∧
      ReaderScopeZipper (parents ++ [current]) child
        (p.parents ++ [{p.current with vals := remaining}]) (Body.Frames.Saved.fresh base .then_ bt ins outs) ∧
      BodyReaderReachability after.reachable (parents ++ [current]) child
        (p.parents ++ [{p.current with vals := remaining}]) (Body.Frames.Saved.fresh base .then_ bt ins outs) ∧
      ReaderScopeFronts (parents ++ [current]) child
        ((p.parents ++ [{p.current with vals := remaining}]).map Body.Frames.Saved.vals) := by
  obtain ⟨bt, ins, outs, remaining, base, callback, read, post⟩ := reader_enter p .then_ (.inr (.inr rfl))
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx
      (by simpa [Body.Frames.Form.opcode, global_simps] using byte)
      (by simpa [Body.Frames.Form.opcode, global_simps] using accepted)
  obtain ⟨signature, selected, matched⟩ := signatures.select post.inputs post.outputs
  obtain ⟨controls, valuesFit, _, _⟩ := post.front (.inr (.inr rfl))
  let front := Body.Stack.stackTypes (out.core.vals.val.take base.val)
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
  have certified := structured_callback_if_dead_prefix ops law initial before after types functions returns locals parents current
    st.core.vals.val p.start.val invariant dead out.core (Body.Frames.Saved.fresh base .then_ bt ins outs).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Body.Frames.Saved.ctrl) bt signature front
    (ins.map Translation.valueType) (outs.map Translation.valueType) selected matched controls valuesFit
    sourceBound consumed callback
  refine ⟨bt, ins, outs, remaining, base, front, post, certified, ?_, ?_, ?_⟩
  · apply same.enter _ _ _ remaining
    exact SourceScopeMatches.fresh bt .then_ _ (.then_ 0#u32) base ins outs front _ _ false
  · apply reach.push after.reachable _ {p.current with vals := remaining} _ rfl
      (by simp [SourceScope.enterIf])
    intro _
    rfl
  · exact post.scope_fronts_dormant (.inr (.inr rfl)) fronts _ rfl

end Itasca.Compiler

end

end IfDormantPrefix

/-! ## LoopDormantPrefix -/

section LoopDormantPrefix

/-!
Dormant loop reader prefixes and source-prefix transport, retaining omitted-code and control-map obligations.
-/

/-! ## Structured Reader Prefix Loop Dormant -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_callback_loop_dead_prefix {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (dead : before.reachable = false)
    (state : code.OpIterState) (ctrl : code.Ctrl) (prior : List code.Ctrl)
    (bt : signature.BlockType) (signature : runtime.compiler.Signature)
    (front params results : List valtype)
    (selected : SignatureAt before.signatures bt signature) (matched : SignatureMatches signature params results)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_loop ops before state bt = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals (parents ++ [current])
      (SourceScope.enterLoop (Body.blockType bt) front params results before.function.code.val.length false) state.vals.val state.pos.val := by
  obtain ⟨_, _, mapsFit, framesFit⟩ := invariant.capacities sourceBound
  obtain ⟨_, parentFrame, _, _, parentShape⟩ := invariant.frames.split
  have bound := invariant.codeBudget.fetch_bound sourceBound
  let pc : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  have positionPc : pc.val = before.function.code.val.length := rfl
  have coordinates := control_entry_coordinates ops before after state ctrl prior .Loop bt controls valuesFit accepted
  obtain ⟨codeEq, deadAfter, height, source, sourceEq, framesEq, mapsEq, fresh, nested, preserve⟩ :=
    callback_loop_dead_scope ops law before after state ctrl prior bt signature pc locals front params results
      parents current parentFrame invariant.frames.nested parentShape matched.paramWords matched.resultWords
      controls selected valuesFit coordinates.1 coordinates.2 positionPc mapsFit framesFit dead accepted
  let child := SourceScope.enterLoop (Body.blockType bt) front params results before.function.code.val.length false
  let frame : runtime.compiler.Frame := ⟨alloc.vec.Vec.len before.function.controls, .Loop, height,
    signature.param_slots, signature.result_slots, pc, none, false, false, alloc.vec.Vec.new Usize⟩
  have aligned : ScopeFrameStack locals after (parents ++ [current]) child :=
    invariant.frames.push child frame framesEq preserve fresh parentShape.bodyBound (by simp [child, SourceScope.enterLoop])
  have stable := compiler_enter_stable_result ops law before after state .Loop bt (.Ok ()) accepted
  have sources := compiler_enter_sources ops law before after state .Loop bt accepted
  have cursor := compiler_enter_cursor ops law before after state .Loop bt accepted
  exact invariant.open_dormant dead deadAfter child frame stable aligned codeEq framesEq
    (by simp [mapsEq]) rfl rfl (DormantFrame.fresh rfl rfl) rfl rfl rfl sources consumed (by rw [cursor])

end Itasca.Compiler

end

/-! ## Structured Reader Prefix Loop Dormant Body -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

theorem structured_reader_prefix_loop_dead {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env localTypes index st}
    (p : Body.Pending data env localTypes index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (reach : BodyReaderReachability before.reachable parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (dead : before.reachable = false)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOOP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_LOOP before = .ok (.Ok (), out, after)) :
    ∃ bt ins outs remaining base front,
      let child := SourceScope.enterLoop (Body.blockType bt) front (ins.map Translation.valueType) (outs.map Translation.valueType) before.function.code.val.length false
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
  obtain ⟨signature, selected, matched⟩ := signatures.select post.inputs post.outputs
  obtain ⟨controls, valuesFit, _, _⟩ := post.front (.inr (.inl rfl))
  let front := Body.Stack.stackTypes (out.core.vals.val.take base.val)
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
  have certified := structured_callback_loop_dead_prefix ops law initial before after types functions returns locals parents current
    st.core.vals.val p.start.val invariant dead out.core (Body.Frames.Saved.fresh base .loop bt ins outs).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Body.Frames.Saved.ctrl) bt signature front
    (ins.map Translation.valueType) (outs.map Translation.valueType) selected matched controls valuesFit
    sourceBound consumed callback
  refine ⟨bt, ins, outs, remaining, base, front, post, certified, ?_, ?_, ?_⟩
  · apply same.enter _ _ _ remaining
    exact SourceScopeMatches.fresh bt .loop _ .loop base ins outs front _ _ false
  · apply reach.push after.reachable _ {p.current with vals := remaining} _ rfl
      (by simp [SourceScope.enterLoop])
    intro _
    rfl
  · exact post.scope_fronts_dormant (.inr (.inl rfl)) fronts _ rfl

end Itasca.Compiler

end

end LoopDormantPrefix

/-! ## EnterCompilation -/

section EnterCompilation

/-!
Structured block, loop and if reader compilation, preserving each control entry shape.
-/

/-! ## Structured Reader Compiler Enter Block -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerState.enter_block {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_BLOCK)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index code.OP_BLOCK before = .ok (.Ok (), out, after)) :
    ∃ bt ins outs remaining base front, StructuredReaderCompilerState jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      (parents ++ [current]) (SourceScope.enterBlock (Body.blockType bt) front (ins.map Translation.valueType) (outs.map Translation.valueType) before.function.code.val.length before.reachable)
      (savedParents ++ [{savedCurrent with vals := remaining}]) (Body.Frames.Saved.fresh base .block bt ins outs) := by
  let p := state.boundary.pending next advance inbounds
  have signaturesBefore : SignatureSequence before.signatures.val env.types.val := by
    simpa only [state.compiled.metadata.fields.1] using signatures
  cases reach : before.reachable with
  | true =>
    obtain ⟨bt, ins, outs, remaining, base, front, post, compiled, same, reachable, fronts⟩ :=
      structured_reader_prefix_block p ops law initial before after out ctx
        types functions returns locals parents current state.compiled state.sources state.reach state.fronts reach signaturesBefore byte accepted
    refine ⟨bt, ins, outs, remaining, base, front, compiled, ?_, ?_, reachable, fronts, ?_⟩
    · exact post.boundary (.inl rfl)
    · exact same
    · apply post.known_fronts state.knownFronts _
      · intro entered
        apply state.reach.current
        simpa only [SourceScope.enterBlock, reach] using entered
      · intro entered
        apply state.compiled.known
        simpa only [SourceScope.enterBlock, reach] using entered
  | false =>
    obtain ⟨bt, ins, outs, remaining, base, front, post, compiled, same, reachable, fronts⟩ :=
      structured_reader_prefix_block_dead p ops law initial before after out ctx
        types functions returns locals parents current state.compiled state.sources state.reach state.fronts reach signaturesBefore byte accepted
    refine ⟨bt, ins, outs, remaining, base, front, compiled, ?_, ?_, reachable, fronts, ?_⟩
    · exact post.boundary (.inl rfl)
    · exact same
    · apply post.known_fronts state.knownFronts _
      · intro entered
        apply state.reach.current
        simpa only [SourceScope.enterBlock, reach] using entered
      · intro entered
        apply state.compiled.known
        simpa only [SourceScope.enterBlock, reach] using entered

end Itasca.Compiler

end

/-! ## Structured Reader Compiler Enter If -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerState.enter_if {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_IF)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index code.OP_IF before = .ok (.Ok (), out, after)) :
    ∃ bt ins outs remaining base front condition, StructuredReaderCompilerState jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      (parents ++ [current]) (SourceScope.enterIf (Body.blockType bt) condition front (ins.map Translation.valueType) (outs.map Translation.valueType) before.function.code.val.length before.reachable)
      (savedParents ++ [{savedCurrent with vals := remaining}]) (Body.Frames.Saved.fresh base .then_ bt ins outs) := by
  let p := state.boundary.pending next advance inbounds
  have signaturesBefore : SignatureSequence before.signatures.val env.types.val := by
    simpa only [state.compiled.metadata.fields.1] using signatures
  cases reach : before.reachable with
  | true =>
    obtain ⟨bt, ins, outs, remaining, base, front, condition, post, compiled, same, reachable, fronts⟩ :=
      structured_reader_prefix_if p ops law initial before after out ctx
        types functions returns locals parents current state.compiled state.sources state.reach state.fronts reach signaturesBefore byte accepted
    refine ⟨bt, ins, outs, remaining, base, front, condition, compiled, ?_, ?_, reachable, fronts, ?_⟩
    · exact post.boundary (.inr (.inr rfl))
    · exact same
    · apply post.known_fronts state.knownFronts _
      · intro entered
        apply state.reach.current
        simpa only [SourceScope.enterIf, reach] using entered
      · intro entered
        apply state.compiled.known
        simpa only [SourceScope.enterIf, reach] using entered
  | false =>
    obtain ⟨bt, ins, outs, remaining, base, front, post, compiled, same, reachable, fronts⟩ :=
      structured_reader_prefix_if_dead p ops law initial before after out ctx
        types functions returns locals parents current state.compiled state.sources state.reach state.fronts reach signaturesBefore byte accepted
    refine ⟨bt, ins, outs, remaining, base, front, 0#u32, compiled, ?_, ?_, reachable, fronts, ?_⟩
    · exact post.boundary (.inr (.inr rfl))
    · exact same
    · apply post.known_fronts state.knownFronts _
      · intro entered
        apply state.reach.current
        simpa only [SourceScope.enterIf, reach] using entered
      · intro entered
        apply state.compiled.known
        simpa only [SourceScope.enterIf, reach] using entered

end Itasca.Compiler

end

/-! ## Structured Reader Compiler Enter Loop -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerState.enter_loop {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_LOOP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index code.OP_LOOP before = .ok (.Ok (), out, after)) :
    ∃ bt ins outs remaining base front, StructuredReaderCompilerState jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      (parents ++ [current]) (SourceScope.enterLoop (Body.blockType bt) front (ins.map Translation.valueType) (outs.map Translation.valueType) before.function.code.val.length before.reachable)
      (savedParents ++ [{savedCurrent with vals := remaining}]) (Body.Frames.Saved.fresh base .loop bt ins outs) := by
  let p := state.boundary.pending next advance inbounds
  have signaturesBefore : SignatureSequence before.signatures.val env.types.val := by
    simpa only [state.compiled.metadata.fields.1] using signatures
  cases reach : before.reachable with
  | true =>
    obtain ⟨bt, ins, outs, remaining, base, front, post, compiled, same, reachable, fronts⟩ :=
      structured_reader_prefix_loop p ops law initial before after out ctx
        types functions returns locals parents current state.compiled state.sources state.reach state.fronts reach signaturesBefore byte accepted
    refine ⟨bt, ins, outs, remaining, base, front, compiled, ?_, ?_, reachable, fronts, ?_⟩
    · exact post.boundary (.inr (.inl rfl))
    · exact same
    · apply post.known_fronts state.knownFronts _
      · intro entered
        apply state.reach.current
        simpa only [SourceScope.enterLoop, reach] using entered
      · intro entered
        apply state.compiled.known
        simpa only [SourceScope.enterLoop, reach] using entered
  | false =>
    obtain ⟨bt, ins, outs, remaining, base, front, post, compiled, same, reachable, fronts⟩ :=
      structured_reader_prefix_loop_dead p ops law initial before after out ctx
        types functions returns locals parents current state.compiled state.sources state.reach state.fronts reach signaturesBefore byte accepted
    refine ⟨bt, ins, outs, remaining, base, front, compiled, ?_, ?_, reachable, fronts, ?_⟩
    · exact post.boundary (.inr (.inl rfl))
    · exact same
    · apply post.known_fronts state.knownFronts _
      · intro entered
        apply state.reach.current
        simpa only [SourceScope.enterLoop, reach] using entered
      · intro entered
        apply state.compiled.known
        simpa only [SourceScope.enterLoop, reach] using entered

end Itasca.Compiler

end

end EnterCompilation

end

/-! ## OrdinaryLedger -/

section

/-!
Proofs for Runtime / Compiler / Body / Reader / Replay.

This module collects OrdinaryLedger, StructuredScopes.
Each section documents its contracts and consumers.
-/

/-! ## OrdinaryLedger -/

section

/-!
Allocation accounting for ordinary reader steps. Auxiliary-table growth and fixup budgets establish the ReaderAllocationLedger used by reached-body resource proofs.
-/

/-! ## Reader Auxiliary Growth -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_stateful_base_auxiliary_growth {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (opcode : U8)
    (member : opcode.val ∈ [37,38,63,64,208,209,210])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index opcode before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after := by
  obtain ⟨op,a,b,arguments,callback,_⟩ := reader_stateful_base p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx opcode member byte accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact compiler_stateful_auxiliary_growth ops law before after out.core op a b callback

theorem reader_stateful_bulk_auxiliary_growth {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (subopcode : U32) (next : Usize)
    (member : subopcode.val ∈ [8,9,10,11,12,13,14,15,16,17])
    (byte : data.val[p.start.val]'p.inbounds = 252#u8)
    (decoded : Binary.Leb128.Decoded data st.core.pos subopcode next)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 252#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after := by
  obtain ⟨op,a,b,arguments,callback,_⟩ := reader_stateful_bulk p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx subopcode next member byte decoded accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact compiler_stateful_auxiliary_growth ops law before after out.core op a b callback

theorem reader_indirect_call_auxiliary_growth {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 17#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after := by
  obtain ⟨idx,table,values,callback,rest⟩ := reader_indirect_call p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_indirect_auxiliary_growth ops law before after out.core idx table callback

theorem SimdReaderEvent.auxiliary_growth {A : Type} {ops : runtime.platform.Alloc A}
    {data env locals index st p before after out C}
    (event : @SimdReaderEvent A ops data env locals index st p before after out C)
    (law : Platform.AllocCorrect ops) : AuxiliaryGrowth before after := by
  have bound := event.meaning.opcode_bound
  have number := event.number
  obtain ⟨mono,simd,pool,indirect,_⟩ := compiler_lower_simd_auxiliary_growth ops law before after out
    event.opcode event.a event.b event.bits (by omega) (by omega) event.callback
  unfold AuxiliaryGrowth
  have same := congrArg (fun xs => xs.val.length) indirect
  omega

theorem reader_typed_select_auxiliary_growth {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 28#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after := by
  obtain ⟨ty,position,callback,rest⟩ := reader_typed_select p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact .of_tables (compiler_core_tables ops law before after out.core (.select true) callback)
    (compiler_core_code_mono ops law before after out.core (.select true) callback)
end Itasca.Compiler

end

/-! ## Reader Extended Fixups -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual scalar/reference callbacks preserve previously emitted code slots. -/
theorem reader_stateful_base_fixup_budget {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (opcode : U8)
    (member : opcode.val ∈ [37,38,63,64,208,209,210])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index opcode before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  obtain ⟨op,a,b,arguments,callback,_⟩ := reader_stateful_base p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx opcode member byte accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact budget.ordinary (compiler_stateful_ordinary_result ops law before after out.core op a b (.Ok ()) callback)
    (compiler_stateful_code_mono ops law before after out.core op a b (.Ok ()) callback)

theorem reader_stateful_bulk_fixup_budget {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (subopcode : U32) (next : Usize)
    (member : subopcode.val ∈ [8,9,10,11,12,13,14,15,16,17])
    (byte : data.val[p.start.val]'p.inbounds = 252#u8)
    (decoded : Binary.Leb128.Decoded data st.core.pos subopcode next)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 252#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  obtain ⟨op,a,b,arguments,callback,_⟩ := reader_stateful_bulk p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx subopcode next member byte decoded accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact budget.ordinary (compiler_stateful_ordinary_result ops law before after out.core op a b (.Ok ()) callback)
    (compiler_stateful_code_mono ops law before after out.core op a b (.Ok ()) callback)

theorem reader_indirect_call_fixup_budget {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 17#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  obtain ⟨idx,table,values,callback,rest⟩ := reader_indirect_call p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact budget.ordinary (compiler_indirect_call_ordinary_result ops law before after out.core idx table (.Ok ()) callback)
    (compiler_indirect_call_code_mono ops law before after out.core idx table (.Ok ()) callback)

theorem reader_typed_select_fixup_budget {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 28#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  obtain ⟨ty,position,callback,rest⟩ := reader_typed_select p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact budget.ordinary (compiler_core_ordinary_result ops law before after out.core (.select true) (.Ok ()) callback)
    (compiler_core_code_mono ops law before after out.core (.select true) callback)

theorem SimdReaderEvent.fixup_budget {A : Type} {ops : runtime.platform.Alloc A}
    {data env locals index st p before after out C}
    (event : @SimdReaderEvent A ops data env locals index st p before after out C)
    (law : Platform.AllocCorrect ops) : FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  have bound := event.meaning.opcode_bound
  have number := event.number
  exact budget.ordinary
    (compiler_lower_simd_effects ops law before after out event.opcode event.a event.b event.bits
      (by omega) (by omega) event.callback).1
    (compiler_lower_simd_code_mono ops law before after out event.opcode event.a event.b event.bits
      (by omega) (by omega) event.callback)

end Itasca.Compiler

end

/-! ## Reader Ordinary Ledger -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Successful ordinary readers charge auxiliary entries and retain the
per-frame branch-fixup allocation budget. -/
structure ReaderAllocationLedger {A} (before after : runtime.compiler.FunctionCompiler A) : Prop where
  auxiliary : AuxiliaryGrowth before after
  fixups : FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length

theorem OrdinaryEffects.ledger {A} {before after : runtime.compiler.FunctionCompiler A}
    {state : code.OpIterState} (effects : OrdinaryEffects before after state) : ReaderAllocationLedger before after :=
  ⟨effects.auxiliary_growth, effects.fixups⟩

private theorem scope_excluded {opcode : U8} (scope : ScopeOpcode opcode)
    (excluded : opcode.val ∉ [2,3,4,5,11,12,13,14,15]) : False := by
  simp only [ScopeOpcode,List.mem_cons,List.not_mem_nil,or_false] at scope excluded
  omega

/-- Every accepted ordinary body step preserves the allocation ledger.
Recognition is derived from this actual step, including decoded prefix bytes. -/
theorem reader_ordinary_ledger {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (opcode : U8) (excluded : opcode.val ∉ [2,3,4,5,11,12,13,14,15])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index opcode before = .ok (.Ok (),out,after)) :
    ReaderAllocationLedger before after := by
  have known := reader_accepted_opcode
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index opcode before after accepted
  rcases known with ordinary | scope | isElse | isEnd | extra | float | memory | indirect | table |
    stateful | misc | simd | select
  · exact (reader_ordinary_effects p ops law before after out ctx opcode ordinary byte accepted).ledger
  · exact (scope_excluded scope excluded).elim
  · simp [isElse] at excluded
  · simp [isEnd] at excluded
  · exact (reader_scalar_effects ops law before after st out data env ctx index opcode extra accepted).ledger
  · obtain ⟨op,base,equal⟩ := float_base_opcode_of_mem float
    rw [←equal] at byte accepted
    exact (reader_float_base_effects ops law before after st out data env ctx index op base accepted).ledger
  · have stateful := stateful_opcode_values (.inl memory)
    exact ⟨reader_stateful_base_auxiliary_growth p ops law before after out ctx opcode stateful byte accepted,
      reader_stateful_base_fixup_budget p ops law before after out ctx opcode stateful byte accepted⟩
  · rw [indirect] at byte accepted
    exact ⟨reader_indirect_call_auxiliary_growth p ops law before after out ctx byte accepted,
      reader_indirect_call_fixup_budget p ops law before after out ctx byte accepted⟩
  · simp [table] at excluded
  · have stateful := stateful_opcode_values (.inr stateful)
    exact ⟨reader_stateful_base_auxiliary_growth p ops law before after out ctx opcode stateful byte accepted,
      reader_stateful_base_fixup_budget p ops law before after out ctx opcode stateful byte accepted⟩
  · rw [misc] at byte accepted
    obtain ⟨sub,next,decoded,choice⟩ := reader_misc_accepted
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index before after accepted
    rcases choice with ⟨op,extension,equal⟩ | bulk
    · exact (reader_saturating_effects p ops law before after out ctx op extension sub next equal decoded byte accepted).ledger
    · exact ⟨reader_stateful_bulk_auxiliary_growth p ops law before after out ctx sub next bulk byte decoded accepted,
        reader_stateful_bulk_fixup_budget p ops law before after out ctx sub next bulk byte decoded accepted⟩
  · rw [simd] at byte accepted
    obtain ⟨event⟩ := reader_simd_event p ops before after out ctx
      (Translation.Environment.context env ⟨locals,p.ft.results⟩) rfl byte accepted
    exact ⟨event.auxiliary_growth law,event.fixup_budget law⟩
  · rw [select] at byte accepted
    exact ⟨reader_typed_select_auxiliary_growth p ops law before after out ctx byte accepted,
      reader_typed_select_fixup_budget p ops law before after out ctx byte accepted⟩

end Itasca.Compiler

end

end

/-! ## StructuredScopes -/

section

/-!
Control-scope compilation through a structured reader point.

Main declarations: `StructuredReaderCompilerPoint.scope_step`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
theorem StructuredReaderCompilerPoint.scope_step {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st}
    (point : StructuredReaderCompilerPoint jumpTables emit initial before types functions returns locals data env ctx.locals index ft st)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (opcode : U8) (supported : ScopeOpcode opcode)
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index opcode before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPoint jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents, current, savedParents, savedCurrent, state⟩ := point
  simp only [ScopeOpcode, List.mem_cons, List.not_mem_nil, or_false] at supported
  rcases supported with h | h | h | h | h
  · have op : opcode = 2#u8 := by apply UScalar.eq_of_val_eq; exact h
    rw [op] at byte accepted
    obtain ⟨x0, x1, x2, x3, x4, x5, post⟩ := state.enter_block ops law next advance inbounds out signatures
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact post.point
  · have op : opcode = 3#u8 := by apply UScalar.eq_of_val_eq; exact h
    rw [op] at byte accepted
    obtain ⟨x0, x1, x2, x3, x4, x5, post⟩ := state.enter_loop ops law next advance inbounds out signatures
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact post.point
  · have op : opcode = 4#u8 := by apply UScalar.eq_of_val_eq; exact h
    rw [op] at byte accepted
    obtain ⟨x0, x1, x2, x3, x4, x5, x6, post⟩ := state.enter_if ops law next advance inbounds out signatures
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact post.point
  · have op : opcode = 12#u8 := by apply UScalar.eq_of_val_eq; exact h
    rw [op] at byte accepted
    obtain ⟨x0, post⟩ := state.br ops law next advance inbounds out
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact post.point
  · have op : opcode = 13#u8 := by apply UScalar.eq_of_val_eq; exact h
    rw [op] at byte accepted
    obtain ⟨x0, x1, post⟩ := state.br_if ops law next advance inbounds out sourceBound
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact post.point
end Itasca.Compiler

end

end
