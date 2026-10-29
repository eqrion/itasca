import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixOpenDormant
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.ScopeCallbackDead
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlEntrySuccess
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerEnterMetadata
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlCursor
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlSources
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownPopStack
import Itasca.Runtime.Compiler.Body.Reader.Control.EnterWasm2
import Itasca.Runtime.Compiler.Body.Callbacks.Calls.ScopeCallbackInputs
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Reader.Control.FrontTransitions

/-!
Dormant if reader prefixes and profile transport, retaining omitted-code and control-map obligations.
-/

/-! ## Structured Reader Prefix If Dormant -/

section

namespace Itasca.Runtime.Compiler
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
      (SourceScope.enterIf (Wasm2.blockType bt) 0#u32 front params results before.function.code.val.length false) state.vals.val state.pos.val := by
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
  let child := SourceScope.enterIf (Wasm2.blockType bt) 0#u32 front params results before.function.code.val.length false
  let frame : runtime.compiler.Frame := ⟨alloc.vec.Vec.len before.function.controls, .Then, height,
    signature.param_slots, signature.result_slots, pc, none, false, false, alloc.vec.Vec.new Usize⟩
  have aligned : ScopeFrameStack locals after (parents ++ [current]) child :=
    invariant.frames.push child frame framesEq preserve fresh parentShape.bodyBound (by simp [child, SourceScope.enterIf])
  have stable := compiler_enter_stable_result ops law before after state .Then bt (.Ok ()) accepted
  have sources := compiler_enter_sources ops law before after state .Then bt accepted
  have cursor := compiler_enter_cursor ops law before after state .Then bt accepted
  exact invariant.open_dormant dead deadAfter child frame stable aligned codeEq framesEq
    (by simp [mapsEq]) rfl rfl (DormantFrame.fresh rfl rfl) rfl  rfl rfl sources consumed (by rw [cursor])

end Itasca.Runtime.Compiler

end

/-! ## Structured Reader Prefix If Dormant Wasm2 -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem structured_reader_prefix_if_dead_wasm2 {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env localTypes index st}
    (p : Wasm2.Pending data env .Wasm2 localTypes index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (reach : ReaderReachabilityWasm2 before.reachable parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (dead : before.reachable = false)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_IF)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_IF before = .ok (.Ok (), out, after)) :
    ∃ bt ins outs remaining base front,
      let child := SourceScope.enterIf (Wasm2.blockType bt) 0#u32 front (ins.map Translate.valueType) (outs.map Translate.valueType) before.function.code.val.length false
      Wasm2.ReaderEnterPost p out .then_ bt ins outs remaining base ∧
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
  obtain ⟨signature, selected, matched⟩ := signatures.select post.inputs post.outputs
  obtain ⟨controls, valuesFit, _, _⟩ := post.front (.inr (.inr rfl))
  let front := Sequence.stackTypes (out.core.vals.val.take base.val)
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
    st.core.vals.val p.start.val invariant dead out.core (Wasm2.Frames.Saved.fresh base .then_ bt ins outs).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Wasm2.Frames.Saved.ctrl) bt signature front
    (ins.map Translate.valueType) (outs.map Translate.valueType) selected matched controls valuesFit
    sourceBound consumed callback
  refine ⟨bt, ins, outs, remaining, base, front, post, certified, ?_, ?_, ?_⟩
  · apply same.enter _ _ _ remaining
    exact SourceScopeMatchesWasm2.fresh bt .then_ _ (.then_ 0#u32) base ins outs front _ _ false
  · apply reach.push after.reachable _ {p.current with vals := remaining} _ rfl
      (by simp [SourceScope.enterIf])
    intro _
    rfl
  · exact post.scope_fronts_dormant (.inr (.inr rfl)) fronts _ rfl

end Itasca.Runtime.Compiler

end
