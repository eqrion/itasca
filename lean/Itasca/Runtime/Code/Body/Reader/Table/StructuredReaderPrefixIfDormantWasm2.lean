import Itasca.Runtime.Code.Body.Reader.Table.StructuredReaderPrefixIfDormant
import Itasca.Runtime.Code.Local.Relations.Common.KnownPopStack
import Itasca.Runtime.Code.Body.Reader.Common.ReaderEnterWasm2
import Itasca.Runtime.Code.Body.Callbacks.Calls.ScopeCallbackInputs
import Itasca.Runtime.Code.Local.Relations.Control.ControlEntrySuccess
import Itasca.Runtime.Code.Body.Reader.Common.ReaderReachability
import Itasca.Runtime.Code.Body.Reader.Common.ReaderFrontTransitions
namespace Itasca.Runtime.Code
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

end Itasca.Runtime.Code
