import Exec.Code.Body.Reader.Table.StructuredReaderPrefixLoop
import Exec.Code.Body.Callbacks.Calls.ScopeCallbackInputs
import Exec.Code.Body.Reader.Common.ReaderReachability
import Exec.Code.Body.Reader.Common.ReaderFrontTransitions
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- An accepted canonical LOOP reader constructs the complete live child
compiler prefix, its source zipper, and validator reachability correspondence. -/
theorem structured_reader_prefix_loop_wasm2 {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env localTypes index st}
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
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOOP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_LOOP before = .ok (.Ok (), out, after)) :
    ∃ bt ins outs remaining base front,
      let child := SourceScope.enterLoop (Wasm2.blockType bt) front (ins.map Translate.valueType)
        (outs.map Translate.valueType) before.function.code.val.length true
      ReaderEnterPostWasm2 p out .loop bt ins outs remaining base ∧
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

end Exec.Code
