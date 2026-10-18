import Exec.Code.Body.Reader.Control.ReaderPrefixIf
import Exec.Code.Body.Callbacks.Calls.ScopeCallbackInputs
import Exec.Code.Body.Reader.Common.ReaderReachability
import Exec.Code.Body.Reader.Common.ReaderFrontTransitions
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem reader_prefix_if_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.vals.val p.start.val)
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current)
    (reach : ReaderReachabilityWasm1 before.reachable parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm1.Frames.Saved.vals))
    (reachable : before.reachable = true)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_IF)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_IF before = .ok (.Ok (), out, after)) :
    ∃ bt remaining front condition,
      let child := SourceScope.enterIf (Control.blockType bt) condition front []
        (Control.resultTypes bt) before.function.code.val.length true
      ReaderEnterPostWasm1 p out .then_ bt remaining (.if_ bt) ∧
      CompilerPrefix initial after types functions returns locals (parents ++ [current]) child out.vals.val out.pos.val ∧
      ReaderScopeZipperWasm1 (parents ++ [current]) child
        (p.parents ++ [{p.current with vals := remaining}]) (Wasm1.Frames.Saved.fresh out .then_ bt) ∧
      ReaderReachabilityWasm1 after.reachable (parents ++ [current]) child
        (p.parents ++ [{p.current with vals := remaining}]) (Wasm1.Frames.Saved.fresh out .then_ bt) ∧
      ReaderScopeFronts (parents ++ [current]) child
        ((p.parents ++ [{p.current with vals := remaining}]).map Wasm1.Frames.Saved.vals) := by
  obtain ⟨bt, remaining, callback, read, post⟩ := reader_if_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out byte accepted
  have liveLayout := (invariant.live reachable).2.layout
  obtain ⟨front, signature, oldTypes, newTypes, known, selected, matched, controls, baseEq, words, height⟩ :=
    post.callback_inputs (reach.current reachable) invariant.known liveLayout
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES, limits.MAX_MODULE_BYTES] at size ⊢
    omega
  have consumed : p.start.val < out.pos.val := by
    have position := p.pos
    have advanced := post.after.2.1
    omega
  have blockTypeEq : Wasm2.blockType (Control.signature bt) = Control.blockType bt := by cases bt <;> rfl
  obtain ⟨condition, conditionEq, certified⟩ := callback_if_prefix ops law initial before after types functions returns locals parents current
    st.vals.val p.start.val invariant reachable out (Wasm1.Frames.Saved.fresh out .then_ bt).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Wasm1.Frames.Saved.ctrl) (Control.signature bt)
    signature front [] (Control.resultTypes bt) selected matched controls (by rw [baseEq]) words
    (by simpa [Wasm1.Frames.Form.inputs] using oldTypes)
    ⟨known, by simpa using newTypes⟩ sourceBound consumed callback
  rw [blockTypeEq] at certified
  refine ⟨bt, remaining, front, condition, post, certified, ?_, ?_, ?_⟩
  · simpa [SourceScope.enterIf] using same.enter _ _ (SourceScopeMatchesWasm1.fresh bt .then_ _ (.then_ condition) out front _ _ true) remaining
  · apply reach.push after.reachable _ {p.current with vals := remaining} _ rfl (fun _ => reachable)
    intro _
    rfl
  · exact post.scope_fronts fronts _ (by simpa [SourceScope.enterIf] using newTypes)

end Exec.Code
