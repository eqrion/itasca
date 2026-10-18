import Exec.Code.Body.Reader.Control.ReaderPrefixLoopDormant
import Exec.Code.Body.Relations.Common.KnownEntryStackWasm1
import Exec.Code.Body.Callbacks.Calls.ScopeCallbackDormantInputs
import Exec.Code.Body.Reader.Common.ReaderReachability
import Exec.Code.Body.Reader.Common.ReaderFrontTransitions
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem reader_prefix_loop_dead_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.vals.val p.start.val)
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current)
    (reach : ReaderReachabilityWasm1 before.reachable parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm1.Frames.Saved.vals))
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOOP)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOOP before = .ok (.Ok (), out, after)) :
    ∃ bt front,
      let child := SourceScope.enterLoop (Control.blockType bt) front [] (Control.resultTypes bt) before.function.code.val.length false
      ReaderEnterPostWasm1 p out .loop bt p.current.vals (.loop bt) ∧
      CompilerPrefix initial after types functions returns locals (parents ++ [current]) child out.vals.val out.pos.val ∧
      ReaderScopeZipperWasm1 (parents ++ [current]) child
        (p.parents ++ [{p.current with vals := p.current.vals}]) (Wasm1.Frames.Saved.fresh out .loop bt) ∧
      ReaderReachabilityWasm1 after.reachable (parents ++ [current]) child
        (p.parents ++ [{p.current with vals := p.current.vals}]) (Wasm1.Frames.Saved.fresh out .loop bt) ∧
      ReaderScopeFronts (parents ++ [current]) child
        ((p.parents ++ [{p.current with vals := p.current.vals}]).map Wasm1.Frames.Saved.vals) := by
  obtain ⟨bt, callback, read, post⟩ := reader_loop_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out byte accepted
  obtain ⟨signature, selected, matched⟩ := wasm1_signature_select before.signatures bt
  obtain ⟨controls, baseEq, _⟩ := post.front
  have known := wasm1_loop_concrete st out data bt p.ctrl_capacity invariant.known read
  let front := Sequence.stackTypes out.vals.val
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
  have certified := callback_loop_dead_prefix ops law initial before after types functions returns locals parents current
    st.vals.val p.start.val invariant dead out (Wasm1.Frames.Saved.fresh out .loop bt).ctrl
    ((p.parents ++ [{p.current with vals := p.current.vals}]).map Wasm1.Frames.Saved.ctrl) (Control.signature bt)
    signature front [] (Control.resultTypes bt) selected matched controls (by rw [baseEq]) known sourceBound consumed callback
  rw [blockTypeEq] at certified
  refine ⟨bt, front, post, certified, ?_, ?_, ?_⟩
  · simpa [SourceScope.enterLoop] using same.enter _ _
      (SourceScopeMatchesWasm1.fresh bt .loop _ .loop out front _ _ false) p.current.vals
  · apply reach.push after.reachable _ {p.current with vals := p.current.vals} _ rfl
      (by simp [SourceScope.enterLoop])
    intro _
    rfl
  · exact post.scope_fronts fronts _ rfl

end Exec.Code
