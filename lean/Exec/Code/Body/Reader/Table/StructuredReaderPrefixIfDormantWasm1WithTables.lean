import Exec.Code.Body.Reader.Table.StructuredReaderPrefixIfDormantWithTables
import Exec.Code.Body.Relations.Common.KnownEntryStackWasm1
import Exec.Code.Body.Callbacks.Calls.ScopeCallbackDormantInputs
import Exec.Code.Body.Reader.Common.ReaderReachability
import Exec.Code.Body.Reader.Common.ReaderFrontTransitions
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem structured_reader_prefix_if_dead_wasm1_with_tables {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.vals.val p.start.val)
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current)
    (reach : ReaderReachabilityWasm1 before.reachable parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm1.Frames.Saved.vals))
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_IF)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_IF before = .ok (.Ok (), out, after)) :
    ∃ bt remaining front,
      let child := SourceScope.enterIf (Control.blockType bt) 0#u32 front [] (Control.resultTypes bt) before.function.code.val.length false
      ReaderEnterPostWasm1 p out .then_ bt remaining (.if_ bt) ∧
      StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial after types functions returns locals (parents ++ [current]) child out.vals.val out.pos.val ∧
      ReaderScopeZipperWasm1 (parents ++ [current]) child
        (p.parents ++ [{p.current with vals := remaining}]) (Wasm1.Frames.Saved.fresh out .then_ bt) ∧
      ReaderReachabilityWasm1 after.reachable (parents ++ [current]) child
        (p.parents ++ [{p.current with vals := remaining}]) (Wasm1.Frames.Saved.fresh out .then_ bt) ∧
      ReaderScopeFronts (parents ++ [current]) child
        ((p.parents ++ [{p.current with vals := remaining}]).map Wasm1.Frames.Saved.vals) := by
  obtain ⟨bt, remaining, callback, read, post⟩ := reader_if_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out byte accepted
  obtain ⟨signature, selected, matched⟩ := wasm1_signature_select before.signatures bt
  obtain ⟨controls, baseEq, _⟩ := post.front
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
  have certified := structured_callback_if_dead_prefix_with_tables ops law initial before after types functions returns locals parents current
    st.vals.val p.start.val invariant dead out (Wasm1.Frames.Saved.fresh out .then_ bt).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Wasm1.Frames.Saved.ctrl) (Control.signature bt)
    signature front [] (Control.resultTypes bt) selected matched controls (by rw [baseEq])  sourceBound consumed callback
  rw [blockTypeEq] at certified
  refine ⟨bt, remaining, front, post, certified, ?_, ?_, ?_⟩
  · simpa [SourceScope.enterIf] using same.enter _ _
      (SourceScopeMatchesWasm1.fresh bt .then_ _ (.then_ 0#u32) out front _ _ false) remaining
  · apply reach.push after.reachable _ {p.current with vals := remaining} _ rfl
      (by simp [SourceScope.enterIf])
    intro _
    rfl
  · exact post.scope_fronts fronts _ rfl

end Exec.Code
