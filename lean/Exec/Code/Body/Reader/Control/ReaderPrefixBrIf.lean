import Exec.Code.Body.Callbacks.Control.CompilerPrefixBrIf
import Exec.Code.Body.Reader.Control.ReaderBranchIfLayout
import Exec.Code.Body.Reader.Control.ReaderBranchWasm2
import Exec.Code.Body.Reader.Control.ReaderBranchWasm1
import Exec.Code.Local.Relations.Control.KnownBranchStackWasm1
import Exec.Code.Body.Reader.Common.ReaderSpan
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_prefix_br_if_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {types functions returns locals parents current}
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (byte : data.val[p.start.val]'p.inbounds = 13#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 13#u8 before = .ok (.Ok (), out, after)) :
    ∃ (depth : U32) (values : List code.StackType),
      ReaderPostWasm2 p out.core (.BR_IF (.mk_uN depth.val)) p.current.ctrl.polymorphic_base values ∧
      CompilerPrefix initial after types functions returns locals parents (current.advance (.BR_IF (.mk_uN depth.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = before.reachable := by
  obtain ⟨depth, view, values, callback, read, post⟩ := reader_br_if_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have consumed : p.start.val < out.core.pos.val := by have position := p.pos; have span := post.span; omega
  refine ⟨depth, values, post, ?_⟩
  by_cases reachable : before.reachable = true
  · obtain ⟨scope, discarded, selected, input, targetStack, known⟩ := reader_br_if_layout_wasm2 p same fronts invariant.known
      (monomorphic reachable) depth view out read
    exact invariant.br_if_live ops law out.core known consumed reachable depth view scope selected discarded input targetStack
      ((Nat.le_of_lt p.inbounds).trans sourceBound) callback
  · obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
    have erased : code.branch st data env true = .ok (.Ok (), out) := by
      simp [code.branch, read, core.result.Result.Insts.CoreOpsTry.branch]
    have known := wasm2_branch_if_concrete st data env outer p.current.vals vals
      (by simpa [Control.base, controls] using base) p.opened.shape.core p.opened.shape.aligned invariant.known
    rw [erased, WP.spec_ok] at known
    exact invariant.br_if_dead ops law out.core (known rfl) consumed (Bool.eq_false_iff.mpr reachable) depth view callback

theorem reader_prefix_br_if_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    {types functions returns locals parents current}
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.vals.val p.start.val)
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm1.Frames.Saved.vals))
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_BR_IF)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_BR_IF before = .ok (.Ok (), out, after)) :
    ∃ (depth : U32) (values : List code.StackType),
      ReaderPostWasm1 p out (.BR_IF (.mk_uN depth.val)) p.current.ctrl.polymorphic_base values ∧
      CompilerPrefix initial after types functions returns locals parents (current.advance (.BR_IF (.mk_uN depth.val)))
        out.vals.val out.pos.val ∧ after.reachable = before.reachable := by
  obtain ⟨depth, resultBt, values, callback, read, post⟩ := reader_br_if_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out byte accepted
  have consumed : p.start.val < out.pos.val := by have position := p.pos; have span := post.span; omega
  refine ⟨depth, values, post, ?_⟩
  by_cases reachable : before.reachable = true
  · obtain ⟨scope, discarded, selected, input, targetStack, known⟩ := reader_br_if_layout_wasm1 p same fronts invariant.known
      (monomorphic reachable) depth resultBt out read
    exact invariant.br_if_live ops law out known consumed reachable depth (Control.resultView resultBt) scope selected discarded input targetStack
      ((Nat.le_of_lt p.inbounds).trans sourceBound) callback
  · obtain ⟨_, outer, _, _, base, _, controls, vals⟩ := p.opened
    have known := wasm1_branch_if_concrete st data outer p.current.vals vals
      (by simpa [Control.base, controls] using base) (Nat.le_of_lt p.val_capacity) invariant.known
    rw [read, WP.spec_ok] at known
    exact invariant.br_if_dead ops law out (known depth resultBt rfl) consumed (Bool.eq_false_iff.mpr reachable)
      depth (Control.resultView resultBt) callback
end Exec.Code
