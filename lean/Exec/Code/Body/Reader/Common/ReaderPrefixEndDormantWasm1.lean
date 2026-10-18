import Exec.Code.Body.Reader.Common.ReaderPrefixEndDormant
import Exec.Code.Local.Relations.Control.KnownControlStack
import Exec.Code.Body.Reader.Common.ReaderReachabilitySteps
import Exec.Code.Body.Reader.Control.ReaderScopeFronts
import Exec.Code.Body.Reader.Control.ReaderControlBoundary
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

private theorem closed_not_body_wasm1 {form bt ops instruction}
    (closed : Wasm1.Frames.Closed form bt ops instruction) : form.kind ≠ .Body := by
  cases closed <;> simp [Wasm1.Frames.Form.kind]

theorem reader_prefix_end_dormant_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.vals.val p.start.val)
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current)
    (reach : ReaderReachabilityWasm1 before.reachable parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm1.Frames.Saved.vals))
    (unentered : current.entered = false)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_END)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_END before = .ok (.Ok (), out, after)) :
    ∃ outer parent savedOuter savedParent instruction,
      parents = outer ++ [parent] ∧ p.parents = savedOuter ++ [savedParent] ∧
      Wasm1.Frames.Closed p.current.form p.current.ctrl.block_type p.current.ops instruction ∧
      after.reachable = false ∧
      CompilerPrefix initial after types functions returns locals outer (parent.advance instruction) out.vals.val out.pos.val ∧
      ReaderScopeZipperWasm1 outer (parent.advance instruction) savedOuter (resumedSourceWasm1 savedParent p.current instruction) ∧
      ReaderReachabilityWasm1 after.reachable outer (parent.advance instruction) savedOuter (resumedSourceWasm1 savedParent p.current instruction) ∧
      ReaderScopeFronts outer (parent.advance instruction) (savedOuter.map Wasm1.Frames.Saved.vals) ∧
      ReaderBoundaryWasm1 data env ctx bodyBt out savedOuter (resumedSourceWasm1 savedParent p.current instruction) ∧ p.After out := by
  obtain ⟨callback, read, encoded, results, zipper, afterState⟩ := reader_end_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out byte accepted
  rcases zipper with ⟨root, savedEmpty, _⟩ | ⟨savedOuter, savedParent, instruction, savedSplit, closed, opened⟩
  · have lengthEq := List.Forall₂.length_eq same.parents
    have sourceEmpty : parents = [] := by simpa [savedEmpty] using lengthEq
    have rootLive := invariant.entryChain.root_entered sourceEmpty
    simp [unentered] at rootLive
  · obtain ⟨outer, parent, sourceSplit, nextSame⟩ := same.close savedOuter savedParent savedSplit instruction
    have nonBody : current.form.kind ≠ .Body := by
      intro body
      have canonical := same.current.form.kind.symm.trans body
      exact closed_not_body_wasm1 closed canonical
    obtain ⟨C, rawOuter, spine, header, base, typed, ctrls, vals⟩ := p.opened
    have outerKnown : ConcreteStack rawOuter := (concreteStack_append.mp (vals ▸ invariant.known)).1
    have known := wasm1_end_concrete st out _ _ rawOuter p.current.vals p.current.ctrl.kind p.current.ctrl.block_type
      ctrls vals base (Nat.le_of_lt p.val_capacity) outerKnown read
    have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
      have size := p.size
      have inside := p.inbounds
      change p.start.val < data.val.length at inside
      norm_num [limits.MAX_FUNCTION_BYTES, limits.MAX_MODULE_BYTES] at size ⊢
      omega
    have consumed : p.start.val < out.pos.val := by
      have position := p.pos
      have advanced := afterState.2.1
      omega
    have coordinate : before.function.body_start.val + out.pos.val ≤ Usize.max := by
      have inside := afterState.2.2
      omega
    have prefixInv : CompilerPrefix initial before types functions returns locals (outer ++ [parent]) current st.vals.val p.start.val := sourceSplit ▸ invariant
    obtain ⟨dead, certified⟩ := callback_end_dormant_prefix ops law initial before after types functions returns locals
      outer parent current st.vals.val p.start.val prefixInv unentered nonBody out p.current.ctrl.kind
      (Control.signature p.current.ctrl.block_type) instruction known coordinate sourceBound consumed callback
    have reach' : ReaderReachabilityWasm1 before.reachable (outer ++ [parent]) current
        (savedOuter ++ [savedParent]) p.current := by simpa only [sourceSplit, savedSplit] using reach
    have fronts' : ReaderScopeFronts (outer ++ [parent]) current
        (savedOuter.map Wasm1.Frames.Saved.vals ++ [savedParent.vals]) := by
      simpa only [sourceSplit, savedSplit, List.map_append, List.map_cons, List.map_nil] using fronts
    exact ⟨outer, parent, savedOuter, savedParent, instruction, sourceSplit, savedSplit, closed, dead,
      certified, nextSame, reach'.close after.reachable instruction (by simp [dead]), fronts'.pop instruction,
      reader_end_boundary_wasm1 p savedSplit encoded opened afterState, afterState⟩
end Exec.Code
