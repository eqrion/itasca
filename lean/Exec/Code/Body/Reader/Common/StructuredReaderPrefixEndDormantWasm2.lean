import Exec.Code.Body.Reader.Common.StructuredReaderPrefixEndDormant
import Exec.Code.Local.Relations.Control.KnownControlStack
import Exec.Code.Body.Reader.Common.ReaderReachabilitySteps
import Exec.Code.Body.Reader.Control.ReaderScopeFronts
import Exec.Code.Body.Reader.Control.ReaderControlBoundary
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

private theorem structured_closed_not_body_wasm2 {form bt ops instruction}
    (closed : Wasm2.Frames.Closed form bt ops instruction) : form.kind ≠ .Body := by
  cases closed <;> simp [Wasm2.Frames.Form.kind]

theorem structured_reader_prefix_end_dormant_wasm2 {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns compilerLocals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix emit initial before types functions returns compilerLocals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (reach : ReaderReachabilityWasm2 before.reachable parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (unentered : current.entered = false)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 0x0b#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 0x0b#u8 before = .ok (.Ok (), out, after)) :
    ∃ outer parent savedOuter savedParent instruction,
      parents = outer ++ [parent] ∧ p.parents = savedOuter ++ [savedParent] ∧
      Wasm2.Frames.Closed p.current.form p.current.bt p.current.ops instruction ∧
      after.reachable = false ∧
      StructuredCompilerPrefix emit initial after types functions returns compilerLocals outer (parent.advance instruction) out.core.vals.val out.core.pos.val ∧
      ReaderScopeZipperWasm2 outer (parent.advance instruction) savedOuter (resumedSource savedParent p.current instruction) ∧
      ReaderReachabilityWasm2 after.reachable outer (parent.advance instruction) savedOuter (resumedSource savedParent p.current instruction) ∧
      ReaderScopeFronts outer (parent.advance instruction) (savedOuter.map Wasm2.Frames.Saved.vals) ∧
      ReaderBoundaryWasm2 data env locals index p.ft out savedOuter (resumedSource savedParent p.current instruction) ∧ p.After out := by
  obtain ⟨callback, read, encoded, results, zipper, afterState⟩ := reader_end_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  rcases zipper with ⟨root, savedEmpty, _⟩ | ⟨savedOuter, savedParent, instruction, savedSplit, closed, opened⟩
  · have lengthEq := List.Forall₂.length_eq same.parents
    have sourceEmpty : parents = [] := by simpa [savedEmpty] using lengthEq
    have rootLive := invariant.entryChain.root_entered sourceEmpty
    simp [unentered] at rootLive
  · obtain ⟨outer, parent, sourceSplit, nextSame⟩ := same.close savedOuter savedParent savedSplit instruction
    have nonBody : current.form.kind ≠ .Body := by
      intro body
      have canonical := same.current.form.kind.symm.trans body
      exact structured_closed_not_body_wasm2 closed canonical
    obtain ⟨C, rawOuter, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
    have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
      have size := p.size
      have inside := p.inbounds
      change p.start.val < data.val.length at inside
      norm_num [limits.MAX_FUNCTION_BYTES, limits.MAX_MODULE_BYTES] at size ⊢
      omega
    have consumed : p.start.val < out.core.pos.val := by
      have position := p.pos
      have advanced := afterState.2.1
      omega
    have coordinate : before.function.body_start.val + out.core.pos.val ≤ Usize.max := by
      have inside := afterState.2.2
      omega
    have prefixInv : StructuredCompilerPrefix emit initial before types functions returns compilerLocals (outer ++ [parent]) current st.core.vals.val p.start.val := sourceSplit ▸ invariant
    obtain ⟨dead, certified⟩ := structured_callback_end_dormant_prefix ops law initial before after types functions returns compilerLocals
      outer parent current st.core.vals.val p.start.val prefixInv unentered nonBody out.core p.current.ctrl.kind
      p.current.bt instruction  coordinate sourceBound consumed callback
    have reach' : ReaderReachabilityWasm2 before.reachable (outer ++ [parent]) current
        (savedOuter ++ [savedParent]) p.current := by simpa only [sourceSplit, savedSplit] using reach
    have fronts' : ReaderScopeFronts (outer ++ [parent]) current
        (savedOuter.map Wasm2.Frames.Saved.vals ++ [savedParent.vals]) := by
      simpa only [sourceSplit, savedSplit, List.map_append, List.map_cons, List.map_nil] using fronts
    exact ⟨outer, parent, savedOuter, savedParent, instruction, sourceSplit, savedSplit, closed, dead,
      certified, nextSame, reach'.close after.reachable instruction (by simp [dead]), fronts'.pop instruction,
      reader_end_boundary_wasm2 p savedSplit encoded opened afterState, afterState⟩
end Exec.Code
