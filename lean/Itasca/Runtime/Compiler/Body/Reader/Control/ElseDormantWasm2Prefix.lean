import Itasca.Runtime.Compiler.Body.Reader.Control.ElseDormantPrefix
import Itasca.Runtime.Compiler.Local.Relations.Control.KnownControlStack
import Itasca.Runtime.Compiler.Body.Reader.Control.ReachabilitySteps
import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeFronts
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlBoundary

/-!
Complete-profile transport of a dormant else prefix.

Main declarations: `structured_reader_prefix_else_dormant_wasm2`. A direct consumer is `Compiler.Body.Reader.Control.ElseCompilation`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem structured_reader_prefix_else_dormant_wasm2 {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns compilerLocals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns compilerLocals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (reach : ReaderReachabilityWasm2 before.reachable parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (unentered : current.entered = false)
    (byte : data.val[p.start.val]'p.inbounds = 0x05#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 0x05#u8 before = .ok (.Ok (), out, after)) :
    ∃ condition noEntry,
      current.form = .then_ (Wasm2.blockType p.current.bt) condition ∧
      noEntry.val = before.function.code.val.length ∧
      let next := current.begin_else (Wasm2.blockType p.current.bt) condition noEntry.val noEntry false
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns compilerLocals parents next out.core.vals.val out.core.pos.val ∧
      ReaderScopeZipperWasm2 parents next p.parents p.current.nextElse ∧
      ReaderReachabilityWasm2 after.reachable parents next p.parents p.current.nextElse ∧
      ReaderScopeFronts parents next (p.parents.map Wasm2.Frames.Saved.vals) ∧
      ReaderBoundaryWasm2 data env locals index p.ft out p.parents p.current.nextElse ∧ p.After out := by
  obtain ⟨callback, read, sourceForm, encoded, results, opened, afterState⟩ := reader_else_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have matched := same.current.form
  rw [sourceForm] at matched
  have sourceThen : ∃ condition, current.form = .then_ (Wasm2.blockType p.current.bt) condition := by
    generalize currentForm : current.form = scopeForm at matched
    cases matched with
    | then_ condition => exact ⟨condition, rfl⟩
  obtain ⟨condition, form⟩ := sourceThen
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
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
  obtain ⟨noEntry, positionEq, certified⟩ := structured_callback_else_dormant_prefix ops law initial before after types functions returns compilerLocals
    parents current st.core.vals.val p.start.val invariant unentered out.core p.current.bt
    (Wasm2.blockType p.current.bt) condition form  sourceBound consumed callback
  exact ⟨condition, noEntry, form, positionEq, certified,
    same.begin_else _ condition form noEntry.val noEntry false,
    reach.begin_else after.reachable _ condition noEntry.val noEntry false,
    fronts.begin_else _ condition noEntry.val noEntry false,
    reader_else_boundary_wasm2 p sourceForm encoded opened afterState, afterState⟩
end Itasca.Runtime.Code
