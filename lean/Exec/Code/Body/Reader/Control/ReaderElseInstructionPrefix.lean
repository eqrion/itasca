import Exec.Code.Body.Reader.Control.StructuredElseInstructionPrefix
import Exec.Code.Body.Reader.Common.ReaderCloseWasm2
import Exec.Code.Body.Reader.Control.ReaderScopeZipper

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Actual ELSE reading preserves stored instruction checks from its matched THEN scope. -/
theorem reader_else_open_instructions_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (held : CompilerInstructionPrefix before)
    (byte : data.val[p.start.val]'p.inbounds = 5#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 5#u8 before = .ok (.Ok (),out,after)) : CompilerInstructionPrefix after := by
  obtain ⟨callback,_,sourceForm,_⟩ := reader_else_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have matched := same.current.form
  rw [sourceForm] at matched
  have sourceThen : ∃ condition, current.form = .then_ (Wasm2.blockType p.current.bt) condition := by
    generalize currentForm : current.form = scopeForm at matched
    cases matched with
    | then_ condition => exact ⟨condition,rfl⟩
  obtain ⟨condition,form⟩ := sourceThen
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES,limits.MAX_MODULE_BYTES] at size ⊢
    omega
  exact invariant.else_open_instructions ops law out.core _ condition form p.current.bt sourceBound held callback

end Exec.Code
