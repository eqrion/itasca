import Exec.Code.Body.Reader.Control.StructuredScopeClosePublication
import Exec.Code.Body.Reader.Common.ReaderCloseWasm1
import Exec.Code.Body.Reader.Common.ReaderCloseWasm2

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The actual Wasm 1 END reader supplies progress and a bounded source
endpoint for both nested scope closing and final function closing. -/
theorem reader_end_publication_wasm1 {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop}
    {data env ctx bodyBt st} (p : Wasm1.Pending data env ctx bodyBt st)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial before types functions returns locals
      parents current st.vals.val p.start.val)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (extent : before.function.body_end.val = before.function.body_start.val+data.length)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_END)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx code.OP_END before = .ok (.Ok (),out,after)) :
    SourceCoordinates after ∧ ControlMapPublication after := by
  obtain ⟨callback,_,_,_,_,afterState⟩ := reader_end_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out byte accepted
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES,limits.MAX_MODULE_BYTES] at size ⊢
    omega
  have consumed : p.start.val < out.pos.val := by
    have position := p.pos
    have advanced := afterState.2.1
    omega
  have endBound : before.function.body_start.val+out.pos.val ≤ before.function.body_end.val := by
    have bounded := afterState.2.2
    omega
  exact structured_scope_close_publication ops law invariant sourceBound out p.current.ctrl.kind
    (Control.signature p.current.ctrl.block_type) coordinates maps consumed endBound callback

/-- The actual Wasm 2 END reader supplies progress and a bounded source
endpoint for both nested scope closing and final function closing. -/
theorem reader_end_publication_wasm2 {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop}
    {data env localTypes index st} (p : Wasm2.Pending data env localTypes index st)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (extent : before.function.body_end.val = before.function.body_start.val+data.length)
    (byte : data.val[p.start.val]'p.inbounds = 11#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx index .Wasm2 11#u8 before = .ok (.Ok (),out,after)) :
    SourceCoordinates after ∧ ControlMapPublication after := by
  obtain ⟨callback,_,_,_,_,afterState⟩ := reader_end_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES,limits.MAX_MODULE_BYTES] at size ⊢
    omega
  have consumed : p.start.val < out.core.pos.val := by
    have position := p.pos
    have advanced := afterState.2.1
    omega
  have endBound : before.function.body_start.val+out.core.pos.val ≤ before.function.body_end.val := by
    have bounded := afterState.2.2
    omega
  exact structured_scope_close_publication ops law invariant sourceBound out.core p.current.ctrl.kind
    p.current.bt coordinates maps consumed endBound callback

end Exec.Code
