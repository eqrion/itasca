import Exec.Code.Body.Control.Control.CumulativePointControl
import Exec.Code.Body.Reader.Table.TableReaderCompilerPreserved
import Exec.Code.Body.Control.Common.CumulativeEmbedding
import Exec.Code.Body.Reader.Table.ReaderControlTables
import Exec.Code.Body.Reader.Control.StructuredReaderCompilerScopes
import Exec.Code.Body.Reader.Control.StructuredReaderCompilerElse
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerEndWasm2
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerRoot
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem TableReaderCompilerPointWasm2.scope_step {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (point : TableReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (opcode : U8) (supported : ScopeOpcode opcode)
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    TableReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have pairs := reader_scope_tables_wasm2 p ops law before after out ctx opcode supported byte accepted
  apply point.preserved_step pairs
  intro future old
  exact old.scope_step ops law next advance inbounds out sourceBound signatures opcode supported byte accepted

theorem TableReaderCompilerPointWasm2.else_ {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (point : TableReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (initialLocals : LocalLayout initial)
    (byte : data.val[st.core.pos.val]'inbounds = 5#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 5#u8 before = .ok (.Ok (),out,after)) :
    TableReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have pairs := reader_else_tables_wasm2 p ops law before after out ctx byte accepted
  apply point.preserved_step pairs
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  exact state.else_ ops law initialLocals next advance inbounds out (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)

theorem TableReaderCompilerPointWasm2.end_nested {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (point : TableReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (initialLocals : LocalLayout initial)
    (typesEq : types = env.types.val.map EnvTranslation.funcType)
    (nonRoot : st.blocks.val.length ≠ 1)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 11#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 11#u8 before = .ok (.Ok (),out,after)) :
    TableReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have pairs := reader_end_tables_wasm2 p ops law before after out ctx byte accepted
  apply point.preserved_step pairs
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  have form : savedCurrent.form ≠ .body := fun h => nonRoot (state.boundary.root_iff.mp h)
  exact state.end_nested ops law initialLocals typesEq next advance inbounds out form bodyBound
    (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
end Exec.Code
