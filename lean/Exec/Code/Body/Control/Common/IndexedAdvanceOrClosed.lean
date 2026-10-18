import Exec.Code.Body.Control.Common.IndexedAdvanceOrClosedWasm1
import Exec.Code.Body.Control.Common.IndexedAdvanceOrClosedWasm2
import Exec.Code.Body.Reader.Common.ReaderOpcodeClassification
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem IndexedTableReaderCompilerPointWasm1.advance_or_closed {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before middle : runtime.compiler.FunctionCompiler A}
    {locals data env ctx bodyBt st} (C : context)
    (point : IndexedTableReaderCompilerPointWasm1 (fun tables => ExecutableEmission tables C) initial before
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt st)
    (initialLocals : LocalLayout initial) (localsMatch : initial.function.locals = ctx.locals)
    (metadata : FunctionParameterSlots initial env)
    (matched : EnvTranslation.Matches env ctx C) (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyResults : Control.resultTypes bodyBt = ctx.results.val.map Translate.valueType)
    (bodyBound : initial.function.body_start.val + data.length ≤ Usize.max)
    (next : Usize) (advance : next.val = st.pos.val + 1)
    (inbounds : st.pos.val < data.length) (out : code.OpIterState)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx data.val[st.pos.val] before = .ok (.Ok (),out,middle)) :
    out.ctrls.val = [] ∨
    IndexedTableReaderCompilerPointWasm1 (fun tables => ExecutableEmission tables C) initial middle
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt out := by
  apply point.advance_or_closed_of_opcode ops law C initialLocals localsMatch metadata matched contextLocals
    signatures bodyResults bodyBound next advance inbounds out _ accepted
  exact reader_accepted_opcode_wasm1 _ _ out data env ctx _ before middle accepted
theorem IndexedTableReaderCompilerPointWasm2.advance_or_closed {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before middle : runtime.compiler.FunctionCompiler A}
    {locals data env ctx index ft st} (C : context)
    (point : IndexedTableReaderCompilerPointWasm2 (fun tables => ExecutableEmission tables C) initial before
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft st)
    (initialLocals : LocalLayout initial) (localsMatch : initial.function.locals = ctx.locals)
    (metadata : FunctionParameterSlots initial env)
    (matched : EnvTranslation.Matches env ⟨ctx.locals,ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyBound : initial.function.body_start.val + data.length ≤ Usize.max)
    (next : Usize) (advance : next.val = st.core.pos.val + 1)
    (inbounds : st.core.pos.val < data.length) (out : code.BodyState)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2
      data.val[st.core.pos.val] before = .ok (.Ok (),out,middle)) :
    out.core.ctrls.val = [] ∨
    IndexedTableReaderCompilerPointWasm2 (fun tables => ExecutableEmission tables C) initial middle
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft out := by
  apply point.advance_or_closed_of_opcode ops law C initialLocals localsMatch metadata matched contextLocals
    signatures bodyBound next advance inbounds out _ accepted
  exact reader_accepted_opcode_wasm2 _ _ out data env ctx index _ before middle accepted
end Exec.Code
