import Exec.Code.Body.Control.Common.IndexedClosingWitnessWasm2
import Exec.Code.Body.Reader.Common.ReaderOpcodeClassification
import Exec.Code.Body.Control.Common.IndexedEndOrClosed
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
theorem IndexedTableReaderCompilerPointWasm2.advance_or_closing {A : Type}
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
    (data.val[st.core.pos.val] = 11#u8 ∧ out.core.ctrls.val = []) ∨
    IndexedTableReaderCompilerPointWasm2 (fun tables => ExecutableEmission tables C) initial middle
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft out := by
  apply point.advance_or_closing_of_opcode ops law C initialLocals localsMatch metadata matched contextLocals
    signatures bodyBound next advance inbounds out _ accepted
  exact reader_accepted_opcode_wasm2 _ _ out data env ctx index _ before middle accepted
end Itasca.Runtime.Code
