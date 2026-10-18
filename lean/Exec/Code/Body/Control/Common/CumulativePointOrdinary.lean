import Exec.Code.Body.Reader.Common.CumulativeReaderCompilerPoint
import Exec.Code.Body.Reader.Calls.ReaderOrdinaryIndirect
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem CumulativeReaderCompilerPointWasm2.ordinary {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types locals data env ctx index ft st}
    (contextLocals : C.LOCALS = locals)
    (point : CumulativeReaderCompilerPointWasm2 C initial before types (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft st)
    (metadata : FunctionParameterSlots initial env)
    (localsMatch : initial.function.locals = ctx.locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (opcode : U8) (ordinary : opcode ∈ readerOrdinaryOpcodes)
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 opcode before = .ok (.Ok (), out, after)) :
    CumulativeReaderCompilerPointWasm2 C initial after types (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point []
  let p := state.boundary.pending next advance inbounds
  have pairs := reader_ordinary_indirect_wasm2 p ops law before after out ctx rfl opcode ordinary byte accepted
  apply point.preserved_step pairs
  intro future old
  have embedding : LinearEmbedding locals (CumulativeEmission (before.function.indirect.val ++ future) C) := by
    intro input instruction code output h
    exact .left (.core (.pure (by simpa only [contextLocals] using h)))
  exact old.ordinary ops law embedding metadata localsMatch next advance inbounds out sourceBound bodyBound opcode ordinary byte accepted
end Exec.Code
