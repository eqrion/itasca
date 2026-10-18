import Exec.Code.Body.Reader.Common.CumulativeReaderCompilerPoint
import Exec.Code.Body.Reader.Calls.ReaderExtraIndirect
import Exec.Code.Body.Lowering.Float.FloatEmbedding
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem CumulativeReaderCompilerPointWasm2.core_extra {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st}
    (C : context)
    (point : CumulativeReaderCompilerPointWasm2 C initial before types functions returns locals data env ctx.locals index ft st)
    (contextLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (opcode : U8) (covered : opcode.val ∈ [27,35,36,67,68,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62])
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    CumulativeReaderCompilerPointWasm2 C initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point []
  let p := state.boundary.pending next advance inbounds
  have pairs := reader_core_extra_indirect_wasm2 p ops law before after out ctx rfl opcode covered byte accepted
  apply point.preserved_step pairs
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  exact state.core_extra ops law C contextLocals contextGlobals contextMemories next advance inbounds out sourceBound bodyBound opcode covered byte accepted
end Exec.Code
