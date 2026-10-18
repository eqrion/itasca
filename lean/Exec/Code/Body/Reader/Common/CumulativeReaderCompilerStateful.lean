import Exec.Code.Body.Reader.Common.CumulativeReaderCompilerState
import Exec.Code.Body.Reader.Common.CumulativeReaderDispatch
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem CumulativeReaderCompilerStateWasm2.stateful_base {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : CumulativeReaderCompilerStateWasm2 C initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (matched : EnvTranslation.Matches env ⟨ctx.locals,ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (opcode : U8) (member : opcode.val ∈ [37,38,63,64,208,209,210])
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    ∃ (op : Abs.Stateful.Instruction), ∃ values,
      CumulativeReaderCompilerStateWasm2 C initial after types functions returns locals data env ctx.locals index ft out
        parents (current.advance op.source) savedParents
        (savedCurrent.advance (.plain op.source) op.source savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨op,values,post,compiled,reachable⟩ := cumulative_reader_base_wasm2 p ops law initial before after C out ctx opcode
    state.compiled state.reach.current matched contextLocals sourceBound bodyBound member byte accepted
  exact ⟨op,values,state.advance next advance inbounds post compiled (fun live => state.reach.current (reachable ▸ live))⟩

theorem CumulativeReaderCompilerStateWasm2.stateful_bulk {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : CumulativeReaderCompilerStateWasm2 C initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (matched : EnvTranslation.Matches env ⟨ctx.locals,ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (subopcode : U32) (afterSubopcode : Usize)
    (member : subopcode.val ∈ [8,9,10,11,12,13,14,15,16,17])
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 252#u8)
    (decoded : Leb128.Decoded data next subopcode afterSubopcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 252#u8 before = .ok (.Ok (),out,after)) :
    ∃ (op : Abs.Stateful.Instruction), ∃ values,
      CumulativeReaderCompilerStateWasm2 C initial after types functions returns locals data env ctx.locals index ft out
        parents (current.advance op.source) savedParents
        (savedCurrent.advance (.plain op.source) op.source savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨op,values,post,compiled,reachable⟩ := cumulative_reader_bulk_wasm2 p ops law initial before after C out ctx
    subopcode afterSubopcode state.compiled state.reach.current matched contextLocals sourceBound bodyBound member byte decoded accepted
  exact ⟨op,values,state.advance next advance inbounds post compiled (fun live => state.reach.current (reachable ▸ live))⟩

end Exec.Code
