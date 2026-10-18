import Exec.Code.Body.Reader.Common.CumulativeReaderCompilerPoint
import Exec.Code.Body.Reader.Common.StatefulReaderPrefix
import Exec.Code.Body.Reader.Common.StatefulReaderBase
import Exec.Code.Body.Reader.Common.StatefulReaderBulkDispatch
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem CumulativeReaderCompilerPointWasm2.stateful_reader {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env sourceLocals index ft st}
    (point : CumulativeReaderCompilerPointWasm2 C initial before types functions returns locals data env sourceLocals index ft st)
    (matched : EnvTranslation.Matches env ⟨sourceLocals,ft.results⟩ C) (contextLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (read : ∀ p : Wasm2.Pending data env sourceLocals index {core := {st.core with pos := next}},
      p.start = st.core.pos → ∃ op a b, StatefulArguments op a b ∧
        runtime.compiler.lower.FunctionCompiler.op ops before out.core (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after) ∧
        StatefulReaderPost p out.core op) :
    CumulativeReaderCompilerPointWasm2 C initial after types functions returns locals data env sourceLocals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point []
  let p := state.boundary.pending next advance inbounds
  obtain ⟨op,a,b,arguments,callback,post⟩ := read p rfl
  obtain ⟨extra,pairs⟩ := post.indirect_prefix ops law initial before after C state.compiled
    state.reach.current matched contextLocals a b arguments callback sourceBound bodyBound
  apply point.append_step extra pairs
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  let p := state.boundary.pending next advance inbounds
  obtain ⟨op,a,b,arguments,callback,post⟩ := read p rfl
  obtain ⟨values,reader,compiled,reachable⟩ := post.future_prefix ops law initial before after C future state.compiled
    state.reach.current matched contextLocals a b arguments callback sourceBound bodyBound
  exact (state.advance next advance inbounds reader reader.declared compiled
    (fun live => state.reach.current (reachable ▸ live))).point

theorem CumulativeReaderCompilerPointWasm2.stateful_base {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env ctx index ft st}
    (point : CumulativeReaderCompilerPointWasm2 C initial before types functions returns locals data env ctx.locals index ft st)
    (matched : EnvTranslation.Matches env ⟨ctx.locals,ft.results⟩ C) (contextLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (opcode : U8) (member : opcode.val ∈ [37,38,63,64,208,209,210])
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    CumulativeReaderCompilerPointWasm2 C initial after types functions returns locals data env ctx.locals index ft out := by
  apply point.stateful_reader ops law matched contextLocals next advance inbounds out sourceBound bodyBound
  intro p start
  obtain ⟨op,a,b,arguments,callback,post⟩ := reader_stateful_base_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx opcode member
    (by simpa only [start] using byte) accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact ⟨op,a,b,arguments,callback,post⟩

theorem CumulativeReaderCompilerPointWasm2.stateful_bulk {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env ctx index ft st}
    (point : CumulativeReaderCompilerPointWasm2 C initial before types functions returns locals data env ctx.locals index ft st)
    (matched : EnvTranslation.Matches env ⟨ctx.locals,ft.results⟩ C) (contextLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (subopcode : U32) (afterSubopcode : Usize)
    (member : subopcode.val ∈ [8,9,10,11,12,13,14,15,16,17])
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 252#u8)
    (decoded : Leb128.Decoded data next subopcode afterSubopcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 252#u8 before = .ok (.Ok (),out,after)) :
    CumulativeReaderCompilerPointWasm2 C initial after types functions returns locals data env ctx.locals index ft out := by
  apply point.stateful_reader ops law matched contextLocals next advance inbounds out sourceBound bodyBound
  intro p start
  obtain ⟨op,a,b,arguments,callback,post⟩ := reader_stateful_bulk_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx subopcode afterSubopcode member
    (by simpa only [start] using byte) decoded accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact ⟨op,a,b,arguments,callback,post⟩

end Exec.Code
