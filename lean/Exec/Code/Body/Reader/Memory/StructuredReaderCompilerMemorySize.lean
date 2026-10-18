import Exec.Code.Body.Reader.Common.StatefulReaderPrefixWasm1
import Exec.Code.Body.Reader.Memory.StatefulMemoryReaderWasm1
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerPoint
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Memory size and growth preserve a fixed cumulative emission relation in
both reachable and unreachable source code. -/
theorem StructuredReaderCompilerPointWasm1.memory_metadata {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C pairs types functions returns locals data env ctx bodyBt st}
    (point : StructuredReaderCompilerPointWasm1 (CumulativeEmission pairs C) initial before
      types functions returns locals data env ctx bodyBt st)
    (matched : EnvTranslation.Matches env ctx C) (contextLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (opcode : U8) (member : opcode.val ∈ [63,64])
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.pos.val]'inbounds = opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx opcode before = .ok (.Ok (),out,after)) :
    StructuredReaderCompilerPointWasm1 (CumulativeEmission pairs C) initial after
      types functions returns locals data env ctx bodyBt out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point
  let p := state.boundary.pending next advance inbounds
  obtain ⟨op,single,arguments,callback,post⟩ := reader_stateful_memory_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out opcode member byte accepted
  rw [stateful_callback_lower ops before out op 0#u32 0#u32 arguments] at callback
  obtain ⟨values,reader,compiled,reachable⟩ := post.single_prefix ops law initial before after C pairs
    state.compiled state.reach.current matched contextLocals 0#u32 0#u32 single arguments callback sourceBound bodyBound
  exact (state.advance next advance inbounds reader compiled
    (fun live => state.reach.current (reachable ▸ live))).point

end Exec.Code
