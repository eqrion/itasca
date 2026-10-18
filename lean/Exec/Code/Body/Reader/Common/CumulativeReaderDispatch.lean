import Exec.Code.Body.Reader.Common.CumulativeReaderStateful
import Exec.Code.Body.Reader.Common.StatefulReaderBase
import Exec.Code.Body.Reader.Common.StatefulReaderBulkDispatch
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem StatefulReaderPost.cumulative_step {data env sourceLocals index st}
    {p : Wasm2.Pending data env sourceLocals index st} {out : code.OpIterState} {op : Abs.Stateful.Instruction}
    (post : StatefulReaderPost p out op) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (C : context)
    {types functions returns locals parents current}
    (invariant : CumulativeCompilerPrefix C initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (matched : EnvTranslation.Matches env ⟨sourceLocals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (a b : U32) (arguments : StatefulArguments op a b)
    (callback : runtime.compiler.lower.FunctionCompiler.op ops before out (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after))
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max) :
    ∃ values, ReaderPostWasm2 p out op.source p.current.ctrl.polymorphic_base values ∧
      CumulativeCompilerPrefix C initial after types functions returns locals parents (current.advance op.source)
        out.vals.val out.pos.val ∧ after.reachable = before.reachable := by
  by_cases reachable : before.reachable = true
  · obtain ⟨values,reader,compiled,liveAfter⟩ := post.cumulative_live ops law initial before after C invariant reachable
      (monomorphic reachable) matched contextLocals a b arguments callback sourceBound bodyBound
    exact ⟨values,reader,compiled,liveAfter.trans reachable.symm⟩
  · have dead : before.reachable = false := Bool.eq_false_iff.mpr reachable
    obtain ⟨values,reader,compiled,deadAfter⟩ := post.cumulative_dead ops law initial before after C invariant dead a b callback
    exact ⟨values,reader,compiled,deadAfter.trans dead.symm⟩

/-- Every accepted base-family M8 step advances the complete cumulative prefix.
Both live and polymorphic dead paths are derived from the actual dispatch. -/
theorem cumulative_reader_base_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (C : context)
    (out : code.BodyState) (ctx : code.Context) (opcode : U8)
    {types functions returns locals parents current}
    (invariant : CumulativeCompilerPrefix C initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (matched : EnvTranslation.Matches env ⟨sourceLocals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (member : opcode.val ∈ [37,38,63,64,208,209,210])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    ∃ (op : Abs.Stateful.Instruction), ∃ values, ReaderPostWasm2 p out.core op.source p.current.ctrl.polymorphic_base values ∧
      CumulativeCompilerPrefix C initial after types functions returns locals parents (current.advance op.source)
        out.core.vals.val out.core.pos.val ∧ after.reachable = before.reachable := by
  obtain ⟨op,a,b,arguments,callback,post⟩ := reader_stateful_base_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx opcode member byte accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact ⟨op,post.cumulative_step ops law initial before after C invariant monomorphic matched contextLocals
    a b arguments callback sourceBound bodyBound⟩

/-- The ten extended M8 instructions retain the exact decoded subopcode and
source immediates while deriving their cumulative emission from the callback. -/
theorem cumulative_reader_bulk_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (C : context)
    (out : code.BodyState) (ctx : code.Context) (subopcode : U32) (next : Usize)
    {types functions returns locals parents current}
    (invariant : CumulativeCompilerPrefix C initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (matched : EnvTranslation.Matches env ⟨sourceLocals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (member : subopcode.val ∈ [8,9,10,11,12,13,14,15,16,17])
    (byte : data.val[p.start.val]'p.inbounds = 252#u8)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 252#u8 before = .ok (.Ok (),out,after)) :
    ∃ (op : Abs.Stateful.Instruction), ∃ values, ReaderPostWasm2 p out.core op.source p.current.ctrl.polymorphic_base values ∧
      CumulativeCompilerPrefix C initial after types functions returns locals parents (current.advance op.source)
        out.core.vals.val out.core.pos.val ∧ after.reachable = before.reachable := by
  obtain ⟨op,a,b,arguments,callback,post⟩ := reader_stateful_bulk_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx subopcode next member byte decoded accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact ⟨op,post.cumulative_step ops law initial before after C invariant monomorphic matched contextLocals
    a b arguments callback sourceBound bodyBound⟩

end Exec.Code
