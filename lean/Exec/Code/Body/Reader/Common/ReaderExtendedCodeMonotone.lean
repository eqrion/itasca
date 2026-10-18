import Exec.Code.Local.Callbacks.Common.CompilerCodeMonotoneStateful
import Exec.Code.Local.Callbacks.Simd.CompilerCodeMonotoneSimd
import Exec.Code.Local.Callbacks.Common.CompilerCodeMonotoneScalar
import Exec.Code.Body.Reader.Common.StatefulReaderBase
import Exec.Code.Body.Reader.Common.StatefulReaderBulkDispatch
import Exec.Code.Body.Reader.Calls.ReaderIndirectCall
import Exec.Code.Body.Reader.Calls.ReaderIndirectCallWasm1
import Exec.Code.Body.Reader.Common.ReaderTypedSelect
import Exec.Code.Body.Reader.Simd.ReaderSimdEvent
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Actual scalar/reference callbacks preserve previously emitted code slots. -/
theorem reader_stateful_base_code_mono_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (opcode : U8)
    (member : opcode.val ∈ [37,38,63,64,208,209,210])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  obtain ⟨op,a,b,arguments,callback,_⟩ := reader_stateful_base_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx opcode member byte accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact compiler_stateful_code_mono ops law before after out.core op a b (.Ok ()) callback

theorem reader_stateful_bulk_code_mono_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (subopcode : U32) (next : Usize)
    (member : subopcode.val ∈ [8,9,10,11,12,13,14,15,16,17])
    (byte : data.val[p.start.val]'p.inbounds = 252#u8)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 252#u8 before = .ok (.Ok (),out,after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  obtain ⟨op,a,b,arguments,callback,_⟩ := reader_stateful_bulk_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx subopcode next member byte decoded accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact compiler_stateful_code_mono ops law before after out.core op a b (.Ok ()) callback

theorem reader_indirect_call_code_mono_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 17#u8 before = .ok (.Ok (),out,after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  obtain ⟨idx,table,values,callback,rest⟩ := reader_indirect_call_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_indirect_call_code_mono ops law before after out.core idx table (.Ok ()) callback

theorem reader_typed_select_code_mono_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 28#u8 before = .ok (.Ok (),out,after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  obtain ⟨ty,position,callback,rest⟩ := reader_typed_select_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_core_code_mono ops law before after out.core (.select true) callback

theorem SimdReaderEvent.code_mono {A : Type} {ops : runtime.platform.Alloc A}
    {data env locals index st p before after out C}
    (event : @SimdReaderEvent A ops data env locals index st p before after out C)
    (law : Platform.AllocCorrect ops) : before.function.code.val.length ≤ after.function.code.val.length := by
  have bound := event.meaning.opcode_bound
  have number := event.number
  exact compiler_lower_simd_code_mono ops law before after out event.opcode event.a event.b event.bits
    (by omega) (by omega) event.callback

theorem reader_indirect_call_code_mono_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 17#u8 before = .ok (.Ok (),out,after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  have capacity : st.vals.val.length < Usize.max := by have := p.val_capacity; omega
  have run := accepted
  obtain ⟨idx,values,callback,rest⟩ := reader_indirect_call_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out capacity byte (by simpa only [global_simps] using run)
  exact compiler_indirect_call_code_mono ops law before after out idx 0#u32 (.Ok ()) callback

theorem reader_memory_size_code_mono_wasm1 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 63#u8 before = .ok (.Ok (),out,after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  have run := accepted
  have dispatch := code.step_memory_size.dispatch
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  cases value
  exact compiler_stateful_code_mono ops law before after out .memorySize 0#u32 0#u32 (.Ok ()) callback

theorem reader_memory_grow_code_mono_wasm1 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 64#u8 before = .ok (.Ok (),out,after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  have run := accepted
  have dispatch := code.step_memory_grow.dispatch
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  cases value
  exact compiler_stateful_code_mono ops law before after out .memoryGrow 0#u32 0#u32 (.Ok ()) callback

end Exec.Code
