import Itasca.Runtime.Code.Local.Relations.Common.StatefulEffects
import Itasca.Runtime.Code.Local.Relations.Calls.IndirectCallMetadata
import Itasca.Runtime.Code.Body.Reader.Common.ReaderExtendedCodeMonotone
import Itasca.Runtime.Code.Local.Callbacks.Common.FixupPreservation
import Itasca.Runtime.Code.Local.Callbacks.Common.CompilerTerminalMetadata
import Itasca.Runtime.Code.Local.Callbacks.Common.CompilerCodeMonotoneStateful
import Itasca.Runtime.Code.Local.Callbacks.Simd.CompilerCodeMonotoneSimd
import Itasca.Runtime.Code.Local.Callbacks.Common.CompilerCodeMonotoneScalar
import Itasca.Runtime.Code.Body.Reader.Common.StatefulReaderBase
import Itasca.Runtime.Code.Body.Reader.Common.StatefulReaderBulkDispatch
import Itasca.Runtime.Code.Body.Reader.Calls.ReaderIndirectCall
import Itasca.Runtime.Code.Body.Reader.Common.ReaderTypedSelect
import Itasca.Runtime.Code.Body.Reader.Simd.ReaderSimdEvent
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Actual scalar/reference callbacks preserve previously emitted code slots. -/
theorem reader_stateful_base_fixup_budget_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (opcode : U8)
    (member : opcode.val ∈ [37,38,63,64,208,209,210])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  obtain ⟨op,a,b,arguments,callback,_⟩ := reader_stateful_base_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx opcode member byte accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact budget.ordinary (compiler_stateful_ordinary_result ops law before after out.core op a b (.Ok ()) callback)
    (compiler_stateful_code_mono ops law before after out.core op a b (.Ok ()) callback)

theorem reader_stateful_bulk_fixup_budget_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (subopcode : U32) (next : Usize)
    (member : subopcode.val ∈ [8,9,10,11,12,13,14,15,16,17])
    (byte : data.val[p.start.val]'p.inbounds = 252#u8)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 252#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  obtain ⟨op,a,b,arguments,callback,_⟩ := reader_stateful_bulk_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx subopcode next member byte decoded accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact budget.ordinary (compiler_stateful_ordinary_result ops law before after out.core op a b (.Ok ()) callback)
    (compiler_stateful_code_mono ops law before after out.core op a b (.Ok ()) callback)

theorem reader_indirect_call_fixup_budget_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 17#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  obtain ⟨idx,table,values,callback,rest⟩ := reader_indirect_call_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact budget.ordinary (compiler_indirect_call_ordinary_result ops law before after out.core idx table (.Ok ()) callback)
    (compiler_indirect_call_code_mono ops law before after out.core idx table (.Ok ()) callback)

theorem reader_typed_select_fixup_budget_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 28#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  obtain ⟨ty,position,callback,rest⟩ := reader_typed_select_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact budget.ordinary (compiler_core_ordinary_result ops law before after out.core (.select true) (.Ok ()) callback)
    (compiler_core_code_mono ops law before after out.core (.select true) callback)

theorem SimdReaderEvent.fixup_budget {A : Type} {ops : runtime.platform.Alloc A}
    {data env locals index st p before after out C}
    (event : @SimdReaderEvent A ops data env locals index st p before after out C)
    (law : Platform.AllocCorrect ops) : FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  have bound := event.meaning.opcode_bound
  have number := event.number
  exact budget.ordinary
    (compiler_lower_simd_effects ops law before after out event.opcode event.a event.b event.bits
      (by omega) (by omega) event.callback).1
    (compiler_lower_simd_code_mono ops law before after out event.opcode event.a event.b event.bits
      (by omega) (by omega) event.callback)

end Itasca.Runtime.Code
