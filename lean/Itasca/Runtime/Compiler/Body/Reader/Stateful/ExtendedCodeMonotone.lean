import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.CompilerCodeMonotoneStateful
import Itasca.Runtime.Compiler.Local.Callbacks.Simd.CompilerCodeMonotoneSimd
import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.CompilerCodeMonotoneScalar
import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulBase
import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulBulkDispatch
import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Runtime.Compiler.Body.Reader.References.TypedSelect
import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdEvent

/-!
Emitted-code monotonicity for indirect calls, typed select and SIMD reader events.

Main declarations: `reader_indirect_call_code_mono_wasm2` and `SimdReaderEvent.code_mono`. A direct consumer is `Compiler.Body.Reader.Replay.IndexedStateful`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_indirect_call_code_mono_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
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
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
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

end Itasca.Runtime.Compiler
