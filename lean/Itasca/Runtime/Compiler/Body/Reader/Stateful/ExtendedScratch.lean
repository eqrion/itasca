import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchStateful
import Itasca.Runtime.Compiler.Local.Callbacks.Simd.CompilerTableScratchSimd
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchScalar
import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulBase
import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulBulkDispatch
import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Runtime.Compiler.Body.Reader.References.TypedSelect
import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdEvent

/-!
Scratch-depth preservation for indirect calls, typed select and SIMD reader events.

Main declarations: `reader_indirect_call_depths_wasm2` and `SimdReaderEvent.depths`. A direct consumer is `Compiler.Body.Reader.Replay.IndexedStateful`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_indirect_call_depths_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 17#u8 before = .ok (.Ok (),out,after)) :
    after.table_depths = before.table_depths := by
  obtain ⟨idx,table,values,callback,rest⟩ := reader_indirect_call_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_indirect_call_depths ops law before after out.core idx table (.Ok ()) callback

theorem reader_typed_select_depths_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 28#u8 before = .ok (.Ok (),out,after)) :
    after.table_depths = before.table_depths := by
  obtain ⟨ty,position,callback,rest⟩ := reader_typed_select_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_core_depths ops law before after out.core (.select true) callback

theorem SimdReaderEvent.depths {A : Type} {ops : runtime.platform.Alloc A}
    {data env locals index st p before after out C}
    (event : @SimdReaderEvent A ops data env locals index st p before after out C)
    (law : Platform.AllocCorrect ops) : after.table_depths = before.table_depths := by
  have bound := event.meaning.opcode_bound
  have number := event.number
  exact compiler_lower_simd_depths ops law before after out event.opcode event.a event.b event.bits
    (by omega) (by omega) event.callback

end Itasca.Runtime.Compiler
