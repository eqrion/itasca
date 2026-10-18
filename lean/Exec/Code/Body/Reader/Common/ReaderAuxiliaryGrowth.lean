import Exec.Code.Local.Capacity.AuxiliaryGrowth
import Exec.Code.Local.Capacity.StatefulAuxiliaryGrowth
import Exec.Code.Local.Capacity.SimdAuxiliaryGrowth
import Exec.Code.Body.Reader.Table.ReaderOrdinaryTables
import Exec.Code.Body.Reader.Table.ReaderOrdinaryTablesWasm1
import Exec.Code.Body.Reader.Table.ReaderExtraTables
import Exec.Code.Body.Reader.Table.ReaderExtraTablesWasm1
import Exec.Code.Body.Reader.Table.ReaderScalarTables
import Exec.Code.Body.Reader.Table.ReaderScalarTablesWasm1
import Exec.Code.Body.Reader.Common.ReaderOrdinaryCodeMonotone
import Exec.Code.Body.Reader.Common.ReaderOrdinaryCodeMonotoneWasm1
import Exec.Code.Body.Reader.Common.ReaderExtraCodeMonotone
import Exec.Code.Body.Reader.Common.ReaderExtraCodeMonotoneWasm1
import Exec.Code.Body.Reader.Common.ReaderScalarCodeMonotone
import Exec.Code.Body.Reader.Common.ReaderScalarCodeMonotoneWasm1
import Exec.Code.Body.Reader.Common.ReaderExtendedCodeMonotone
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_ordinary_auxiliary_growth_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (ctxLocals : ctx.locals = locals) (opcode : U8) (ordinary : opcode ∈ readerOrdinaryOpcodes)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_ordinary_tables_wasm2 p ops law before after out ctx ctxLocals opcode ordinary byte accepted)
    (reader_ordinary_code_mono_wasm2 p ops law before after out ctx ctxLocals opcode ordinary byte accepted)

theorem reader_ordinary_auxiliary_growth_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (opcode : U8) (ordinary : opcode ∈ readerOrdinaryOpcodes)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_ordinary_tables_wasm1 p ops law before after out opcode ordinary byte accepted)
    (reader_ordinary_code_mono_wasm1 p ops law before after out opcode ordinary byte accepted)

theorem reader_core_extra_auxiliary_growth_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (contextLocals : ctx.locals = locals)
    (opcode : U8) (covered : opcode.val ∈ [27,35,36,67,68,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_core_extra_tables_wasm2 p ops law before after out ctx contextLocals opcode covered byte accepted)
    (reader_core_extra_code_mono_wasm2 p ops law before after out ctx contextLocals opcode covered byte accepted)

theorem reader_core_extra_auxiliary_growth_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (opcode : U8) (covered : opcode.val ∈ [27,35,36,67,68,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_core_extra_tables_wasm1 p ops law before after out opcode covered byte accepted)
    (reader_core_extra_code_mono_wasm1 p ops law before after out opcode covered byte accepted)

theorem reader_float_base_auxiliary_growth_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : Abs.Float.Instruction) (baseOpcode : (floatOpcode op).val < 256)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (floatOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_float_base_tables_wasm2 p ops law before after out ctx contextLocals op baseOpcode byte accepted)
    (reader_float_base_code_mono_wasm2 p ops law before after out ctx contextLocals op baseOpcode byte accepted)

theorem reader_float_base_auxiliary_growth_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (op : Abs.Float.Instruction) (baseOpcode : (floatOpcode op).val < 256)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (floatOpcode op))
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_float_base_tables_wasm1 p ops law before after out op baseOpcode byte accepted)
    (reader_float_base_code_mono_wasm1 p ops law before after out op baseOpcode byte accepted)

theorem reader_saturating_auxiliary_growth_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (op : Abs.Float.Instruction) (extension : 256 ≤ (floatOpcode op).val)
    (subopcode : U32) (next : Usize) (subopcodeEq : subopcode.val = (floatOpcode op).val - 256)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (byte : data.val[p.start.val]'p.inbounds = 252#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 252#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_saturating_tables_wasm2 p ops law before after out ctx op extension subopcode next subopcodeEq decoded byte accepted)
    (reader_saturating_code_mono_wasm2 p ops law before after out ctx op extension subopcode next subopcodeEq decoded byte accepted)

theorem reader_stateful_base_auxiliary_growth_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (opcode : U8)
    (member : opcode.val ∈ [37,38,63,64,208,209,210])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after := by
  obtain ⟨op,a,b,arguments,callback,_⟩ := reader_stateful_base_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx opcode member byte accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact compiler_stateful_auxiliary_growth ops law before after out.core op a b callback


theorem reader_stateful_bulk_auxiliary_growth_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (subopcode : U32) (next : Usize)
    (member : subopcode.val ∈ [8,9,10,11,12,13,14,15,16,17])
    (byte : data.val[p.start.val]'p.inbounds = 252#u8)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 252#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after := by
  obtain ⟨op,a,b,arguments,callback,_⟩ := reader_stateful_bulk_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx subopcode next member byte decoded accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact compiler_stateful_auxiliary_growth ops law before after out.core op a b callback


theorem reader_indirect_call_auxiliary_growth_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 17#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after := by
  obtain ⟨idx,table,values,callback,rest⟩ := reader_indirect_call_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_indirect_auxiliary_growth ops law before after out.core idx table callback


theorem reader_indirect_call_auxiliary_growth_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 17#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after := by
  have capacity : st.vals.val.length < Usize.max := by have := p.val_capacity; omega
  have run := accepted
  obtain ⟨idx,values,callback,rest⟩ := reader_indirect_call_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out capacity byte (by simpa only [global_simps] using run)
  exact compiler_indirect_auxiliary_growth ops law before after out idx 0#u32 callback


theorem reader_memory_size_auxiliary_growth_wasm1 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 63#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after := by
  have run := accepted
  have dispatch := code.step_memory_size.dispatch
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  cases value
  exact compiler_stateful_auxiliary_growth ops law before after out .memorySize 0#u32 0#u32 callback


theorem reader_memory_grow_auxiliary_growth_wasm1 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 64#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after := by
  have run := accepted
  have dispatch := code.step_memory_grow.dispatch
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  cases value
  exact compiler_stateful_auxiliary_growth ops law before after out .memoryGrow 0#u32 0#u32 callback


theorem SimdReaderEvent.auxiliary_growth {A : Type} {ops : runtime.platform.Alloc A}
    {data env locals index st p before after out C}
    (event : @SimdReaderEvent A ops data env locals index st p before after out C)
    (law : Platform.AllocCorrect ops) : AuxiliaryGrowth before after := by
  have bound := event.meaning.opcode_bound
  have number := event.number
  obtain ⟨mono,simd,pool,indirect,_⟩ := compiler_lower_simd_auxiliary_growth ops law before after out
    event.opcode event.a event.b event.bits (by omega) (by omega) event.callback
  unfold AuxiliaryGrowth
  have same := congrArg (fun xs => xs.val.length) indirect
  omega

theorem reader_typed_select_auxiliary_growth_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 28#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after := by
  obtain ⟨ty,position,callback,rest⟩ := reader_typed_select_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact .of_tables (compiler_core_tables ops law before after out.core (.select true) callback)
    (compiler_core_code_mono ops law before after out.core (.select true) callback)
end Exec.Code
