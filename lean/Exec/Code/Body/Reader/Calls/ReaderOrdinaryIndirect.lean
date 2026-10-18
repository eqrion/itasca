import Exec.Code.Body.Reader.Calls.ReaderLiteralIndirect
import Exec.Code.Body.Reader.Calls.ReaderScalarIndirect
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerOrdinary
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_ordinary_base_indirect_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (ctxLocals : ctx.locals = locals) (opcode : U8) (ordinary : opcode ∈ readerBaseOrdinaryOpcodes)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    after.function.indirect = before.function.indirect := by
  simp only [readerBaseOrdinaryOpcodes,List.mem_cons,List.not_mem_nil,or_false] at ordinary
  rcases ordinary with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reader_unreachable_indirect_wasm2 ops law before after st out data env ctx index accepted
  · exact reader_nop_indirect_wasm2 ops law before after st out data env ctx index accepted
  · exact reader_return_indirect_wasm2 ops law before after st out data env ctx index accepted
  · exact reader_call_indirect_wasm2 ops law before after st out data env ctx index accepted
  · exact reader_drop_indirect_wasm2 ops law before after st out data env ctx index accepted
  · exact reader_local_get_indirect_wasm2 ops law before after st out data env ctx index accepted
  · exact reader_local_set_indirect_wasm2 ops law before after st out data env ctx index accepted
  · exact reader_local_tee_indirect_wasm2 ops law before after st out data env ctx index accepted
  · exact reader_i32_const_indirect_wasm2 ops law before after st out data env ctx index accepted
  · exact reader_i64_const_indirect_wasm2 ops law before after st out data env ctx index accepted
  · exact reader_numeric_indirect_wasm2 p ops law before after out ctx ctxLocals (.eqz .I32) byte accepted
  · exact reader_numeric_indirect_wasm2 p ops law before after out ctx ctxLocals (.compare .I32 .EQ) byte accepted
  · exact reader_numeric_indirect_wasm2 p ops law before after out ctx ctxLocals (.compare .I32 (.LT .U)) byte accepted
  · exact reader_numeric_indirect_wasm2 p ops law before after out ctx ctxLocals (.eqz .I64) byte accepted
  · exact reader_numeric_indirect_wasm2 p ops law before after out ctx ctxLocals (.compare .I64 .EQ) byte accepted
  · exact reader_numeric_indirect_wasm2 p ops law before after out ctx ctxLocals (.compare .I64 (.LT .U)) byte accepted
  · exact reader_numeric_indirect_wasm2 p ops law before after out ctx ctxLocals (.binary .I32 .ADD) byte accepted
  · exact reader_numeric_indirect_wasm2 p ops law before after out ctx ctxLocals (.binary .I32 .SUB) byte accepted
  · exact reader_numeric_indirect_wasm2 p ops law before after out ctx ctxLocals (.binary .I64 .ADD) byte accepted
  · exact reader_numeric_indirect_wasm2 p ops law before after out ctx ctxLocals (.binary .I64 .SUB) byte accepted

theorem reader_ordinary_indirect_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (ctxLocals : ctx.locals = locals) (opcode : U8) (ordinary : opcode ∈ readerOrdinaryOpcodes)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    after.function.indirect = before.function.indirect := by
  rcases List.mem_append.mp ordinary with base | numeric
  · exact reader_ordinary_base_indirect_wasm2 p ops law before after out ctx ctxLocals opcode base byte accepted
  · obtain ⟨op,rfl⟩ := integer_opcode_of_mem numeric
    exact reader_numeric_indirect_wasm2 p ops law before after out ctx ctxLocals op byte accepted
end Exec.Code
