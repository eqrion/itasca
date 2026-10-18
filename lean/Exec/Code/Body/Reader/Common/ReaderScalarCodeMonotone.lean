import Exec.Code.Local.Callbacks.Common.CompilerCodeMonotoneScalar
import Exec.Code.Body.Reader.Common.NumericReaderFacts
import Exec.Code.Body.Reader.Float.FloatReaderFacts
import Exec.Code.Body.Reader.Common.ReaderSignExtension
import Exec.Code.Body.Reader.Common.ReaderSaturating
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem reader_numeric_base_code_mono_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : Abs.Numeric.Instruction) (baseOpcode : (integerOpcode op).val < 192)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (),out,after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  obtain ⟨operation,hook,meaning,handler,instruction,inputs,output,hookEq,ordinary,base,sign,misc⟩ :=
    integer_reader_facts ops before out.core op baseOpcode
  obtain ⟨capacity,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals,p.ft.results⟩ index _ before after ordinary base sign misc contextLocals accepted
  obtain ⟨callback,_,_,_,values,effect,post⟩ := reader_numeric_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ operation hook
    capacity byte meaning handler run
  rw [hookEq] at callback
  exact compiler_numeric_code_mono ops law before after out.core op callback

theorem reader_float_base_code_mono_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : Abs.Float.Instruction) (baseOpcode : (floatOpcode op).val < 256)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (floatOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (),out,after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  obtain ⟨operation,hook,meaning,handler,instruction,inputs,output,hookEq,ordinary,base,sign,misc⟩ :=
    float_reader_facts ops before out.core op baseOpcode
  obtain ⟨capacity,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals,p.ft.results⟩ index _ before after ordinary base sign misc contextLocals accepted
  obtain ⟨callback,_,_,_,values,effect,post⟩ := reader_numeric_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ operation hook
    capacity byte meaning handler run
  rw [hookEq] at callback
  exact compiler_float_code_mono ops law before after out.core op callback

theorem reader_numeric_code_mono_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : Abs.Numeric.Instruction)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (),out,after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  by_cases base : (integerOpcode op).val < 192
  · exact reader_numeric_base_code_mono_wasm2 p ops law before after out ctx contextLocals op base byte accepted
  · obtain ⟨operation,instruction,inputs,output,callback,rest⟩ :=
      reader_integer_sign_wasm2 p ops before after out ctx op (by omega) byte accepted
    exact compiler_numeric_code_mono ops law before after out.core op callback

theorem reader_saturating_code_mono_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (op : Abs.Float.Instruction) (extension : 256 ≤ (floatOpcode op).val)
    (subopcode : U32) (next : Usize) (subopcodeEq : subopcode.val = (floatOpcode op).val - 256)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (byte : data.val[p.start.val]'p.inbounds = 252#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 252#u8 before = .ok (.Ok (),out,after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  obtain ⟨operation,instruction,inputs,output,callback,rest⟩ :=
    reader_float_saturating_wasm2 p ops before after out ctx op extension subopcode next subopcodeEq decoded byte accepted
  exact compiler_float_code_mono ops law before after out.core op callback

end Exec.Code
