import Exec.Code.Body.Reader.Common.ReaderScalarCodeMonotoneWasm1
import Exec.Code.Local.Callbacks.Common.FixupPreservation
import Exec.Code.Local.Callbacks.Common.CompilerTerminalMetadata
import Exec.Code.Local.Callbacks.Common.CompilerCodeMonotoneScalar
import Exec.Code.Body.Reader.Common.NumericReaderFacts
import Exec.Code.Body.Reader.Float.FloatReaderFacts
import Exec.Code.Body.Reader.Common.ReaderSignExtension
import Exec.Code.Body.Reader.Common.ReaderSaturating
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem reader_numeric_base_fixup_budget_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (op : Abs.Numeric.Instruction) (baseOpcode : (integerOpcode op).val < 192)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  obtain ⟨operation,hook,meaning,handler,instruction,inputs,output,hookEq,ordinary,base,sign,misc⟩ :=
    integer_reader_facts ops before out op baseOpcode
  have capacity : st.vals.val.length < Usize.max := by have := p.val_capacity; omega
  obtain ⟨callback,_,_,_,values,effect,post⟩ := reader_numeric_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out _ operation hook
    capacity byte meaning handler accepted
  rw [hookEq] at callback
  exact budget.ordinary (compiler_numeric_ordinary_result ops law before after out op (.Ok ()) callback)
    (compiler_numeric_code_mono ops law before after out op callback)

theorem reader_float_base_fixup_budget_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (op : Abs.Float.Instruction) (baseOpcode : (floatOpcode op).val < 256)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (floatOpcode op))
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  obtain ⟨operation,hook,meaning,handler,instruction,inputs,output,hookEq,ordinary,base,sign,misc⟩ :=
    float_reader_facts ops before out op baseOpcode
  have capacity : st.vals.val.length < Usize.max := by have := p.val_capacity; omega
  obtain ⟨callback,_,_,_,values,effect,post⟩ := reader_numeric_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out _ operation hook
    capacity byte meaning handler accepted
  rw [hookEq] at callback
  exact budget.ordinary (compiler_float_ordinary_result ops law before after out op (.Ok ()) callback)
    (compiler_float_code_mono ops law before after out op callback)

theorem reader_numeric_fixup_budget_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (op : Abs.Numeric.Instruction)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  by_cases base : (integerOpcode op).val < 192
  · exact reader_numeric_base_fixup_budget_wasm1 p ops law before after out op base byte accepted budget
  · exact False.elim (reader_integer_sign_wasm1_impossible ops before after st out data env ctx op (by omega) accepted)
end Exec.Code
