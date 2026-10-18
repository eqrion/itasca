import Exec.Code.Body.Reader.Common.ReaderSignExtension
import Exec.Code.Local.Lowering.Common.NumericEffects
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Accepted sign-extension dispatch changes frame capacity only through the
actual final operand observation, without a source-pending premise. -/
theorem reader_sign_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (op : Abs.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    CapacityStep before after out.core := by
  obtain ⟨operation, hook, meaning, _, _, _, encoding, hookEq, ordinary, base⟩ :=
    integer_sign_reader_facts ops before out.core op extension
  obtain ⟨capacity, run⟩ := profile_scalar_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index _ before after ordinary accepted
  rw [code.step_wasm2.base _ _ _ _ _ _ _ base,
    code.step_extended.sign _ _ _ _ _ _ operation _ meaning] at run
  obtain ⟨unit, read, callback⟩ := reader_run_success _ _ _ _ _ run
  have dispatch := ExtendedNumericHook.dispatch
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before out.core hook
  rw [encoding] at dispatch
  dsimp only at dispatch
  rw [dispatch, hookEq] at callback
  exact compiler_numeric_capacity ops law before after out.core op callback
end Exec.Code
