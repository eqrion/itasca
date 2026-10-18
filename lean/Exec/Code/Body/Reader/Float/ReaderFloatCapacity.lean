import Exec.Code.Body.Reader.Float.FloatReaderFacts
import Exec.Code.Local.Lowering.Float.FloatEffects
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem reader_float_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (operation : Abs.Float.Instruction) (base : (floatOpcode operation).val < 256)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (floatOpcode operation)) before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  obtain ⟨row, hook, meaning, handler, _, _, _, callback, _⟩ := float_reader_facts ops before out operation base
  rw [dispatch_numeric _ _ _ _ _ _ _ row hook meaning handler] at accepted
  obtain ⟨value, _, called⟩ := reader_run_success _ _ _ _ _ accepted
  rw [callback] at called
  exact compiler_float_capacity ops law before after out operation called

theorem reader_float_capacity_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (operation : Abs.Float.Instruction) (base : (floatOpcode operation).val < 256)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (floatOpcode operation)) before = .ok (.Ok (), out, after)) :
    CapacityStep before after out.core := by
  obtain ⟨row, hook, meaning, handler, instruction, inputs, output, hookEq, ordinary, absent, sign, misc⟩ :=
    float_reader_facts ops before out.core operation base
  obtain ⟨_, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index _ before after
    ordinary absent sign misc rfl accepted
  exact reader_float_capacity ops law before after st.core out.core data env ctx operation base run
end Exec.Code
