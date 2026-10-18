import Exec.Code.Local.Lowering.Local.LoweringLocal
namespace Exec.Code
open Aeneas Aeneas.Std

def eqzOpcode : Inn → U16 | .I32 => 69#u16 | .I64 => 80#u16

def eqzTarget (ty : Inn) (operand : U32) : Bytecode :=
  match ty with | .I32 => .I32Eqz operand operand operand | .I64 => .I64Eqz operand operand operand

def eqzSource (ty : Inn) : instr := .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ)

set_option maxRecDepth 4096 in
theorem lower_eqz_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (ty : Inn) (operand : U32) (reachable : compiler.reachable = true)
    (hoperand : runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok operand)) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (eqzOpcode ty) 0#u32 0#u32 0#u128 =
      runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (eqzTarget ty operand) := by
  have binary : runtime.compiler.lower.scalar_binary (eqzOpcode ty) = .ok false := by cases ty <;> rfl
  have make (a : U32) : runtime.bytecode.Instr.make_scalar (eqzOpcode ty) a a a =
      .ok (some (eqzTarget ty a)) := by cases ty <;> rfl
  have run : runtime.compiler.lower.FunctionCompiler.op ops compiler state (eqzOpcode ty) 0#u32 0#u32 0#u128 = (do
    let binary ← runtime.compiler.lower.scalar_binary (eqzOpcode ty)
    let depth ← if binary
                  then Result.ok 2#usize
                  else Result.ok 1#usize
    let r ←
      runtime.compiler.FunctionCompiler.operand ops compiler depth
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ←
        runtime.compiler.FunctionCompiler.operand ops compiler
          1#usize
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let o ← runtime.bytecode.Instr.make_scalar (eqzOpcode ty) val val val1
        let r2 ←
          core.option.Option.ok_or o
            _root_.Itasca.error.VisitError.OutOfMemory
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          runtime.compiler.lower.FunctionCompiler.finish_op ops
            compiler state val2
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r3 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
              residual
          Result.ok (r3, compiler)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
            residual
        Result.ok (r2, compiler)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      Result.ok (r1, compiler)) := by
    cases ty <;> unfold runtime.compiler.lower.FunctionCompiler.op <;> rw [if_pos reachable] <;> rfl
  rewrite [run, binary, bind_ok]
  simp only [Bool.false_eq_true, ite_false, bind_ok, hoperand,
    core.result.Result.Insts.CoreOpsTry.branch, make, core.option.Option.ok_or]

noncomputable def eqzCallback {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (ty : Inn) := match ty with
  | .I32 => runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_eqz ops compiler state
  | .I64 => runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_eqz ops compiler state

theorem eqzCallback_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (ty : Inn) :
    eqzCallback ops compiler state ty =
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (eqzOpcode ty) 0#u32 0#u32 0#u128 := by
  cases ty <;> rfl

@[step] theorem callback_eqz {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (front : List valtype) (ty : Inn)
    (layout : CompilerLayout compiler (front ++ [integerType ty]))
    (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ [.I32])
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    eqzCallback ops compiler state ty ⦃ out => out.1 = .Ok () →
      ∃ operand : U32, operand.val = slots (compilerLocals compiler) + slots front ∧
        Lowered compiler out.2 (eqzTarget ty operand) (front ++ [.I32]) ∧
        LinearEmission (compilerLocals compiler) (front ++ [integerType ty]) (eqzSource ty)
          [eqzTarget ty operand] (front ++ [.I32]) ⦄ := by
  obtain ⟨operand, read, position⟩ := last_operand ops compiler front (integerType ty) layout
  rw [eqzCallback_eq, lower_eqz_eq ops compiler state ty operand reachable read]
  apply WP.spec_mono (finish_op ops law compiler state types _ _ layout concrete codeFits sourceFits coordinateFits)
  intro out lowered accepted
  refine ⟨operand, position, ?_, ?_⟩
  · simpa only [typed] using lowered accepted
  · cases ty
    · exact LinearEmission.eqz32 front operand position
    · exact LinearEmission.eqz64 front operand position

end Exec.Code
