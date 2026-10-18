import Exec.Code.Local.Lowering.Common.LoweringArithmetic
namespace Exec.Code
open Aeneas Aeneas.Std

def binaryOpcode : Inn → IntegerBinary → U16
  | .I32, .add => 106#u16
  | .I32, .sub => 107#u16
  | .I32, .mul => 108#u16
  | .I32, .eq => 70#u16
  | .I32, .ne => 71#u16
  | .I32, .ltU => 73#u16
  | .I32, .gtU => 75#u16
  | .I32, .leU => 77#u16
  | .I32, .geU => 79#u16
  | .I64, .add => 124#u16
  | .I64, .sub => 125#u16
  | .I64, .mul => 126#u16
  | .I64, .eq => 81#u16
  | .I64, .ne => 82#u16
  | .I64, .ltU => 84#u16
  | .I64, .gtU => 86#u16
  | .I64, .leU => 88#u16
  | .I64, .geU => 90#u16

set_option maxRecDepth 4096 in
theorem lower_integer_binary_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (ty : Inn) (op : IntegerBinary) (left right : U32) (reachable : compiler.reachable = true)
    (hleft : runtime.compiler.FunctionCompiler.operand ops compiler 2#usize = .ok (.Ok left))
    (hright : runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok right)) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (binaryOpcode ty op) 0#u32 0#u32 0#u128 =
      runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (op.target ty left right) := by
  have binary : runtime.compiler.lower.scalar_binary (binaryOpcode ty op) = .ok true := by cases ty <;> cases op <;> rfl
  have make (a b : U32) : runtime.bytecode.Instr.make_scalar (binaryOpcode ty op) a a b =
      .ok (some (op.target ty a b)) := by cases ty <;> cases op <;> rfl
  have run : runtime.compiler.lower.FunctionCompiler.op ops compiler state (binaryOpcode ty op) 0#u32 0#u32 0#u128 = (do
    let binary ← runtime.compiler.lower.scalar_binary (binaryOpcode ty op)
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
        let o ← runtime.bytecode.Instr.make_scalar (binaryOpcode ty op) val val val1
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
    cases ty <;> cases op <;> unfold runtime.compiler.lower.FunctionCompiler.op <;> rw [if_pos reachable] <;> rfl
  rewrite [run, binary, bind_ok]
  simp only [ite_true, bind_ok, hleft, hright,
    core.result.Result.Insts.CoreOpsTry.branch, make, core.option.Option.ok_or]

noncomputable def binaryCallback {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (ty : Inn) (op : IntegerBinary) :=
  match ty, op with
  | .I32, .add => runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_add ops compiler state
  | .I32, .sub => runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_sub ops compiler state
  | .I32, .mul => runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_mul ops compiler state
  | .I32, .eq => runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_eq ops compiler state
  | .I32, .ne => runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_ne ops compiler state
  | .I32, .ltU => runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_lt_u ops compiler state
  | .I32, .gtU => runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_gt_u ops compiler state
  | .I32, .leU => runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_le_u ops compiler state
  | .I32, .geU => runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_ge_u ops compiler state
  | .I64, .add => runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_add ops compiler state
  | .I64, .sub => runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_sub ops compiler state
  | .I64, .mul => runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_mul ops compiler state
  | .I64, .eq => runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_eq ops compiler state
  | .I64, .ne => runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_ne ops compiler state
  | .I64, .ltU => runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_lt_u ops compiler state
  | .I64, .gtU => runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_gt_u ops compiler state
  | .I64, .leU => runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_le_u ops compiler state
  | .I64, .geU => runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_ge_u ops compiler state

theorem binaryCallback_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (ty : Inn) (op : IntegerBinary) : binaryCallback ops compiler state ty op =
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (binaryOpcode ty op) 0#u32 0#u32 0#u128 := by
  cases ty <;> cases op <;> rfl

@[step] theorem callback_integer_binary {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (front : List valtype) (ty : Inn) (op : IntegerBinary)
    (layout : CompilerLayout compiler (front ++ [integerType ty, integerType ty]))
    (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ [op.output ty])
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    binaryCallback ops compiler state ty op ⦃ out => out.1 = .Ok () →
      ∃ left right, left.val = slots (compilerLocals compiler) + slots front ∧
        right.val = left.val + 1 ∧ Lowered compiler out.2 (op.target ty left right) (front ++ [op.output ty]) ⦄ := by
  obtain ⟨left, right, hl, hr, hleft, hright⟩ := binary_operands ops compiler front ty layout
  rw [binaryCallback_eq, lower_integer_binary_eq ops compiler state ty op left right reachable hl hr]
  step with finish_op ops law compiler state types (op.target ty left right) _ layout concrete
    codeFits sourceFits coordinateFits as ⟨out, hout, success⟩
  exact ⟨left, right, hleft, hright, by simpa only [typed] using hout success⟩

@[step] theorem callback_integer_binary_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (front : List valtype) (ty : Inn) (op : IntegerBinary)
    (locals initial : List valtype) (source : List instr)
    (invariant : LinearCompileInv compiler locals initial source (front ++ [integerType ty, integerType ty]))
    (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ [op.output ty])
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    binaryCallback ops compiler state ty op ⦃ out => out.1 = .Ok () →
      LinearCompileInv out.2 locals initial (source ++ [op.source ty]) (front ++ [op.output ty]) ⦄ := by
  apply WP.spec_mono (callback_integer_binary ops law compiler state types front ty op invariant.layout
    reachable concrete typed codeFits sourceFits coordinateFits)
  intro out result accepted
  obtain ⟨left, right, hleft, hright, lowered⟩ := result accepted
  apply lowered.extend_prefix invariant
  exact LinearEmission.binary front ty op left right (by simpa [invariant.localsEq] using hleft) hright
end Exec.Code
