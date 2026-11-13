import Itasca.Runtime.SourceMachine.Float.Results
import Itasca.Runtime.Equations
import Itasca.Runtime.Compiler.Local.Lowering.Integer.LoweringArithmetic

/-!
Sections, each formerly its own module: FloatOpcode, FloatLowering.
-/

/-! ## FloatOpcode -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

def floatOpcode (op : SourceMachine.Float.Instruction) : U16 :=
  UScalar.ofNat op.opcode (by have := op.opcode_bound; change op.opcode ≤ 65535; omega)

def floatInstruction (op : SourceMachine.Float.Instruction) (dst a b : U32) : runtime.bytecode.Instr :=
  match op with
  | .unary .F32 .ABS => .F32Abs dst a b
  | .unary .F32 .NEG => .F32Neg dst a b
  | .unary .F32 .CEIL => .F32Ceil dst a b
  | .unary .F32 .FLOOR => .F32Floor dst a b
  | .unary .F32 .TRUNC => .F32Trunc dst a b
  | .unary .F32 .NEAREST => .F32Nearest dst a b
  | .unary .F32 .SQRT => .F32Sqrt dst a b
  | .unary .F64 .ABS => .F64Abs dst a b
  | .unary .F64 .NEG => .F64Neg dst a b
  | .unary .F64 .CEIL => .F64Ceil dst a b
  | .unary .F64 .FLOOR => .F64Floor dst a b
  | .unary .F64 .TRUNC => .F64Trunc dst a b
  | .unary .F64 .NEAREST => .F64Nearest dst a b
  | .unary .F64 .SQRT => .F64Sqrt dst a b
  | .binary .F32 .ADD => .F32Add dst a b
  | .binary .F32 .SUB => .F32Sub dst a b
  | .binary .F32 .MUL => .F32Mul dst a b
  | .binary .F32 .DIV => .F32Div dst a b
  | .binary .F32 .MIN => .F32Min dst a b
  | .binary .F32 .MAX => .F32Max dst a b
  | .binary .F32 .COPYSIGN => .F32Copysign dst a b
  | .binary .F64 .ADD => .F64Add dst a b
  | .binary .F64 .SUB => .F64Sub dst a b
  | .binary .F64 .MUL => .F64Mul dst a b
  | .binary .F64 .DIV => .F64Div dst a b
  | .binary .F64 .MIN => .F64Min dst a b
  | .binary .F64 .MAX => .F64Max dst a b
  | .binary .F64 .COPYSIGN => .F64Copysign dst a b
  | .compare .F32 .EQ => .F32Eq dst a b
  | .compare .F32 .NE => .F32Ne dst a b
  | .compare .F32 .LT => .F32Lt dst a b
  | .compare .F32 .GT => .F32Gt dst a b
  | .compare .F32 .LE => .F32Le dst a b
  | .compare .F32 .GE => .F32Ge dst a b
  | .compare .F64 .EQ => .F64Eq dst a b
  | .compare .F64 .NE => .F64Ne dst a b
  | .compare .F64 .LT => .F64Lt dst a b
  | .compare .F64 .GT => .F64Gt dst a b
  | .compare .F64 .LE => .F64Le dst a b
  | .compare .F64 .GE => .F64Ge dst a b
  | .convert .I32 .F32 .S => .F32ConvertI32S dst a b
  | .convert .I32 .F32 .U => .F32ConvertI32U dst a b
  | .convert .I32 .F64 .S => .F64ConvertI32S dst a b
  | .convert .I32 .F64 .U => .F64ConvertI32U dst a b
  | .convert .I64 .F32 .S => .F32ConvertI64S dst a b
  | .convert .I64 .F32 .U => .F32ConvertI64U dst a b
  | .convert .I64 .F64 .S => .F64ConvertI64S dst a b
  | .convert .I64 .F64 .U => .F64ConvertI64U dst a b
  | .truncate .F32 .I32 .S false => .I32TruncF32S dst a b
  | .truncate .F32 .I32 .S true => .I32TruncSatF32S dst a b
  | .truncate .F32 .I32 .U false => .I32TruncF32U dst a b
  | .truncate .F32 .I32 .U true => .I32TruncSatF32U dst a b
  | .truncate .F32 .I64 .S false => .I64TruncF32S dst a b
  | .truncate .F32 .I64 .S true => .I64TruncSatF32S dst a b
  | .truncate .F32 .I64 .U false => .I64TruncF32U dst a b
  | .truncate .F32 .I64 .U true => .I64TruncSatF32U dst a b
  | .truncate .F64 .I32 .S false => .I32TruncF64S dst a b
  | .truncate .F64 .I32 .S true => .I32TruncSatF64S dst a b
  | .truncate .F64 .I32 .U false => .I32TruncF64U dst a b
  | .truncate .F64 .I32 .U true => .I32TruncSatF64U dst a b
  | .truncate .F64 .I64 .S false => .I64TruncF64S dst a b
  | .truncate .F64 .I64 .S true => .I64TruncSatF64S dst a b
  | .truncate .F64 .I64 .U false => .I64TruncF64U dst a b
  | .truncate .F64 .I64 .U true => .I64TruncSatF64U dst a b
  | .reinterpretFloat .F32 => .I32ReinterpretF32 dst a b
  | .reinterpretFloat .F64 => .I64ReinterpretF64 dst a b
  | .reinterpretInt .I32 => .F32ReinterpretI32 dst a b
  | .reinterpretInt .I64 => .F64ReinterpretI64 dst a b
  | .promote => .F64PromoteF32 dst a b
  | .demote => .F32DemoteF64 dst a b

theorem float_instruction_make (op : SourceMachine.Float.Instruction) (dst a b : U32) :
    runtime.bytecode.Instr.make_scalar (floatOpcode op) dst a b =
      .ok (some (floatInstruction op dst a b)) := by
  cases op with
  | unary ty operator => cases ty <;> cases operator <;> rfl
  | binary ty operator => cases ty <;> cases operator <;> rfl
  | compare ty operator => cases ty <;> cases operator <;> rfl
  | convert source target sign => cases source <;> cases target <;> cases sign <;> rfl
  | truncate source target sign saturating => cases source <;> cases target <;> cases sign <;> cases saturating <;> rfl
  | reinterpretFloat source => cases source <;> rfl
  | reinterpretInt source => cases source <;> rfl
  | promote | demote => rfl

theorem float_opcode_binary (op : SourceMachine.Float.Instruction) :
    runtime.compiler.lower.scalar_binary (floatOpcode op) = .ok (decide (op.arity = 2)) := by
  cases op with
  | unary ty operator => cases ty <;> cases operator <;> rfl
  | binary ty operator => cases ty <;> cases operator <;> rfl
  | compare ty operator => cases ty <;> cases operator <;> rfl
  | convert source target sign => cases source <;> cases target <;> cases sign <;> rfl
  | truncate source target sign saturating => cases source <;> cases target <;> cases sign <;> cases saturating <;> rfl
  | reinterpretFloat source => cases source <;> rfl
  | reinterpretInt source => cases source <;> rfl
  | promote | demote => rfl
end Itasca.Runtime.Compiler

end

/-! ## FloatLowering -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std SourceMachine.Float

/-- The shared scalar lowering path, before resolving its source operands. -/
noncomputable def floatLowering {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : Instruction) : Result (core.result.Result Unit Itasca.error.VisitError × runtime.compiler.FunctionCompiler A) := do
    let binary ← runtime.compiler.lower.scalar_binary (floatOpcode op)
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
        let o ← runtime.bytecode.Instr.make_scalar (floatOpcode op) val val val1
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
      Result.ok (r1, compiler)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem lower_float_dispatch {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : Instruction) (reachable : compiler.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (floatOpcode op) 0#u32 0#u32 0#u128 =
      floatLowering ops compiler state op := by
  cases op with
  | unary ty operator => cases ty <;> cases operator <;> (unfold runtime.compiler.lower.FunctionCompiler.op; rw [if_pos reachable]; rfl)
  | binary ty operator => cases ty <;> cases operator <;> (unfold runtime.compiler.lower.FunctionCompiler.op; rw [if_pos reachable]; rfl)
  | compare ty operator => cases ty <;> cases operator <;> (unfold runtime.compiler.lower.FunctionCompiler.op; rw [if_pos reachable]; rfl)
  | convert source target sign => cases source <;> cases target <;> cases sign <;> (unfold runtime.compiler.lower.FunctionCompiler.op; rw [if_pos reachable]; rfl)
  | truncate source target sign saturating => cases source <;> cases target <;> cases sign <;> cases saturating <;> (unfold runtime.compiler.lower.FunctionCompiler.op; rw [if_pos reachable]; rfl)
  | reinterpretFloat source => cases source <;> (unfold runtime.compiler.lower.FunctionCompiler.op; rw [if_pos reachable]; rfl)
  | reinterpretInt source => cases source <;> (unfold runtime.compiler.lower.FunctionCompiler.op; rw [if_pos reachable]; rfl)
  | promote | demote => skip <;> (unfold runtime.compiler.lower.FunctionCompiler.op; rw [if_pos reachable]; rfl)

def floatDepth (op : Instruction) : Usize := if op.arity = 2 then 2#usize else 1#usize

theorem lower_float_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : Instruction) (left right : U32) (reachable : compiler.reachable = true)
    (hleft : runtime.compiler.FunctionCompiler.operand ops compiler (floatDepth op) = .ok (.Ok left))
    (hright : runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok right)) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (floatOpcode op) 0#u32 0#u32 0#u128 =
      runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (floatInstruction op left left right) := by
  rw [lower_float_dispatch ops compiler state op reachable]
  unfold floatLowering
  rw [float_opcode_binary]
  by_cases binary : op.arity = 2
  · simp only [floatDepth, binary, ↓reduceIte] at hleft
    simp only [binary, ↓reduceIte, decide_true, bind_ok,
      hleft, hright, core.result.Result.Insts.CoreOpsTry.branch, float_instruction_make,
      core.option.Option.ok_or]
  · simp only [floatDepth, binary, ↓reduceIte] at hleft
    have same : left = right := by simpa only [Result.ok.injEq, core.result.Result.Ok.injEq] using hleft.symm.trans hright
    subst right
    simp only [binary, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok,
      hleft, core.result.Result.Insts.CoreOpsTry.branch, float_instruction_make,
      core.option.Option.ok_or]
end Itasca.Runtime.Compiler

end
