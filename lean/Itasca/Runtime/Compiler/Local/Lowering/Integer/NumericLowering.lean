import Itasca.Runtime.Compiler.Local.Lowering.Emission.OpEquations
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericOpcode
import Itasca.Spec.Checks
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty

/-!
Sections, each formerly its own module: NumericEncoding, LoweringArithmetic, NumericLowering.
-/

/-! ## NumericEncoding -/

section

/-!
All scalar integer numeric opcode bytes.

Main declarations: `integerOpcodes`. A direct consumer is `Compiler.Module.CompileSlice`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- All scalar integer numeric opcode bytes. -/
def integerOpcodes : List U8 :=
  [106#u8, 107#u8, 108#u8, 109#u8, 110#u8, 111#u8, 112#u8, 113#u8, 114#u8, 115#u8, 116#u8, 117#u8, 118#u8, 119#u8, 120#u8, 124#u8, 125#u8, 126#u8, 127#u8, 128#u8, 129#u8, 130#u8, 131#u8, 132#u8, 133#u8, 134#u8, 135#u8, 136#u8, 137#u8, 138#u8, 70#u8, 71#u8, 72#u8, 73#u8, 74#u8, 75#u8, 76#u8, 77#u8, 78#u8, 79#u8, 81#u8, 82#u8, 83#u8, 84#u8, 85#u8, 86#u8, 87#u8, 88#u8, 89#u8, 90#u8, 103#u8, 104#u8, 105#u8, 192#u8, 193#u8, 121#u8, 122#u8, 123#u8, 194#u8, 195#u8, 196#u8, 69#u8, 80#u8, 167#u8, 173#u8, 172#u8]

theorem integer_opcode_of_mem {opcode : U8} (member : opcode ∈ integerOpcodes) :
    ∃ op : SourceMachine.Numeric.Instruction, UScalar.cast .U8 (integerOpcode op) = opcode := by
  simp only [integerOpcodes, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.binary .I32 (.ADD), rfl⟩
  · exact ⟨.binary .I32 (.SUB), rfl⟩
  · exact ⟨.binary .I32 (.MUL), rfl⟩
  · exact ⟨.binary .I32 (.DIV .S), rfl⟩
  · exact ⟨.binary .I32 (.DIV .U), rfl⟩
  · exact ⟨.binary .I32 (.REM .S), rfl⟩
  · exact ⟨.binary .I32 (.REM .U), rfl⟩
  · exact ⟨.binary .I32 (.AND), rfl⟩
  · exact ⟨.binary .I32 (.OR), rfl⟩
  · exact ⟨.binary .I32 (.XOR), rfl⟩
  · exact ⟨.binary .I32 (.SHL), rfl⟩
  · exact ⟨.binary .I32 (.SHR .S), rfl⟩
  · exact ⟨.binary .I32 (.SHR .U), rfl⟩
  · exact ⟨.binary .I32 (.ROTL), rfl⟩
  · exact ⟨.binary .I32 (.ROTR), rfl⟩
  · exact ⟨.binary .I64 (.ADD), rfl⟩
  · exact ⟨.binary .I64 (.SUB), rfl⟩
  · exact ⟨.binary .I64 (.MUL), rfl⟩
  · exact ⟨.binary .I64 (.DIV .S), rfl⟩
  · exact ⟨.binary .I64 (.DIV .U), rfl⟩
  · exact ⟨.binary .I64 (.REM .S), rfl⟩
  · exact ⟨.binary .I64 (.REM .U), rfl⟩
  · exact ⟨.binary .I64 (.AND), rfl⟩
  · exact ⟨.binary .I64 (.OR), rfl⟩
  · exact ⟨.binary .I64 (.XOR), rfl⟩
  · exact ⟨.binary .I64 (.SHL), rfl⟩
  · exact ⟨.binary .I64 (.SHR .S), rfl⟩
  · exact ⟨.binary .I64 (.SHR .U), rfl⟩
  · exact ⟨.binary .I64 (.ROTL), rfl⟩
  · exact ⟨.binary .I64 (.ROTR), rfl⟩
  · exact ⟨.compare .I32 (.EQ), rfl⟩
  · exact ⟨.compare .I32 (.NE), rfl⟩
  · exact ⟨.compare .I32 (.LT .S), rfl⟩
  · exact ⟨.compare .I32 (.LT .U), rfl⟩
  · exact ⟨.compare .I32 (.GT .S), rfl⟩
  · exact ⟨.compare .I32 (.GT .U), rfl⟩
  · exact ⟨.compare .I32 (.LE .S), rfl⟩
  · exact ⟨.compare .I32 (.LE .U), rfl⟩
  · exact ⟨.compare .I32 (.GE .S), rfl⟩
  · exact ⟨.compare .I32 (.GE .U), rfl⟩
  · exact ⟨.compare .I64 (.EQ), rfl⟩
  · exact ⟨.compare .I64 (.NE), rfl⟩
  · exact ⟨.compare .I64 (.LT .S), rfl⟩
  · exact ⟨.compare .I64 (.LT .U), rfl⟩
  · exact ⟨.compare .I64 (.GT .S), rfl⟩
  · exact ⟨.compare .I64 (.GT .U), rfl⟩
  · exact ⟨.compare .I64 (.LE .S), rfl⟩
  · exact ⟨.compare .I64 (.LE .U), rfl⟩
  · exact ⟨.compare .I64 (.GE .S), rfl⟩
  · exact ⟨.compare .I64 (.GE .U), rfl⟩
  · exact ⟨.unary .I32 .clz, rfl⟩
  · exact ⟨.unary .I32 .ctz, rfl⟩
  · exact ⟨.unary .I32 .popcnt, rfl⟩
  · exact ⟨.unary .I32 .extend8, rfl⟩
  · exact ⟨.unary .I32 .extend16, rfl⟩
  · exact ⟨.unary .I64 .clz, rfl⟩
  · exact ⟨.unary .I64 .ctz, rfl⟩
  · exact ⟨.unary .I64 .popcnt, rfl⟩
  · exact ⟨.unary .I64 .extend8, rfl⟩
  · exact ⟨.unary .I64 .extend16, rfl⟩
  · exact ⟨.unary .I64 .extend32, rfl⟩
  · exact ⟨.eqz .I32, rfl⟩
  · exact ⟨.eqz .I64, rfl⟩
  · exact ⟨.conversion .wrap, rfl⟩
  · exact ⟨.conversion .extendUnsigned, rfl⟩
  · exact ⟨.conversion .extendSigned, rfl⟩

theorem integer_source_declared (op : SourceMachine.Numeric.Instruction) (refs : List funcidx) :
    DeclaredReferences.Instruction refs op.source := by
  cases op with
  | binary ty operator => cases ty <;> cases operator <;> simp [SourceMachine.Numeric.Instruction.source, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]
  | compare ty operator => cases ty <;> cases operator <;> simp [SourceMachine.Numeric.Instruction.source, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]
  | unary ty operator => cases ty <;> cases operator <;> simp [SourceMachine.Numeric.Instruction.source, SourceMachine.Numeric.UnaryOperator.operation, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]
  | eqz ty => cases ty <;> simp [SourceMachine.Numeric.Instruction.source, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]
  | conversion operator => cases operator <;> simp [SourceMachine.Numeric.Instruction.source, SourceMachine.Numeric.Conversion.source, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

end Itasca.Runtime.Compiler

end

/-! ## LoweringArithmetic -/

section

/-! Actual integer-add callbacks preserve the source-prefix lowering relation.
Operand addresses come from the compiler's live layout; the proof then follows
the extracted opcode classifier, constructor, emitter, and post-stack observer. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

theorem binary_operands {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (front : List valtype) (ty : Inn)
    (layout : CompilerLayout compiler (front ++ [integerType ty, integerType ty])) :
    ∃ left right : U32,
      runtime.compiler.FunctionCompiler.operand ops compiler 2#usize = .ok (.Ok left) ∧
      runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok right) ∧
      left.val = slots (compilerLocals compiler) + slots front ∧ right.val = left.val + 1 := by
  obtain ⟨r, hr, left, rfl, hl⟩ := WP.spec_imp_exists
    (compiler_operand ops compiler _ layout 2#usize (by decide) (by simp))
  obtain ⟨r, hr', right, rfl, hh⟩ := WP.spec_imp_exists
    (compiler_operand ops compiler _ layout 1#usize (by decide) (by simp))
  have leftPos : left.val = slots (compilerLocals compiler) + slots front := by
    simpa [offset, List.take_append] using hl
  have rightPos : right.val = left.val + 1 := by
    have take : front.take (front.length + 1) = front := List.take_of_length_le (by omega)
    rw [leftPos]
    cases ty <;> simpa [offset, List.take_append, slots_append, slots, width, integerType, take,
      Nat.add_assoc] using hh
  exact ⟨left, right, hr, hr', leftPos, rightPos⟩

end Itasca.Runtime.Compiler

end

/-! ## NumericLowering -/

section

/-!
The shared scalar lowering path, before resolving its source operands.

Main declarations: `numericLowering` and `integerDepth`. A direct consumer is `Compiler.Local.Lowering.Integer.NumericEffects`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std SourceMachine.Numeric

/-- The shared scalar lowering path, before resolving its source operands. -/
noncomputable def numericLowering {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : Instruction) : Result (core.result.Result Unit Itasca.error.VisitError × runtime.compiler.FunctionCompiler A) := do
    let binary ← runtime.compiler.lower.scalar_binary (integerOpcode op)
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
        let o ← runtime.bytecode.Instr.make_scalar (integerOpcode op) val val val1
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

set_option maxRecDepth 4096 in
theorem lower_numeric_dispatch {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : Instruction) (reachable : compiler.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (integerOpcode op) 0#u32 0#u32 0#u128 =
      numericLowering ops compiler state op := by
  have allowed : (69 ≤ (integerOpcode op).val ∧ (integerOpcode op).val ≤ 196) ∨
      (256 ≤ (integerOpcode op).val ∧ (integerOpcode op).val ≤ 263) := by
    cases op with
    | binary ty operator =>
      cases operator with
      | DIV sign | REM sign | SHR sign => cases sign <;> cases ty <;> decide
      | ADD | SUB | MUL | AND | OR | XOR | SHL | ROTL | ROTR => cases ty <;> decide
    | compare ty operator =>
      cases operator with
      | LT sign | GT sign | LE sign | GE sign => cases sign <;> cases ty <;> decide
      | EQ | NE => cases ty <;> decide
    | unary ty operator => cases ty <;> cases operator <;> decide
    | eqz ty => cases ty <;> decide
    | conversion operator => cases operator <;> decide
  exact runtime.compiler.lower.FunctionCompiler.op.scalar ops compiler state (integerOpcode op)
    0#u32 0#u32 0#u128 reachable allowed

def integerDepth (op : Instruction) : Usize := if op.arity = 2 then 2#usize else 1#usize

theorem lower_numeric_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : Instruction) (left right : U32) (reachable : compiler.reachable = true)
    (hleft : runtime.compiler.FunctionCompiler.operand ops compiler (integerDepth op) = .ok (.Ok left))
    (hright : runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok right)) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (integerOpcode op) 0#u32 0#u32 0#u128 =
      runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (integerInstruction op left left right) := by
  rw [lower_numeric_dispatch ops compiler state op reachable]
  unfold numericLowering
  rw [integer_opcode_binary]
  by_cases binary : op.arity = 2
  · simp only [integerDepth, binary, ↓reduceIte] at hleft
    simp only [binary, ↓reduceIte, decide_true, bind_ok,
      hleft, hright, core.result.Result.Insts.CoreOpsTry.branch, integer_instruction_make,
      core.option.Option.ok_or]
  · simp only [integerDepth, binary, ↓reduceIte] at hleft
    have same : left = right := by simpa only [Result.ok.injEq, core.result.Result.Ok.injEq] using hleft.symm.trans hright
    subst right
    simp only [binary, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok,
      hleft, core.result.Result.Insts.CoreOpsTry.branch, integer_instruction_make,
      core.option.Option.ok_or]
end Itasca.Runtime.Compiler

end
