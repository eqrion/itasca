import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericSafety
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatLowering
import Itasca.Runtime.SourceMachine.Float.Results
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Representation.Values

/-!
Sections, each formerly its own module: FloatSafety, FloatEmissionInversion, FloatValueEncoding.
-/

/-! ## FloatSafety -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem compiler_float_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : SourceMachine.Float.Instruction)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state
      (floatOpcode op) 0#u32 0#u32 0#u128 ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases live : compiler.reachable = true
  · rw [lower_float_dispatch ops compiler state op live]
    unfold floatLowering
    rw [float_opcode_binary]
    simp only [bind_ok]
    have depthEq : (if decide (op.arity = 2) = true then Result.ok 2#usize else Result.ok 1#usize) =
        Result.ok (floatDepth op) := by simp [floatDepth]; split <;> rfl
    rw [depthEq, bind_ok]
    step with compiler_operand_total ops compiler _ as ⟨leftResult, _⟩
    cases leftResult with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok left =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with compiler_operand_total ops compiler 1#usize as ⟨rightResult, _⟩
      cases rightResult with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok right =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          float_instruction_make, core.option.Option.ok_or]
        exact finish_op_observed ops law compiler state _ codeFits sourceFits coordinateFits
  · have dead : runtime.compiler.lower.FunctionCompiler.op ops compiler state
        (floatOpcode op) 0#u32 0#u32 0#u128 =
        runtime.compiler.FunctionCompiler.observe ops compiler state := by
      rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)]
    rw [dead]
    exact compiler_observe_stack ops law compiler state

end Itasca.Runtime.Compiler

end

/-! ## FloatEmissionInversion -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

theorem LinearEmission.float_decode_none {locals before instruction emitted after}
    (emission : LinearEmission locals before instruction emitted after) :
    SourceMachine.Float.decodeInstruction instruction = none := by
  cases emission with
  | binary stack ty op => cases ty <;> cases op <;> rfl
  | numeric stack op =>
    cases op with
    | binary ty operator => cases ty <;> rfl
    | compare ty operator => cases ty <;> rfl
    | unary ty operator => cases ty <;> cases operator <;> rfl
    | eqz ty => cases ty <;> rfl
    | conversion operator => cases operator <;> rfl
  | _ => rfl

theorem ScalarEmission.float_inv {C before emitted after}
    (op : SourceMachine.Float.Instruction)
    (emission : ScalarEmission C before op.source emitted after) :
    ∃ stack left right,
      before = stack ++ List.replicate op.arity (valtype_numtype op.input) ∧
      after = stack ++ [valtype_numtype op.output] ∧
      emitted = [floatInstruction op left left right] ∧
      left.val = slots C.LOCALS + slots stack ∧
      right.val = left.val + (op.arity - 1) := by
  generalize sourceEq : op.source = instruction at emission
  cases emission with
  | linear h =>
    have impossible := h.float_decode_none
    rw [← sourceEq, SourceMachine.Float.decode_instruction_source] at impossible
    contradiction
  | float stack selected left right leftSlot rightSlot =>
    have same : op = selected := SourceMachine.Float.Instruction.source_injective sourceEq
    subst selected
    exact ⟨stack,left,right,rfl,rfl,rfl,leftSlot,rightSlot⟩
  | _ =>
    have decoded := congrArg SourceMachine.Float.decodeInstruction sourceEq
    rw [SourceMachine.Float.decode_instruction_source] at decoded
    simp [SourceMachine.Float.decodeInstruction,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at decoded
end Itasca.Runtime.Compiler

end

/-! ## FloatValueEncoding -/

section

namespace Itasca.Runtime.Compiler
open SpecExt.Builtins SpecExt.Builtins.Float

theorem encode_float_number (ty : numtype) (bits : Nat) (bound : bits < 2^sizenn ty) :
    encodeValue (.CONST ty (SourceMachine.Float.numberOfBits ty bits)) = [bits] := by
  cases ty
  · rfl
  · rfl
  · change [floatBits 32 (floatOfBits 32 bits)] = [bits]
    rw [float_bits_roundtrip_32 bits bound]
  · change [floatBits 64 (floatOfBits 64 bits)] = [bits]
    rw [float_bits_roundtrip_64 bits bound]

theorem encode_float_operands (op : SourceMachine.Float.Instruction) (a b : Nat)
    (first : a < 2^sizenn op.input) (second : b < 2^sizenn op.input) :
    encodeValues (op.operands a b) = if op.arity = 1 then [a] else [a,b] := by
  unfold SourceMachine.Float.Instruction.operands
  split
  all_goals simp only [encodeValues, List.flatMap_cons, List.flatMap_nil,
    encode_float_number _ _ first, encode_float_number _ _ second, List.append_nil, List.singleton_append]
end Itasca.Runtime.Compiler

end
