import Itasca.Runtime.Interp.Numeric.Float.FloatDispatch
import Itasca.Runtime.Interp.Relations.Fetch
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatOpcode
import Itasca.Runtime.Interp.Numeric.Integer.NumericWords
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatValueEncoding
import Itasca.Runtime.Interp.Relations.PrefixEffect

/-!
Floating-point instruction execution from source values through word operands and fetch. Word effects, decoded value effects and dispatch equations establish the concrete step result.
-/

/-! ## Float Bytecode Dispatch -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std Platform
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

set_option maxHeartbeats 2000000 in
theorem dispatch_float_eq (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (index inst function base : Usize)
    (op : Abs.Float.Instruction) (dst left right : U32) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (Code.floatInstruction op dst left right) = (do
        let (r, next) ← runtime.interp.execute_scalar floats exec base
          (floatOpcode op) dst left right
        Result.ok (r, next, store, platform)) := by
  cases op with
  | unary ty operation => cases ty <;> cases operation <;> simp [Code.floatInstruction, floatOpcode, Abs.Float.Instruction.opcode,
    Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex, Abs.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | binary ty operation => cases ty <;> cases operation <;> simp [Code.floatInstruction, floatOpcode, Abs.Float.Instruction.opcode,
    Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex, Abs.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | compare ty operation => cases ty <;> cases operation <;> simp [Code.floatInstruction, floatOpcode, Abs.Float.Instruction.opcode,
    Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex, Abs.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | convert source target sign => cases source <;> cases target <;> cases sign <;> simp [Code.floatInstruction, floatOpcode, Abs.Float.Instruction.opcode,
    Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex, Abs.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | truncate source target sign sat => cases source <;> cases target <;> cases sign <;> cases sat <;> simp [Code.floatInstruction, floatOpcode, Abs.Float.Instruction.opcode,
    Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex, Abs.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | reinterpretFloat source => cases source <;> simp [Code.floatInstruction, floatOpcode, Abs.Float.Instruction.opcode,
    Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex, Abs.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | reinterpretInt source => cases source <;> simp [Code.floatInstruction, floatOpcode, Abs.Float.Instruction.opcode,
    Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex, Abs.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | promote | demote => skip <;> simp [Code.floatInstruction, floatOpcode, Abs.Float.Instruction.opcode,
    Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex, Abs.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]

end Itasca.Runtime.Interp

end

/-! ## Float Words -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std Platform

theorem floatInput_of_val (ty : numtype) (raw : U64) (bits : Nat)
    (same : raw.val = bits) (bound : bits < 2^sizenn ty) : floatInput ty raw = bits := by
  cases ty <;> simp only [floatInput]
  all_goals first
    | exact same
    | simp only [UScalar.cast_val_eq, UScalarTy.numBits, same]
      exact Nat.mod_eq_of_lt bound

theorem floatResult_unary (op : Abs.Float.Instruction) (a b : Nat) (result : Option Nat)
    (one : op.arity = 1) : op.Result a a result = op.Result a b result := by
  cases result <;> simp only [Abs.Float.Instruction.Result, Abs.Float.Instruction.operands, one, if_true]

def FloatWordsEffect (op : Abs.Float.Instruction) (a b : Nat)
    (exec : runtime.interp.Execution) (base : Nat) (front : List Nat)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution) : Prop :=
  (∃ bits, op.Result a b (some bits) ∧ out.1 = .Ok () ∧
    WordsAt out.2.slots.val base (front ++ [bits]) ∧ { out.2 with slots := exec.slots } = exec) ∨
  (op.Result a b none ∧ ∃ trap, (trap = .IntegerOverflow ∨ trap = .InvalidConversionToInteger) ∧
    out = (.Err (.Trap trap), exec))

theorem float_binary_words {F : Type} (floats : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (base : Usize) (op : Abs.Float.Instruction)
    (left right : U32) (front : List Nat) (a b : Nat)
    (first : a < 2^sizenn op.input) (second : b < 2^sizenn op.input)
    (words : WordsAt exec.slots.val base.val (front ++ [a, b]))
    (hl : left.val = front.length) (hr : right.val = front.length + 1) :
    runtime.interp.execute_scalar floats exec base (floatOpcode op) left left right ⦃
      FloatWordsEffect op a b exec base.val front ⦄ := by
  have operand := words.append_right
  have ha : base.val + left.val < exec.slots.length := by simpa [hl] using (operand 0 (by simp)).1
  have hb : base.val + right.val < exec.slots.length := by simpa [hr, Nat.add_assoc] using (operand 1 (by simp)).1
  have va : floatInput op.input exec.slots.val[base.val + left.val]! = a := by
    apply floatInput_of_val _ _ _ ?_ first
    simpa [hl] using (operand 0 (by simp)).2
  have vb : floatInput op.input exec.slots.val[base.val + right.val]! = b := by
    apply floatInput_of_val _ _ _ ?_ second
    simpa [hr, Nat.add_assoc] using (operand 1 (by simp)).2
  apply WP.spec_mono (execute_float_effect floats correct exec base op left left right ha hb ha)
  rintro out ⟨numeric, exactResult, effect⟩
  cases numeric with
  | Ok value =>
    change op.Result _ _ (some value.val) at exactResult
    rw [va, vb] at exactResult
    obtain ⟨success, slots, unchanged⟩ := effect
    left
    refine ⟨value.val, exactResult, success, ?_, unchanged⟩
    rw [slots, hl]
    exact words.binary_result value
  | Err error =>
    cases error <;> simp only [FloatScalarOutcome] at exactResult
    case Trap trap =>
      rw [va, vb] at exactResult
      exact Or.inr ⟨exactResult.1, trap, exactResult.2, effect⟩

theorem float_unary_words {F : Type} (floats : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (base : Usize) (op : Abs.Float.Instruction)
    (left : U32) (front : List Nat) (a b : Nat)
    (one : op.arity = 1) (first : a < 2^sizenn op.input)
    (words : WordsAt exec.slots.val base.val (front ++ [a]))
    (hl : left.val = front.length) :
    runtime.interp.execute_scalar floats exec base (floatOpcode op) left left left ⦃
      FloatWordsEffect op a b exec base.val front ⦄ := by
  have operand := words.append_right
  have ha : base.val + left.val < exec.slots.length := by simpa [hl] using (operand 0 (by simp)).1
  have va : floatInput op.input exec.slots.val[base.val + left.val]! = a := by
    apply floatInput_of_val _ _ _ ?_ first
    simpa [hl] using (operand 0 (by simp)).2
  apply WP.spec_mono (execute_float_effect floats correct exec base op left left left ha ha ha)
  rintro out ⟨numeric, exactResult, effect⟩
  cases numeric with
  | Ok value =>
    change op.Result _ _ (some value.val) at exactResult
    rw [va, floatResult_unary op a b _ one] at exactResult
    obtain ⟨success, slots, unchanged⟩ := effect
    left
    refine ⟨value.val, exactResult, success, ?_, unchanged⟩
    rw [slots, hl]
    exact words.unary_result value
  | Err error =>
    cases error <;> simp only [FloatScalarOutcome] at exactResult
    case Trap trap =>
      rw [va, floatResult_unary op a b _ one] at exactResult
      exact Or.inr ⟨exactResult.1, trap, exactResult.2, effect⟩
end Itasca.Runtime.Interp

end

/-! ## Float Values -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std Platform

def FloatValuesEffect (op : Abs.Float.Instruction) (a b : Nat)
    (exec : runtime.interp.Execution) (base : Nat) (front : List val)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution) : Prop :=
  (∃ bits, op.Result a b (some bits) ∧ out.1 = .Ok () ∧
    ValuesAt out.2.slots.val base (front ++ [.CONST op.output (Abs.Float.numberOfBits op.output bits)]) ∧
    { out.2 with slots := exec.slots } = exec) ∨
  (op.Result a b none ∧ ∃ trap, (trap = .IntegerOverflow ∨ trap = .InvalidConversionToInteger) ∧
    out = (.Err (.Trap trap), exec))

theorem float_values {F : Type} (floats : runtime.platform.FloatOps F) (correct : FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (base : Usize) (op : Abs.Float.Instruction)
    (left right : U32) (front : List val) (a b : Nat)
    (first : a < 2^sizenn op.input) (second : b < 2^sizenn op.input)
    (values : ValuesAt exec.slots.val base.val (front ++ op.operands a b))
    (hl : left.val = Code.slots (front.map Code.valueType))
    (hr : right.val = left.val + (op.arity - 1)) :
    runtime.interp.execute_scalar floats exec base (floatOpcode op) left left right ⦃
      FloatValuesEffect op a b exec base.val front ⦄ := by
  have position : left.val = (Code.encodeValues front).length := by
    simpa only [Code.encodeValues_length] using hl
  have post : ∀ out, FloatWordsEffect op a b exec base.val (Code.encodeValues front) out →
      FloatValuesEffect op a b exec base.val front out := by
    intro out effect
    rcases effect with ⟨bits, semantic, success, words, unchanged⟩ | trap
    · left
      refine ⟨bits, semantic, success, ?_, unchanged⟩
      change WordsAt out.2.slots.val base.val (Code.encodeValues (front ++ [.CONST op.output (Abs.Float.numberOfBits op.output bits)]))
      rw [Code.encodeValues_append]
      simpa only [Code.encodeValues, List.flatMap_cons, List.flatMap_nil,
        Code.encode_float_number _ _ semantic.1, List.append_nil] using words
    · exact Or.inr trap
  rcases op.arity_valid with one | two
  · have same : right = left := UScalar.eq_of_val_eq (by simpa [one] using hr)
    subst right
    have words : WordsAt exec.slots.val base.val (Code.encodeValues front ++ [a]) := by
      simpa only [ValuesAt, Code.encodeValues_append, Code.encode_float_operands op a b first second,
        one, if_true] using values
    exact WP.spec_mono (float_unary_words floats correct exec base op left (Code.encodeValues front) a b one first words position) post
  · have words : WordsAt exec.slots.val base.val (Code.encodeValues front ++ [a,b]) := by
      simpa only [ValuesAt, Code.encodeValues_append, Code.encode_float_operands op a b first second,
        two, Nat.reduceEqDiff, if_false] using values
    have secondPosition : right.val = (Code.encodeValues front).length + 1 := by simpa [two, position] using hr
    exact WP.spec_mono (float_binary_words floats correct exec base op left right (Code.encodeValues front) a b first second words position secondPosition) post
end Itasca.Runtime.Interp

end

/-! ## Float Fetch -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std Abs.Float

theorem step_float_values {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (op : Instruction) (left right : U32) (front : List val)
    (a b : Nat)
    (first : a < 2^sizenn op.input) (second : b < 2^sizenn op.input)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetched : compiled.code.val[raw.pc.val]? = some (Code.floatInstruction op left left right))
    (pcBound : raw.pc.val < U32.max)
    (values : ValuesAt exec.slots.val raw.base.val (front ++ op.operands a b))
    (hl : left.val = Code.slots (front.map Code.valueType))
    (hr : right.val = left.val + (op.arity - 1)) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ pc : U32, pc.val = raw.pc.val + 1 ∧
        FloatValuesEffect op a b
          { exec with frames := exec.frames.set index { raw with pc := pc } }
          raw.base.val front (out.1, out.2.1) ∧
        SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
    (Code.floatInstruction op left left right) last hf hi hc fetched pcBound
  intro pc position
  rw [dispatch_float_eq]
  obtain ⟨out, equation, effect⟩ := WP.spec_imp_exists (float_values floats correct
    { exec with frames := exec.frames.set index { raw with pc := pc } } raw.base op left right front a b first second values hl hr)
  have prefixEffect := execute_scalar_prefix floats
    { exec with frames := exec.frames.set index { raw with pc := pc } } raw.base
    (floatOpcode op) left left right out equation
  rw [equation]
  rcases out with ⟨status, changed⟩
  simp only [bind_ok]
  with_unfolding_all apply WP.spec.ret
  exact ⟨rfl, rfl, pc, position, effect, prefixEffect⟩
end Itasca.Runtime.Interp

end
