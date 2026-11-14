import Itasca.Runtime.Interp.Numeric.Float.FloatInstructionComparison
import Itasca.Runtime.Interp.Numeric.Float.FloatTruncInstruction
import Itasca.Runtime.Interp.Relations.Defaults
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatLowering
import Itasca.Runtime.Interp.Numeric.Integer.NumericFetch
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatValueEncoding
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.SourceMachine.Float.Transition
import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership

/-!
Sections, each formerly its own module: FloatDispatch, FloatFetch, FloatOwnership.
-/

/-! ## FloatDispatch -/

section

/-!
Floating-point opcode dispatch and its complete instruction effect. The dispatcher selects the separately proved arithmetic, comparison and conversion instruction cases.
-/

/-! ## Float Instruction -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std Platform

/-- Every scalar float opcode returns a bounded permitted source result or its exact numeric trap. -/
theorem scalar_float_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (op : SourceMachine.Float.Instruction) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode op) a b ⦃ result =>
      FloatScalarOutcome op a b result ⦄ := by
  cases op with
  | unary ty operation =>
    cases ty <;> cases operation
    all_goals first
      | exact scalar_f32_abs_instruction ops a b
      | exact scalar_f32_neg_instruction ops a b
      | exact scalar_f32_ceil_instruction ops correct a b
      | exact scalar_f32_floor_instruction ops correct a b
      | exact scalar_f32_trunc_instruction ops correct a b
      | exact scalar_f32_nearest_instruction ops correct a b
      | exact scalar_f32_sqrt_instruction ops correct a b
      | exact scalar_f64_abs_instruction ops a b
      | exact scalar_f64_neg_instruction ops a b
      | exact scalar_f64_ceil_instruction ops correct a b
      | exact scalar_f64_floor_instruction ops correct a b
      | exact scalar_f64_trunc_instruction ops correct a b
      | exact scalar_f64_nearest_instruction ops correct a b
      | exact scalar_f64_sqrt_instruction ops correct a b
  | binary ty operation =>
    cases ty <;> cases operation
    all_goals first
      | exact scalar_f32_add_instruction ops correct a b
      | exact scalar_f32_sub_instruction ops correct a b
      | exact scalar_f32_mul_instruction ops correct a b
      | exact scalar_f32_div_instruction ops correct a b
      | exact scalar_f32_min_instruction ops a b
      | exact scalar_f32_max_instruction ops a b
      | exact scalar_f32_copysign_instruction ops a b
      | exact scalar_f64_add_instruction ops correct a b
      | exact scalar_f64_sub_instruction ops correct a b
      | exact scalar_f64_mul_instruction ops correct a b
      | exact scalar_f64_div_instruction ops correct a b
      | exact scalar_f64_min_instruction ops a b
      | exact scalar_f64_max_instruction ops a b
      | exact scalar_f64_copysign_instruction ops a b
  | compare ty operation =>
    cases ty <;> cases operation
    all_goals first
      | exact scalar_f32_eq_instruction ops a b
      | exact scalar_f32_ne_instruction ops a b
      | exact scalar_f32_lt_instruction ops a b
      | exact scalar_f32_gt_instruction ops a b
      | exact scalar_f32_le_instruction ops a b
      | exact scalar_f32_ge_instruction ops a b
      | exact scalar_f64_eq_instruction ops a b
      | exact scalar_f64_ne_instruction ops a b
      | exact scalar_f64_lt_instruction ops a b
      | exact scalar_f64_gt_instruction ops a b
      | exact scalar_f64_le_instruction ops a b
      | exact scalar_f64_ge_instruction ops a b
  | convert source target sign =>
    cases source <;> cases target <;> cases sign
    all_goals first
      | exact scalar_f32_convert_i32_s_instruction ops correct a b
      | exact scalar_f32_convert_i32_u_instruction ops correct a b
      | exact scalar_f32_convert_i64_s_instruction ops correct a b
      | exact scalar_f32_convert_i64_u_instruction ops correct a b
      | exact scalar_f64_convert_i32_s_instruction ops correct a b
      | exact scalar_f64_convert_i32_u_instruction ops correct a b
      | exact scalar_f64_convert_i64_s_instruction ops correct a b
      | exact scalar_f64_convert_i64_u_instruction ops correct a b
  | truncate source target sign sat =>
    cases source <;> cases target <;> cases sign <;> cases sat
    all_goals first
      | exact scalar_i32_trunc_f32_s_instruction ops a b
      | exact scalar_i32_trunc_f32_u_instruction ops a b
      | exact scalar_i32_trunc_f64_s_instruction ops a b
      | exact scalar_i32_trunc_f64_u_instruction ops a b
      | exact scalar_i64_trunc_f32_s_instruction ops a b
      | exact scalar_i64_trunc_f32_u_instruction ops a b
      | exact scalar_i64_trunc_f64_s_instruction ops a b
      | exact scalar_i64_trunc_f64_u_instruction ops a b
      | exact scalar_i32_trunc_sat_f32_s_instruction ops a b
      | exact scalar_i32_trunc_sat_f32_u_instruction ops a b
      | exact scalar_i32_trunc_sat_f64_s_instruction ops a b
      | exact scalar_i32_trunc_sat_f64_u_instruction ops a b
      | exact scalar_i64_trunc_sat_f32_s_instruction ops a b
      | exact scalar_i64_trunc_sat_f32_u_instruction ops a b
      | exact scalar_i64_trunc_sat_f64_s_instruction ops a b
      | exact scalar_i64_trunc_sat_f64_u_instruction ops a b
  | reinterpretFloat source =>
    cases source
    all_goals first
      | exact scalar_i64_reinterpret_f64_instruction ops a b
      | exact scalar_i32_reinterpret_f32_instruction ops a b
  | reinterpretInt source =>
    cases source
    all_goals first
      | exact scalar_f64_reinterpret_i64_instruction ops a b
      | exact scalar_f32_reinterpret_i32_instruction ops a b
  | promote => exact scalar_f64_promote_f32_instruction ops a b
  | demote => exact scalar_f32_demote_f64_instruction ops correct a b

end Itasca.Runtime.Interp

end

/-! ## Float Dispatch -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std Platform

theorem scalar_float_dispatch {F : Type} (ops : runtime.platform.FloatOps F)
    (op : SourceMachine.Float.Instruction) (a b : U64) :
    runtime.interp.int.scalar ops (floatOpcode op) a b =
      runtime.interp.float.scalar ops (floatOpcode op) a b := by
  unfold runtime.interp.int.scalar
  rw [show lift (UScalar.cast .U32 a) = Result.ok (UScalar.cast .U32 a) from rfl, bind_ok]
  rw [show lift (UScalar.cast .U32 b) = Result.ok (UScalar.cast .U32 b) from rfl, bind_ok]
  cases op with
  | unary ty operation => cases ty <;> cases operation <;> with_unfolding_all rfl
  | binary ty operation => cases ty <;> cases operation <;> with_unfolding_all rfl
  | compare ty operation => cases ty <;> cases operation <;> with_unfolding_all rfl
  | convert source target sign => cases source <;> cases target <;> cases sign <;> with_unfolding_all rfl
  | truncate source target sign sat => cases source <;> cases target <;> cases sign <;> cases sat <;> with_unfolding_all rfl
  | reinterpretFloat source => cases source <;> with_unfolding_all rfl
  | reinterpretInt source => cases source <;> with_unfolding_all rfl
  | promote | demote => with_unfolding_all rfl

theorem execute_float_effect {F : Type} (floats : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (base : Usize) (op : SourceMachine.Float.Instruction) (dst left right : U32)
    (hl : base.val + left.val < exec.slots.length)
    (hr : base.val + right.val < exec.slots.length)
    (hd : base.val + dst.val < exec.slots.length) :
    runtime.interp.execute_scalar floats exec base (floatOpcode op) dst left right ⦃ out =>
      ∃ numeric, FloatScalarOutcome op exec.slots.val[base.val + left.val]! exec.slots.val[base.val + right.val]! numeric ∧
        ScalarEffect exec (base.val + dst.val) numeric out ⦄ := by
  obtain ⟨numeric, equation, exactResult⟩ := WP.spec_imp_exists
    (scalar_float_instruction floats correct op exec.slots.val[base.val + left.val]! exec.slots.val[base.val + right.val]!)
  rw [← scalar_float_dispatch] at equation
  apply WP.spec_mono (execute_scalar_effect floats exec base (floatOpcode op) dst left right hl hr hd numeric equation)
  exact fun _ effect => ⟨numeric, exactResult, effect⟩
end Itasca.Runtime.Interp

end

end

/-! ## FloatFetch -/

section

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
    (op : SourceMachine.Float.Instruction) (dst left right : U32) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (Compiler.floatInstruction op dst left right) = (do
        let (r, next) ← runtime.interp.execute_scalar floats exec base
          (floatOpcode op) dst left right
        Result.ok (r, next, store, platform)) := by
  cases op with
  | unary ty operation => cases ty <;> cases operation <;> simp [Compiler.floatInstruction, floatOpcode, SourceMachine.Float.Instruction.opcode,
    SourceMachine.Float.unaryIndex, SourceMachine.Float.binaryIndex, SourceMachine.Float.compareIndex, SourceMachine.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | binary ty operation => cases ty <;> cases operation <;> simp [Compiler.floatInstruction, floatOpcode, SourceMachine.Float.Instruction.opcode,
    SourceMachine.Float.unaryIndex, SourceMachine.Float.binaryIndex, SourceMachine.Float.compareIndex, SourceMachine.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | compare ty operation => cases ty <;> cases operation <;> simp [Compiler.floatInstruction, floatOpcode, SourceMachine.Float.Instruction.opcode,
    SourceMachine.Float.unaryIndex, SourceMachine.Float.binaryIndex, SourceMachine.Float.compareIndex, SourceMachine.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | convert source target sign => cases source <;> cases target <;> cases sign <;> simp [Compiler.floatInstruction, floatOpcode, SourceMachine.Float.Instruction.opcode,
    SourceMachine.Float.unaryIndex, SourceMachine.Float.binaryIndex, SourceMachine.Float.compareIndex, SourceMachine.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | truncate source target sign sat => cases source <;> cases target <;> cases sign <;> cases sat <;> simp [Compiler.floatInstruction, floatOpcode, SourceMachine.Float.Instruction.opcode,
    SourceMachine.Float.unaryIndex, SourceMachine.Float.binaryIndex, SourceMachine.Float.compareIndex, SourceMachine.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | reinterpretFloat source => cases source <;> simp [Compiler.floatInstruction, floatOpcode, SourceMachine.Float.Instruction.opcode,
    SourceMachine.Float.unaryIndex, SourceMachine.Float.binaryIndex, SourceMachine.Float.compareIndex, SourceMachine.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | reinterpretInt source => cases source <;> simp [Compiler.floatInstruction, floatOpcode, SourceMachine.Float.Instruction.opcode,
    SourceMachine.Float.unaryIndex, SourceMachine.Float.binaryIndex, SourceMachine.Float.compareIndex, SourceMachine.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | promote | demote => skip <;> simp [Compiler.floatInstruction, floatOpcode, SourceMachine.Float.Instruction.opcode,
    SourceMachine.Float.unaryIndex, SourceMachine.Float.binaryIndex, SourceMachine.Float.compareIndex, SourceMachine.Float.signIndex,
    runtime.interp.dispatch, runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]

end Itasca.Runtime.Interp

end

/-! ## Float Words -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std Platform

theorem float_input_of_val (ty : numtype) (raw : U64) (bits : Nat)
    (same : raw.val = bits) (bound : bits < 2^sizenn ty) : floatInput ty raw = bits := by
  cases ty <;> simp only [floatInput]
  all_goals first
    | exact same
    | simp only [UScalar.cast_val_eq, UScalarTy.numBits, same]
      exact Nat.mod_eq_of_lt bound

theorem float_result_unary (op : SourceMachine.Float.Instruction) (a b : Nat) (result : Option Nat)
    (one : op.arity = 1) : op.Result a a result = op.Result a b result := by
  cases result <;> simp only [SourceMachine.Float.Instruction.Result, SourceMachine.Float.Instruction.operands, one, if_true]

def FloatWordsEffect (op : SourceMachine.Float.Instruction) (a b : Nat)
    (exec : runtime.interp.Execution) (base : Nat) (front : List Nat)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution) : Prop :=
  (∃ bits, op.Result a b (some bits) ∧ out.1 = .Ok () ∧
    WordsAt out.2.slots.val base (front ++ [bits]) ∧ { out.2 with slots := exec.slots } = exec) ∨
  (op.Result a b none ∧ ∃ trap, (trap = .IntegerOverflow ∨ trap = .InvalidConversionToInteger) ∧
    out = (.Err (.Trap trap), exec))

theorem float_binary_words {F : Type} (floats : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (base : Usize) (op : SourceMachine.Float.Instruction)
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
    apply float_input_of_val _ _ _ ?_ first
    simpa [hl] using (operand 0 (by simp)).2
  have vb : floatInput op.input exec.slots.val[base.val + right.val]! = b := by
    apply float_input_of_val _ _ _ ?_ second
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
    (exec : runtime.interp.Execution) (base : Usize) (op : SourceMachine.Float.Instruction)
    (left : U32) (front : List Nat) (a b : Nat)
    (one : op.arity = 1) (first : a < 2^sizenn op.input)
    (words : WordsAt exec.slots.val base.val (front ++ [a]))
    (hl : left.val = front.length) :
    runtime.interp.execute_scalar floats exec base (floatOpcode op) left left left ⦃
      FloatWordsEffect op a b exec base.val front ⦄ := by
  have operand := words.append_right
  have ha : base.val + left.val < exec.slots.length := by simpa [hl] using (operand 0 (by simp)).1
  have va : floatInput op.input exec.slots.val[base.val + left.val]! = a := by
    apply float_input_of_val _ _ _ ?_ first
    simpa [hl] using (operand 0 (by simp)).2
  apply WP.spec_mono (execute_float_effect floats correct exec base op left left left ha ha ha)
  rintro out ⟨numeric, exactResult, effect⟩
  cases numeric with
  | Ok value =>
    change op.Result _ _ (some value.val) at exactResult
    rw [va, float_result_unary op a b _ one] at exactResult
    obtain ⟨success, slots, unchanged⟩ := effect
    left
    refine ⟨value.val, exactResult, success, ?_, unchanged⟩
    rw [slots, hl]
    exact words.unary_result value
  | Err error =>
    cases error <;> simp only [FloatScalarOutcome] at exactResult
    case Trap trap =>
      rw [va, float_result_unary op a b _ one] at exactResult
      exact Or.inr ⟨exactResult.1, trap, exactResult.2, effect⟩
end Itasca.Runtime.Interp

end

/-! ## Float Values -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std Platform

def FloatValuesEffect (op : SourceMachine.Float.Instruction) (a b : Nat)
    (exec : runtime.interp.Execution) (base : Nat) (front : List val)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution) : Prop :=
  (∃ bits, op.Result a b (some bits) ∧ out.1 = .Ok () ∧
    ValuesAt out.2.slots.val base (front ++ [.CONST op.output (SourceMachine.Float.numberOfBits op.output bits)]) ∧
    { out.2 with slots := exec.slots } = exec) ∨
  (op.Result a b none ∧ ∃ trap, (trap = .IntegerOverflow ∨ trap = .InvalidConversionToInteger) ∧
    out = (.Err (.Trap trap), exec))

theorem float_values {F : Type} (floats : runtime.platform.FloatOps F) (correct : FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (base : Usize) (op : SourceMachine.Float.Instruction)
    (left right : U32) (front : List val) (a b : Nat)
    (first : a < 2^sizenn op.input) (second : b < 2^sizenn op.input)
    (values : ValuesAt exec.slots.val base.val (front ++ op.operands a b))
    (hl : left.val = Compiler.slots (front.map Compiler.valueType))
    (hr : right.val = left.val + (op.arity - 1)) :
    runtime.interp.execute_scalar floats exec base (floatOpcode op) left left right ⦃
      FloatValuesEffect op a b exec base.val front ⦄ := by
  have position : left.val = (Compiler.encodeValues front).length := by
    simpa only [Compiler.encode_values_length] using hl
  have post : ∀ out, FloatWordsEffect op a b exec base.val (Compiler.encodeValues front) out →
      FloatValuesEffect op a b exec base.val front out := by
    intro out effect
    rcases effect with ⟨bits, semantic, success, words, unchanged⟩ | trap
    · left
      refine ⟨bits, semantic, success, ?_, unchanged⟩
      change WordsAt out.2.slots.val base.val (Compiler.encodeValues (front ++ [.CONST op.output (SourceMachine.Float.numberOfBits op.output bits)]))
      rw [Compiler.encode_values_append]
      simpa only [Compiler.encodeValues, List.flatMap_cons, List.flatMap_nil,
        Compiler.encode_float_number _ _ semantic.1, List.append_nil] using words
    · exact Or.inr trap
  rcases op.arity_valid with one | two
  · have same : right = left := UScalar.eq_of_val_eq (by simpa [one] using hr)
    subst right
    have words : WordsAt exec.slots.val base.val (Compiler.encodeValues front ++ [a]) := by
      simpa only [ValuesAt, Compiler.encode_values_append, Compiler.encode_float_operands op a b first second,
        one, if_true] using values
    exact WP.spec_mono (float_unary_words floats correct exec base op left (Compiler.encodeValues front) a b one first words position) post
  · have words : WordsAt exec.slots.val base.val (Compiler.encodeValues front ++ [a,b]) := by
      simpa only [ValuesAt, Compiler.encode_values_append, Compiler.encode_float_operands op a b first second,
        two, Nat.reduceEqDiff, if_false] using values
    have secondPosition : right.val = (Compiler.encodeValues front).length + 1 := by simpa [two, position] using hr
    exact WP.spec_mono (float_binary_words floats correct exec base op left right (Compiler.encodeValues front) a b first second words position secondPosition) post
end Itasca.Runtime.Interp

end

/-! ## Float Fetch -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SourceMachine.Float

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
    (fetched : compiled.code.val[raw.pc.val]? = some (Compiler.floatInstruction op left left right))
    (pcBound : raw.pc.val < U32.max)
    (values : ValuesAt exec.slots.val raw.base.val (front ++ op.operands a b))
    (hl : left.val = Compiler.slots (front.map Compiler.valueType))
    (hr : right.val = left.val + (op.arity - 1)) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ pc : U32, pc.val = raw.pc.val + 1 ∧
        FloatValuesEffect op a b
          { exec with frames := exec.frames.set index { raw with pc := pc } }
          raw.base.val front (out.1, out.2.1) ∧
        SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
    (Compiler.floatInstruction op left left right) last hf hi hc fetched pcBound
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

end

/-! ## FloatOwnership -/

section

namespace Itasca.Runtime.Interp
open SourceMachine.Ownership

theorem float_transition_frame_ownership (s : _root_.store) (ambient : frame)
    (f g : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (op : SourceMachine.Float.Instruction)
    (step : SourceMachine.Float.Transition ⟨s,ambient,{f with code := op.source :: after}::rest,[]⟩
      {f with code := op.source :: after} rest after op (.next ⟨s,ambient,g::rest,[]⟩)) :
    FrameOwnershipClosure {f with code := op.source :: after} g := by
  cases step with
  | next front a b bits values first second effect =>
    intro bounds owned
    change ValuesOwned bounds f.locals ∧ ValuesOwned bounds
      (front ++ [.CONST op.output (SourceMachine.Float.numberOfBits op.output bits)])
    have old := owned.2
    change ValuesOwned bounds f.vals at old
    change f.vals = front ++ op.operands a b at values
    rw [values] at old
    refine ⟨owned.1,values_owned_append.mpr ⟨(values_owned_append.mp old).1,?_⟩⟩
    intro value member
    simp only [List.mem_singleton] at member
    subst value
    trivial
end Itasca.Runtime.Interp

end
