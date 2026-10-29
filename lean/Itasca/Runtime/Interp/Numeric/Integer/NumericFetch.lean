import Itasca.Runtime.Interp.Numeric.Integer.NumericWords
import Itasca.Runtime.Interp.Numeric.Integer.NumericDispatch

/-!
Integer instruction execution on decoded values. The value/word relation supplies the fetched instruction step and its concrete result slots.
-/

/-! ## Numeric Values -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SourceMachine.Numeric

def NumericValuesEffect (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (exec : runtime.interp.Execution) (base : Nat) (front : List val)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution) : Prop :=
  match op.apply a b with
  | some value => out.1 = .Ok () ∧
      ValuesAt out.2.slots.val base (front ++ [SourceMachine.integerVal op.output value.toNat]) ∧
      { out.2 with slots := exec.slots } = exec
  | none => ∃ trap, (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧ out = (.Err (.Trap trap), exec)

theorem integer_values {F : Type} (floats : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (op : Instruction)
    (left right : U32) (front : List val)
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (values : ValuesAt exec.slots.val base.val (front ++ op.operands a b))
    (hl : left.val = Compiler.slots (front.map Compiler.valueType))
    (hr : right.val = left.val + (op.arity - 1)) :
    runtime.interp.execute_scalar floats exec base (Compiler.integerOpcode op) left left right ⦃
      NumericValuesEffect op a b exec base.val front ⦄ := by
  have position : left.val = (Compiler.encodeValues front).length := by
    simpa only [Compiler.encode_values_length] using hl
  have post : ∀ out, NumericWordsEffect op a b exec base.val (Compiler.encodeValues front) out →
      NumericValuesEffect op a b exec base.val front out := by
    intro out effect
    cases operation : op.apply a b <;>
      simpa only [NumericWordsEffect, NumericValuesEffect, operation, ValuesAt,
        Compiler.encode_values_append, Compiler.encodeValues, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        SourceMachine.integerVal, Compiler.encodeValue, List.append_nil] using effect
  rcases op.arity_cases with one | two
  · have same : right = left := UScalar.eq_of_val_eq (by simpa [one] using hr)
    subst right
    have words : WordsAt exec.slots.val base.val (Compiler.encodeValues front ++ [a.toNat]) := by
      simpa only [ValuesAt, Instruction.operands, one, if_true, Compiler.encode_values_append,
        Compiler.encodeValues, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, SourceMachine.integerVal, Compiler.encodeValue,
        List.append_nil] using values
    exact WP.spec_mono (integer_unary_words floats exec base op left (Compiler.encodeValues front) a b one words position) post
  · have words : WordsAt exec.slots.val base.val (Compiler.encodeValues front ++ [a.toNat, b.toNat]) := by
      simpa only [ValuesAt, Instruction.operands, two, Nat.reduceEqDiff, if_false, Compiler.encode_values_append,
        Compiler.encodeValues, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, SourceMachine.integerVal, Compiler.encodeValue,
        List.singleton_append, List.append_nil] using values
    have second : right.val = (Compiler.encodeValues front).length + 1 := by simpa [two, position] using hr
    exact WP.spec_mono (integer_binary_words floats exec base op left right (Compiler.encodeValues front) a b words position second) post
end Itasca.Runtime.Interp

end

/-! ## Numeric Fetch -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SourceMachine.Numeric

theorem step_integer_values {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (op : Instruction) (left right : U32) (front : List val)
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetched : compiled.code.val[raw.pc.val]? = some (Compiler.integerInstruction op left left right))
    (pcBound : raw.pc.val < U32.max)
    (values : ValuesAt exec.slots.val raw.base.val (front ++ op.operands a b))
    (hl : left.val = Compiler.slots (front.map Compiler.valueType))
    (hr : right.val = left.val + (op.arity - 1)) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ pc : U32, pc.val = raw.pc.val + 1 ∧
        NumericValuesEffect op a b
          { exec with frames := exec.frames.set index { raw with pc := pc } }
          raw.base.val front (out.1, out.2.1) ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
    (Compiler.integerInstruction op left left right) last hf hi hc fetched pcBound
  intro pc position
  rw [dispatch_integer_eq]
  obtain ⟨out, equation, effect⟩ := WP.spec_imp_exists (integer_values floats
    { exec with frames := exec.frames.set index { raw with pc := pc } } raw.base op left right front a b values hl hr)
  rw [equation]
  rcases out with ⟨status, changed⟩
  simp only [bind_ok]
  with_unfolding_all apply WP.spec.ret
  exact ⟨rfl, rfl, pc, position, effect⟩
end Itasca.Runtime.Interp

end
