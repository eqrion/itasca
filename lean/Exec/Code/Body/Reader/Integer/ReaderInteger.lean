import Exec.Code.Body.Reader.Common.ReaderValues
import Exec.Code.Body.Reader.Common.ReaderProfile
import Exec.Code.Local.Lowering.Integer.LoweringInteger
import Exec.Code.Local.Relations.Common.PrefixEmission
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- The canonical binary reader rows, visitor hooks, and emitted integer
callbacks agree on opcode and generated source instruction. -/
theorem binary_reader_facts {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (ty : Inn) (op : IntegerBinary) :
    ∃ (operation : Numeric.Operation) (hook : NumericHook),
      Numeric.opcodeMeaning (UScalar.cast .U8 (binaryOpcode ty op)) = some operation ∧
      NumericHook.ofOpcode (UScalar.cast .U8 (binaryOpcode ty op)) = some hook ∧
      operation.instruction = op.source ty ∧
      operation.inputs.map Translate.valueType = [integerType ty, integerType ty] ∧
      Translate.valueType operation.output = op.output ty ∧
      invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler (.op state (.numeric hook)) =
        binaryCallback ops compiler state ty op ∧
      (UScalar.cast .U8 (binaryOpcode ty op)).val ∉ Wasm2.controlOpcodes ∧
      (UScalar.cast .U8 (binaryOpcode ty op)).val ∉ [28, 37, 38, 208, 209, 210, 252, 253] ∧
      Wasm2.NumericExtensions.signMeaning (UScalar.cast .U8 (binaryOpcode ty op)) = none ∧
      UScalar.cast .U8 (binaryOpcode ty op) ≠ code.OP_MISC_PREFIX := by
  cases ty <;> cases op <;>
    refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩ <;>
    simp only [global_simps] <;> decide

theorem reader_lower_integer_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (ty : Inn) (op : IntegerBinary)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (sourceTypes functions returns localTypes labels groups initial source start)
    (invariant : ResolvedCompileInv before sourceTypes functions returns localTypes labels groups initial source start
      (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (binaryOpcode ty op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (binaryOpcode ty op)) before = .ok (.Ok (), out, after)) :
    ∃ front values,
      Sequence.stackTypes st.core.vals.val = front ++ [integerType ty, integerType ty] ∧
      ReaderPostWasm2 p out.core (op.source ty) p.current.ctrl.polymorphic_base values ∧
      ResolvedCompileInv after sourceTypes functions returns localTypes labels groups initial
        (source ++ [op.source ty]) start (front ++ [op.output ty]) := by
  obtain ⟨operation, hook, meaning, handler, instruction, inputs, output,
    hookEq, ordinary, base, sign, misc⟩ := binary_reader_facts ops before out.core ty op
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index _ before after ordinary base sign misc contextLocals accepted
  obtain ⟨callback, _, _, _, values, effect, post⟩ := reader_numeric_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ operation hook
    capacity byte meaning handler run
  rw [hookEq] at callback
  rw [monomorphic] at effect
  obtain ⟨old, new⟩ := post.values
  obtain ⟨front, types, oldTypes, concrete, newTypes⟩ := numeric_full_stack_types known old new effect
  rw [inputs] at oldTypes
  rw [output] at newTypes
  rw [instruction] at post
  rw [oldTypes] at invariant
  have lowered := callback_integer_binary ops law before out.core types front ty op invariant.layout reachable
    concrete newTypes codeFits sourceFits coordinateFits
  rw [callback, WP.spec_ok] at lowered
  obtain ⟨left, right, leftPosition, rightPosition, lower⟩ := lowered rfl
  refine ⟨front, values, oldTypes, post, lower.resolved_advance invariant ?_⟩
  exact LinearEmission.binary front ty op left right
    (by simpa only [invariant.localsEq] using leftPosition) rightPosition

theorem reader_lower_integer_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (ty : Inn) (op : IntegerBinary)
    (known : ConcreteStack st.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (sourceTypes functions returns localTypes labels groups initial source start)
    (invariant : ResolvedCompileInv before sourceTypes functions returns localTypes labels groups initial source start
      (Sequence.stackTypes st.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (binaryOpcode ty op))
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (binaryOpcode ty op)) before = .ok (.Ok (), out, after)) :
    ∃ front values,
      Sequence.stackTypes st.vals.val = front ++ [integerType ty, integerType ty] ∧
      ReaderPostWasm1 p out (op.source ty) p.current.ctrl.polymorphic_base values ∧
      ResolvedCompileInv after sourceTypes functions returns localTypes labels groups initial
        (source ++ [op.source ty]) start (front ++ [op.output ty]) := by
  obtain ⟨operation, hook, meaning, handler, instruction, inputs, output,
    hookEq, ordinary, base, sign, misc⟩ := binary_reader_facts ops before out ty op
  have capacity : st.vals.val.length < Usize.max := by have := p.val_capacity; omega
  obtain ⟨callback, _, _, _, values, effect, post⟩ := reader_numeric_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out _ operation hook
    capacity byte meaning handler accepted
  rw [hookEq] at callback
  rw [monomorphic] at effect
  obtain ⟨old, new⟩ := post.values
  obtain ⟨front, types, oldTypes, concrete, newTypes⟩ := numeric_full_stack_types known old new effect
  rw [inputs] at oldTypes
  rw [output] at newTypes
  rw [instruction] at post
  rw [oldTypes] at invariant
  have lowered := callback_integer_binary ops law before out types front ty op invariant.layout reachable
    concrete newTypes codeFits sourceFits coordinateFits
  rw [callback, WP.spec_ok] at lowered
  obtain ⟨left, right, leftPosition, rightPosition, lower⟩ := lowered rfl
  refine ⟨front, values, oldTypes, post, lower.resolved_advance invariant ?_⟩
  exact LinearEmission.binary front ty op left right
    (by simpa only [invariant.localsEq] using leftPosition) rightPosition

end Exec.Code
