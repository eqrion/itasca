import Exec.Code.Local.Lowering.Common.LiteralSources
import Exec.Code.Local.Lowering.Integer.IntegerSources
import Exec.Code.Local.Lowering.Common.LiteralCursor
import Exec.Code.Local.Lowering.Integer.IntegerCursor
import Exec.Code.Body.Source.TypedLowering
import Exec.Code.Local.Callbacks.Common.CompilerLiteralMetadata
import Exec.Code.Local.Callbacks.Integer.CompilerIntegerMetadata
import Exec.Code.Body.Reader.Common.ReaderEmissions
import Exec.Code.Local.Lowering.Common.LoweringEqz
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- The canonical binary reader rows, visitor hooks, and emitted integer
callbacks agree on opcode and generated source instruction. -/
theorem eqz_reader_facts {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (ty : Inn) :
    ∃ (operation : Numeric.Operation) (hook : NumericHook),
      Numeric.opcodeMeaning (UScalar.cast .U8 (eqzOpcode ty)) = some operation ∧
      NumericHook.ofOpcode (UScalar.cast .U8 (eqzOpcode ty)) = some hook ∧
      operation.instruction = eqzSource ty ∧
      operation.inputs.map Translate.valueType = [integerType ty] ∧
      Translate.valueType operation.output = valtype.I32 ∧
      invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler (.op state (.numeric hook)) =
        eqzCallback ops compiler state ty ∧
      (UScalar.cast .U8 (eqzOpcode ty)).val ∉ Wasm2.controlOpcodes ∧
      (UScalar.cast .U8 (eqzOpcode ty)).val ∉ [28, 37, 38, 208, 209, 210, 252, 253] ∧
      Wasm2.NumericExtensions.signMeaning (UScalar.cast .U8 (eqzOpcode ty)) = none ∧
      UScalar.cast .U8 (eqzOpcode ty) ≠ code.OP_MISC_PREFIX := by
  cases ty <;>
    refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩ <;>
    simp only [global_simps] <;> decide

theorem reader_emit_eqz_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (ty : Inn)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (eqzOpcode ty))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (eqzOpcode ty)) before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ front values,
      Sequence.stackTypes st.core.vals.val = front ++ [integerType ty] ∧
      ReaderPostWasm2 p out.core (eqzSource ty) p.current.ctrl.polymorphic_base values ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (front ++ [valtype.I32]) ∧
        LinearEmission (compilerLocals before) (front ++ [integerType ty])
          (eqzSource ty) [emitted] (front ++ [valtype.I32])) := by
  obtain ⟨operation, hook, meaning, handler, instruction, inputs, output,
    hookEq, ordinary, base, sign, misc⟩ := eqz_reader_facts ops before out.core ty
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index _ before after ordinary base sign misc contextLocals accepted
  obtain ⟨callback, _, _, _, values, effect, post⟩ := reader_numeric_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ operation hook
    capacity byte meaning handler run
  rw [hookEq] at callback
  have ordinary := compiler_eqz_callback_ordinary_result ops law before after out.core ty (.Ok ()) callback
  have sources := compiler_eqz_callback_sources ops law before after out.core ty callback
  have cursor := compiler_eqz_callback_cursor ops law before after out.core ty callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [monomorphic] at effect
  obtain ⟨old, new⟩ := post.values
  obtain ⟨front, types, oldTypes, concrete, newTypes⟩ := numeric_full_stack_types known old new effect
  rw [inputs] at oldTypes
  rw [output] at newTypes
  rw [instruction] at post
  rw [oldTypes] at layout
  have lowered := callback_eqz ops law before out.core types front ty layout reachable
    concrete newTypes codeFits sourceFits coordinateFits
  rw [callback, WP.spec_ok] at lowered
  obtain ⟨operand, position, lower, emission⟩ := lowered rfl
  refine ⟨front, values, oldTypes, post, _, ⟨lower, SourceStack.of_map types concrete newTypes⟩, ?_⟩
  exact emission

theorem reader_emit_eqz_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (ty : Inn)
    (known : ConcreteStack st.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (eqzOpcode ty))
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (eqzOpcode ty)) before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.pos ∧
    (∃ front values,
      Sequence.stackTypes st.vals.val = front ++ [integerType ty] ∧
      ReaderPostWasm1 p out (eqzSource ty) p.current.ctrl.polymorphic_base values ∧
      ∃ emitted, TypedLowered before after out.vals.val emitted (front ++ [valtype.I32]) ∧
        LinearEmission (compilerLocals before) (front ++ [integerType ty])
          (eqzSource ty) [emitted] (front ++ [valtype.I32])) := by
  obtain ⟨operation, hook, meaning, handler, instruction, inputs, output,
    hookEq, ordinary, base, sign, misc⟩ := eqz_reader_facts ops before out ty
  have capacity : st.vals.val.length < Usize.max := by have := p.val_capacity; omega
  obtain ⟨callback, _, _, _, values, effect, post⟩ := reader_numeric_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out _ operation hook
    capacity byte meaning handler accepted
  rw [hookEq] at callback
  have ordinary := compiler_eqz_callback_ordinary_result ops law before after out ty (.Ok ()) callback
  have sources := compiler_eqz_callback_sources ops law before after out ty callback
  have cursor := compiler_eqz_callback_cursor ops law before after out ty callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [monomorphic] at effect
  obtain ⟨old, new⟩ := post.values
  obtain ⟨front, types, oldTypes, concrete, newTypes⟩ := numeric_full_stack_types known old new effect
  rw [inputs] at oldTypes
  rw [output] at newTypes
  rw [instruction] at post
  rw [oldTypes] at layout
  have lowered := callback_eqz ops law before out types front ty layout reachable
    concrete newTypes codeFits sourceFits coordinateFits
  rw [callback, WP.spec_ok] at lowered
  obtain ⟨operand, position, lower, emission⟩ := lowered rfl
  refine ⟨front, values, oldTypes, post, _, ⟨lower, SourceStack.of_map types concrete newTypes⟩, ?_⟩
  exact emission

end Exec.Code
