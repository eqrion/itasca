import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericOperands
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericEffects
import Itasca.Runtime.Compiler.Body.Reader.Scalar.SignExtension
import Itasca.Runtime.Compiler.Body.Source.TypedLowering

/-!
Emission of integer sign-extension instructions.

Main declarations: `reader_emit_sign_wasm2`. A direct consumer is `Compiler.Body.Reader.Checking.OperationInstructionPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_emit_sign_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : SourceMachine.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ front values,
      Sequence.stackTypes st.core.vals.val = front ++ List.replicate op.arity (integerType op.input) ∧
      Wasm2.ReaderPost p out.core op.source p.current.ctrl.polymorphic_base values ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (front ++ [integerType op.output]) ∧
        LinearEmission (compilerLocals before) (front ++ List.replicate op.arity (integerType op.input))
          op.source [emitted] (front ++ [integerType op.output])) := by
  obtain ⟨operation, instruction, inputs, output, callback, read, converted,
    controls, position, values, effect, post⟩ :=
    reader_integer_sign_wasm2 p ops before after out ctx op extension byte accepted
  have ordinary := compiler_numeric_ordinary_result ops law before after out.core op (.Ok ()) callback
  have sources := compiler_numeric_sources ops law before after out.core op callback
  have cursor := compiler_numeric_cursor ops law before after out.core op callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [monomorphic] at effect
  obtain ⟨old, new⟩ := post.values
  obtain ⟨front, types, oldTypes, concrete, newTypes⟩ := numeric_full_stack_types known old new effect
  rw [inputs] at oldTypes
  rw [output] at newTypes
  rw [oldTypes] at layout
  have lowered := compiler_numeric_lowered ops law before out.core types front op layout reachable
    concrete newTypes codeFits sourceFits coordinateFits
  rw [callback, WP.spec_ok] at lowered
  obtain ⟨left, right, leftPosition, rightPosition, lower⟩ := lowered rfl
  refine ⟨front, values, oldTypes, post, _, ⟨lower, SourceStack.of_map types concrete newTypes⟩, ?_⟩
  exact LinearEmission.numeric front op left right
    leftPosition rightPosition

end Itasca.Runtime.Compiler
