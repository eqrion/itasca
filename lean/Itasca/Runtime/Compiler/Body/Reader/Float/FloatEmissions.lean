import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatOperands
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatEffects
import Itasca.Runtime.Compiler.Body.Reader.Float.FloatFacts
import Itasca.Runtime.Compiler.Body.Source.TypedLowering
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission

/-!
Floating-point operation emission from accepted reader steps.

Main declarations: `reader_emit_float_wasm2`. A direct consumer is `Compiler.Body.Reader.Float.Compilation`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_emit_float_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : SourceMachine.Float.Instruction) (C : context)
    (contextLocalsCode : C.LOCALS = compilerLocals before) (baseOpcode : (floatOpcode op).val < 256)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (floatOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ front values,
      Sequence.stackTypes st.core.vals.val = front ++ List.replicate op.arity (valtype_numtype op.input) ∧
      Wasm2.ReaderPost p out.core op.source p.current.ctrl.polymorphic_base values ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (front ++ [valtype_numtype op.output]) ∧
        ScalarEmission C (front ++ List.replicate op.arity (valtype_numtype op.input))
          op.source [emitted] (front ++ [valtype_numtype op.output])) := by
  obtain ⟨operation, hook, meaning, handler, instruction, inputs, output,
    hookEq, ordinary, base, sign, misc⟩ := float_reader_facts ops before out.core op baseOpcode
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index _ before after ordinary base sign misc contextLocals accepted
  obtain ⟨callback, _, _, _, values, effect, post⟩ := reader_numeric_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ operation hook
    capacity byte meaning handler run
  rw [hookEq] at callback
  have ordinary := compiler_float_ordinary_result ops law before after out.core op (.Ok ()) callback
  have sources := compiler_float_sources ops law before after out.core op callback
  have cursor := compiler_float_cursor ops law before after out.core op callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [monomorphic] at effect
  obtain ⟨old, new⟩ := post.values
  obtain ⟨front, types, oldTypes, concrete, newTypes⟩ := numeric_full_stack_types known old new effect
  rw [inputs] at oldTypes
  rw [output] at newTypes
  rw [instruction] at post
  rw [oldTypes] at layout
  have lowered := compiler_float_lowered ops law before out.core types front op layout reachable
    concrete newTypes codeFits sourceFits coordinateFits
  rw [callback, WP.spec_ok] at lowered
  obtain ⟨left, right, leftPosition, rightPosition, lower⟩ := lowered rfl
  refine ⟨front, values, oldTypes, post, _, ⟨lower, SourceStack.of_map types concrete newTypes⟩, ?_⟩
  exact ScalarEmission.float front op left right
    (by simpa only [contextLocalsCode] using leftPosition) rightPosition

end Itasca.Runtime.Compiler
