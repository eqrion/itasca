import Exec.Code.Body.Reader.Common.ReaderWasm2Select
import Exec.Code.Body.Reader.Common.ReaderSelectTypes
import Exec.Code.Local.Relations.Common.CoreBasicEmissions
import Exec.Code.Local.Relations.Common.CoreLoweringEffects
import Exec.Code.Body.Reader.Common.ReaderProfile
import Exec.Code.Body.Source.TypedLowering
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem reader_emit_select_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env .Wasm2 locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (C : context) (localsMatch : compilerLocals before = C.LOCALS)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 27#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 code.OP_SELECT before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.core.pos ∧
    ∃ (ty : Itasca.types.ValueType) (front : List valtype) (values : List code.StackType),
      Sequence.stackTypes st.core.vals.val = front ++ [Translate.valueType ty, Translate.valueType ty, .I32] ∧
      ReaderPostWasm2 p out.core (.SELECT none) p.current.ctrl.polymorphic_base values ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (front ++ [Translate.valueType ty]) ∧
        ScalarEmission C (front ++ [Translate.valueType ty, Translate.valueType ty, .I32]) (.SELECT none)
          [emitted] (front ++ [Translate.valueType ty]) := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ typeIndex code.OP_SELECT before after (by simp only [global_simps]; decide)
    (by simp only [global_simps]; decide) (by simp only [global_simps]; rfl)
    (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨selected, values, callback, read, effect, post⟩ := reader_select_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  rw [monomorphic] at effect
  obtain ⟨old, new⟩ := post.values
  obtain ⟨ty, front, types, selectedEq, beforeTypes, concrete, output⟩ := select_full_stack_types known old new effect
  rw [beforeTypes] at layout
  have lowered := compiler_select_emission ops law before out.core types C front (Translate.valueType ty)
    localsMatch layout reachable concrete output codeFits sourceFits coordinateFits
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 27#u16 0#u32 0#u32 0#u128 = _ at callback
  have ordinary := compiler_core_ordinary_result ops law before after out.core (.select false) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out.core (.select false) callback
  have cursor := compiler_core_cursor ops law before after out.core (.select false) callback
  rw [callback, WP.spec_ok] at lowered
  obtain ⟨emitted, lower, emission⟩ := lowered rfl
  exact ⟨ordinary, sources, cursor, ty, front, values, beforeTypes, post, emitted,
    ⟨lower, SourceStack.of_map types concrete output⟩, emission⟩
end Itasca.Runtime.Code
