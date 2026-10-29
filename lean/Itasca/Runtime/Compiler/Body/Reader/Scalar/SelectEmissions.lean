import Itasca.Runtime.Compiler.Body.Reader.Local.Wasm2Local
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownStackTransfer
import Itasca.Runtime.Compiler.Body.Reader.Scalar.SelectTypes
import Itasca.Runtime.Compiler.Local.Relations.Operations.CoreBasicEmissions
import Itasca.Runtime.Compiler.Local.Relations.Emission.CoreLoweringEffects
import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileAgreement
import Itasca.Runtime.Compiler.Body.Source.TypedLowering

/-!
Reader inversion and compiler emission for untyped select.
-/

/-! ## Reader Wasm2 Select -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace

theorem reader_select_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 27#u8)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_SELECT before =
      .ok (.Ok (), out, after)) :
    ∃ selected values, visitor.on_select before out selected = .ok (.Ok (), after) ∧
      code.read_select st.core = .ok (.Ok selected, out) ∧
      StackSemantics.SelectEffect p.current.ctrl.polymorphic_base p.current.vals selected values ∧
      ReaderPostWasm2 p out (.SELECT none) p.current.ctrl.polymorphic_base values := by
  rw [code.step_select.dispatch] at accepted
  obtain ⟨selected, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have polymorphic : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have effect := code.read_select.segment st.core outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base) capacity
  rw [read, WP.spec_ok] at effect
  obtain ⟨controls, position, values, stack, length, selectedEffect⟩ := effect
  dsimp only at controls position stack length selectedEffect
  have Cwf := Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have newTyped := selectedEffect.wasm2_prefix _ Cwf p.current.ops (by simpa [polymorphic] using typed)
  rw [polymorphic] at selectedEffect newTyped
  refine ⟨selected, values, callback, read, selectedEffect, ?_⟩
  have encoded : Wasm1.At data p.start (.plain (.SELECT none)) out.pos := by
    rw [position]
    exact .no_immediate p.inbounds byte p.pos .select
  apply reader_append_context_wasm2 p C outer spine header base out (.SELECT none)
    p.current.ctrl.polymorphic_base values (.instr_case_3 _) (.plain encoded) newTyped
  · simpa [controls] using ctrls
  · simpa [controls] using blocks
  · exact stack
  · exact encoded.declared _
end Itasca.Runtime.Compiler

end

/-! ## Reader Select Emissions -/

section

namespace Itasca.Runtime.Compiler
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
end Itasca.Runtime.Compiler

end
