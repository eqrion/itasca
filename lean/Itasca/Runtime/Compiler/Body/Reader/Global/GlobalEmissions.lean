import Itasca.Runtime.Compiler.Body.Reader.Local.Wasm2Local
import Itasca.Runtime.Compiler.Body.Reader.Global.GlobalEffects
import Itasca.Runtime.Compiler.Local.Relations.Operations.CoreBasicEmissions
import Itasca.Runtime.Compiler.Local.Relations.Emission.CoreLoweringEffects
import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileAgreement
import Itasca.Runtime.Compiler.Body.Source.TypedLowering

/-!
Global get/set reader inversion and compiler emission, with source global types retained.
-/

/-! ## Reader Wasm2 Global -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace
theorem reader_global_get_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 35#u8)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_GLOBAL_GET before =
      .ok (.Ok (), out, after)) :
    ∃ idx values, visitor.on_global_get before out idx = .ok (.Ok (), after) ∧
      code.read_global_get st.core data env = .ok (.Ok idx, out) ∧
      Wasm2.ReaderPost p out (.GLOBAL_GET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [dispatch_global_get] at accepted
  obtain ⟨idx, read, callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have polymorphic : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have contextMatch : EnvTranslation.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  have post := code.read_global_get.wasm2_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    capacity _ contextMatch p.current.ops (by simpa [polymorphic] using typed)
  rw [read, WP.spec_ok] at post
  obtain ⟨values, _, source⟩ := Wasm2.Pending.index_reader_post p C outer spine header base ctrls blocks
    35#u8 _ byte (fun idx => .instr_case_46 _ (EnvTranslation.index_wf idx))
    (fun idx _ encoded => .globalGet idx encoded) out idx post
  exact ⟨idx, values, callback, read, source⟩

theorem reader_global_set_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 36#u8)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_GLOBAL_SET before =
      .ok (.Ok (), out, after)) :
    ∃ idx values, visitor.on_global_set before out idx = .ok (.Ok (), after) ∧
      code.read_global_set st.core data env = .ok (.Ok idx, out) ∧
      Wasm2.ReaderPost p out (.GLOBAL_SET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [dispatch_global_set] at accepted
  obtain ⟨idx, read, callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have polymorphic : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have contextMatch : EnvTranslation.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  have post := code.read_global_set.wasm2_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base) _ contextMatch p.current.ops (by simpa [polymorphic] using typed)
  rw [read, WP.spec_ok] at post
  obtain ⟨values, _, source⟩ := Wasm2.Pending.index_reader_post p C outer spine header base ctrls blocks
    36#u8 _ byte (fun idx => .instr_case_47 _ (EnvTranslation.index_wf idx))
    (fun idx _ encoded => .globalSet idx encoded) out idx post
  exact ⟨idx, values, callback, read, source⟩

end Itasca.Runtime.Compiler

end

/-! ## Reader Global Emissions -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_emit_global_get_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env .Wasm2 locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (C : context) (localsMatch : compilerLocals before = C.LOCALS)
    (globalsMatch : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (types : List types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 35#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 code.OP_GLOBAL_GET before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.core.pos ∧
    ∃ (index : U32) (ty : Itasca.types.GlobalType) (values : List code.StackType),
      env.global_types.val[index.val]? = some ty ∧
      Wasm2.ReaderPost p out.core (.GLOBAL_GET (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted
        (types.map Translate.valueType ++ [Translate.valueType ty.valtype]) ∧
        ScalarEmission C (types.map Translate.valueType) (.GLOBAL_GET (.mk_uN index.val)) [emitted]
          (types.map Translate.valueType ++ [Translate.valueType ty.valtype]) := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ typeIndex code.OP_GLOBAL_GET before after (by simp only [global_simps]; decide)
    (by simp only [global_simps]; decide) (by simp only [global_simps]; rfl)
    (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨index, values, callback, read, post⟩ := reader_global_get_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  obtain ⟨ty, found, vals⟩ := reader_global_get_effect st.core out.core data env index capacity read
  have globalFound : C.GLOBALS[index.val]? = some (Translate.globalType ty) := by
    simp [globalsMatch, List.getElem?_map, found]
  have postConcrete : out.core.vals.val = (types ++ [ty.valtype]).map code.StackType.Val := by simp [vals, concrete]
  have lowered := compiler_global_get_emission ops law before out.core types ty.valtype index C
    (Translate.mutability ty.mutability) localsMatch globalFound layout reachable postConcrete
    codeFits sourceFits coordinateFits
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 35#u16 index 0#u32 0#u128 = _ at callback
  have ordinary := compiler_core_ordinary_result ops law before after out.core (.globalGet index) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out.core (.globalGet index) callback
  have cursor := compiler_core_cursor ops law before after out.core (.globalGet index) callback
  rw [callback, WP.spec_ok] at lowered
  obtain ⟨emitted, lower, emission⟩ := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil] at lower emission
  exact ⟨ordinary, sources, cursor, index, ty, values, found, post, emitted,
    ⟨lower, SourceStack.of_map (types ++ [ty.valtype]) postConcrete (by simp)⟩, emission⟩
theorem reader_emit_global_set_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env .Wasm2 locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (C : context) (localsMatch : compilerLocals before = C.LOCALS)
    (globalsMatch : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 36#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 code.OP_GLOBAL_SET before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ (index : U32) (ty : Itasca.types.GlobalType) (values : List code.StackType) (front : List valtype),
      env.global_types.val[index.val]? = some ty ∧ ty.mutability = .Var ∧
      Sequence.stackTypes st.core.vals.val = front ++ [Translate.valueType ty.valtype] ∧
      Wasm2.ReaderPost p out.core (.GLOBAL_SET (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted front ∧
        ScalarEmission C (front ++ [Translate.valueType ty.valtype]) (.GLOBAL_SET (.mk_uN index.val)) [emitted] front) := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ typeIndex code.OP_GLOBAL_SET before after (by simp only [global_simps]; decide)
    (by simp only [global_simps]; decide) (by simp only [global_simps]; rfl)
    (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨index, values, callback, read, post⟩ := reader_global_set_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core byte run
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  have segmentKnown : ConcreteStack p.current.vals := (concrete_stack_append.mp (vals ▸ known)).2
  obtain ⟨ty, found, mutable, shape⟩ := reader_global_set_effect st.core out.core data env index
    outer p.current.vals vals (by simpa [Control.base, controls] using base)
    (by simpa [Control.polymorphic, controls] using monomorphic) segmentKnown read
  have afterKnown : ConcreteStack out.core.vals.val := (concrete_stack_append.mp (shape ▸ known)).1
  obtain ⟨types, concrete⟩ := (concrete_stack_iff out.core.vals.val).mp afterKnown
  have beforeTypes : Sequence.stackTypes st.core.vals.val = types.map Translate.valueType ++ [Translate.valueType ty.valtype] := by
    simp [shape, concrete, Sequence.stackTypes, List.map_map, Function.comp_def]
  have globalFound : C.GLOBALS[index.val]? = some (.mk_globaltype (some .MUT) (Translate.valueType ty.valtype)) := by
    simp [globalsMatch, List.getElem?_map, found, Translate.globalType, mutable, Translate.mutability]
  rw [beforeTypes] at layout
  have lowered := compiler_global_set_emission ops law before out.core types (types.map Translate.valueType)
    (Translate.valueType ty.valtype) index C localsMatch globalFound layout reachable concrete rfl
    codeFits sourceFits coordinateFits
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 36#u16 index 0#u32 0#u128 = _ at callback
  have ordinary := compiler_core_ordinary_result ops law before after out.core (.globalSet index) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out.core (.globalSet index) callback
  have cursor := compiler_core_cursor ops law before after out.core (.globalSet index) callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [callback, WP.spec_ok] at lowered
  obtain ⟨emitted, lower, emission⟩ := lowered rfl
  exact ⟨index, ty, values, types.map Translate.valueType, found, mutable, beforeTypes, post,
    emitted, ⟨lower, SourceStack.of_map types concrete rfl⟩, emission⟩

end Itasca.Runtime.Compiler

end
