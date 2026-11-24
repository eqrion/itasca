import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEffects
import Itasca.Runtime.Compiler.Local.Relations.Operations.CoreBasicEmissions
import Itasca.Runtime.Compiler.Local.Relations.LoweringEffects
import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Runtime.Compiler.Body.CapacityTrace

/-! ## GlobalEffects -/

section

/-!
Successful global reads return the declared global type and append exactly that concrete operand to the physical validator stack.

Main declarations: `reader_global_get_effect` and `reader_global_set_effect`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
/-- Successful global reads return the declared global type and append exactly
that concrete operand to the physical validator stack. -/
theorem reader_global_get_effect (st out : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (index : U32) (capacity : st.vals.val.length < Usize.max)
    (accepted : code.read_global_get st data env = .ok (.Ok index, out)) :
    ∃ ty : wasm_types.GlobalType, env.global_types.val[index.val]? = some ty ∧
      out.vals.val = st.vals.val ++ [.Val ty.valtype] := by
  obtain ⟨⟨result, state⟩, read, values, controls, post⟩ := WP.spec_imp_exists (code.take_global.spec st data env)
  dsimp only at values controls post
  cases result with
  | Err error =>
    simp [code.read_global_get, read, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨idx, ty⟩ := pair
    obtain ⟨_, bound, lookup⟩ := post
    obtain ⟨next, pushed, nextValues, _, _⟩ := WP.spec_imp_exists
      (code.push_val.spec state (.Val ty.valtype) (by simpa [values] using capacity))
    simp [code.read_global_get, read, core.result.Result.Insts.CoreOpsTry.branch,
      pushed, bind_ok, Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    exact ⟨ty, by simpa [List.getElem?_eq_getElem bound] using congrArg some lookup,
      by simpa [values] using nextValues⟩

/-- A live, concrete global write consumes exactly the global's declared type. -/
theorem reader_global_set_effect (st out : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (index : U32) (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Body.Control.base st).val = outer.length)
    (monomorphic : Body.Control.polymorphic st = false) (known : ConcreteStack segment)
    (accepted : code.read_global_set st data env = .ok (.Ok index, out)) :
    ∃ ty : wasm_types.GlobalType, env.global_types.val[index.val]? = some ty ∧ ty.mutability = .Var ∧
      st.vals.val = out.vals.val ++ [.Val ty.valtype] := by
  obtain ⟨⟨result, state⟩, read, stateValues, controls, post⟩ := WP.spec_imp_exists (code.take_global.spec st data env)
  dsimp only at stateValues controls post
  cases result with
  | Err error =>
    simp [code.read_global_set, read, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨idx, ty⟩ := pair
    obtain ⟨_, bound, lookup⟩ := post
    cases mutable : ty.mutability with
    | Const =>
      simp [code.read_global_set, read, mutable, core.result.Result.Insts.CoreOpsTry.branch] at accepted
    | Var =>
      obtain ⟨⟨popResult, next⟩, popped, _, _, rest, nextValues, popEffect⟩ := WP.spec_imp_exists
        (code.pop_with_type.segment state outer segment ty.valtype (by simpa [stateValues] using values)
          (by simpa [Body.Control.base, controls] using base))
      dsimp only at nextValues popEffect
      cases popResult with
      | Err error =>
        simp [code.read_global_set, read, popped, mutable, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
      | Ok raw =>
        have poly : Body.Control.polymorphic state = false := by simpa [Body.Control.polymorphic, controls] using monomorphic
        rw [poly] at popEffect
        have segmentShape := typed_pop_exact known popEffect
        simp [code.read_global_set, read, popped, mutable, core.result.Result.Insts.CoreOpsTry.branch] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        exact ⟨ty, by simpa [List.getElem?_eq_getElem bound] using congrArg some lookup, mutable,
          by simp [values, nextValues, segmentShape, List.append_assoc]⟩

end Itasca.Compiler

end

/-! ## GlobalEmissions -/

section

/-!
Global get/set reader inversion and compiler emission, with source global types retained.
-/

/-! ## Reader Body Global -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body Itasca.Visitor.Trace
theorem reader_global_get {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 35#u8)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_GLOBAL_GET before =
      .ok (.Ok (), out, after)) :
    ∃ idx values, visitor.on_global_get before out idx = .ok (.Ok (), after) ∧
      code.read_global_get st.core data env = .ok (.Ok idx, out) ∧
      Body.ReaderPost p out (.GLOBAL_GET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [dispatch_global_get] at accepted
  obtain ⟨idx, read, callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have polymorphic : Body.Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Body.Control.polymorphic, ctrls]
  have contextMatch : Translation.Environment.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (Translation.Environment.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  have post := code.read_global_get.prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    capacity _ contextMatch p.current.ops (by simpa [polymorphic] using typed)
  rw [read, WP.spec_ok] at post
  obtain ⟨values, _, source⟩ := Body.Pending.index_reader_post p C outer spine header base ctrls blocks
    35#u8 _ byte (fun idx => .instr_case_46 _ (Translation.Environment.index_wf idx))
    (fun idx _ encoded => .globalGet idx encoded) out idx post
  exact ⟨idx, values, callback, read, source⟩

theorem reader_global_set {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 36#u8)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_GLOBAL_SET before =
      .ok (.Ok (), out, after)) :
    ∃ idx values, visitor.on_global_set before out idx = .ok (.Ok (), after) ∧
      code.read_global_set st.core data env = .ok (.Ok idx, out) ∧
      Body.ReaderPost p out (.GLOBAL_SET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [dispatch_global_set] at accepted
  obtain ⟨idx, read, callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have polymorphic : Body.Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Body.Control.polymorphic, ctrls]
  have contextMatch : Translation.Environment.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (Translation.Environment.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  have post := code.read_global_set.prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    (by simpa [Body.Control.base, ctrls] using base) _ contextMatch p.current.ops (by simpa [polymorphic] using typed)
  rw [read, WP.spec_ok] at post
  obtain ⟨values, _, source⟩ := Body.Pending.index_reader_post p C outer spine header base ctrls blocks
    36#u8 _ byte (fun idx => .instr_case_47 _ (Translation.Environment.index_wf idx))
    (fun idx _ encoded => .globalSet idx encoded) out idx post
  exact ⟨idx, values, callback, read, source⟩

end Itasca.Compiler

end

/-! ## Reader Global Emissions -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_emit_global_get {data env locals typeIndex st}
    (p : Body.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (C : context) (localsMatch : compilerLocals before = C.LOCALS)
    (globalsMatch : C.GLOBALS = env.global_types.val.map Translation.globalType)
    (types : List wasm_types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translation.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 35#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex code.OP_GLOBAL_GET before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.core.pos ∧
    ∃ (index : U32) (ty : Itasca.wasm_types.GlobalType) (values : List code.StackType),
      env.global_types.val[index.val]? = some ty ∧
      Body.ReaderPost p out.core (.GLOBAL_GET (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted
        (types.map Translation.valueType ++ [Translation.valueType ty.valtype]) ∧
        ScalarEmission C (types.map Translation.valueType) (.GLOBAL_GET (.mk_uN index.val)) [emitted]
          (types.map Translation.valueType ++ [Translation.valueType ty.valtype]) := by
  obtain ⟨capacity, run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ typeIndex code.OP_GLOBAL_GET before after (by simp only [global_simps]; decide)
    (by simp only [global_simps]; decide) (by simp only [global_simps]; rfl)
    (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨index, values, callback, read, post⟩ := reader_global_get p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  obtain ⟨ty, found, vals⟩ := reader_global_get_effect st.core out.core data env index capacity read
  have globalFound : C.GLOBALS[index.val]? = some (Translation.globalType ty) := by
    simp [globalsMatch, List.getElem?_map, found]
  have postConcrete : out.core.vals.val = (types ++ [ty.valtype]).map code.StackType.Val := by simp [vals, concrete]
  have lowered := compiler_global_get_emission ops law before out.core types ty.valtype index C
    (Translation.mutability ty.mutability) localsMatch globalFound layout reachable postConcrete
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
theorem reader_emit_global_set {data env locals typeIndex st}
    (p : Body.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (C : context) (localsMatch : compilerLocals before = C.LOCALS)
    (globalsMatch : C.GLOBALS = env.global_types.val.map Translation.globalType)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Body.Stack.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 36#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex code.OP_GLOBAL_SET before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ (index : U32) (ty : Itasca.wasm_types.GlobalType) (values : List code.StackType) (front : List valtype),
      env.global_types.val[index.val]? = some ty ∧ ty.mutability = .Var ∧
      Body.Stack.stackTypes st.core.vals.val = front ++ [Translation.valueType ty.valtype] ∧
      Body.ReaderPost p out.core (.GLOBAL_SET (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted front ∧
        ScalarEmission C (front ++ [Translation.valueType ty.valtype]) (.GLOBAL_SET (.mk_uN index.val)) [emitted] front) := by
  obtain ⟨capacity, run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ typeIndex code.OP_GLOBAL_SET before after (by simp only [global_simps]; decide)
    (by simp only [global_simps]; decide) (by simp only [global_simps]; rfl)
    (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨index, values, callback, read, post⟩ := reader_global_set p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core byte run
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  have segmentKnown : ConcreteStack p.current.vals := (concrete_stack_append.mp (vals ▸ known)).2
  obtain ⟨ty, found, mutable, shape⟩ := reader_global_set_effect st.core out.core data env index
    outer p.current.vals vals (by simpa [Body.Control.base, controls] using base)
    (by simpa [Body.Control.polymorphic, controls] using monomorphic) segmentKnown read
  have afterKnown : ConcreteStack out.core.vals.val := (concrete_stack_append.mp (shape ▸ known)).1
  obtain ⟨types, concrete⟩ := (concrete_stack_iff out.core.vals.val).mp afterKnown
  have beforeTypes : Body.Stack.stackTypes st.core.vals.val = types.map Translation.valueType ++ [Translation.valueType ty.valtype] := by
    simp [shape, concrete, Body.Stack.stackTypes, List.map_map, Function.comp_def]
  have globalFound : C.GLOBALS[index.val]? = some (.mk_globaltype (some .MUT) (Translation.valueType ty.valtype)) := by
    simp [globalsMatch, List.getElem?_map, found, Translation.globalType, mutable, Translation.mutability]
  rw [beforeTypes] at layout
  have lowered := compiler_global_set_emission ops law before out.core types (types.map Translation.valueType)
    (Translation.valueType ty.valtype) index C localsMatch globalFound layout reachable concrete rfl
    codeFits sourceFits coordinateFits
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 36#u16 index 0#u32 0#u128 = _ at callback
  have ordinary := compiler_core_ordinary_result ops law before after out.core (.globalSet index) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out.core (.globalSet index) callback
  have cursor := compiler_core_cursor ops law before after out.core (.globalSet index) callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [callback, WP.spec_ok] at lowered
  obtain ⟨emitted, lower, emission⟩ := lowered rfl
  exact ⟨index, ty, values, types.map Translation.valueType, found, mutable, beforeTypes, post,
    emitted, ⟨lower, SourceStack.of_map types concrete rfl⟩, emission⟩

end Itasca.Compiler

end

end
