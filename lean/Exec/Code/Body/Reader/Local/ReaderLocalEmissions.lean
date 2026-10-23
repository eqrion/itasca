import Exec.Code.Local.Lowering.Common.LiteralSources
import Exec.Code.Local.Source.SourceLengthsTactic
import Exec.Code.Local.Lowering.Common.LoweringArithmetic
import Exec.Code.Local.Lowering.Common.LiteralCursor
import Exec.Code.Local.Source.SourceCursorTactic
import Exec.Code.Body.Source.TypedLowering
import Exec.Code.Local.Callbacks.Common.CompilerLiteralMetadata
import Exec.Code.Local.Callbacks.Common.CompilerMetadataTactic
import Exec.Code.Body.Reader.Local.ReaderLocalEffects
import Exec.Code.Body.Reader.Common.ReaderProfile
import Exec.Code.Local.Lowering.Local.LoweringLocal
import Exec.Code.Local.Relations.Common.Prefix
import Exec.Code.Local.Relations.Common.ResolvedPrefix
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_emit_local_get_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env .Wasm2 locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (localsMatch : before.function.locals = locals)
    (types : List types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 32#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 code.OP_LOCAL_GET before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ (index : U32) (ty : Itasca.types.ValueType) (values : List code.StackType),
      locals.val[index.val]? = some ty ∧
      ReaderPostWasm2 p out.core (.LOCAL_GET (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (types.map Translate.valueType ++ [Translate.valueType ty]) ∧
        LinearEmission (compilerLocals before) (types.map Translate.valueType) (.LOCAL_GET (.mk_uN index.val)) [emitted] (types.map Translate.valueType ++ [Translate.valueType ty])) := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ typeIndex code.OP_LOCAL_GET before after (by simp only [global_simps]; decide)
    (by simp only [global_simps]; decide) (by simp only [global_simps]; rfl)
    (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨index, values, callback, read, post⟩ := reader_local_get_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  obtain ⟨ty, found, vals⟩ := reader_local_get_effect st.core out.core data ⟨locals, p.ft.results⟩ index capacity read
  have localFound : before.function.locals.val[index.val]? = some ty := by simpa [localsMatch] using found
  have postConcrete : out.core.vals.val = (types ++ [ty]).map code.StackType.Val := by simp [vals, concrete]
  have lowered := lower_local_get ops law before out.core (types ++ [ty])
    (types.map Translate.valueType) index ty layout reachable localFound postConcrete
    codeFits sourceFits coordinateFits
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 32#u16 index 0#u32 0#u128 = _ at callback
  have ordinary := compiler_op32_ordinary_result ops law before after out.core index 0#u32 0#u128 (.Ok ()) callback
  have sources := compiler_op32_sources ops law before after out.core index 0#u32 0#u128 callback
  have cursor := compiler_op32_cursor ops law before after out.core index 0#u32 0#u128 callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [callback, WP.spec_ok] at lowered
  obtain ⟨localSlot, slotPosition, lower⟩ := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil] at lower
  refine ⟨index, ty, values, found, post, _, ⟨lower, SourceStack.of_map (types ++ [ty]) postConcrete (by simp)⟩, ?_⟩
  apply LinearEmission.localGet
  · simp [compilerLocals, List.getElem?_map, localFound]
  · exact slotPosition
  · exact layout.height

theorem reader_emit_local_set_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env .Wasm2 locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (localsMatch : before.function.locals = locals)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 33#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 code.OP_LOCAL_SET before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ (index : U32) (ty : Itasca.types.ValueType) (values : List code.StackType) (front : List valtype),
      locals.val[index.val]? = some ty ∧
      Sequence.stackTypes st.core.vals.val = front ++ [Translate.valueType ty] ∧
      ReaderPostWasm2 p out.core (.LOCAL_SET (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted front ∧
        LinearEmission (compilerLocals before) (front ++ [Translate.valueType ty]) (.LOCAL_SET (.mk_uN index.val)) [emitted] front) := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ typeIndex code.OP_LOCAL_SET before after (by simp only [global_simps]; decide)
    (by simp only [global_simps]; decide) (by simp only [global_simps]; rfl)
    (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨index, values, callback, read, post⟩ := reader_local_set_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core byte run
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  have segmentKnown : ConcreteStack p.current.vals := (concreteStack_append.mp (vals ▸ known)).2
  obtain ⟨ty, found, shape⟩ := reader_local_set_effect st.core out.core data ⟨locals, p.ft.results⟩ index
    outer p.current.vals vals (by simpa [Control.base, controls] using base)
    (by simpa [Control.polymorphic, controls] using monomorphic) segmentKnown read
  have afterKnown : ConcreteStack out.core.vals.val := (concreteStack_append.mp (shape ▸ known)).1
  obtain ⟨types, concrete⟩ := (concreteStack_iff out.core.vals.val).mp afterKnown
  have beforeTypes : Sequence.stackTypes st.core.vals.val = types.map Translate.valueType ++ [Translate.valueType ty] := by
    simp [shape, concrete, Sequence.stackTypes, List.map_map, Function.comp_def]
  have localFound : before.function.locals.val[index.val]? = some ty := by simpa [localsMatch] using found
  rw [beforeTypes] at layout
  have lowered := lower_local_write ops law before out.core types (types.map Translate.valueType) index ty false
    layout reachable localFound concrete codeFits sourceFits coordinateFits
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 33#u16 index 0#u32 0#u128 = _ at callback
  have ordinary := compiler_op33_ordinary_result ops law before after out.core index 0#u32 0#u128 (.Ok ()) callback
  have sources := compiler_op33_sources ops law before after out.core index 0#u32 0#u128 callback
  have cursor := compiler_op33_cursor ops law before after out.core index 0#u32 0#u128 callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [if_neg Bool.false_ne_true, callback, WP.spec_ok] at lowered
  obtain ⟨localSlot, operand, localPosition, operandPosition, lower⟩ := lowered rfl
  refine ⟨index, ty, values, types.map Translate.valueType, found, beforeTypes, post,
    _, ⟨lower, SourceStack.of_map types concrete rfl⟩, ?_⟩
  apply LinearEmission.localSet
  · simp [compilerLocals, List.getElem?_map, localFound]
  · exact localPosition
  · exact operandPosition

theorem reader_emit_local_tee_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env .Wasm2 locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (localsMatch : before.function.locals = locals)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 34#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 code.OP_LOCAL_TEE before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ (index : U32) (ty : Itasca.types.ValueType) (values : List code.StackType) (front : List valtype),
      locals.val[index.val]? = some ty ∧
      Sequence.stackTypes st.core.vals.val = front ++ [Translate.valueType ty] ∧
      ReaderPostWasm2 p out.core (.LOCAL_TEE (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (front ++ [Translate.valueType ty]) ∧
        LinearEmission (compilerLocals before) (front ++ [Translate.valueType ty]) (.LOCAL_TEE (.mk_uN index.val)) [emitted] (front ++ [Translate.valueType ty])) := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ typeIndex code.OP_LOCAL_TEE before after (by simp only [global_simps]; decide)
    (by simp only [global_simps]; decide) (by simp only [global_simps]; rfl)
    (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨index, values, callback, read, post⟩ := reader_local_tee_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  have segmentKnown : ConcreteStack p.current.vals := (concreteStack_append.mp (vals ▸ known)).2
  obtain ⟨ty, found, rest, shape, unchanged⟩ := reader_local_tee_effect st.core out.core data ⟨locals, p.ft.results⟩ index capacity
    outer p.current.vals vals (by simpa [Control.base, controls] using base)
    (by simpa [Control.polymorphic, controls] using monomorphic) segmentKnown read
  have restKnown : ConcreteStack rest := (concreteStack_append.mp (shape ▸ known)).1
  obtain ⟨types, concrete⟩ := (concreteStack_iff rest).mp restKnown
  have postConcrete : out.core.vals.val = (types ++ [ty]).map code.StackType.Val := by simp [unchanged, shape, concrete]
  have beforeTypes : Sequence.stackTypes st.core.vals.val = types.map Translate.valueType ++ [Translate.valueType ty] := by
    simp [shape, concrete, Sequence.stackTypes, List.map_map, Function.comp_def]
  have localFound : before.function.locals.val[index.val]? = some ty := by simpa [localsMatch] using found
  rw [beforeTypes] at layout
  have lowered := lower_local_write ops law before out.core (types ++ [ty]) (types.map Translate.valueType) index ty true
    layout reachable localFound postConcrete codeFits sourceFits coordinateFits
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 34#u16 index 0#u32 0#u128 = _ at callback
  have ordinary := compiler_op34_ordinary_result ops law before after out.core index 0#u32 0#u128 (.Ok ()) callback
  have sources := compiler_op34_sources ops law before after out.core index 0#u32 0#u128 callback
  have cursor := compiler_op34_cursor ops law before after out.core index 0#u32 0#u128 callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [if_pos rfl, callback, WP.spec_ok] at lowered
  obtain ⟨localSlot, operand, localPosition, operandPosition, lower⟩ := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil] at lower
  refine ⟨index, ty, values, types.map Translate.valueType, found, beforeTypes, post,
    _, ⟨lower, SourceStack.of_map (types ++ [ty]) postConcrete (by simp)⟩, ?_⟩
  apply LinearEmission.localTee
  · simp [compilerLocals, List.getElem?_map, localFound]
  · exact localPosition
  · exact operandPosition

end Exec.Code
