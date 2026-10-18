import Exec.Code.Body.Reader.Local.ReaderLocalEffects
import Exec.Code.Body.Reader.Common.ReaderProfile
import Exec.Code.Local.Lowering.Local.LoweringLocal
import Exec.Code.Local.Relations.Common.PrefixEmission
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_lower_local_get_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (localsMatch : before.function.locals = locals)
    (types : List types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (sourceTypes functions returns localTypes labels groups initial source start)
    (invariant : ResolvedCompileInv before sourceTypes functions returns localTypes labels groups initial source start
      (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 32#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 code.OP_LOCAL_GET before = .ok (.Ok (), out, after)) :
    ∃ (index : U32) (ty : Itasca.types.ValueType) (values : List code.StackType),
      locals.val[index.val]? = some ty ∧
      ReaderPostWasm2 p out.core (.LOCAL_GET (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
      ResolvedCompileInv after sourceTypes functions returns localTypes labels groups initial
        (source ++ [.LOCAL_GET (.mk_uN index.val)]) start (types.map Translate.valueType ++ [Translate.valueType ty]) := by
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
    (types.map Translate.valueType) index ty invariant.layout reachable localFound postConcrete
    codeFits sourceFits coordinateFits
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 32#u16 index 0#u32 0#u128 = _ at callback
  rw [callback, WP.spec_ok] at lowered
  obtain ⟨localSlot, slotPosition, lower⟩ := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil] at lower
  refine ⟨index, ty, values, found, post, lower.resolved_advance invariant ?_⟩
  apply LinearEmission.localGet
  · rw [← invariant.localsEq]
    simp [compilerLocals, List.getElem?_map, localFound]
  · simpa only [invariant.localsEq] using slotPosition
  · simpa only [invariant.localsEq] using invariant.layout.height

theorem reader_lower_local_get_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (localsMatch : before.function.locals = ctx.locals)
    (types : List types.ValueType) (concrete : st.vals.val = types.map code.StackType.Val)
    (sourceTypes functions returns localTypes labels groups initial source start)
    (invariant : ResolvedCompileInv before sourceTypes functions returns localTypes labels groups initial source start
      (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 32#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_GET before = .ok (.Ok (), out, after)) :
    ∃ (index : U32) (ty : Itasca.types.ValueType) (values : List code.StackType),
      ctx.locals.val[index.val]? = some ty ∧
      ReaderPostWasm1 p out (.LOCAL_GET (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
      ResolvedCompileInv after sourceTypes functions returns localTypes labels groups initial
        (source ++ [.LOCAL_GET (.mk_uN index.val)]) start (types.map Translate.valueType ++ [Translate.valueType ty]) := by
  have capacity : st.vals.val.length < Usize.max := by have := p.val_capacity; omega
  obtain ⟨index, values, callback, read, post⟩ := reader_local_get_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out capacity byte accepted
  obtain ⟨ty, found, vals⟩ := reader_local_get_effect st out data ctx index capacity read
  have localFound : before.function.locals.val[index.val]? = some ty := by simpa [localsMatch] using found
  have postConcrete : out.vals.val = (types ++ [ty]).map code.StackType.Val := by simp [vals, concrete]
  have lowered := lower_local_get ops law before out (types ++ [ty])
    (types.map Translate.valueType) index ty invariant.layout reachable localFound postConcrete
    codeFits sourceFits coordinateFits
  change runtime.compiler.lower.FunctionCompiler.op ops before out 32#u16 index 0#u32 0#u128 = _ at callback
  rw [callback, WP.spec_ok] at lowered
  obtain ⟨localSlot, slotPosition, lower⟩ := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil] at lower
  refine ⟨index, ty, values, found, post, lower.resolved_advance invariant ?_⟩
  apply LinearEmission.localGet
  · rw [← invariant.localsEq]
    simp [compilerLocals, List.getElem?_map, localFound]
  · simpa only [invariant.localsEq] using slotPosition
  · simpa only [invariant.localsEq] using invariant.layout.height

theorem reader_lower_local_set_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (localsMatch : before.function.locals = locals)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (sourceTypes functions returns localTypes labels groups initial source start)
    (invariant : ResolvedCompileInv before sourceTypes functions returns localTypes labels groups initial source start
      (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 33#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 code.OP_LOCAL_SET before = .ok (.Ok (), out, after)) :
    ∃ (index : U32) (ty : Itasca.types.ValueType) (values : List code.StackType) (front : List valtype),
      locals.val[index.val]? = some ty ∧
      Sequence.stackTypes st.core.vals.val = front ++ [Translate.valueType ty] ∧
      ReaderPostWasm2 p out.core (.LOCAL_SET (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
      ResolvedCompileInv after sourceTypes functions returns localTypes labels groups initial
        (source ++ [.LOCAL_SET (.mk_uN index.val)]) start front := by
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
  rw [beforeTypes] at invariant
  have lowered := lower_local_write ops law before out.core types (types.map Translate.valueType) index ty false
    invariant.layout reachable localFound concrete codeFits sourceFits coordinateFits
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 33#u16 index 0#u32 0#u128 = _ at callback
  rw [if_neg Bool.false_ne_true, callback, WP.spec_ok] at lowered
  obtain ⟨localSlot, operand, localPosition, operandPosition, lower⟩ := lowered rfl
  refine ⟨index, ty, values, types.map Translate.valueType, found, beforeTypes, post,
    lower.resolved_advance invariant ?_⟩
  apply LinearEmission.localSet
  · rw [← invariant.localsEq]
    simp [compilerLocals, List.getElem?_map, localFound]
  · simpa only [invariant.localsEq] using localPosition
  · simpa only [invariant.localsEq] using operandPosition

theorem reader_lower_local_tee_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (localsMatch : before.function.locals = locals)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (sourceTypes functions returns localTypes labels groups initial source start)
    (invariant : ResolvedCompileInv before sourceTypes functions returns localTypes labels groups initial source start
      (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 34#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 code.OP_LOCAL_TEE before = .ok (.Ok (), out, after)) :
    ∃ (index : U32) (ty : Itasca.types.ValueType) (values : List code.StackType) (front : List valtype),
      locals.val[index.val]? = some ty ∧
      Sequence.stackTypes st.core.vals.val = front ++ [Translate.valueType ty] ∧
      ReaderPostWasm2 p out.core (.LOCAL_TEE (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
      ResolvedCompileInv after sourceTypes functions returns localTypes labels groups initial
        (source ++ [.LOCAL_TEE (.mk_uN index.val)]) start (front ++ [Translate.valueType ty]) := by
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
  rw [beforeTypes] at invariant
  have lowered := lower_local_write ops law before out.core (types ++ [ty]) (types.map Translate.valueType) index ty true
    invariant.layout reachable localFound postConcrete codeFits sourceFits coordinateFits
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 34#u16 index 0#u32 0#u128 = _ at callback
  rw [if_pos rfl, callback, WP.spec_ok] at lowered
  obtain ⟨localSlot, operand, localPosition, operandPosition, lower⟩ := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil] at lower
  refine ⟨index, ty, values, types.map Translate.valueType, found, beforeTypes, post,
    lower.resolved_advance invariant ?_⟩
  apply LinearEmission.localTee
  · rw [← invariant.localsEq]
    simp [compilerLocals, List.getElem?_map, localFound]
  · simpa only [invariant.localsEq] using localPosition
  · simpa only [invariant.localsEq] using operandPosition

theorem reader_lower_local_set_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (localsMatch : before.function.locals = ctx.locals)
    (known : ConcreteStack st.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (sourceTypes functions returns localTypes labels groups initial source start)
    (invariant : ResolvedCompileInv before sourceTypes functions returns localTypes labels groups initial source start
      (Sequence.stackTypes st.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 33#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_SET before = .ok (.Ok (), out, after)) :
    ∃ (index : U32) (ty : Itasca.types.ValueType) (values : List code.StackType) (front : List valtype),
      ctx.locals.val[index.val]? = some ty ∧
      Sequence.stackTypes st.vals.val = front ++ [Translate.valueType ty] ∧
      ReaderPostWasm1 p out (.LOCAL_SET (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
      ResolvedCompileInv after sourceTypes functions returns localTypes labels groups initial
        (source ++ [.LOCAL_SET (.mk_uN index.val)]) start front := by
  have capacity : st.vals.val.length < Usize.max := by have := p.val_capacity; omega
  obtain ⟨index, values, callback, read, post⟩ := reader_local_set_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out byte accepted
  obtain ⟨_, outer, _, _, base, _, controls, vals⟩ := p.opened
  have segmentKnown : ConcreteStack p.current.vals := (concreteStack_append.mp (vals ▸ known)).2
  obtain ⟨ty, found, shape⟩ := reader_local_set_effect st out data ctx index
    outer p.current.vals vals (by simpa [Control.base, controls] using base)
    (by simpa [Control.polymorphic, controls] using monomorphic) segmentKnown read
  have afterKnown : ConcreteStack out.vals.val := (concreteStack_append.mp (shape ▸ known)).1
  obtain ⟨types, concrete⟩ := (concreteStack_iff out.vals.val).mp afterKnown
  have beforeTypes : Sequence.stackTypes st.vals.val = types.map Translate.valueType ++ [Translate.valueType ty] := by
    simp [shape, concrete, Sequence.stackTypes, List.map_map, Function.comp_def]
  have localFound : before.function.locals.val[index.val]? = some ty := by simpa [localsMatch] using found
  rw [beforeTypes] at invariant
  have lowered := lower_local_write ops law before out types (types.map Translate.valueType) index ty false
    invariant.layout reachable localFound concrete codeFits sourceFits coordinateFits
  change runtime.compiler.lower.FunctionCompiler.op ops before out 33#u16 index 0#u32 0#u128 = _ at callback
  rw [if_neg Bool.false_ne_true, callback, WP.spec_ok] at lowered
  obtain ⟨localSlot, operand, localPosition, operandPosition, lower⟩ := lowered rfl
  refine ⟨index, ty, values, types.map Translate.valueType, found, beforeTypes, post,
    lower.resolved_advance invariant ?_⟩
  apply LinearEmission.localSet
  · rw [← invariant.localsEq]
    simp [compilerLocals, List.getElem?_map, localFound]
  · simpa only [invariant.localsEq] using localPosition
  · simpa only [invariant.localsEq] using operandPosition

theorem reader_lower_local_tee_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (localsMatch : before.function.locals = ctx.locals)
    (known : ConcreteStack st.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (sourceTypes functions returns localTypes labels groups initial source start)
    (invariant : ResolvedCompileInv before sourceTypes functions returns localTypes labels groups initial source start
      (Sequence.stackTypes st.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 34#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_TEE before = .ok (.Ok (), out, after)) :
    ∃ (index : U32) (ty : Itasca.types.ValueType) (values : List code.StackType) (front : List valtype),
      ctx.locals.val[index.val]? = some ty ∧
      Sequence.stackTypes st.vals.val = front ++ [Translate.valueType ty] ∧
      ReaderPostWasm1 p out (.LOCAL_TEE (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
      ResolvedCompileInv after sourceTypes functions returns localTypes labels groups initial
        (source ++ [.LOCAL_TEE (.mk_uN index.val)]) start (front ++ [Translate.valueType ty]) := by
  have capacity : st.vals.val.length < Usize.max := by have := p.val_capacity; omega
  obtain ⟨index, values, callback, read, post⟩ := reader_local_tee_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out capacity byte accepted
  obtain ⟨_, outer, _, _, base, _, controls, vals⟩ := p.opened
  have segmentKnown : ConcreteStack p.current.vals := (concreteStack_append.mp (vals ▸ known)).2
  obtain ⟨ty, found, rest, shape, unchanged⟩ := reader_local_tee_effect st out data ctx index capacity
    outer p.current.vals vals (by simpa [Control.base, controls] using base)
    (by simpa [Control.polymorphic, controls] using monomorphic) segmentKnown read
  have restKnown : ConcreteStack rest := (concreteStack_append.mp (shape ▸ known)).1
  obtain ⟨types, concrete⟩ := (concreteStack_iff rest).mp restKnown
  have postConcrete : out.vals.val = (types ++ [ty]).map code.StackType.Val := by simp [unchanged, shape, concrete]
  have beforeTypes : Sequence.stackTypes st.vals.val = types.map Translate.valueType ++ [Translate.valueType ty] := by
    simp [shape, concrete, Sequence.stackTypes, List.map_map, Function.comp_def]
  have localFound : before.function.locals.val[index.val]? = some ty := by simpa [localsMatch] using found
  rw [beforeTypes] at invariant
  have lowered := lower_local_write ops law before out (types ++ [ty]) (types.map Translate.valueType) index ty true
    invariant.layout reachable localFound postConcrete codeFits sourceFits coordinateFits
  change runtime.compiler.lower.FunctionCompiler.op ops before out 34#u16 index 0#u32 0#u128 = _ at callback
  rw [if_pos rfl, callback, WP.spec_ok] at lowered
  obtain ⟨localSlot, operand, localPosition, operandPosition, lower⟩ := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil] at lower
  refine ⟨index, ty, values, types.map Translate.valueType, found, beforeTypes, post,
    lower.resolved_advance invariant ?_⟩
  apply LinearEmission.localTee
  · rw [← invariant.localsEq]
    simp [compilerLocals, List.getElem?_map, localFound]
  · simpa only [invariant.localsEq] using localPosition
  · simpa only [invariant.localsEq] using operandPosition

end Exec.Code
