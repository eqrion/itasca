import Itasca.Runtime.Compiler.Local.Lowering.Literal.LiteralSources
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericLowering
import Itasca.Runtime.Compiler.Local.Source.SourceCursorTactic
import Itasca.Runtime.Compiler.Body.Source.TypedLowering
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEffects
import Itasca.Runtime.Compiler.Body.Reader.Replay.BulkAndSaturatingAcceptance
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix
import Itasca.Visitor.BodyReplay
import Itasca.Runtime.Compiler.Local.Capacity.CallAvailability

/-!
Sections, each formerly its own module: LocalEmissions, LocalAcceptance.
-/

/-! ## LocalEmissions -/

section

/-!
Local get/set/tee emission from accepted reader steps.

Main declarations: `reader_emit_local_get_wasm2` and `reader_emit_local_tee_wasm2`. A direct consumer is `Compiler.Body.Reader.Checking.CoreInstructionPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_emit_local_get_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (localsMatch : before.function.locals = locals)
    (types : List wasm_types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 32#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex code.OP_LOCAL_GET before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ (index : U32) (ty : Itasca.wasm_types.ValueType) (values : List code.StackType),
      locals.val[index.val]? = some ty ∧
      Wasm2.ReaderPost p out.core (.LOCAL_GET (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
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
    (p : Wasm2.Pending data env locals typeIndex st) {A : Type}
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
      st data env ctx typeIndex code.OP_LOCAL_SET before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ (index : U32) (ty : Itasca.wasm_types.ValueType) (values : List code.StackType) (front : List valtype),
      locals.val[index.val]? = some ty ∧
      Sequence.stackTypes st.core.vals.val = front ++ [Translate.valueType ty] ∧
      Wasm2.ReaderPost p out.core (.LOCAL_SET (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
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
  have segmentKnown : ConcreteStack p.current.vals := (concrete_stack_append.mp (vals ▸ known)).2
  obtain ⟨ty, found, shape⟩ := reader_local_set_effect st.core out.core data ⟨locals, p.ft.results⟩ index
    outer p.current.vals vals (by simpa [Control.base, controls] using base)
    (by simpa [Control.polymorphic, controls] using monomorphic) segmentKnown read
  have afterKnown : ConcreteStack out.core.vals.val := (concrete_stack_append.mp (shape ▸ known)).1
  obtain ⟨types, concrete⟩ := (concrete_stack_iff out.core.vals.val).mp afterKnown
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
    (p : Wasm2.Pending data env locals typeIndex st) {A : Type}
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
      st data env ctx typeIndex code.OP_LOCAL_TEE before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ (index : U32) (ty : Itasca.wasm_types.ValueType) (values : List code.StackType) (front : List valtype),
      locals.val[index.val]? = some ty ∧
      Sequence.stackTypes st.core.vals.val = front ++ [Translate.valueType ty] ∧
      Wasm2.ReaderPost p out.core (.LOCAL_TEE (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
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
  have segmentKnown : ConcreteStack p.current.vals := (concrete_stack_append.mp (vals ▸ known)).2
  obtain ⟨ty, found, rest, shape, unchanged⟩ := reader_local_tee_effect st.core out.core data ⟨locals, p.ft.results⟩ index capacity
    outer p.current.vals vals (by simpa [Control.base, controls] using base)
    (by simpa [Control.polymorphic, controls] using monomorphic) segmentKnown read
  have restKnown : ConcreteStack rest := (concrete_stack_append.mp (shape ▸ known)).1
  obtain ⟨types, concrete⟩ := (concrete_stack_iff rest).mp restKnown
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

end Itasca.Runtime.Compiler

end

/-! ## LocalAcceptance -/

section

/-!
Independently accepted local.get reading supplies the declared type and live operand shape. It needs no successful compiler callback premise.

Main declarations: `compiler_reader_local_get_available` and `compiler_reader_local_tee_available`. A direct consumer is `Compiler.Body.Reader.Acceptance.ScalarAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Independently accepted local.get reading supplies the declared type
and live operand shape. It needs no successful compiler callback premise. -/
theorem compiler_reader_local_get_available {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler out bound) (localsMatch : compiler.function.locals = ctx.locals)
    (capacity : st.vals.val.length < Usize.max)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.vals.val))
    (reference : code.step source st data env ctx code.OP_LOCAL_GET before = .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_GET compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [code.step_local_get.dispatch] at reference ⊢
  obtain ⟨index,read,_⟩ := CoreVisitor.run.accepted _ _ _ _ _ reference
  have callback : (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_local_get compiler out index ⦃ result =>
      result.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget result.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    change runtime.compiler.lower.FunctionCompiler.op ops compiler out 32#u16 index 0#u32 0#u128 ⦃ _ ⦄
    by_cases live : compiler.reachable = true
    · obtain ⟨ty,found,_⟩ := reader_local_get_effect st out data ctx index capacity read
      exact compiler_local_variable_available ops bound available compiler out demand (Sequence.stackTypes st.vals.val)
        index ty false false (fun _ => wholeLayout live) (fun _ => by simpa [localsMatch] using found)
    · apply WP.spec_mono (compiler_dead_op_available ops bound available compiler out 32#u16 index 0#u32
        0#u128 live demand.operands demand.slots)
      intro result held
      rw [held.2]
      exact ⟨held.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩
  exact CoreVisitor.run.available_of_read (code.read_local_get st data ctx)
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_local_get compiler index out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) read callback

/-- Independently accepted local.set reading supplies the declared type
and live operand shape. It needs no successful compiler callback premise. -/
theorem compiler_reader_local_set_available {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler out bound) (localsMatch : compiler.function.locals = ctx.locals)
    (capacity : st.vals.val.length < Usize.max)
    (outer segment : List code.StackType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length)
    (monomorphic : compiler.reachable = true → Control.polymorphic st = false)
    (known : compiler.reachable = true → ConcreteStack st.vals.val)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.vals.val))
    (reference : code.step source st data env ctx code.OP_LOCAL_SET before = .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_SET compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [code.step_local_set.dispatch] at reference ⊢
  obtain ⟨index,read,_⟩ := CoreVisitor.run.accepted _ _ _ _ _ reference
  have callback : (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_local_set compiler out index ⦃ result =>
      result.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget result.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    change runtime.compiler.lower.FunctionCompiler.op ops compiler out 33#u16 index 0#u32 0#u128 ⦃ _ ⦄
    by_cases live : compiler.reachable = true
    · have currentKnown : ConcreteStack segment := (concrete_stack_append.mp (values ▸ known live)).2
      obtain ⟨ty,found,shape⟩ := reader_local_set_effect st out data ctx index outer segment values base
        (monomorphic live) currentKnown read
      have typed : Sequence.stackTypes st.vals.val = Sequence.stackTypes out.vals.val ++ [Translate.valueType ty] := by
        simp [shape,Sequence.stackTypes,Translate.valueType]
      have layout := wholeLayout live
      rw [typed] at layout
      exact compiler_local_variable_available ops bound available compiler out demand (Sequence.stackTypes out.vals.val)
        index ty true false (fun _ => layout) (fun _ => by simpa [localsMatch] using found)
    · apply WP.spec_mono (compiler_dead_op_available ops bound available compiler out 33#u16 index 0#u32
        0#u128 live demand.operands demand.slots)
      intro result held
      rw [held.2]
      exact ⟨held.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩
  exact CoreVisitor.run.available_of_read (code.read_local_set st data ctx)
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_local_set compiler index out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) read callback

/-- Independently accepted local.tee reading supplies the declared type
and live operand shape. It needs no successful compiler callback premise. -/
theorem compiler_reader_local_tee_available {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler out bound) (localsMatch : compiler.function.locals = ctx.locals)
    (capacity : st.vals.val.length < Usize.max)
    (outer segment : List code.StackType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length)
    (monomorphic : compiler.reachable = true → Control.polymorphic st = false)
    (known : compiler.reachable = true → ConcreteStack st.vals.val)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.vals.val))
    (reference : code.step source st data env ctx code.OP_LOCAL_TEE before = .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_TEE compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [code.step_local_tee.dispatch] at reference ⊢
  obtain ⟨index,read,_⟩ := CoreVisitor.run.accepted _ _ _ _ _ reference
  have callback : (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_local_tee compiler out index ⦃ result =>
      result.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget result.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    change runtime.compiler.lower.FunctionCompiler.op ops compiler out 34#u16 index 0#u32 0#u128 ⦃ _ ⦄
    by_cases live : compiler.reachable = true
    · have currentKnown : ConcreteStack segment := (concrete_stack_append.mp (values ▸ known live)).2
      obtain ⟨ty,found,rest,shape,_⟩ := reader_local_tee_effect st out data ctx index capacity outer segment values base
        (monomorphic live) currentKnown read
      have typed : Sequence.stackTypes st.vals.val = Sequence.stackTypes rest ++ [Translate.valueType ty] := by
        simp [shape,Sequence.stackTypes,Translate.valueType]
      have layout := wholeLayout live
      rw [typed] at layout
      exact compiler_local_variable_available ops bound available compiler out demand (Sequence.stackTypes rest)
        index ty true true (fun _ => layout) (fun _ => by simpa [localsMatch] using found)
    · apply WP.spec_mono (compiler_dead_op_available ops bound available compiler out 34#u16 index 0#u32
        0#u128 live demand.operands demand.slots)
      intro result held
      rw [held.2]
      exact ⟨held.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩
  exact CoreVisitor.run.available_of_read (code.read_local_tee st data ctx)
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_local_tee compiler index out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) read callback

end Itasca.Runtime.Compiler

end
