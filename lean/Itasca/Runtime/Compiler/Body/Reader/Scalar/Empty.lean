import Itasca.Wasm2.Scalar.StackReader
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Local.Lowering.Literal.LiteralSources
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Lowering.Integer.LoweringArithmetic
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal
import Itasca.Runtime.Compiler.Local.Lowering.Literal.LiteralCursor
import Itasca.Runtime.Compiler.Local.Source.SourceCursorTactic
import Itasca.Runtime.Compiler.Body.Source.TypedLowering
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerLiteralMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerMetadataTactic
import Itasca.Runtime.Compiler.Body.Reader.Stacks.Values
import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileAgreement
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty

/-!
Reader inversion and compiler emission for nop and drop, including exact popped operand correspondence.
-/

/-! ## Reader Wasm2 Drop -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace

theorem reader_drop_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_DROP)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_DROP before =
      .ok (.Ok (), out, after)) :
    ∃ value values, visitor.on_drop before out value = .ok (.Ok (), after) ∧
      code.read_drop st.core = .ok (.Ok value, out) ∧
      StackSemantics.Popped p.current.ctrl.polymorphic_base p.current.vals value values ∧
      Wasm2.ReaderPost p out .DROP p.current.ctrl.polymorphic_base values := by
  rw [dispatch_drop] at accepted
  obtain ⟨value, read, callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  have effect := p.read_drop byte
  rw [read, WP.spec_ok] at effect
  obtain ⟨values, operands, post⟩ := effect value rfl
  exact ⟨value, values, callback, read, operands, post⟩

end Itasca.Runtime.Compiler

end

/-! ## Reader Empty -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_emit_nop_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (byte : data.val[p.start.val]'p.inbounds = code.OP_NOP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_NOP before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (Wasm2.ReaderPost p out.core .NOP p.current.ctrl.polymorphic_base p.current.vals ∧
      TypedLoweredEmpty before after out.core.vals.val (types.map Translate.valueType) ∧
      LinearEmission (compilerLocals before) (types.map Translate.valueType) .NOP [] (types.map Translate.valueType)) := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index code.OP_NOP before after (by simp only [global_simps]; decide)
    (by simp only [global_simps]; decide) (by simp only [global_simps]; rfl)
    (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨callback, post⟩ := reader_nop_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core byte run
  have vals : out.core.vals.val = st.core.vals.val := post.values.2.trans post.values.1.symm
  have postConcrete : out.core.vals.val = types.map code.StackType.Val := vals.trans concrete
  have lowered := compiler_observe_empty ops law before out.core types _ layout postConcrete
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 1#u16 0#u32 0#u32 0#u128 = _ at callback
  have ordinary := compiler_op1_ordinary_result ops law before after out.core 0#u32 0#u32 0#u128 (.Ok ()) callback
  have sources := compiler_op1_sources ops law before after out.core 0#u32 0#u32 0#u128 callback
  have cursor := compiler_op1_cursor ops law before after out.core 0#u32 0#u32 0#u128 callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  have lowerEq := lower_empty_eq ops before out.core false
  simp only [Bool.false_eq_true, ite_false, ite_true] at lowerEq
  rw [lowerEq] at callback
  rw [callback, WP.spec_ok] at lowered
  exact ⟨post, ⟨lowered rfl, SourceStack.of_map types postConcrete rfl⟩, .nop _⟩

theorem popped_concrete_exact {segment rest : List code.StackType} {value}
    (known : ConcreteStack segment) (popped : StackSemantics.Popped false segment value rest) :
    ∃ ty : types.ValueType, value = .Val ty ∧ segment = rest ++ [.Val ty] := by
  cases popped with
  | explicit =>
    cases value with
    | Bot => exact False.elim (known .Bot (by simp) rfl)
    | Val raw => exact ⟨raw, rfl, rfl⟩

theorem reader_emit_drop_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = code.OP_DROP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_DROP before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ (front : List valtype) (ty : types.ValueType) (values : List code.StackType),
      Sequence.stackTypes st.core.vals.val = front ++ [Translate.valueType ty] ∧
      Wasm2.ReaderPost p out.core .DROP p.current.ctrl.polymorphic_base values ∧
      TypedLoweredEmpty before after out.core.vals.val front ∧
      LinearEmission (compilerLocals before) (front ++ [Translate.valueType ty]) .DROP [] front) := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index code.OP_DROP before after (by simp only [global_simps]; decide)
    (by simp only [global_simps]; decide) (by simp only [global_simps]; rfl)
    (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, values, callback, _, popped, post⟩ := reader_drop_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core byte run
  obtain ⟨old, new⟩ := post.values
  have currentKnown := (concrete_stack_append.mp (old ▸ known)).2
  rw [monomorphic] at popped
  obtain ⟨ty, valueType, segmentShape⟩ := popped_concrete_exact currentKnown popped
  have shape : st.core.vals.val = out.core.vals.val ++ [.Val ty] := by
    rw [old, new, segmentShape, List.append_assoc]
  have afterKnown : ConcreteStack out.core.vals.val := (concrete_stack_append.mp (shape ▸ known)).1
  obtain ⟨types, concrete⟩ := (concrete_stack_iff out.core.vals.val).mp afterKnown
  have beforeTypes : Sequence.stackTypes st.core.vals.val = types.map Translate.valueType ++ [Translate.valueType ty] := by
    simp [shape, concrete, Sequence.stackTypes, List.map_map, Function.comp_def]
  have lowered := compiler_observe_empty ops law before out.core types _ layout concrete
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 26#u16 0#u32 0#u32 0#u128 = _ at callback
  have ordinary := compiler_op26_ordinary_result ops law before after out.core 0#u32 0#u32 0#u128 (.Ok ()) callback
  have sources := compiler_op26_sources ops law before after out.core 0#u32 0#u32 0#u128 callback
  have cursor := compiler_op26_cursor ops law before after out.core 0#u32 0#u32 0#u128 callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  have lowerEq := lower_empty_eq ops before out.core true
  simp only [Bool.false_eq_true, ite_false, ite_true] at lowerEq
  rw [lowerEq] at callback
  rw [callback, WP.spec_ok] at lowered
  exact ⟨types.map Translate.valueType, ty, values, beforeTypes, post, ⟨lowered rfl, SourceStack.of_map types concrete rfl⟩, .drop _ _⟩

end Itasca.Runtime.Compiler

end
