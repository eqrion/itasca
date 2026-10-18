import Exec.Code.Local.Lowering.Common.LiteralSources
import Exec.Code.Local.Lowering.Integer.IntegerSources
import Exec.Code.Local.Lowering.Common.LiteralCursor
import Exec.Code.Local.Lowering.Integer.IntegerCursor
import Exec.Code.Body.Source.TypedLowering
import Exec.Code.Local.Callbacks.Common.CompilerLiteralMetadata
import Exec.Code.Local.Callbacks.Integer.CompilerIntegerMetadata
import Exec.Code.Body.Reader.Common.ReaderLowering
import Exec.Code.Body.Reader.Integer.ReaderInteger
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- An actual successful constant reader and compiler callback extends the
retained code prefix and the supplied source zipper together. -/
theorem reader_emit_const32_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I32_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_I32_CONST before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ value,
      ReaderPostWasm2 p out.core (Spec.i32Const value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .I32]) ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (types.map Translate.valueType ++ [.I32]) ∧
        LinearEmission (compilerLocals before) (types.map Translate.valueType) (Spec.i32Const value) [emitted]
          (types.map Translate.valueType ++ [.I32])) := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index code.OP_I32_CONST before after (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, callback, _, vals, post⟩ := reader_i32_const_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  have postConcrete : out.core.vals.val = (types ++ [Itasca.types.ValueType.I32]).map code.StackType.Val := by
    simp [vals, concrete]
  have lowered := callback_const32 ops law before out.core (types ++ [Itasca.types.ValueType.I32])
    (types.map Translate.valueType) value layout reachable postConcrete codeFits sourceFits coordinateFits
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const ops before out.core value = _ at callback
  have ordinary := compiler_i32_const_ordinary_result ops law before after out.core value (.Ok ()) callback
  have sources := compiler_i32_const_sources ops law before after out.core value callback
  have cursor := compiler_i32_const_cursor ops law before after out.core value callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [callback, WP.spec_ok] at lowered
  have lower := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil, Translate.valueType] at lower
  have instruction : Spec.i32Const value =
      .CONST .I32 (.mk_num__0 .I32 (.mk_uN (IScalar.hcast .U32 value).val)) := by rfl
  refine ⟨value, post, _, ⟨lower, SourceStack.of_map (types ++ [.I32]) postConcrete (by simp [Translate.valueType])⟩, ?_⟩
  rw [instruction]
  apply LinearEmission.const32
  exact layout.height

/-- An actual successful constant reader and compiler callback extends the
retained code prefix and the supplied source zipper together. -/
theorem reader_emit_const64_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I64_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_I64_CONST before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ value,
      ReaderPostWasm2 p out.core (ScalarConst.i64 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .I64]) ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (types.map Translate.valueType ++ [.I64]) ∧
        LinearEmission (compilerLocals before) (types.map Translate.valueType) (ScalarConst.i64 value) [emitted]
          (types.map Translate.valueType ++ [.I64])) := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index code.OP_I64_CONST before after (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, callback, _, vals, post⟩ := reader_i64_const_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  have postConcrete : out.core.vals.val = (types ++ [Itasca.types.ValueType.I64]).map code.StackType.Val := by
    simp [vals, concrete]
  have lowered := callback_const64 ops law before out.core (types ++ [Itasca.types.ValueType.I64])
    (types.map Translate.valueType) value layout reachable postConcrete codeFits sourceFits coordinateFits
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const ops before out.core value = _ at callback
  have ordinary := compiler_i64_const_ordinary_result ops law before after out.core value (.Ok ()) callback
  have sources := compiler_i64_const_sources ops law before after out.core value callback
  have cursor := compiler_i64_const_cursor ops law before after out.core value callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [callback, WP.spec_ok] at lowered
  have lower := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil, Translate.valueType] at lower
  have instruction : ScalarConst.i64 value =
      .CONST .I64 (.mk_num__0 .I64 (.mk_uN (IScalar.hcast .U64 value).val)) := by rfl
  refine ⟨value, post, _, ⟨lower, SourceStack.of_map (types ++ [.I64]) postConcrete (by simp [Translate.valueType])⟩, ?_⟩
  rw [instruction]
  apply LinearEmission.const64
  exact layout.height

/-- An actual successful constant reader and compiler callback extends the
retained code prefix and the supplied source zipper together. -/
theorem reader_emit_const32_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (types : List types.ValueType) (concrete : st.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I32_CONST)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_I32_CONST before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.pos ∧
    (∃ value,
      ReaderPostWasm1 p out (Spec.i32Const value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .I32]) ∧
      ∃ emitted, TypedLowered before after out.vals.val emitted (types.map Translate.valueType ++ [.I32]) ∧
        LinearEmission (compilerLocals before) (types.map Translate.valueType) (Spec.i32Const value) [emitted]
          (types.map Translate.valueType ++ [.I32])) := by
  have capacity : st.vals.val.length < Usize.max := by have := p.val_capacity; omega
  obtain ⟨value, callback, _, vals, post⟩ := reader_i32_const_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out capacity byte accepted
  have postConcrete : out.vals.val = (types ++ [Itasca.types.ValueType.I32]).map code.StackType.Val := by
    simp [vals, concrete]
  have lowered := callback_const32 ops law before out (types ++ [Itasca.types.ValueType.I32])
    (types.map Translate.valueType) value layout reachable postConcrete codeFits sourceFits coordinateFits
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const ops before out value = _ at callback
  have ordinary := compiler_i32_const_ordinary_result ops law before after out value (.Ok ()) callback
  have sources := compiler_i32_const_sources ops law before after out value callback
  have cursor := compiler_i32_const_cursor ops law before after out value callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [callback, WP.spec_ok] at lowered
  have lower := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil, Translate.valueType] at lower
  have instruction : Spec.i32Const value =
      .CONST .I32 (.mk_num__0 .I32 (.mk_uN (IScalar.hcast .U32 value).val)) := by rfl
  refine ⟨value, post, _, ⟨lower, SourceStack.of_map (types ++ [.I32]) postConcrete (by simp [Translate.valueType])⟩, ?_⟩
  rw [instruction]
  apply LinearEmission.const32
  exact layout.height

/-- An actual successful constant reader and compiler callback extends the
retained code prefix and the supplied source zipper together. -/
theorem reader_emit_const64_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (types : List types.ValueType) (concrete : st.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I64_CONST)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_I64_CONST before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.pos ∧
    (∃ value,
      ReaderPostWasm1 p out (ScalarConst.i64 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .I64]) ∧
      ∃ emitted, TypedLowered before after out.vals.val emitted (types.map Translate.valueType ++ [.I64]) ∧
        LinearEmission (compilerLocals before) (types.map Translate.valueType) (ScalarConst.i64 value) [emitted]
          (types.map Translate.valueType ++ [.I64])) := by
  have capacity : st.vals.val.length < Usize.max := by have := p.val_capacity; omega
  obtain ⟨value, callback, _, vals, post⟩ := reader_i64_const_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out capacity byte accepted
  have postConcrete : out.vals.val = (types ++ [Itasca.types.ValueType.I64]).map code.StackType.Val := by
    simp [vals, concrete]
  have lowered := callback_const64 ops law before out (types ++ [Itasca.types.ValueType.I64])
    (types.map Translate.valueType) value layout reachable postConcrete codeFits sourceFits coordinateFits
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const ops before out value = _ at callback
  have ordinary := compiler_i64_const_ordinary_result ops law before after out value (.Ok ()) callback
  have sources := compiler_i64_const_sources ops law before after out value callback
  have cursor := compiler_i64_const_cursor ops law before after out value callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [callback, WP.spec_ok] at lowered
  have lower := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil, Translate.valueType] at lower
  have instruction : ScalarConst.i64 value =
      .CONST .I64 (.mk_num__0 .I64 (.mk_uN (IScalar.hcast .U64 value).val)) := by rfl
  refine ⟨value, post, _, ⟨lower, SourceStack.of_map (types ++ [.I64]) postConcrete (by simp [Translate.valueType])⟩, ?_⟩
  rw [instruction]
  apply LinearEmission.const64
  exact layout.height

theorem reader_emit_integer_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (ty : Inn) (op : IntegerBinary)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (binaryOpcode ty op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (binaryOpcode ty op)) before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ front values,
      Sequence.stackTypes st.core.vals.val = front ++ [integerType ty, integerType ty] ∧
      ReaderPostWasm2 p out.core (op.source ty) p.current.ctrl.polymorphic_base values ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (front ++ [op.output ty]) ∧
        LinearEmission (compilerLocals before) (front ++ [integerType ty, integerType ty])
          (op.source ty) [emitted] (front ++ [op.output ty])) := by
  obtain ⟨operation, hook, meaning, handler, instruction, inputs, output,
    hookEq, ordinary, base, sign, misc⟩ := binary_reader_facts ops before out.core ty op
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index _ before after ordinary base sign misc contextLocals accepted
  obtain ⟨callback, _, _, _, values, effect, post⟩ := reader_numeric_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ operation hook
    capacity byte meaning handler run
  rw [hookEq] at callback
  have ordinary := compiler_integer_callback_ordinary_result ops law before after out.core ty op (.Ok ()) callback
  have sources := compiler_integer_callback_sources ops law before after out.core ty op callback
  have cursor := compiler_integer_callback_cursor ops law before after out.core ty op callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [monomorphic] at effect
  obtain ⟨old, new⟩ := post.values
  obtain ⟨front, types, oldTypes, concrete, newTypes⟩ := numeric_full_stack_types known old new effect
  rw [inputs] at oldTypes
  rw [output] at newTypes
  rw [instruction] at post
  rw [oldTypes] at layout
  have lowered := callback_integer_binary ops law before out.core types front ty op layout reachable
    concrete newTypes codeFits sourceFits coordinateFits
  rw [callback, WP.spec_ok] at lowered
  obtain ⟨left, right, leftPosition, rightPosition, lower⟩ := lowered rfl
  refine ⟨front, values, oldTypes, post, _, ⟨lower, SourceStack.of_map types concrete newTypes⟩, ?_⟩
  exact LinearEmission.binary front ty op left right
    leftPosition rightPosition

theorem reader_emit_integer_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (ty : Inn) (op : IntegerBinary)
    (known : ConcreteStack st.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (binaryOpcode ty op))
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (binaryOpcode ty op)) before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.pos ∧
    (∃ front values,
      Sequence.stackTypes st.vals.val = front ++ [integerType ty, integerType ty] ∧
      ReaderPostWasm1 p out (op.source ty) p.current.ctrl.polymorphic_base values ∧
      ∃ emitted, TypedLowered before after out.vals.val emitted (front ++ [op.output ty]) ∧
        LinearEmission (compilerLocals before) (front ++ [integerType ty, integerType ty])
          (op.source ty) [emitted] (front ++ [op.output ty])) := by
  obtain ⟨operation, hook, meaning, handler, instruction, inputs, output,
    hookEq, ordinary, base, sign, misc⟩ := binary_reader_facts ops before out ty op
  have capacity : st.vals.val.length < Usize.max := by have := p.val_capacity; omega
  obtain ⟨callback, _, _, _, values, effect, post⟩ := reader_numeric_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out _ operation hook
    capacity byte meaning handler accepted
  rw [hookEq] at callback
  have ordinary := compiler_integer_callback_ordinary_result ops law before after out ty op (.Ok ()) callback
  have sources := compiler_integer_callback_sources ops law before after out ty op callback
  have cursor := compiler_integer_callback_cursor ops law before after out ty op callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [monomorphic] at effect
  obtain ⟨old, new⟩ := post.values
  obtain ⟨front, types, oldTypes, concrete, newTypes⟩ := numeric_full_stack_types known old new effect
  rw [inputs] at oldTypes
  rw [output] at newTypes
  rw [instruction] at post
  rw [oldTypes] at layout
  have lowered := callback_integer_binary ops law before out types front ty op layout reachable
    concrete newTypes codeFits sourceFits coordinateFits
  rw [callback, WP.spec_ok] at lowered
  obtain ⟨left, right, leftPosition, rightPosition, lower⟩ := lowered rfl
  refine ⟨front, values, oldTypes, post, _, ⟨lower, SourceStack.of_map types concrete newTypes⟩, ?_⟩
  exact LinearEmission.binary front ty op left right
    leftPosition rightPosition

end Exec.Code
