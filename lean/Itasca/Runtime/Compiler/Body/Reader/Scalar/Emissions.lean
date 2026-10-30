import Itasca.Runtime.Compiler.Local.Lowering.Literal.LiteralSources
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Lowering.Integer.LoweringArithmetic
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal
import Itasca.Runtime.Compiler.Local.Lowering.Literal.LiteralCursor
import Itasca.Runtime.Compiler.Local.Source.SourceCursorTactic
import Itasca.Runtime.Compiler.Body.Source.TypedLowering
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerLiteralMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerMetadataTactic
import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileAgreement
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Prefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedPrefix
import Itasca.Runtime.Compiler.Body.Reader.Stacks.Values

/-!
An actual successful constant reader and compiler callback extends the retained code prefix and the supplied source zipper together.

Main declarations: `reader_emit_const32_wasm2` and `reader_emit_const64_wasm2`. A direct consumer is `Compiler.Body.Reader.Checking.ScalarInstructionPrefixWasm2`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- An actual successful constant reader and compiler callback extends the
retained code prefix and the supplied source zipper together. -/
theorem reader_emit_const32_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List wasm_types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
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
      Wasm2.ReaderPost p out.core (Spec.i32Const value) p.current.ctrl.polymorphic_base
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
  have postConcrete : out.core.vals.val = (types ++ [Itasca.wasm_types.ValueType.I32]).map code.StackType.Val := by
    simp [vals, concrete]
  have lowered := callback_const32 ops law before out.core (types ++ [Itasca.wasm_types.ValueType.I32])
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
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List wasm_types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
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
      Wasm2.ReaderPost p out.core (ScalarConst.i64 value) p.current.ctrl.polymorphic_base
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
  have postConcrete : out.core.vals.val = (types ++ [Itasca.wasm_types.ValueType.I64]).map code.StackType.Val := by
    simp [vals, concrete]
  have lowered := callback_const64 ops law before out.core (types ++ [Itasca.wasm_types.ValueType.I64])
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

end Itasca.Runtime.Compiler
