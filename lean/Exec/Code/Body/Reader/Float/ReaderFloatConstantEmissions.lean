import Exec.Code.Body.Reader.Float.ReaderFloatConstant
import Exec.Code.Body.Reader.Float.ReaderFloatConstantLowering
import Exec.Code.Body.Reader.Common.ReaderProfile
import Exec.Code.Body.Reader.Common.ReaderWasm2
import Exec.Code.Local.Relations.Common.Prefix
import Exec.Code.Local.Relations.Common.ResolvedPrefix
import Exec.Code.Body.Source.TypedLowering
import Exec.Code.Body.Reader.Float.ReaderFloatConstantEncoding
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
/-- An actual successful constant reader and compiler callback extends the
retained code prefix and the supplied source zipper together. -/
theorem reader_emit_float32_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A)
    (C : context) (localTypes : C.LOCALS = compilerLocals before) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F32_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_F32_CONST before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ value,
      ReaderPostWasm2 p out.core (ScalarConst.f32 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .F32]) ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (types.map Translate.valueType ++ [.F32]) ∧
        ScalarEmission C (types.map Translate.valueType) (ScalarConst.f32 value) [emitted]
          (types.map Translate.valueType ++ [.F32])) := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index code.OP_F32_CONST before after (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, callback, _, vals, post⟩ := reader_f32_const_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  have postConcrete : out.core.vals.val = (types ++ [Itasca.types.ValueType.F32]).map code.StackType.Val := by
    simp [vals, concrete]
  have lowered := callback_float32 ops law before out.core (types ++ [Itasca.types.ValueType.F32])
    (types.map Translate.valueType) value layout reachable postConcrete codeFits sourceFits coordinateFits
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const ops before out.core value = _ at callback
  rw [callback_float32_eq] at callback
  have ordinary := compiler_op65_ordinary_result ops law before after out.core 0#u32 0#u32 (UScalar.cast .U128 value) (.Ok ()) callback
  have sources := compiler_op65_sources ops law before after out.core 0#u32 0#u32 (UScalar.cast .U128 value) callback
  have cursor := compiler_op65_cursor ops law before after out.core 0#u32 0#u32 (UScalar.cast .U128 value) callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [callback_float32_eq, callback, WP.spec_ok] at lowered
  have lower := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil, Translate.valueType] at lower
  have instruction : ScalarConst.f32 value =
      .CONST .F32 (.mk_num__1 .F32 (SpecExt.Builtins.floatOfBits 32 value.val)) := by rw [scalar_float_value_32]; rfl
  refine ⟨value, post, _, ⟨lower, SourceStack.of_map (types ++ [.F32]) postConcrete (by simp [Translate.valueType])⟩, ?_⟩
  rw [instruction]
  apply ScalarEmission.float32
  simpa only [localTypes] using layout.height

/-- An actual successful constant reader and compiler callback extends the
retained code prefix and the supplied source zipper together. -/
theorem reader_emit_float64_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A)
    (C : context) (localTypes : C.LOCALS = compilerLocals before) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F64_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_F64_CONST before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ value,
      ReaderPostWasm2 p out.core (ScalarConst.f64 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .F64]) ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (types.map Translate.valueType ++ [.F64]) ∧
        ScalarEmission C (types.map Translate.valueType) (ScalarConst.f64 value) [emitted]
          (types.map Translate.valueType ++ [.F64])) := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index code.OP_F64_CONST before after (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, callback, _, vals, post⟩ := reader_f64_const_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  have postConcrete : out.core.vals.val = (types ++ [Itasca.types.ValueType.F64]).map code.StackType.Val := by
    simp [vals, concrete]
  have lowered := callback_float64 ops law before out.core (types ++ [Itasca.types.ValueType.F64])
    (types.map Translate.valueType) value layout reachable postConcrete codeFits sourceFits coordinateFits
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const ops before out.core value = _ at callback
  rw [callback_float64_eq] at callback
  have ordinary := compiler_op66_ordinary_result ops law before after out.core 0#u32 0#u32 (UScalar.cast .U128 value) (.Ok ()) callback
  have sources := compiler_op66_sources ops law before after out.core 0#u32 0#u32 (UScalar.cast .U128 value) callback
  have cursor := compiler_op66_cursor ops law before after out.core 0#u32 0#u32 (UScalar.cast .U128 value) callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [callback_float64_eq, callback, WP.spec_ok] at lowered
  have lower := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil, Translate.valueType] at lower
  have instruction : ScalarConst.f64 value =
      .CONST .F64 (.mk_num__1 .F64 (SpecExt.Builtins.floatOfBits 64 value.val)) := by rw [scalar_float_value_64]; rfl
  refine ⟨value, post, _, ⟨lower, SourceStack.of_map (types ++ [.F64]) postConcrete (by simp [Translate.valueType])⟩, ?_⟩
  rw [instruction]
  apply ScalarEmission.float64
  simpa only [localTypes] using layout.height

end Itasca.Runtime.Code
