import Exec.Code.Body.Reader.Common.ReaderProfile
import Exec.Code.Body.Reader.Common.ReaderWasm2
import Exec.Code.Body.Reader.Common.ReaderWasm1
import Exec.Code.Local.Relations.Common.PrefixEmission
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- An actual successful constant reader and compiler callback extends the
retained code prefix and the supplied source zipper together. -/
theorem reader_lower_const32_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (sourceTypes functions returns localTypes labels groups initial source start)
    (invariant : ResolvedCompileInv before sourceTypes functions returns localTypes labels groups initial source start
      (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I32_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_I32_CONST before = .ok (.Ok (), out, after)) :
    ∃ value,
      ReaderPostWasm2 p out.core (Spec.i32Const value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .I32]) ∧
      ResolvedCompileInv after sourceTypes functions returns localTypes labels groups initial
        (source ++ [Spec.i32Const value]) start (types.map Translate.valueType ++ [.I32]) := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index code.OP_I32_CONST before after (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, callback, _, vals, post⟩ := reader_i32_const_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  have postConcrete : out.core.vals.val = (types ++ [Itasca.types.ValueType.I32]).map code.StackType.Val := by
    simp [vals, concrete]
  have lowered := callback_const32 ops law before out.core (types ++ [Itasca.types.ValueType.I32])
    (types.map Translate.valueType) value invariant.layout reachable postConcrete codeFits sourceFits coordinateFits
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const ops before out.core value = _ at callback
  rw [callback, WP.spec_ok] at lowered
  have lower := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil, Translate.valueType] at lower
  have instruction : Spec.i32Const value =
      .CONST .I32 (.mk_num__0 .I32 (.mk_uN (IScalar.hcast .U32 value).val)) := by rfl
  refine ⟨value, post, lower.resolved_advance invariant ?_⟩
  rw [instruction]
  apply LinearEmission.const32
  simpa only [invariant.localsEq] using invariant.layout.height

/-- An actual successful constant reader and compiler callback extends the
retained code prefix and the supplied source zipper together. -/
theorem reader_lower_const64_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (sourceTypes functions returns localTypes labels groups initial source start)
    (invariant : ResolvedCompileInv before sourceTypes functions returns localTypes labels groups initial source start
      (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I64_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_I64_CONST before = .ok (.Ok (), out, after)) :
    ∃ value,
      ReaderPostWasm2 p out.core (ScalarConst.i64 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .I64]) ∧
      ResolvedCompileInv after sourceTypes functions returns localTypes labels groups initial
        (source ++ [ScalarConst.i64 value]) start (types.map Translate.valueType ++ [.I64]) := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index code.OP_I64_CONST before after (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, callback, _, vals, post⟩ := reader_i64_const_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  have postConcrete : out.core.vals.val = (types ++ [Itasca.types.ValueType.I64]).map code.StackType.Val := by
    simp [vals, concrete]
  have lowered := callback_const64 ops law before out.core (types ++ [Itasca.types.ValueType.I64])
    (types.map Translate.valueType) value invariant.layout reachable postConcrete codeFits sourceFits coordinateFits
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const ops before out.core value = _ at callback
  rw [callback, WP.spec_ok] at lowered
  have lower := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil, Translate.valueType] at lower
  have instruction : ScalarConst.i64 value =
      .CONST .I64 (.mk_num__0 .I64 (.mk_uN (IScalar.hcast .U64 value).val)) := by rfl
  refine ⟨value, post, lower.resolved_advance invariant ?_⟩
  rw [instruction]
  apply LinearEmission.const64
  simpa only [invariant.localsEq] using invariant.layout.height

/-- An actual successful constant reader and compiler callback extends the
retained code prefix and the supplied source zipper together. -/
theorem reader_lower_const32_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (types : List types.ValueType) (concrete : st.vals.val = types.map code.StackType.Val)
    (sourceTypes functions returns localTypes labels groups initial source start)
    (invariant : ResolvedCompileInv before sourceTypes functions returns localTypes labels groups initial source start
      (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I32_CONST)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_I32_CONST before = .ok (.Ok (), out, after)) :
    ∃ value,
      ReaderPostWasm1 p out (Spec.i32Const value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .I32]) ∧
      ResolvedCompileInv after sourceTypes functions returns localTypes labels groups initial
        (source ++ [Spec.i32Const value]) start (types.map Translate.valueType ++ [.I32]) := by
  have capacity : st.vals.val.length < Usize.max := by have := p.val_capacity; omega
  obtain ⟨value, callback, _, vals, post⟩ := reader_i32_const_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out capacity byte accepted
  have postConcrete : out.vals.val = (types ++ [Itasca.types.ValueType.I32]).map code.StackType.Val := by
    simp [vals, concrete]
  have lowered := callback_const32 ops law before out (types ++ [Itasca.types.ValueType.I32])
    (types.map Translate.valueType) value invariant.layout reachable postConcrete codeFits sourceFits coordinateFits
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const ops before out value = _ at callback
  rw [callback, WP.spec_ok] at lowered
  have lower := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil, Translate.valueType] at lower
  have instruction : Spec.i32Const value =
      .CONST .I32 (.mk_num__0 .I32 (.mk_uN (IScalar.hcast .U32 value).val)) := by rfl
  refine ⟨value, post, lower.resolved_advance invariant ?_⟩
  rw [instruction]
  apply LinearEmission.const32
  simpa only [invariant.localsEq] using invariant.layout.height

/-- An actual successful constant reader and compiler callback extends the
retained code prefix and the supplied source zipper together. -/
theorem reader_lower_const64_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (types : List types.ValueType) (concrete : st.vals.val = types.map code.StackType.Val)
    (sourceTypes functions returns localTypes labels groups initial source start)
    (invariant : ResolvedCompileInv before sourceTypes functions returns localTypes labels groups initial source start
      (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I64_CONST)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_I64_CONST before = .ok (.Ok (), out, after)) :
    ∃ value,
      ReaderPostWasm1 p out (ScalarConst.i64 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .I64]) ∧
      ResolvedCompileInv after sourceTypes functions returns localTypes labels groups initial
        (source ++ [ScalarConst.i64 value]) start (types.map Translate.valueType ++ [.I64]) := by
  have capacity : st.vals.val.length < Usize.max := by have := p.val_capacity; omega
  obtain ⟨value, callback, _, vals, post⟩ := reader_i64_const_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out capacity byte accepted
  have postConcrete : out.vals.val = (types ++ [Itasca.types.ValueType.I64]).map code.StackType.Val := by
    simp [vals, concrete]
  have lowered := callback_const64 ops law before out (types ++ [Itasca.types.ValueType.I64])
    (types.map Translate.valueType) value invariant.layout reachable postConcrete codeFits sourceFits coordinateFits
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const ops before out value = _ at callback
  rw [callback, WP.spec_ok] at lowered
  have lower := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil, Translate.valueType] at lower
  have instruction : ScalarConst.i64 value =
      .CONST .I64 (.mk_num__0 .I64 (.mk_uN (IScalar.hcast .U64 value).val)) := by rfl
  refine ⟨value, post, lower.resolved_advance invariant ?_⟩
  rw [instruction]
  apply LinearEmission.const64
  simpa only [invariant.localsEq] using invariant.layout.height

end Exec.Code
