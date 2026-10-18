import Exec.Code.Local.Control.Table.StructuredCodeTableExclusion
import Exec.Code.Body.Control.Common.StructuredCoreEmbedding
import Exec.Code.Body.Control.Table.StructuredCompilerPrefixWithTables
import Exec.Code.Body.Reader.Float.ReaderFloatConstantEmissions
import Exec.Code.Body.Reader.Common.ReaderSpan
import Exec.Code.Body.Control.Table.StructuredLinearEmbeddingWithTables
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_prefix_float32_wasm2_with_tables {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (C : context) {emit} [CoreEmbedding C emit] {types functions returns locals parents current}
    (contextCodeLocals : C.LOCALS = locals)
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F32_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_F32_CONST before = .ok (.Ok (), out, after)) :
    ∃ value,
      ReaderPostWasm2 p out.core (ScalarConst.f32 value) p.current.ctrl.polymorphic_base (p.current.vals ++ [.Val .F32]) ∧
      StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (ScalarConst.f32 value))
        out.core.vals.val out.core.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨rawTypes, concrete⟩ := (concreteStack_iff _).mp (invariant.known reachable)
  have decoded := (SourceStack.of_map rawTypes concrete rfl).decoded
  have layout : CompilerLayout before (rawTypes.map Translate.valueType) := decoded ▸ retained.layout
  have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
  have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  obtain ⟨ordinary, sources, cursor, value, post, emitted, lower, emission⟩ :=
    reader_emit_float32_wasm2 p ops law before after C (contextCodeLocals.trans retained.localsEq.symm) out ctx contextLocals rawTypes concrete layout reachable
      codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨value, post, invariant.ordinary reachable ordinary lower ?_ sources consumed ?_ emission.not_branchTable⟩
  · simpa only [decoded] using (CoreEmbedding.lift (emit := emit) emission)
  · rw [cursor]

theorem reader_prefix_float64_wasm2_with_tables {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (C : context) {emit} [CoreEmbedding C emit] {types functions returns locals parents current}
    (contextCodeLocals : C.LOCALS = locals)
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F64_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_F64_CONST before = .ok (.Ok (), out, after)) :
    ∃ value,
      ReaderPostWasm2 p out.core (ScalarConst.f64 value) p.current.ctrl.polymorphic_base (p.current.vals ++ [.Val .F64]) ∧
      StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (ScalarConst.f64 value))
        out.core.vals.val out.core.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨rawTypes, concrete⟩ := (concreteStack_iff _).mp (invariant.known reachable)
  have decoded := (SourceStack.of_map rawTypes concrete rfl).decoded
  have layout : CompilerLayout before (rawTypes.map Translate.valueType) := decoded ▸ retained.layout
  have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
  have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  obtain ⟨ordinary, sources, cursor, value, post, emitted, lower, emission⟩ :=
    reader_emit_float64_wasm2 p ops law before after C (contextCodeLocals.trans retained.localsEq.symm) out ctx contextLocals rawTypes concrete layout reachable
      codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨value, post, invariant.ordinary reachable ordinary lower ?_ sources consumed ?_ emission.not_branchTable⟩
  · simpa only [decoded] using (CoreEmbedding.lift (emit := emit) emission)
  · rw [cursor]

theorem reader_prefix_float32_wasm1_with_tables {jumpTables : List U32} {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (C : context) {emit} [CoreEmbedding C emit] {types functions returns locals parents current}
    (contextCodeLocals : C.LOCALS = locals)
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.vals.val p.start.val)
    (reachable : before.reachable = true)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F32_CONST)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_F32_CONST before = .ok (.Ok (), out, after)) :
    ∃ value,
      ReaderPostWasm1 p out (ScalarConst.f32 value) p.current.ctrl.polymorphic_base (p.current.vals ++ [.Val .F32]) ∧
      StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (ScalarConst.f32 value))
        out.vals.val out.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨rawTypes, concrete⟩ := (concreteStack_iff _).mp (invariant.known reachable)
  have decoded := (SourceStack.of_map rawTypes concrete rfl).decoded
  have layout : CompilerLayout before (rawTypes.map Translate.valueType) := decoded ▸ retained.layout
  have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
  have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  obtain ⟨ordinary, sources, cursor, value, post, emitted, lower, emission⟩ :=
    reader_emit_float32_wasm1 p ops law before after C (contextCodeLocals.trans retained.localsEq.symm) out rawTypes concrete layout reachable
      codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨value, post, invariant.ordinary reachable ordinary lower ?_ sources consumed ?_ emission.not_branchTable⟩
  · simpa only [decoded] using (CoreEmbedding.lift (emit := emit) emission)
  · rw [cursor]

theorem reader_prefix_float64_wasm1_with_tables {jumpTables : List U32} {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (C : context) {emit} [CoreEmbedding C emit] {types functions returns locals parents current}
    (contextCodeLocals : C.LOCALS = locals)
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.vals.val p.start.val)
    (reachable : before.reachable = true)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F64_CONST)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_F64_CONST before = .ok (.Ok (), out, after)) :
    ∃ value,
      ReaderPostWasm1 p out (ScalarConst.f64 value) p.current.ctrl.polymorphic_base (p.current.vals ++ [.Val .F64]) ∧
      StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (ScalarConst.f64 value))
        out.vals.val out.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨rawTypes, concrete⟩ := (concreteStack_iff _).mp (invariant.known reachable)
  have decoded := (SourceStack.of_map rawTypes concrete rfl).decoded
  have layout : CompilerLayout before (rawTypes.map Translate.valueType) := decoded ▸ retained.layout
  have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
  have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  obtain ⟨ordinary, sources, cursor, value, post, emitted, lower, emission⟩ :=
    reader_emit_float64_wasm1 p ops law before after C (contextCodeLocals.trans retained.localsEq.symm) out rawTypes concrete layout reachable
      codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨value, post, invariant.ordinary reachable ordinary lower ?_ sources consumed ?_ emission.not_branchTable⟩
  · simpa only [decoded] using (CoreEmbedding.lift (emit := emit) emission)
  · rw [cursor]

end Exec.Code
