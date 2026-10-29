import Itasca.Runtime.Compiler.Body.Reader.Replay.DormantOperation
import Itasca.Runtime.Compiler.Body.Reader.Float.FloatConstant
import Itasca.Runtime.Compiler.Body.Reader.Float.FloatConstantLowering
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredCodeTableExclusion
import Itasca.Runtime.Compiler.Body.Control.Embedding.StructuredScalarEmbedding
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefix
import Itasca.Runtime.Compiler.Body.Reader.Float.FloatConstantEmissions
import Itasca.Runtime.Compiler.Body.Reader.Replay.Span
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredLinearEmbedding
import Itasca.Runtime.Compiler.Body.Reader.Replay.StructuredPoint

/-!
Live and dormant floating-point constant prefixes and their compiler-state composition, used by whole-reader compilation.
-/

/-! ## Reader Float Constant Dead -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
theorem reader_prefix_dead_float32_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F32_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_F32_CONST before = .ok (.Ok (), out, after)) :
    ∃ value,
      ReaderPostWasm2 p out.core (ScalarConst.f32 value) p.current.ctrl.polymorphic_base (p.current.vals ++ [.Val .F32]) ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (ScalarConst.f32 value))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_F32_CONST before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, callback, read, values, post⟩ := reader_f32_const_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  refine ⟨value, post, ?_⟩
  apply post.structured_dead_op ops law invariant dead 67#u16 0#u32 0#u32 (UScalar.cast .U128 value)
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const ops before out.core value = _ at callback
  simpa only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const, lift, bind_ok] using callback

theorem reader_prefix_dead_float64_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F64_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_F64_CONST before = .ok (.Ok (), out, after)) :
    ∃ value,
      ReaderPostWasm2 p out.core (ScalarConst.f64 value) p.current.ctrl.polymorphic_base (p.current.vals ++ [.Val .F64]) ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (ScalarConst.f64 value))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_F64_CONST before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, callback, read, values, post⟩ := reader_f64_const_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  refine ⟨value, post, ?_⟩
  apply post.structured_dead_op ops law invariant dead 68#u16 0#u32 0#u32 (UScalar.cast .U128 value)
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const ops before out.core value = _ at callback
  simpa only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const, lift, bind_ok] using callback

end Itasca.Runtime.Code

end

/-! ## Reader Float Constant Prefix -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem reader_prefix_float32_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (C : context) {emit} [ScalarEmbedding C emit] {types functions returns locals parents current}
    (contextCodeLocals : C.LOCALS = locals)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F32_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_F32_CONST before = .ok (.Ok (), out, after)) :
    ∃ value,
      ReaderPostWasm2 p out.core (ScalarConst.f32 value) p.current.ctrl.polymorphic_base (p.current.vals ++ [.Val .F32]) ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (ScalarConst.f32 value))
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
  · simpa only [decoded] using (ScalarEmbedding.lift (emit := emit) emission)
  · rw [cursor]

theorem reader_prefix_float64_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (C : context) {emit} [ScalarEmbedding C emit] {types functions returns locals parents current}
    (contextCodeLocals : C.LOCALS = locals)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F64_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_F64_CONST before = .ok (.Ok (), out, after)) :
    ∃ value,
      ReaderPostWasm2 p out.core (ScalarConst.f64 value) p.current.ctrl.polymorphic_base (p.current.vals ++ [.Val .F64]) ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (ScalarConst.f64 value))
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
  · simpa only [decoded] using (ScalarEmbedding.lift (emit := emit) emission)
  · rw [cursor]

end Itasca.Runtime.Code

end

/-! ## Reader Float Constant State -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
theorem StructuredReaderCompilerStateWasm2.float32 {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) {emit} [ScalarEmbedding C emit]
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (contextCodeLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 67#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 67#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨value, post, compiled⟩ := reader_prefix_float32_wasm2 p ops law initial before after out ctx rfl C
      contextCodeLocals state.compiled live sourceBound bodyBound (by simpa only [p, ReaderBoundaryWasm2.pending, global_simps] using byte) (by simpa only [code.OP_F32_CONST] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices, ScalarConst.f32]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨value, post, compiled, dead⟩ := reader_prefix_dead_float32_wasm2 p ops law initial before after out ctx rfl
      state.compiled live (by simpa only [p, ReaderBoundaryWasm2.pending, global_simps] using byte) (by simpa only [code.OP_F32_CONST] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices, ScalarConst.f32]) compiled (by simp [dead])).point

theorem StructuredReaderCompilerStateWasm2.float64 {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) {emit} [ScalarEmbedding C emit]
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (contextCodeLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 68#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 68#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨value, post, compiled⟩ := reader_prefix_float64_wasm2 p ops law initial before after out ctx rfl C
      contextCodeLocals state.compiled live sourceBound bodyBound (by simpa only [p, ReaderBoundaryWasm2.pending, global_simps] using byte) (by simpa only [code.OP_F64_CONST] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices, ScalarConst.f64]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨value, post, compiled, dead⟩ := reader_prefix_dead_float64_wasm2 p ops law initial before after out ctx rfl
      state.compiled live (by simpa only [p, ReaderBoundaryWasm2.pending, global_simps] using byte) (by simpa only [code.OP_F64_CONST] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices, ScalarConst.f64]) compiled (by simp [dead])).point

end Itasca.Runtime.Code

end
