import Itasca.Runtime.Compiler.Local.Control.Table.StructuredCodeTableExclusion
import Itasca.Runtime.Compiler.Body.Control.Embedding.StructuredScalarEmbedding
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefix
import Itasca.Runtime.Compiler.Body.Reader.Global.GlobalEmissions
import Itasca.Runtime.Compiler.Body.Reader.Scalar.SelectEmissions
import Itasca.Runtime.Compiler.Body.Reader.Replay.Span
import Itasca.Runtime.Compiler.Body.Reader.Replay.SkippedOperation
import Itasca.Runtime.Compiler.Body.Reader.Replay.StructuredPoint

/-!
Live/dormant global get/set and untyped-select prefixes, composed into structured reader compilation.
-/

/-! ## Reader Prefix Core Basic -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
theorem reader_prefix_global_get_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (C : context) {emit} [ScalarEmbedding C emit] {types functions returns locals parents current}
    (contextCodeLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 35#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_GLOBAL_GET before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      ReaderPostWasm2 p out.core (.GLOBAL_GET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.GLOBAL_GET (.mk_uN idx.val)))
        out.core.vals.val out.core.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
  have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  obtain ⟨rawTypes, concrete⟩ := (concreteStack_iff st.core.vals.val).mp (invariant.known reachable)
  have decoded : Sequence.stackTypes st.core.vals.val = rawTypes.map Translate.valueType := by
    simp [concrete, Sequence.stackTypes, List.map_map, Function.comp_def]
  obtain ⟨ordinary, sources, cursor, idx, ty, values, found, post, emitted, lower, emission⟩ :=
    reader_emit_global_get_wasm2 p ops law before after out ctx contextLocals C
      (retained.localsEq.trans contextCodeLocals.symm) contextGlobals rawTypes concrete
      (by simpa only [decoded] using retained.layout) reachable codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨idx, values, post, invariant.ordinary reachable ordinary lower ?_ sources consumed ?_ emission.not_branchTable⟩
  · simpa only [decoded] using (ScalarEmbedding.lift (emit := emit) emission)
  · rw [cursor]

theorem reader_prefix_global_set_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (C : context) {emit} [ScalarEmbedding C emit] {types functions returns locals parents current}
    (contextCodeLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true)
    (monomorphic : p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 36#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_GLOBAL_SET before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      ReaderPostWasm2 p out.core (.GLOBAL_SET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.GLOBAL_SET (.mk_uN idx.val)))
        out.core.vals.val out.core.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
  have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  obtain ⟨ordinary, sources, cursor, idx, ty, values, front, found, mutable, inputTypes, post, emitted, lower, emission⟩ :=
    reader_emit_global_set_wasm2 p ops law before after out ctx contextLocals C
      (retained.localsEq.trans contextCodeLocals.symm) contextGlobals (invariant.known reachable) monomorphic
      retained.layout reachable codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨idx, values, post, invariant.ordinary reachable ordinary lower ?_ sources consumed ?_ emission.not_branchTable⟩
  · simpa only [inputTypes] using (ScalarEmbedding.lift (emit := emit) emission)
  · rw [cursor]

theorem reader_prefix_select_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (C : context) {emit} [ScalarEmbedding C emit] {types functions returns locals parents current}
    (contextCodeLocals : C.LOCALS = locals)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true)
    (monomorphic : p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 27#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_SELECT before = .ok (.Ok (), out, after)) :
    ∃ values,
      ReaderPostWasm2 p out.core (.SELECT none) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.SELECT none))
        out.core.vals.val out.core.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
  have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  obtain ⟨ordinary, sources, cursor, ty, front, values, inputTypes, post, emitted, lower, emission⟩ :=
    reader_emit_select_wasm2 p ops law before after out ctx contextLocals C
      (retained.localsEq.trans contextCodeLocals.symm) (invariant.known reachable) monomorphic
      retained.layout reachable codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨values, post, invariant.ordinary reachable ordinary lower ?_ sources consumed ?_ emission.not_branchTable⟩
  · simpa only [inputTypes] using (ScalarEmbedding.lift (emit := emit) emission)
  · rw [cursor]
end Itasca.Runtime.Code

end

/-! ## Reader Prefix Dead Core Basic -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
theorem reader_prefix_dead_global_get_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = 35#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_GLOBAL_GET before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      ReaderPostWasm2 p out.core (.GLOBAL_GET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.GLOBAL_GET (.mk_uN idx.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_GLOBAL_GET before after (by simp only [global_simps]; decide)
    (by simp only [global_simps]; decide) (by simp only [global_simps]; rfl)
    (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨idx, values, callback, read, post⟩ := reader_global_get_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 35#u16 idx 0#u32 0#u128 = _ at callback
  have ordinary := compiler_core_ordinary_result ops law before after out.core (.globalGet idx) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out.core (.globalGet idx) callback
  have cursor := compiler_core_cursor ops law before after out.core (.globalGet idx) callback
  exact ⟨idx, values, post, post.structured_skip ops law invariant dead ordinary sources cursor
    35#u16 idx 0#u32 0#u128 callback⟩

theorem reader_prefix_dead_global_set_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = 36#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_GLOBAL_SET before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      ReaderPostWasm2 p out.core (.GLOBAL_SET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.GLOBAL_SET (.mk_uN idx.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_GLOBAL_SET before after (by simp only [global_simps]; decide)
    (by simp only [global_simps]; decide) (by simp only [global_simps]; rfl)
    (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨idx, values, callback, read, post⟩ := reader_global_set_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core byte run
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 36#u16 idx 0#u32 0#u128 = _ at callback
  have ordinary := compiler_core_ordinary_result ops law before after out.core (.globalSet idx) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out.core (.globalSet idx) callback
  have cursor := compiler_core_cursor ops law before after out.core (.globalSet idx) callback
  exact ⟨idx, values, post, post.structured_skip ops law invariant dead ordinary sources cursor
    36#u16 idx 0#u32 0#u128 callback⟩

theorem reader_prefix_dead_select_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = 27#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_SELECT before = .ok (.Ok (), out, after)) :
    ∃ values,
      ReaderPostWasm2 p out.core (.SELECT none) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.SELECT none))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_SELECT before after (by simp only [global_simps]; decide)
    (by simp only [global_simps]; decide) (by simp only [global_simps]; rfl)
    (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨selected, values, callback, read, effect, post⟩ := reader_select_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 27#u16 0#u32 0#u32 0#u128 = _ at callback
  have ordinary := compiler_core_ordinary_result ops law before after out.core (.select false) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out.core (.select false) callback
  have cursor := compiler_core_cursor ops law before after out.core (.select false) callback
  exact ⟨values, post, post.structured_skip ops law invariant dead ordinary sources cursor
    27#u16 0#u32 0#u32 0#u128 callback⟩
end Itasca.Runtime.Code

end

/-! ## Structured Reader Core Basic -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
theorem StructuredReaderCompilerStateWasm2.global_get {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) {emit} [ScalarEmbedding C emit]
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (contextCodeLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 35#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 35#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨idx, values, post, compiled⟩ := reader_prefix_global_get_wasm2 p ops law initial before after out ctx rfl C
      contextCodeLocals contextGlobals state.compiled live sourceBound bodyBound byte (by simpa only [code.OP_GLOBAL_GET] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨idx, values, post, compiled, dead⟩ := reader_prefix_dead_global_get_wasm2 p ops law initial before after out ctx rfl
      state.compiled live byte (by simpa only [code.OP_GLOBAL_GET] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])).point

theorem StructuredReaderCompilerStateWasm2.global_set {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) {emit} [ScalarEmbedding C emit]
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (contextCodeLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 36#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 36#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨idx, values, post, compiled⟩ := reader_prefix_global_set_wasm2 p ops law initial before after out ctx rfl C
      contextCodeLocals contextGlobals state.compiled live (state.reach.current live) sourceBound bodyBound byte (by simpa only [code.OP_GLOBAL_SET] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨idx, values, post, compiled, dead⟩ := reader_prefix_dead_global_set_wasm2 p ops law initial before after out ctx rfl
      state.compiled live byte (by simpa only [code.OP_GLOBAL_SET] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])).point

theorem StructuredReaderCompilerStateWasm2.select {jumpTables : List U32} {A : Type}
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
    (byte : data.val[st.core.pos.val]'inbounds = 27#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 27#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨values, post, compiled⟩ := reader_prefix_select_wasm2 p ops law initial before after out ctx rfl C
      contextCodeLocals state.compiled live (state.reach.current live) sourceBound bodyBound byte (by simpa only [code.OP_SELECT] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨values, post, compiled, dead⟩ := reader_prefix_dead_select_wasm2 p ops law initial before after out ctx rfl
      state.compiled live byte (by simpa only [code.OP_SELECT] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])).point

end Itasca.Runtime.Code

end
