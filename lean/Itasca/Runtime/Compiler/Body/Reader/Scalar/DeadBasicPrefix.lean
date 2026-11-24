import Itasca.Runtime.Compiler.Local.Callbacks.CallbackEquations
import Itasca.Runtime.Compiler.Local.Control.Structured.Prefixes
import Itasca.Runtime.Compiler.Body.Control.BranchesAndDormantEntry
import Itasca.Runtime.Compiler.Body.Control.StructuredPrefixes
import Itasca.Runtime.Compiler.Body.Reader.GlobalEmissions
import Itasca.Runtime.Compiler.Body.Reader.Scalar.ScalarEffects
import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Runtime.Compiler.Local.Relations.Stacks.ConcretePops
import Itasca.Runtime.Compiler.Body.Control.CompiledBody
import Itasca.Runtime.Compiler.Body.Callbacks.CompilerPrefixStart
import Itasca.Runtime.Compiler.Local.Callbacks.MetadataPreservation
import Itasca.Runtime.Compiler.Local.Source.SourceTactics
import Itasca.Runtime.Compiler.Local.Relations.Operations.CoreBasicEmissions
import Itasca.Runtime.Compiler.Local.Lowering.Integer.Lowering
import Itasca.Runtime.Compiler.Body.Reader.Memory.MemoryEmissions
import Itasca.Runtime.Compiler.Body.Reader.Float.ConstantAndSaturatingCompilation

/-!
Proofs for Runtime / Compiler / Body / Reader / Scalar.

This module collects DeadBasicPrefix, IntegerAndGlobalCompilation.
Each section documents its contracts and consumers.
-/

/-! ## DeadBasicPrefix -/

section

/-! ## GlobalSelectCompilation -/

section

/-!
Live/dormant global get/set and untyped-select prefixes, composed into structured reader compilation.
-/

/-! ## Reader Prefix Core Basic -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
theorem reader_prefix_global_get {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (C : context) {emit} [ScalarEmbedding C emit] {types functions returns locals parents current}
    (contextCodeLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translation.globalType)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 35#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_GLOBAL_GET before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      Body.ReaderPost p out.core (.GLOBAL_GET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.GLOBAL_GET (.mk_uN idx.val)))
        out.core.vals.val out.core.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
  have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  obtain ⟨rawTypes, concrete⟩ := (concrete_stack_iff st.core.vals.val).mp (invariant.known reachable)
  have decoded : Body.Stack.stackTypes st.core.vals.val = rawTypes.map Translation.valueType := by
    simp [concrete, Body.Stack.stackTypes, List.map_map, Function.comp_def]
  obtain ⟨ordinary, sources, cursor, idx, ty, values, found, post, emitted, lower, emission⟩ :=
    reader_emit_global_get p ops law before after out ctx contextLocals C
      (retained.localsEq.trans contextCodeLocals.symm) contextGlobals rawTypes concrete
      (by simpa only [decoded] using retained.layout) reachable codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨idx, values, post, invariant.ordinary reachable ordinary lower ?_ sources consumed ?_ emission.not_branch_table⟩
  · simpa only [decoded] using (ScalarEmbedding.lift (emit := emit) emission)
  · rw [cursor]

theorem reader_prefix_global_set {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (C : context) {emit} [ScalarEmbedding C emit] {types functions returns locals parents current}
    (contextCodeLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translation.globalType)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true)
    (monomorphic : p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 36#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_GLOBAL_SET before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      Body.ReaderPost p out.core (.GLOBAL_SET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
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
    reader_emit_global_set p ops law before after out ctx contextLocals C
      (retained.localsEq.trans contextCodeLocals.symm) contextGlobals (invariant.known reachable) monomorphic
      retained.layout reachable codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨idx, values, post, invariant.ordinary reachable ordinary lower ?_ sources consumed ?_ emission.not_branch_table⟩
  · simpa only [inputTypes] using (ScalarEmbedding.lift (emit := emit) emission)
  · rw [cursor]

theorem reader_prefix_select {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
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
      st data env ctx index code.OP_SELECT before = .ok (.Ok (), out, after)) :
    ∃ values,
      Body.ReaderPost p out.core (.SELECT none) p.current.ctrl.polymorphic_base values ∧
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
    reader_emit_select p ops law before after out ctx contextLocals C
      (retained.localsEq.trans contextCodeLocals.symm) (invariant.known reachable) monomorphic
      retained.layout reachable codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨values, post, invariant.ordinary reachable ordinary lower ?_ sources consumed ?_ emission.not_branch_table⟩
  · simpa only [inputTypes] using (ScalarEmbedding.lift (emit := emit) emission)
  · rw [cursor]
end Itasca.Compiler

end

/-! ## Reader Prefix Dead Core Basic -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
theorem reader_prefix_dead_global_get {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = 35#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_GLOBAL_GET before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      Body.ReaderPost p out.core (.GLOBAL_GET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.GLOBAL_GET (.mk_uN idx.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_GLOBAL_GET before after (by simp only [global_simps]; decide)
    (by simp only [global_simps]; decide) (by simp only [global_simps]; rfl)
    (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨idx, values, callback, read, post⟩ := reader_global_get p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 35#u16 idx 0#u32 0#u128 = _ at callback
  have ordinary := compiler_core_ordinary_result ops law before after out.core (.globalGet idx) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out.core (.globalGet idx) callback
  have cursor := compiler_core_cursor ops law before after out.core (.globalGet idx) callback
  exact ⟨idx, values, post, post.structured_skip ops law invariant dead ordinary sources cursor
    35#u16 idx 0#u32 0#u128 callback⟩

theorem reader_prefix_dead_global_set {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = 36#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_GLOBAL_SET before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      Body.ReaderPost p out.core (.GLOBAL_SET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.GLOBAL_SET (.mk_uN idx.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_GLOBAL_SET before after (by simp only [global_simps]; decide)
    (by simp only [global_simps]; decide) (by simp only [global_simps]; rfl)
    (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨idx, values, callback, read, post⟩ := reader_global_set p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core byte run
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 36#u16 idx 0#u32 0#u128 = _ at callback
  have ordinary := compiler_core_ordinary_result ops law before after out.core (.globalSet idx) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out.core (.globalSet idx) callback
  have cursor := compiler_core_cursor ops law before after out.core (.globalSet idx) callback
  exact ⟨idx, values, post, post.structured_skip ops law invariant dead ordinary sources cursor
    36#u16 idx 0#u32 0#u128 callback⟩

theorem reader_prefix_dead_select {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = 27#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_SELECT before = .ok (.Ok (), out, after)) :
    ∃ values,
      Body.ReaderPost p out.core (.SELECT none) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.SELECT none))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_SELECT before after (by simp only [global_simps]; decide)
    (by simp only [global_simps]; decide) (by simp only [global_simps]; rfl)
    (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨selected, values, callback, read, effect, post⟩ := reader_select p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 27#u16 0#u32 0#u32 0#u128 = _ at callback
  have ordinary := compiler_core_ordinary_result ops law before after out.core (.select false) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out.core (.select false) callback
  have cursor := compiler_core_cursor ops law before after out.core (.select false) callback
  exact ⟨values, post, post.structured_skip ops law invariant dead ordinary sources cursor
    27#u16 0#u32 0#u32 0#u128 callback⟩
end Itasca.Compiler

end

/-! ## Structured Reader Core Basic -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
theorem StructuredReaderCompilerState.global_get {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) {emit} [ScalarEmbedding C emit]
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (contextCodeLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translation.globalType)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 35#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index 35#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPoint jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨idx, values, post, compiled⟩ := reader_prefix_global_get p ops law initial before after out ctx rfl C
      contextCodeLocals contextGlobals state.compiled live sourceBound bodyBound byte (by simpa only [code.OP_GLOBAL_GET] using accepted)
    exact (state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨idx, values, post, compiled, dead⟩ := reader_prefix_dead_global_get p ops law initial before after out ctx rfl
      state.compiled live byte (by simpa only [code.OP_GLOBAL_GET] using accepted)
    exact (state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) compiled (by simp [dead])).point

theorem StructuredReaderCompilerState.global_set {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) {emit} [ScalarEmbedding C emit]
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (contextCodeLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translation.globalType)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 36#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index 36#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPoint jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨idx, values, post, compiled⟩ := reader_prefix_global_set p ops law initial before after out ctx rfl C
      contextCodeLocals contextGlobals state.compiled live (state.reach.current live) sourceBound bodyBound byte (by simpa only [code.OP_GLOBAL_SET] using accepted)
    exact (state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨idx, values, post, compiled, dead⟩ := reader_prefix_dead_global_set p ops law initial before after out ctx rfl
      state.compiled live byte (by simpa only [code.OP_GLOBAL_SET] using accepted)
    exact (state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) compiled (by simp [dead])).point

theorem StructuredReaderCompilerState.select {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) {emit} [ScalarEmbedding C emit]
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (contextCodeLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 27#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index 27#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPoint jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨values, post, compiled⟩ := reader_prefix_select p ops law initial before after out ctx rfl C
      contextCodeLocals state.compiled live (state.reach.current live) sourceBound bodyBound byte (by simpa only [code.OP_SELECT] using accepted)
    exact (state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨values, post, compiled, dead⟩ := reader_prefix_dead_select p ops law initial before after out ctx rfl
      state.compiled live byte (by simpa only [code.OP_SELECT] using accepted)
    exact (state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) compiled (by simp [dead])).point

end Itasca.Compiler

end

end

/-! ## DeadBasicPrefix -/

section

/-!
Dormant source prefixes for constants, nop and drop.

Main declarations: `structured_reader_prefix_dead_const32` and `structured_reader_prefix_dead_drop`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_dead_const32 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I32_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_I32_CONST before = .ok (.Ok (), out, after)) :
    ∃ value,
      Body.ReaderPost p out.core (Spec.i32Const value) p.current.ctrl.polymorphic_base (p.current.vals ++ [.Val .I32]) ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (Spec.i32Const value))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_I32_CONST before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, callback, read, values, post⟩ := reader_i32_const p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  refine ⟨value, post, ?_⟩
  apply post.structured_dead_op ops law invariant dead 65#u16 0#u32 0#u32 (UScalar.cast .U128 (IScalar.hcast .U32 value))
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const ops before out.core value = _ at callback
  simpa only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const.eq, lift, bind_ok] using callback

theorem structured_reader_prefix_dead_const64 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I64_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_I64_CONST before = .ok (.Ok (), out, after)) :
    ∃ value,
      Body.ReaderPost p out.core (Spec.Constants.i64 value) p.current.ctrl.polymorphic_base (p.current.vals ++ [.Val .I64]) ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (Spec.Constants.i64 value))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_I64_CONST before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, callback, read, values, post⟩ := reader_i64_const p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  refine ⟨value, post, ?_⟩
  apply post.structured_dead_op ops law invariant dead 66#u16 0#u32 0#u32 (UScalar.cast .U128 (IScalar.hcast .U64 value))
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const ops before out.core value = _ at callback
  simpa only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const.eq, lift, bind_ok] using callback

theorem structured_reader_prefix_dead_nop {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_NOP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_NOP before = .ok (.Ok (), out, after)) :
    Body.ReaderPost p out.core .NOP p.current.ctrl.polymorphic_base p.current.vals ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance .NOP)
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_NOP before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨callback, post⟩ := reader_nop p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core byte run
  have same : out.core.vals.val = st.core.vals.val := post.values.2.trans post.values.1.symm
  refine ⟨post, ?_⟩
  apply post.structured_dead_op ops law invariant dead 1#u16 0#u32 0#u32 0#u128
  exact callback

theorem structured_reader_prefix_dead_drop {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_DROP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_DROP before = .ok (.Ok (), out, after)) :
    ∃ values,
      Body.ReaderPost p out.core .DROP p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance .DROP)
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_DROP before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, values, callback, read, popped, post⟩ := reader_drop p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core byte run
  obtain ⟨old, new⟩ := post.values
  refine ⟨values, post, ?_⟩
  apply post.structured_dead_op ops law invariant dead 26#u16 0#u32 0#u32 0#u128
  exact callback

end Itasca.Compiler

end

end

/-! ## IntegerAndGlobalCompilation -/

section

/-!
Proofs for Runtime / Compiler / Body / Reader / Scalar.

This module collects IntegerCompilation, GlobalSelectAndSignCompilation.
Each section documents its contracts and consumers.
-/

/-! ## IntegerCompilation -/

section

/-!
Live/dormant integer-operation prefixes, including sign extension, and their structured compiler-state composition.
-/

/-! ## Structured Reader Prefix Dead Numeric -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_dead_numeric {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (op : SourceMachine.Numeric.Instruction) (standard : (integerOpcode op).val < 192)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    ∃ values,
      Body.ReaderPost p out.core op.source p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance op.source)
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨operation, hook, meaning, handler, instruction, inputs, output,
    hookEq, ordinary, baseOpcode, sign, misc⟩ := integer_reader_facts ops before out.core op standard
  obtain ⟨capacity, run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index _ before after ordinary baseOpcode sign misc contextLocals accepted
  obtain ⟨callback, read, _, _, values, effect, post⟩ := reader_numeric p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ operation hook
    capacity byte meaning handler run
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  have physicalBase : (Body.Control.base st.core).val = outer.length := by
    simpa [Body.Control.base, controls] using base
  rw [instruction] at post
  rw [hookEq] at callback
  exact ⟨values, post, post.structured_dead_op ops law invariant dead (integerOpcode op) 0#u32 0#u32 0#u128 callback⟩

end Itasca.Compiler

end

/-! ## Structured Reader Prefix Numeric -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_numeric {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (embedding : LinearEmbedding locals emit)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (op : SourceMachine.Numeric.Instruction) (baseOpcode : (integerOpcode op).val < 192)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    ∃ values,
      Body.ReaderPost p out.core op.source p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance op.source)
        out.core.vals.val out.core.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
  have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  obtain ⟨ordinary, sources, cursor, front, values, inputTypes, post, emitted, lower, emission⟩ :=
    reader_emit_numeric p ops law before after out ctx contextLocals op baseOpcode (invariant.known reachable) monomorphic retained.layout reachable
      codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨values, post, invariant.ordinary_linear embedding reachable ordinary lower ?_ sources consumed ?_⟩
  · simpa only [retained.localsEq, inputTypes] using emission
  · rw [cursor]

end Itasca.Compiler

end

/-! ## Structured Reader Prefix Sign -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_sign {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (embedding : LinearEmbedding locals emit)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (op : SourceMachine.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    ∃ values,
      Body.ReaderPost p out.core op.source p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance op.source)
        out.core.vals.val out.core.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
  have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  obtain ⟨ordinary, sources, cursor, front, values, inputTypes, post, emitted, lower, emission⟩ :=
    reader_emit_sign p ops law before after out ctx contextLocals op extension (invariant.known reachable) monomorphic retained.layout reachable
      codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨values, post, invariant.ordinary_linear embedding reachable ordinary lower ?_ sources consumed ?_⟩
  · simpa only [retained.localsEq, inputTypes] using emission
  · rw [cursor]

theorem structured_reader_prefix_dead_sign {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (op : SourceMachine.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    ∃ values,
      Body.ReaderPost p out.core op.source p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance op.source)
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨operation, instruction, inputs, output, callback, read, converted,
    ctrlsEq, position, values, effect, post⟩ :=
    reader_integer_sign p ops before after out ctx op extension byte accepted
  obtain ⟨_, _, _, _, _, _, _, _, ordinary, _⟩ := integer_sign_reader_facts ops before out.core op extension
  have capacity := (scalar_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index _ before after ordinary accepted).1
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  have physicalBase : (Body.Control.base st.core).val = outer.length := by
    simpa [Body.Control.base, controls] using base
  exact ⟨values, post, post.structured_dead_op ops law invariant dead (integerOpcode op) 0#u32 0#u32 0#u128 callback⟩

end Itasca.Compiler

end

/-! ## Structured Reader Compiler Numeric -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerState.numeric {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (op : SourceMachine.Numeric.Instruction) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = (UScalar.cast .U8 (integerOpcode op)))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    ∃ values, StructuredReaderCompilerState jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance op.source) savedParents
      (savedCurrent.advance (.plain op.source) op.source
        savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    by_cases standard : (integerOpcode op).val < 192
    · obtain ⟨values, post, compiled⟩ := structured_reader_prefix_numeric p ops law initial before after out ctx rfl
        embedding state.compiled reach (state.reach.current reach) op standard sourceBound bodyBound byte accepted
      exact ⟨values, state.advance next advance inbounds post (integer_source_declared op _) compiled (fun _ => state.reach.current reach)⟩
    · obtain ⟨values, post, compiled⟩ := structured_reader_prefix_sign p ops law initial before after out ctx rfl
        embedding state.compiled reach (state.reach.current reach) op (by omega) sourceBound bodyBound byte accepted
      exact ⟨values, state.advance next advance inbounds post (integer_source_declared op _) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    by_cases standard : (integerOpcode op).val < 192
    · obtain ⟨values, post, compiled, dead⟩ := structured_reader_prefix_dead_numeric p ops law initial before after out ctx rfl
        state.compiled reach op standard byte accepted
      exact ⟨values, state.advance next advance inbounds post (integer_source_declared op _) compiled (by simp [dead])⟩
    · obtain ⟨values, post, compiled, dead⟩ := structured_reader_prefix_dead_sign p ops law initial before after out ctx rfl
        state.compiled reach op (by omega) byte accepted
      exact ⟨values, state.advance next advance inbounds post (integer_source_declared op _) compiled (by simp [dead])⟩

end Itasca.Compiler

end

end

/-! ## GlobalSelectAndSignCompilation -/

section

/-!
Compilation of the additional core scalar reader cases.

Main declarations: `StructuredReaderCompilerState.core_extra`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerState.core_extra {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) {emit} [ScalarEmbedding C emit]
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st parents current savedParents savedCurrent)
    (contextLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translation.globalType)
    (contextMemories : C.MEMS = env.mem_types.val.map Translation.Environment.memType)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (opcode : U8) (covered : opcode.val ∈ [27,35,36,67,68,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62])
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index opcode before = .ok (.Ok (),out,after)) :
    StructuredReaderCompilerPoint jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at covered
  rcases covered with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h

  · have equal : opcode = 27#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    exact state.select ops law C contextLocals next advance inbounds out sourceBound bodyBound byte accepted
  · have equal : opcode = 35#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    exact state.global_get ops law C contextLocals contextGlobals next advance inbounds out sourceBound bodyBound byte accepted
  · have equal : opcode = 36#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    exact state.global_set ops law C contextLocals contextGlobals next advance inbounds out sourceBound bodyBound byte accepted
  · have equal : opcode = 67#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    exact state.float32 ops law C contextLocals next advance inbounds out sourceBound bodyBound byte accepted
  · have equal : opcode = 68#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    exact state.float64 ops law C contextLocals next advance inbounds out sourceBound bodyBound byte accepted
  · have equal : opcode = 40#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.full .I32)) = 40#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.full .I32) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 41#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.full .I64)) = 41#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.full .I64) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 42#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.full .F32)) = 42#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.full .F32) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 43#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.full .F64)) = 43#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.full .F64) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 44#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I32 .byte .S)) = 44#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.packed .I32 .byte .S) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 45#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I32 .byte .U)) = 45#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.packed .I32 .byte .U) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 46#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I32 .half .S)) = 46#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.packed .I32 .half .S) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 47#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I32 .half .U)) = 47#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.packed .I32 .half .U) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 48#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .byte .S)) = 48#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.packed .I64 .byte .S) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 49#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .byte .U)) = 49#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.packed .I64 .byte .U) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 50#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .half .S)) = 50#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.packed .I64 .half .S) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 51#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .half .U)) = 51#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.packed .I64 .half .U) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 52#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .word .S)) = 52#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.packed .I64 .word .S) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 53#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .word .U)) = 53#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.packed .I64 .word .U) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 54#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.full .I32)) = 54#u8 := rfl
    exact state.memory_store ops law C contextLocals contextMemories next advance inbounds out (.full .I32) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 55#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.full .I64)) = 55#u8 := rfl
    exact state.memory_store ops law C contextLocals contextMemories next advance inbounds out (.full .I64) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 56#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.full .F32)) = 56#u8 := rfl
    exact state.memory_store ops law C contextLocals contextMemories next advance inbounds out (.full .F32) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 57#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.full .F64)) = 57#u8 := rfl
    exact state.memory_store ops law C contextLocals contextMemories next advance inbounds out (.full .F64) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 58#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.packed .I32 .byte)) = 58#u8 := rfl
    exact state.memory_store ops law C contextLocals contextMemories next advance inbounds out (.packed .I32 .byte) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 59#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.packed .I32 .half)) = 59#u8 := rfl
    exact state.memory_store ops law C contextLocals contextMemories next advance inbounds out (.packed .I32 .half) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 60#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.packed .I64 .byte)) = 60#u8 := rfl
    exact state.memory_store ops law C contextLocals contextMemories next advance inbounds out (.packed .I64 .byte) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 61#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.packed .I64 .half)) = 61#u8 := rfl
    exact state.memory_store ops law C contextLocals contextMemories next advance inbounds out (.packed .I64 .half) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 62#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.packed .I64 .word)) = 62#u8 := rfl
    exact state.memory_store ops law C contextLocals contextMemories next advance inbounds out (.packed .I64 .word) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
end Itasca.Compiler

end

end
