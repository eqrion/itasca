import Itasca.Runtime.Compiler.Body.Reader.Replay.DormantOperation
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownNumericStack
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEffects
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefix
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEmissions
import Itasca.Runtime.Compiler.Body.Reader.Replay.Span
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredLinearEmbedding
import Itasca.Runtime.Compiler.Body.Reader.Replay.StructuredState

/-!
Live and dormant local get/set/tee prefixes and their structured compiler-state composition.
-/

/-! ## Structured Reader Prefix Dead Local -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_dead_local_get_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_GET)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_LOCAL_GET before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      ReaderPostWasm2 p out.core (.LOCAL_GET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.LOCAL_GET (.mk_uN idx.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_LOCAL_GET before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨idx, values, callback, read, post⟩ := reader_local_get_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity (by simpa only [global_simps] using byte) run
  obtain ⟨ty, _, vals⟩ := reader_local_get_effect st.core out.core data ⟨sourceLocals, p.ft.results⟩ idx capacity read
  refine ⟨idx, values, post, ?_⟩
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 32#u16 idx 0#u32 0#u128 = _ at callback
  exact post.structured_dead_op ops law invariant dead 32#u16 idx 0#u32 0#u128 callback

theorem structured_reader_prefix_dead_local_set_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_SET)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_LOCAL_SET before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      ReaderPostWasm2 p out.core (.LOCAL_SET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.LOCAL_SET (.mk_uN idx.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_LOCAL_SET before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨idx, values, callback, read, post⟩ := reader_local_set_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core (by simpa only [global_simps] using byte) run
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  refine ⟨idx, values, post, ?_⟩
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 33#u16 idx 0#u32 0#u128 = _ at callback
  exact post.structured_dead_op ops law invariant dead 33#u16 idx 0#u32 0#u128 callback

theorem structured_reader_prefix_dead_local_tee_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_TEE)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_LOCAL_TEE before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      ReaderPostWasm2 p out.core (.LOCAL_TEE (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.LOCAL_TEE (.mk_uN idx.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_LOCAL_TEE before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨idx, values, callback, read, post⟩ := reader_local_tee_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity (by simpa only [global_simps] using byte) run
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  refine ⟨idx, values, post, ?_⟩
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 34#u16 idx 0#u32 0#u128 = _ at callback
  exact post.structured_dead_op ops law invariant dead 34#u16 idx 0#u32 0#u128 callback

end Itasca.Runtime.Compiler

end

/-! ## Structured Reader Prefix Local -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_local_get_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (embedding : LinearEmbedding locals emit)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (localsMatch : before.function.locals = sourceLocals)
    (reachable : before.reachable = true)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_GET)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_LOCAL_GET before = .ok (.Ok (), out, after)) :
    ∃ (localIndex : U32) (values : List code.StackType),
      ReaderPostWasm2 p out.core ((.LOCAL_GET (.mk_uN localIndex.val))) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance ((.LOCAL_GET (.mk_uN localIndex.val))))
        out.core.vals.val out.core.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨rawTypes, concrete⟩ := (concrete_stack_iff _).mp (invariant.known reachable)
  have decoded := (SourceStack.of_map rawTypes concrete rfl).decoded
  have layout : CompilerLayout before (rawTypes.map Translate.valueType) := decoded ▸ retained.layout
  have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
  have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  obtain ⟨ordinary, sources, cursor, localIndex, localType, values, found, post, emitted, lower, emission⟩ :=
    reader_emit_local_get_wasm2 p ops law before after out ctx contextLocals localsMatch rawTypes concrete layout reachable
      codeFits sourceFits coordinateFits (by simpa only [global_simps] using byte) accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨localIndex, values, post, invariant.ordinary_linear embedding reachable ordinary lower ?_ sources consumed ?_⟩
  · simpa only [retained.localsEq, decoded] using emission
  · rw [cursor]

theorem structured_reader_prefix_local_set_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (embedding : LinearEmbedding locals emit)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (localsMatch : before.function.locals = sourceLocals)
    (reachable : before.reachable = true) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_SET)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (code.OP_LOCAL_SET) before = .ok (.Ok (), out, after)) :
    ∃ (localIndex : U32) (values : List code.StackType),
      ReaderPostWasm2 p out.core (.LOCAL_SET (.mk_uN localIndex.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.LOCAL_SET (.mk_uN localIndex.val)))
        out.core.vals.val out.core.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
  have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  obtain ⟨ordinary, sources, cursor, localIndex, localType, values, front, found, inputTypes, post, emitted, lower, emission⟩ :=
    reader_emit_local_set_wasm2 p ops law before after out ctx contextLocals localsMatch (invariant.known reachable) monomorphic retained.layout reachable
      codeFits sourceFits coordinateFits (by simpa only [global_simps] using byte) accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨localIndex, values, post, invariant.ordinary_linear embedding reachable ordinary lower ?_ sources consumed ?_⟩
  · simpa only [retained.localsEq, inputTypes] using emission
  · rw [cursor]

theorem structured_reader_prefix_local_tee_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (embedding : LinearEmbedding locals emit)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (localsMatch : before.function.locals = sourceLocals)
    (reachable : before.reachable = true) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_TEE)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (code.OP_LOCAL_TEE) before = .ok (.Ok (), out, after)) :
    ∃ (localIndex : U32) (values : List code.StackType),
      ReaderPostWasm2 p out.core (.LOCAL_TEE (.mk_uN localIndex.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.LOCAL_TEE (.mk_uN localIndex.val)))
        out.core.vals.val out.core.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
  have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  obtain ⟨ordinary, sources, cursor, localIndex, localType, values, front, found, inputTypes, post, emitted, lower, emission⟩ :=
    reader_emit_local_tee_wasm2 p ops law before after out ctx contextLocals localsMatch (invariant.known reachable) monomorphic retained.layout reachable
      codeFits sourceFits coordinateFits (by simpa only [global_simps] using byte) accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨localIndex, values, post, invariant.ordinary_linear embedding reachable ordinary lower ?_ sources consumed ?_⟩
  · simpa only [retained.localsEq, inputTypes] using emission
  · rw [cursor]

end Itasca.Runtime.Compiler

end

/-! ## Structured Reader Compiler Local -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.local_get {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (localsMatch : initial.function.locals = ctx.locals)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_LOCAL_GET)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_LOCAL_GET before = .ok (.Ok (), out, after)) :
    ∃ (localIndex : U32) (values : List code.StackType), StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.LOCAL_GET (.mk_uN localIndex.val))) savedParents
      (savedCurrent.advance (.plain (.LOCAL_GET (.mk_uN localIndex.val))) (.LOCAL_GET (.mk_uN localIndex.val)) savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  have currentLocals : before.function.locals = ctx.locals := state.compiled.metadata.fields.2.2.2.2.1.trans localsMatch
  cases reach : before.reachable with
  | true =>
    obtain ⟨localIndex, values, post, compiled⟩ := structured_reader_prefix_local_get_wasm2 p ops law initial before after out ctx rfl
      embedding state.compiled currentLocals reach sourceBound bodyBound byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨localIndex, values, post, compiled, dead⟩ := structured_reader_prefix_dead_local_get_wasm2 p ops law initial before after out ctx rfl
      state.compiled reach byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

theorem StructuredReaderCompilerStateWasm2.local_set {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (localsMatch : initial.function.locals = ctx.locals)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_LOCAL_SET)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_LOCAL_SET before = .ok (.Ok (), out, after)) :
    ∃ (localIndex : U32) (values : List code.StackType), StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.LOCAL_SET (.mk_uN localIndex.val))) savedParents
      (savedCurrent.advance (.plain (.LOCAL_SET (.mk_uN localIndex.val))) (.LOCAL_SET (.mk_uN localIndex.val)) savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  have currentLocals : before.function.locals = ctx.locals := state.compiled.metadata.fields.2.2.2.2.1.trans localsMatch
  cases reach : before.reachable with
  | true =>
    obtain ⟨localIndex, values, post, compiled⟩ := structured_reader_prefix_local_set_wasm2 p ops law initial before after out ctx rfl
      embedding state.compiled currentLocals reach (state.reach.current reach) sourceBound bodyBound byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨localIndex, values, post, compiled, dead⟩ := structured_reader_prefix_dead_local_set_wasm2 p ops law initial before after out ctx rfl
      state.compiled reach byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

theorem StructuredReaderCompilerStateWasm2.local_tee {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (localsMatch : initial.function.locals = ctx.locals)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_LOCAL_TEE)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_LOCAL_TEE before = .ok (.Ok (), out, after)) :
    ∃ (localIndex : U32) (values : List code.StackType), StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.LOCAL_TEE (.mk_uN localIndex.val))) savedParents
      (savedCurrent.advance (.plain (.LOCAL_TEE (.mk_uN localIndex.val))) (.LOCAL_TEE (.mk_uN localIndex.val)) savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  have currentLocals : before.function.locals = ctx.locals := state.compiled.metadata.fields.2.2.2.2.1.trans localsMatch
  cases reach : before.reachable with
  | true =>
    obtain ⟨localIndex, values, post, compiled⟩ := structured_reader_prefix_local_tee_wasm2 p ops law initial before after out ctx rfl
      embedding state.compiled currentLocals reach (state.reach.current reach) sourceBound bodyBound byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨localIndex, values, post, compiled, dead⟩ := structured_reader_prefix_dead_local_tee_wasm2 p ops law initial before after out ctx rfl
      state.compiled reach byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

end Itasca.Runtime.Compiler

end
