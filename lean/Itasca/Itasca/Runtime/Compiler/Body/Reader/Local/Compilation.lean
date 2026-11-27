import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Runtime.Compiler.Local.Relations.Stacks.ConcretePops
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEffects
import Itasca.Runtime.Compiler.Body.Control.StructuredPrefixes
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.Compiler.Body.Control.CompiledBody
import Itasca.Runtime.Compiler.Local.Source.TypedRunClosed
import Itasca.Visitor.BodyReplay
import Itasca.Visitor.RunTrace
import Itasca.Runtime.Compiler.Body.Reader.Safety.Run
import Itasca.Runtime.Compiler.Body.Relations.CallbackReadiness
import Itasca.Runtime.Compiler.Local.Relations.Local.LocalSafety
import Itasca.Body.Scalar.Env

open WebAssembly

/-!
Proofs for Runtime / Compiler / Body / Reader / Local.

This module collects Compilation, LocalSafety.
Each section documents its contracts and consumers.
-/

/-! ## Compilation -/

section

/-!
Live and dormant local get/set/tee prefixes and their structured compiler-state composition.
-/

/-! ## Structured Reader Prefix Dead Local -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_dead_local_get {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_GET)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_LOCAL_GET before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      Body.ReaderPost p out.core (.LOCAL_GET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.LOCAL_GET (.mk_uN idx.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_LOCAL_GET before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨idx, values, callback, read, post⟩ := reader_local_get p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity (by simpa only [global_simps] using byte) run
  obtain ⟨ty, _, vals⟩ := reader_local_get_effect st.core out.core data ⟨sourceLocals, p.ft.results⟩ idx capacity read
  refine ⟨idx, values, post, ?_⟩
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 32#u16 idx 0#u32 0#u128 = _ at callback
  exact post.structured_dead_op ops law invariant dead 32#u16 idx 0#u32 0#u128 callback

theorem structured_reader_prefix_dead_local_set {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_SET)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_LOCAL_SET before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      Body.ReaderPost p out.core (.LOCAL_SET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.LOCAL_SET (.mk_uN idx.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_LOCAL_SET before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨idx, values, callback, read, post⟩ := reader_local_set p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core (by simpa only [global_simps] using byte) run
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  refine ⟨idx, values, post, ?_⟩
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 33#u16 idx 0#u32 0#u128 = _ at callback
  exact post.structured_dead_op ops law invariant dead 33#u16 idx 0#u32 0#u128 callback

theorem structured_reader_prefix_dead_local_tee {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_TEE)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_LOCAL_TEE before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      Body.ReaderPost p out.core (.LOCAL_TEE (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.LOCAL_TEE (.mk_uN idx.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_LOCAL_TEE before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨idx, values, callback, read, post⟩ := reader_local_tee p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity (by simpa only [global_simps] using byte) run
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  refine ⟨idx, values, post, ?_⟩
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 34#u16 idx 0#u32 0#u128 = _ at callback
  exact post.structured_dead_op ops law invariant dead 34#u16 idx 0#u32 0#u128 callback

end Itasca.Compiler

end

/-! ## Structured Reader Prefix Local -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_local_get {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
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
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_LOCAL_GET before = .ok (.Ok (), out, after)) :
    ∃ (localIndex : U32) (values : List code.StackType),
      Body.ReaderPost p out.core ((.LOCAL_GET (.mk_uN localIndex.val))) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance ((.LOCAL_GET (.mk_uN localIndex.val))))
        out.core.vals.val out.core.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨rawTypes, concrete⟩ := (concrete_stack_iff _).mp (invariant.known reachable)
  have decoded := (SourceStack.of_map rawTypes concrete rfl).decoded
  have layout : CompilerLayout before (rawTypes.map Translation.valueType) := decoded ▸ retained.layout
  have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
  have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  obtain ⟨ordinary, sources, cursor, localIndex, localType, values, found, post, emitted, lower, emission⟩ :=
    reader_emit_local_get p ops law before after out ctx contextLocals localsMatch rawTypes concrete layout reachable
      codeFits sourceFits coordinateFits (by simpa only [global_simps] using byte) accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨localIndex, values, post, invariant.ordinary_linear embedding reachable ordinary lower ?_ sources consumed ?_⟩
  · simpa only [retained.localsEq, decoded] using emission
  · rw [cursor]

theorem structured_reader_prefix_local_set {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
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
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (code.OP_LOCAL_SET) before = .ok (.Ok (), out, after)) :
    ∃ (localIndex : U32) (values : List code.StackType),
      Body.ReaderPost p out.core (.LOCAL_SET (.mk_uN localIndex.val)) p.current.ctrl.polymorphic_base values ∧
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
    reader_emit_local_set p ops law before after out ctx contextLocals localsMatch (invariant.known reachable) monomorphic retained.layout reachable
      codeFits sourceFits coordinateFits (by simpa only [global_simps] using byte) accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨localIndex, values, post, invariant.ordinary_linear embedding reachable ordinary lower ?_ sources consumed ?_⟩
  · simpa only [retained.localsEq, inputTypes] using emission
  · rw [cursor]

theorem structured_reader_prefix_local_tee {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
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
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (code.OP_LOCAL_TEE) before = .ok (.Ok (), out, after)) :
    ∃ (localIndex : U32) (values : List code.StackType),
      Body.ReaderPost p out.core (.LOCAL_TEE (.mk_uN localIndex.val)) p.current.ctrl.polymorphic_base values ∧
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
    reader_emit_local_tee p ops law before after out ctx contextLocals localsMatch (invariant.known reachable) monomorphic retained.layout reachable
      codeFits sourceFits coordinateFits (by simpa only [global_simps] using byte) accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨localIndex, values, post, invariant.ordinary_linear embedding reachable ordinary lower ?_ sources consumed ?_⟩
  · simpa only [retained.localsEq, inputTypes] using emission
  · rw [cursor]

end Itasca.Compiler

end

/-! ## Structured Reader Compiler Local -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerState.local_get {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (localsMatch : initial.function.locals = ctx.locals)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_LOCAL_GET)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index code.OP_LOCAL_GET before = .ok (.Ok (), out, after)) :
    ∃ (localIndex : U32) (values : List code.StackType), StructuredReaderCompilerState jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.LOCAL_GET (.mk_uN localIndex.val))) savedParents
      (savedCurrent.advance (.plain (.LOCAL_GET (.mk_uN localIndex.val))) (.LOCAL_GET (.mk_uN localIndex.val)) savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  have currentLocals : before.function.locals = ctx.locals := state.compiled.metadata.fields.2.2.2.2.1.trans localsMatch
  cases reach : before.reachable with
  | true =>
    obtain ⟨localIndex, values, post, compiled⟩ := structured_reader_prefix_local_get p ops law initial before after out ctx rfl
      embedding state.compiled currentLocals reach sourceBound bodyBound byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨localIndex, values, post, compiled, dead⟩ := structured_reader_prefix_dead_local_get p ops law initial before after out ctx rfl
      state.compiled reach byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

theorem StructuredReaderCompilerState.local_set {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (localsMatch : initial.function.locals = ctx.locals)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_LOCAL_SET)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index code.OP_LOCAL_SET before = .ok (.Ok (), out, after)) :
    ∃ (localIndex : U32) (values : List code.StackType), StructuredReaderCompilerState jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.LOCAL_SET (.mk_uN localIndex.val))) savedParents
      (savedCurrent.advance (.plain (.LOCAL_SET (.mk_uN localIndex.val))) (.LOCAL_SET (.mk_uN localIndex.val)) savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  have currentLocals : before.function.locals = ctx.locals := state.compiled.metadata.fields.2.2.2.2.1.trans localsMatch
  cases reach : before.reachable with
  | true =>
    obtain ⟨localIndex, values, post, compiled⟩ := structured_reader_prefix_local_set p ops law initial before after out ctx rfl
      embedding state.compiled currentLocals reach (state.reach.current reach) sourceBound bodyBound byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨localIndex, values, post, compiled, dead⟩ := structured_reader_prefix_dead_local_set p ops law initial before after out ctx rfl
      state.compiled reach byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

theorem StructuredReaderCompilerState.local_tee {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (localsMatch : initial.function.locals = ctx.locals)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_LOCAL_TEE)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index code.OP_LOCAL_TEE before = .ok (.Ok (), out, after)) :
    ∃ (localIndex : U32) (values : List code.StackType), StructuredReaderCompilerState jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.LOCAL_TEE (.mk_uN localIndex.val))) savedParents
      (savedCurrent.advance (.plain (.LOCAL_TEE (.mk_uN localIndex.val))) (.LOCAL_TEE (.mk_uN localIndex.val)) savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  have currentLocals : before.function.locals = ctx.locals := state.compiled.metadata.fields.2.2.2.2.1.trans localsMatch
  cases reach : before.reachable with
  | true =>
    obtain ⟨localIndex, values, post, compiled⟩ := structured_reader_prefix_local_tee p ops law initial before after out ctx rfl
      embedding state.compiled currentLocals reach (state.reach.current reach) sourceBound bodyBound byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨localIndex, values, post, compiled, dead⟩ := structured_reader_prefix_dead_local_tee p ops law initial before after out ctx rfl
      state.compiled reach byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

end Itasca.Compiler

end

end

/-! ## LocalSafety -/

section

/-!
Local-index bounds and normal return of local get/set/tee reader callbacks.
-/

/-! ## Reader Local Bounds -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Successful local parsing checks the namespace before the compiler callback,
including unreachable stacks and without assuming successful compilation. -/
theorem reader_local_get_bound (st out : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (index : U32) (accepted : code.read_local_get st data ctx = .ok (.Ok index,out)) :
    index.val < ctx.locals.val.length := by
  obtain ⟨⟨result,state⟩,read,values,controls,post⟩ := WP.spec_imp_exists (code.take_local.spec st data ctx)
  dsimp only at post
  cases result with
  | Err error => simp [code.read_local_get,read,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨idx,ty⟩ := pair
    simp only [code.read_local_get,read,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at accepted
    obtain ⟨next,pushed,tail⟩ := Computation.bind_ok_inv _ _ _ accepted
    simp only [Result.ok.injEq,Prod.mk.injEq,core.result.Result.Ok.injEq] at tail
    obtain ⟨rfl,rfl⟩ := tail
    exact post.2.choose

theorem reader_local_set_bound (st out : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (index : U32) (accepted : code.read_local_set st data ctx = .ok (.Ok index,out)) :
    index.val < ctx.locals.val.length := by
  obtain ⟨⟨result,state⟩,read,values,controls,post⟩ := WP.spec_imp_exists (code.take_local.spec st data ctx)
  dsimp only at post
  cases result with
  | Err error => simp [code.read_local_set,read,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨idx,ty⟩ := pair
    simp only [code.read_local_set,read,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at accepted
    obtain ⟨⟨reply,next⟩,popped,tail⟩ := Computation.bind_ok_inv _ _ _ accepted
    simp only [Std.uncurry] at tail
    cases reply with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
    | Ok value =>
      simp [core.result.Result.Insts.CoreOpsTry.branch] at tail
      obtain ⟨rfl,rfl⟩ := tail
      exact post.2.choose

theorem reader_local_tee_bound (st out : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (index : U32) (accepted : code.read_local_tee st data ctx = .ok (.Ok index,out)) :
    index.val < ctx.locals.val.length := by
  obtain ⟨⟨result,state⟩,read,values,controls,post⟩ := WP.spec_imp_exists (code.take_local.spec st data ctx)
  dsimp only at post
  cases result with
  | Err error => simp [code.read_local_tee,read,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨idx,ty⟩ := pair
    simp only [code.read_local_tee,read,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at accepted
    obtain ⟨⟨reply,next⟩,popped,tail⟩ := Computation.bind_ok_inv _ _ _ accepted
    simp only [Std.uncurry] at tail
    cases reply with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at tail
      obtain ⟨final,pushed,tail⟩ := Computation.bind_ok_inv _ _ _ tail
      simp only [Result.ok.injEq,Prod.mk.injEq,core.result.Result.Ok.injEq] at tail
      obtain ⟨rfl,rfl⟩ := tail
      exact post.2.choose
end Itasca.Compiler

end

/-! ## Reader Local Safety -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual local.get dispatch returns normally on parsing rejection as well as
compiler rejection; accepted reads supply their checked local index. -/
theorem compiler_reader_local_get_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_GET compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_local_get.dispatch]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Body.ScalarReaders.local_get st data ctx shape capacity) (by simp)
  · intro state index read
    have bound := reader_local_get_bound st state data ctx index read
    exact compiler_local_get_total ops law compiler state index
      (by simpa [ready.namespaces.offsets] using bound)
      (by simpa [ready.namespaces.locals] using bound)
      ready.codeFits ready.sourceFits ready.coordinateFits

/-- Actual local.set dispatch returns normally on parsing rejection as well as
compiler rejection; accepted reads supply their checked local index. -/
theorem compiler_reader_local_set_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_SET compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_local_set.dispatch]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Body.ScalarReaders.local_set st data ctx shape capacity) (by simp)
  · intro state index read
    have bound := reader_local_set_bound st state data ctx index read
    exact compiler_local_write_total ops law compiler state index false
      (by simpa [ready.namespaces.offsets] using bound)
      (by simpa [ready.namespaces.locals] using bound)
      ready.codeFits ready.sourceFits ready.coordinateFits

/-- Actual local.tee dispatch returns normally on parsing rejection as well as
compiler rejection; accepted reads supply their checked local index. -/
theorem compiler_reader_local_tee_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_TEE compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_local_tee.dispatch]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Body.ScalarReaders.local_tee st data ctx shape capacity) (by simp)
  · intro state index read
    have bound := reader_local_tee_bound st state data ctx index read
    exact compiler_local_write_total ops law compiler state index true
      (by simpa [ready.namespaces.offsets] using bound)
      (by simpa [ready.namespaces.locals] using bound)
      ready.codeFits ready.sourceFits ready.coordinateFits
end Itasca.Compiler

end

end
