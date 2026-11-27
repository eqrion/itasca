import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Runtime.Compiler.Local.Relations.Stacks.ConcretePops
import Itasca.Runtime.Compiler.Body.Reader.Float.FloatConstantEmissions
import Itasca.Runtime.Compiler.Local.Control.Structured.Prefixes
import Itasca.Runtime.Compiler.Body.Control.BranchesAndDormantEntry
import Itasca.Runtime.Compiler.Body.Control.StructuredPrefixes
import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.Compiler.Body.Control.CompiledBody
import Itasca.Runtime.Compiler.Local.Lowering.Float.LoweringAndEffects
import Itasca.Runtime.Compiler.Body.Reader.Scalar.ScalarEffects
import Itasca.Runtime.Compiler.Local.Callbacks.CallbackEquations

open WebAssembly

/-!
Proofs for Runtime / Compiler / Body / Reader / Float.

This module collects SaturatingCompilation, ConstantPrefix.
Each section documents its contracts and consumers.
-/

/-! ## SaturatingCompilation -/

section

/-! ## Compilation -/

section

/-!
Floating-point operation compilation through live and dormant structured reader prefixes.
-/

/-! ## Structured Reader Prefix Dead Float -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_dead_float {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (op : SourceMachine.Float.Instruction) (standard : (floatOpcode op).val < 256)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (floatOpcode op))
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (), out, after)) :
    ∃ values,
      Body.ReaderPost p out.core op.source p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance op.source)
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨operation, hook, meaning, handler, instruction, inputs, output,
    hookEq, ordinary, baseOpcode, sign, misc⟩ := float_reader_facts ops before out.core op standard
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
  exact ⟨values, post, post.structured_dead_op ops law invariant dead (floatOpcode op) 0#u32 0#u32 0#u128 callback⟩

end Itasca.Compiler

end

/-! ## Structured Reader Prefix Float -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_float {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (C : context) {emit} [ScalarEmbedding C emit] {types functions returns locals parents current}
    (contextCodeLocals : C.LOCALS = locals)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (op : SourceMachine.Float.Instruction) (baseOpcode : (floatOpcode op).val < 256)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (floatOpcode op))
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (), out, after)) :
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
    reader_emit_float p ops law before after out ctx contextLocals op C (contextCodeLocals.trans retained.localsEq.symm) baseOpcode (invariant.known reachable) monomorphic retained.layout reachable
      codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨values, post, invariant.ordinary reachable ordinary lower ?_ sources consumed ?_ emission.not_branch_table⟩
  · simpa only [inputTypes] using (ScalarEmbedding.lift emission)
  · rw [cursor]

end Itasca.Compiler

end

/-! ## Structured Reader Compiler Float -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerState.float_base {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) (contextCodeLocals : C.LOCALS = locals) {emit} [ScalarEmbedding C emit]
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (op : SourceMachine.Float.Instruction) (baseOpcode : (floatOpcode op).val < 256) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = (UScalar.cast .U8 (floatOpcode op)))
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (), out, after)) :
    ∃ values, StructuredReaderCompilerState jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance op.source) savedParents
      (savedCurrent.advance (.plain op.source) op.source
        savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨values, post, compiled⟩ := structured_reader_prefix_float p ops law initial before after out ctx rfl
      C contextCodeLocals state.compiled reach (state.reach.current reach) op baseOpcode sourceBound bodyBound byte accepted
    exact ⟨values, state.advance next advance inbounds post (float_source_declared op _) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨values, post, compiled, dead⟩ := structured_reader_prefix_dead_float p ops law initial before after out ctx rfl
      state.compiled reach op baseOpcode byte accepted
    exact ⟨values, state.advance next advance inbounds post (float_source_declared op _) compiled (by simp [dead])⟩

end Itasca.Compiler

end

end

/-! ## SaturatingCompilation -/

section

/-!
Live/dormant saturating-conversion prefixes and their structured compiler-state composition.
-/

/-! ## Structured Reader Prefix Dead Saturating -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_dead_saturating {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (op : SourceMachine.Float.Instruction) (extension : 256 ≤ (floatOpcode op).val)
    (subopcode : U32) (next : Usize)
    (subopcodeEq : subopcode.val = (floatOpcode op).val - 256)
    (decoded : Binary.Leb128.Decoded data st.core.pos subopcode next)
    (byte : data.val[p.start.val]'p.inbounds = 0xfc#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (0xfc#u8) before = .ok (.Ok (), out, after)) :
    ∃ values,
      Body.ReaderPost p out.core op.source p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance op.source)
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨operation,instruction,inputs,output,callback,_,_,_,_,values,effect,post⟩ :=
    reader_float_saturating p ops before after out ctx op extension subopcode next subopcodeEq decoded byte accepted
  exact ⟨values, post, post.structured_dead_op ops law invariant dead (floatOpcode op) 0#u32 0#u32 0#u128 callback⟩

end Itasca.Compiler

end

/-! ## Structured Reader Prefix Saturating -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_saturating {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (C : context) {emit} [ScalarEmbedding C emit] {types functions returns locals parents current}
    (contextCodeLocals : C.LOCALS = locals)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (op : SourceMachine.Float.Instruction) (extension : 256 ≤ (floatOpcode op).val)
    (subopcode : U32) (next : Usize)
    (subopcodeEq : subopcode.val = (floatOpcode op).val - 256)
    (decoded : Binary.Leb128.Decoded data st.core.pos subopcode next)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 0xfc#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (0xfc#u8) before = .ok (.Ok (), out, after)) :
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
    reader_emit_saturating p ops law before after out ctx contextLocals op C (contextCodeLocals.trans retained.localsEq.symm) extension subopcode next subopcodeEq decoded (invariant.known reachable) monomorphic retained.layout reachable
      codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨values, post, invariant.ordinary reachable ordinary lower ?_ sources consumed ?_ emission.not_branch_table⟩
  · simpa only [inputTypes] using (ScalarEmbedding.lift emission)
  · rw [cursor]

end Itasca.Compiler

end

/-! ## Structured Reader Compiler Saturating -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerState.float_saturating {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) (contextCodeLocals : C.LOCALS = locals) {emit} [ScalarEmbedding C emit]
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (op : SourceMachine.Float.Instruction) (extension : 256 ≤ (floatOpcode op).val)
    (subopcode : U32) (endPosition : Usize)
    (subopcodeEq : subopcode.val = (floatOpcode op).val - 256)
    (decoded : Binary.Leb128.Decoded data next subopcode endPosition)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 252#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index 252#u8 before = .ok (.Ok (), out, after)) :
    ∃ values, StructuredReaderCompilerState jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance op.source) savedParents
      (savedCurrent.advance (.plain op.source) op.source
        savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨values, post, compiled⟩ := structured_reader_prefix_saturating p ops law initial before after out ctx rfl
      C contextCodeLocals state.compiled reach (state.reach.current reach) op extension subopcode endPosition subopcodeEq decoded sourceBound bodyBound byte accepted
    exact ⟨values, state.advance next advance inbounds post (float_source_declared op _) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨values, post, compiled, dead⟩ := structured_reader_prefix_dead_saturating p ops law initial before after out ctx rfl
      state.compiled reach op extension subopcode endPosition subopcodeEq decoded byte accepted
    exact ⟨values, state.advance next advance inbounds post (float_source_declared op _) compiled (by simp [dead])⟩

end Itasca.Compiler

end

end

end

/-! ## ConstantPrefix -/

section

/-!
Live and dormant floating-point constant prefixes and their compiler-state composition, used by whole-reader compilation.
-/

/-! ## Reader Float Constant Dead -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
theorem reader_prefix_dead_float32 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F32_CONST)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_F32_CONST before = .ok (.Ok (), out, after)) :
    ∃ value,
      Body.ReaderPost p out.core (Spec.Constants.f32 value) p.current.ctrl.polymorphic_base (p.current.vals ++ [.Val .F32]) ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (Spec.Constants.f32 value))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_F32_CONST before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, callback, read, values, post⟩ := reader_f32_const p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  refine ⟨value, post, ?_⟩
  apply post.structured_dead_op ops law invariant dead 67#u16 0#u32 0#u32 (UScalar.cast .U128 value)
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const ops before out.core value = _ at callback
  simpa only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const.eq, lift, bind_ok] using callback

theorem reader_prefix_dead_float64 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F64_CONST)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_F64_CONST before = .ok (.Ok (), out, after)) :
    ∃ value,
      Body.ReaderPost p out.core (Spec.Constants.f64 value) p.current.ctrl.polymorphic_base (p.current.vals ++ [.Val .F64]) ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (Spec.Constants.f64 value))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_F64_CONST before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, callback, read, values, post⟩ := reader_f64_const p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  refine ⟨value, post, ?_⟩
  apply post.structured_dead_op ops law invariant dead 68#u16 0#u32 0#u32 (UScalar.cast .U128 value)
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const ops before out.core value = _ at callback
  simpa only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const.eq, lift, bind_ok] using callback

end Itasca.Compiler

end

/-! ## Reader Float Constant Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_prefix_float32 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
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
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_F32_CONST before = .ok (.Ok (), out, after)) :
    ∃ value,
      Body.ReaderPost p out.core (Spec.Constants.f32 value) p.current.ctrl.polymorphic_base (p.current.vals ++ [.Val .F32]) ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (Spec.Constants.f32 value))
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
  obtain ⟨ordinary, sources, cursor, value, post, emitted, lower, emission⟩ :=
    reader_emit_float32 p ops law before after C (contextCodeLocals.trans retained.localsEq.symm) out ctx contextLocals rawTypes concrete layout reachable
      codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨value, post, invariant.ordinary reachable ordinary lower ?_ sources consumed ?_ emission.not_branch_table⟩
  · simpa only [decoded] using (ScalarEmbedding.lift (emit := emit) emission)
  · rw [cursor]

theorem reader_prefix_float64 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
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
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_F64_CONST before = .ok (.Ok (), out, after)) :
    ∃ value,
      Body.ReaderPost p out.core (Spec.Constants.f64 value) p.current.ctrl.polymorphic_base (p.current.vals ++ [.Val .F64]) ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (Spec.Constants.f64 value))
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
  obtain ⟨ordinary, sources, cursor, value, post, emitted, lower, emission⟩ :=
    reader_emit_float64 p ops law before after C (contextCodeLocals.trans retained.localsEq.symm) out ctx contextLocals rawTypes concrete layout reachable
      codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨value, post, invariant.ordinary reachable ordinary lower ?_ sources consumed ?_ emission.not_branch_table⟩
  · simpa only [decoded] using (ScalarEmbedding.lift (emit := emit) emission)
  · rw [cursor]

end Itasca.Compiler

end

/-! ## Reader Float Constant State -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
theorem StructuredReaderCompilerState.float32 {jumpTables : List U32} {A : Type}
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
    (byte : data.val[st.core.pos.val]'inbounds = 67#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index 67#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPoint jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨value, post, compiled⟩ := reader_prefix_float32 p ops law initial before after out ctx rfl C
      contextCodeLocals state.compiled live sourceBound bodyBound (by simpa only [p, ReaderBoundary.pending, global_simps] using byte) (by simpa only [code.OP_F32_CONST] using accepted)
    exact (state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices, Spec.Constants.f32]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨value, post, compiled, dead⟩ := reader_prefix_dead_float32 p ops law initial before after out ctx rfl
      state.compiled live (by simpa only [p, ReaderBoundary.pending, global_simps] using byte) (by simpa only [code.OP_F32_CONST] using accepted)
    exact (state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices, Spec.Constants.f32]) compiled (by simp [dead])).point

theorem StructuredReaderCompilerState.float64 {jumpTables : List U32} {A : Type}
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
    (byte : data.val[st.core.pos.val]'inbounds = 68#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index 68#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPoint jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨value, post, compiled⟩ := reader_prefix_float64 p ops law initial before after out ctx rfl C
      contextCodeLocals state.compiled live sourceBound bodyBound (by simpa only [p, ReaderBoundary.pending, global_simps] using byte) (by simpa only [code.OP_F64_CONST] using accepted)
    exact (state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices, Spec.Constants.f64]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨value, post, compiled, dead⟩ := reader_prefix_dead_float64 p ops law initial before after out ctx rfl
      state.compiled live (by simpa only [p, ReaderBoundary.pending, global_simps] using byte) (by simpa only [code.OP_F64_CONST] using accepted)
    exact (state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices, Spec.Constants.f64]) compiled (by simp [dead])).point

end Itasca.Compiler

end

end
