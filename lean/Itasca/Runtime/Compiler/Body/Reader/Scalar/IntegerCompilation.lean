import Itasca.Runtime.Compiler.Body.Reader.Replay.DormantOperation
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownNumericStack
import Itasca.Runtime.Compiler.Body.Reader.Scalar.IntegerFacts
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefix
import Itasca.Runtime.Compiler.Body.Reader.Scalar.NumericEmissions
import Itasca.Runtime.Compiler.Body.Reader.Replay.Span
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredLinearEmbedding
import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefix
import Itasca.Runtime.Compiler.Body.Reader.Scalar.SignEmissions
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerDeadMetadata
import Itasca.Runtime.Compiler.Local.Source.SourceCursor
import Itasca.Runtime.Compiler.Local.Relations.Operations.DeadCode
import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileAgreement
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownPopStack
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericEncoding
import Itasca.Runtime.Compiler.Body.Reader.Scalar.SignExtension
import Itasca.Runtime.Compiler.Body.Reader.Replay.StructuredState

/-!
Live/dormant integer-operation prefixes, including sign extension, and their structured compiler-state composition.
-/

/-! ## Structured Reader Prefix Dead Numeric -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_dead_numeric_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (op : Abs.Numeric.Instruction) (standard : (integerOpcode op).val < 192)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    ∃ values,
      ReaderPostWasm2 p out.core op.source p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance op.source)
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨operation, hook, meaning, handler, instruction, inputs, output,
    hookEq, ordinary, baseOpcode, sign, misc⟩ := integer_reader_facts ops before out.core op standard
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index _ before after ordinary baseOpcode sign misc contextLocals accepted
  obtain ⟨callback, read, _, _, values, effect, post⟩ := reader_numeric_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ operation hook
    capacity byte meaning handler run
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  have physicalBase : (Control.base st.core).val = outer.length := by
    simpa [Control.base, controls] using base
  rw [instruction] at post
  rw [hookEq] at callback
  exact ⟨values, post, post.structured_dead_op ops law invariant dead (integerOpcode op) 0#u32 0#u32 0#u128 callback⟩

end Itasca.Runtime.Code

end

/-! ## Structured Reader Prefix Numeric -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_numeric_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (embedding : LinearEmbedding locals emit)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (op : Abs.Numeric.Instruction) (baseOpcode : (integerOpcode op).val < 192)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    ∃ values,
      ReaderPostWasm2 p out.core op.source p.current.ctrl.polymorphic_base values ∧
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
    reader_emit_numeric_wasm2 p ops law before after out ctx contextLocals op baseOpcode (invariant.known reachable) monomorphic retained.layout reachable
      codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨values, post, invariant.ordinary_linear embedding reachable ordinary lower ?_ sources consumed ?_⟩
  · simpa only [retained.localsEq, inputTypes] using emission
  · rw [cursor]

end Itasca.Runtime.Code

end

/-! ## Structured Reader Prefix Sign -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_sign_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (embedding : LinearEmbedding locals emit)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (op : Abs.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    ∃ values,
      ReaderPostWasm2 p out.core op.source p.current.ctrl.polymorphic_base values ∧
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
    reader_emit_sign_wasm2 p ops law before after out ctx contextLocals op extension (invariant.known reachable) monomorphic retained.layout reachable
      codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨values, post, invariant.ordinary_linear embedding reachable ordinary lower ?_ sources consumed ?_⟩
  · simpa only [retained.localsEq, inputTypes] using emission
  · rw [cursor]

theorem structured_reader_prefix_dead_sign_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (op : Abs.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    ∃ values,
      ReaderPostWasm2 p out.core op.source p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance op.source)
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨operation, instruction, inputs, output, callback, read, converted,
    ctrlsEq, position, values, effect, post⟩ :=
    reader_integer_sign_wasm2 p ops before after out ctx op extension byte accepted
  obtain ⟨_, _, _, _, _, _, _, _, ordinary, _⟩ := integer_sign_reader_facts ops before out.core op extension
  have capacity := (profile_scalar_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index _ before after ordinary accepted).1
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  have physicalBase : (Control.base st.core).val = outer.length := by
    simpa [Control.base, controls] using base
  exact ⟨values, post, post.structured_dead_op ops law invariant dead (integerOpcode op) 0#u32 0#u32 0#u128 callback⟩

end Itasca.Runtime.Code

end

/-! ## Structured Reader Compiler Numeric -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.numeric {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (op : Abs.Numeric.Instruction) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = (UScalar.cast .U8 (integerOpcode op)))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    ∃ values, StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance op.source) savedParents
      (savedCurrent.advance (.plain op.source) op.source
        savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    by_cases standard : (integerOpcode op).val < 192
    · obtain ⟨values, post, compiled⟩ := structured_reader_prefix_numeric_wasm2 p ops law initial before after out ctx rfl
        embedding state.compiled reach (state.reach.current reach) op standard sourceBound bodyBound byte accepted
      exact ⟨values, state.advance next advance inbounds post (integer_source_declared op _) compiled (fun _ => state.reach.current reach)⟩
    · obtain ⟨values, post, compiled⟩ := structured_reader_prefix_sign_wasm2 p ops law initial before after out ctx rfl
        embedding state.compiled reach (state.reach.current reach) op (by omega) sourceBound bodyBound byte accepted
      exact ⟨values, state.advance next advance inbounds post (integer_source_declared op _) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    by_cases standard : (integerOpcode op).val < 192
    · obtain ⟨values, post, compiled, dead⟩ := structured_reader_prefix_dead_numeric_wasm2 p ops law initial before after out ctx rfl
        state.compiled reach op standard byte accepted
      exact ⟨values, state.advance next advance inbounds post (integer_source_declared op _) compiled (by simp [dead])⟩
    · obtain ⟨values, post, compiled, dead⟩ := structured_reader_prefix_dead_sign_wasm2 p ops law initial before after out ctx rfl
        state.compiled reach op (by omega) byte accepted
      exact ⟨values, state.advance next advance inbounds post (integer_source_declared op _) compiled (by simp [dead])⟩

end Itasca.Runtime.Code

end
