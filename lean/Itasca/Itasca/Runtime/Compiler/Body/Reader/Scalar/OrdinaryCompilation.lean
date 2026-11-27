import Itasca.Runtime.Compiler.Body.Control.StructuredPrefixes
import Itasca.Runtime.Compiler.Body.Reader.Scalar.ScalarEffects
import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.Compiler.Body.Control.CompiledBody
import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Runtime.Compiler.Body.Reader.Scalar.DeadBasicPrefix
import Itasca.Runtime.Compiler.Local.Relations.Syntax.ReaderOpcode
import Itasca.Runtime.Compiler.Local.Lowering.Integer.Lowering
import Itasca.Runtime.Compiler.Body.Callbacks.CompilerPrefixStart
import Itasca.Runtime.Compiler.Local.Callbacks.MetadataPreservation
import Itasca.Runtime.Compiler.Local.Source.SourceTactics
import Itasca.Runtime.Compiler.Local.Relations.Operations.CoreBasicEmissions
import Itasca.Runtime.Compiler.Local.Relations.Stacks.ConcretePops
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Local.Lowering.Literal.SourceEffects
import Itasca.Runtime.Compiler.Local.Lowering.LoweringLocal
import Itasca.Runtime.Compiler.Body.CapacityTrace
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEffects
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Body.Reader.Calls.Acceptance
import Itasca.Support.Translation
import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CallbackRetention
import Itasca.Runtime.Compiler.Local.Capacity.EmissionGrowth
import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchAndTerminalEffects
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Body.Reader.Control.StackPrefixes
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchAndScopeEffects
import Itasca.Runtime.Compiler.Body.Reader.Local.Compilation
import Itasca.Runtime.Compiler.Body.Reader.Calls.Safety
import Itasca.Runtime.Compiler.Body.Reader.Control.TerminalCompilationAndSafety

/-!
# Ordinary reader compilation

Empty and value-producing scalar reader cases preserve the compiler/source relation and complete the ordinary-instruction argument.
-/

/-! ## EmptyCompilation -/

section EmptyCompilation

/-! ## ConstantCompilation -/

section

/-!
Integer-constant source prefixes and their structured compiler-state composition.
-/

/-! ## Structured Reader Prefix Const -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_const32 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (embedding : LinearEmbedding locals emit)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I32_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_I32_CONST before = .ok (.Ok (), out, after)) :
    ∃ value,
      Body.ReaderPost p out.core (Spec.i32Const value) p.current.ctrl.polymorphic_base (p.current.vals ++ [.Val .I32]) ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (Spec.i32Const value))
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
    reader_emit_const32 p ops law before after out ctx contextLocals rawTypes concrete layout reachable
      codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨value, post, invariant.ordinary_linear embedding reachable ordinary lower ?_ sources consumed ?_⟩
  · simpa only [retained.localsEq, decoded] using emission
  · rw [cursor]

theorem structured_reader_prefix_const64 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (embedding : LinearEmbedding locals emit)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I64_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_I64_CONST before = .ok (.Ok (), out, after)) :
    ∃ value,
      Body.ReaderPost p out.core (Spec.Constants.i64 value) p.current.ctrl.polymorphic_base (p.current.vals ++ [.Val .I64]) ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (Spec.Constants.i64 value))
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
    reader_emit_const64 p ops law before after out ctx contextLocals rawTypes concrete layout reachable
      codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨value, post, invariant.ordinary_linear embedding reachable ordinary lower ?_ sources consumed ?_⟩
  · simpa only [retained.localsEq, decoded] using emission
  · rw [cursor]

end Itasca.Compiler

end

/-! ## Structured Reader Compiler Constants -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerState.const32 {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_I32_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index code.OP_I32_CONST before = .ok (.Ok (), out, after)) :
    ∃ value, StructuredReaderCompilerState jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (Spec.i32Const value)) savedParents
      (savedCurrent.advance (.plain (Spec.i32Const value)) (Spec.i32Const value)
        savedCurrent.ctrl.polymorphic_base (savedCurrent.vals ++ [.Val .I32])) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨value, post, compiled⟩ := structured_reader_prefix_const32 p ops law initial before after out ctx rfl
      embedding state.compiled reach sourceBound bodyBound byte accepted
    exact ⟨value, state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices, Spec.i32Const, Spec.Constants.i64]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨value, post, compiled, dead⟩ := structured_reader_prefix_dead_const32 p ops law initial before after out ctx rfl
      state.compiled reach byte accepted
    exact ⟨value, state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices, Spec.i32Const, Spec.Constants.i64]) compiled (by simp [dead])⟩

theorem StructuredReaderCompilerState.const64 {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_I64_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index code.OP_I64_CONST before = .ok (.Ok (), out, after)) :
    ∃ value, StructuredReaderCompilerState jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (Spec.Constants.i64 value)) savedParents
      (savedCurrent.advance (.plain (Spec.Constants.i64 value)) (Spec.Constants.i64 value)
        savedCurrent.ctrl.polymorphic_base (savedCurrent.vals ++ [.Val .I64])) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨value, post, compiled⟩ := structured_reader_prefix_const64 p ops law initial before after out ctx rfl
      embedding state.compiled reach sourceBound bodyBound byte accepted
    exact ⟨value, state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices, Spec.i32Const, Spec.Constants.i64]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨value, post, compiled, dead⟩ := structured_reader_prefix_dead_const64 p ops law initial before after out ctx rfl
      state.compiled reach byte accepted
    exact ⟨value, state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices, Spec.i32Const, Spec.Constants.i64]) compiled (by simp [dead])⟩

end Itasca.Compiler

end

end

/-! ## EmptyCompilation -/

section

/-!
Nop/drop source prefixes and their structured compiler-state composition.
-/

/-! ## Structured Reader Prefix Empty -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_nop {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (embedding : LinearEmbedding locals emit)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_NOP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_NOP before = .ok (.Ok (), out, after)) :
    Body.ReaderPost p out.core .NOP p.current.ctrl.polymorphic_base p.current.vals ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance .NOP)
        out.core.vals.val out.core.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨rawTypes, concrete⟩ := (concrete_stack_iff _).mp (invariant.known reachable)
  have decoded := (SourceStack.of_map rawTypes concrete rfl).decoded
  have layout : CompilerLayout before (rawTypes.map Translation.valueType) := decoded ▸ retained.layout
  obtain ⟨ordinary, sources, cursor, post, lower, emission⟩ :=
    reader_emit_nop p ops law before after out ctx contextLocals rawTypes concrete layout byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨post, invariant.ordinary_empty_linear embedding reachable ordinary lower ?_ sources consumed ?_⟩
  · simpa only [retained.localsEq, decoded] using emission
  · rw [cursor]

theorem structured_reader_prefix_drop {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (embedding : LinearEmbedding locals emit)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_DROP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_DROP before = .ok (.Ok (), out, after)) :
    ∃ values,
      Body.ReaderPost p out.core .DROP p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance .DROP)
        out.core.vals.val out.core.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨ordinary, sources, cursor, front, ty, values, inputTypes, post, lower, emission⟩ :=
    reader_emit_drop p ops law before after out ctx contextLocals (invariant.known reachable) monomorphic retained.layout
      byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨values, post, invariant.ordinary_empty_linear embedding reachable ordinary lower ?_ sources consumed ?_⟩
  · simpa only [retained.localsEq, inputTypes] using emission
  · rw [cursor]

end Itasca.Compiler

end

/-! ## Structured Reader Compiler Empty -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerState.nop {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_NOP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index code.OP_NOP before = .ok (.Ok (), out, after)) :
    ∃ values, StructuredReaderCompilerState jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.NOP)) savedParents
      (savedCurrent.advance (.plain (.NOP)) (.NOP) savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨post, compiled⟩ := structured_reader_prefix_nop p ops law initial before after out ctx rfl
      embedding state.compiled reach byte accepted
    exact ⟨savedCurrent.vals, state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨post, compiled, dead⟩ := structured_reader_prefix_dead_nop p ops law initial before after out ctx rfl
      state.compiled reach byte accepted
    exact ⟨savedCurrent.vals, state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

theorem StructuredReaderCompilerState.drop {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_DROP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index code.OP_DROP before = .ok (.Ok (), out, after)) :
    ∃ values, StructuredReaderCompilerState jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.DROP)) savedParents
      (savedCurrent.advance (.plain (.DROP)) (.DROP) savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨values, post, compiled⟩ := structured_reader_prefix_drop p ops law initial before after out ctx rfl
      embedding state.compiled reach (state.reach.current reach) byte accepted
    exact ⟨values, state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨values, post, compiled, dead⟩ := structured_reader_prefix_dead_drop p ops law initial before after out ctx rfl
      state.compiled reach byte accepted
    exact ⟨values, state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

end Itasca.Compiler

end

end

end EmptyCompilation

/-! ## OrdinaryCompilation -/

section OrdinaryCompilation

/-!
Actual accepted ordinary dispatch preserves the retained compiler/source point. All opcode-specific stack and callback facts are derived internally.

Main declarations: `StructuredReaderCompilerState.ordinary_base` and `StructuredReaderCompilerPoint.ordinary`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
/-- Actual accepted ordinary dispatch preserves the retained compiler/source
point. All opcode-specific stack and callback facts are derived internally. -/
theorem StructuredReaderCompilerState.ordinary_base {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerState jumpTables emit initial before types (env.func_types.val.map Translation.Environment.funcType) (ft.results.val.map Translation.valueType) locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (metadata : FunctionParameterSlots initial env)
    (localsMatch : initial.function.locals = ctx.locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (opcode : U8) (ordinary : opcode ∈ readerBaseOrdinaryOpcodes)
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index opcode before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPoint jumpTables emit initial after types (env.func_types.val.map Translation.Environment.funcType) (ft.results.val.map Translation.valueType) locals data env ctx.locals index ft out := by
  simp only [readerBaseOrdinaryOpcodes, List.mem_cons, List.mem_nil_iff, or_false] at ordinary
  rcases ordinary with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (state.unreachable ops law next advance inbounds out (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)).point
  · obtain ⟨_, changed⟩ := state.nop ops law embedding next advance inbounds out (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · exact (state.return_ ops law next advance inbounds out sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)).point
  · obtain ⟨_, _, changed⟩ := state.call ops law metadata next advance inbounds out sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, changed⟩ := state.drop ops law embedding next advance inbounds out (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, _, changed⟩ := state.local_get ops law embedding next advance inbounds out localsMatch sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, _, changed⟩ := state.local_set ops law embedding next advance inbounds out localsMatch sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, _, changed⟩ := state.local_tee ops law embedding next advance inbounds out localsMatch sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, changed⟩ := state.const32 ops law embedding next advance inbounds out sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, changed⟩ := state.const64 ops law embedding next advance inbounds out sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.eqz .I32)) = 69#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.eqz .I32) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.compare .I32 .EQ)) = 70#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.compare .I32 .EQ) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.compare .I32 (.LT .U))) = 73#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.compare .I32 (.LT .U)) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.eqz .I64)) = 80#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.eqz .I64) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.compare .I64 .EQ)) = 81#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.compare .I64 .EQ) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.compare .I64 (.LT .U))) = 84#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.compare .I64 (.LT .U)) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.binary .I32 .ADD)) = 106#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.binary .I32 .ADD) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.binary .I32 .SUB)) = 107#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.binary .I32 .SUB) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.binary .I64 .ADD)) = 124#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.binary .I64 .ADD) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.binary .I64 .SUB)) = 125#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.binary .I64 .SUB) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point

theorem StructuredReaderCompilerState.ordinary {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerState jumpTables emit initial before types (env.func_types.val.map Translation.Environment.funcType) (ft.results.val.map Translation.valueType) locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (metadata : FunctionParameterSlots initial env)
    (localsMatch : initial.function.locals = ctx.locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (opcode : U8) (ordinary : opcode ∈ readerOrdinaryOpcodes)
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index opcode before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPoint jumpTables emit initial after types (env.func_types.val.map Translation.Environment.funcType) (ft.results.val.map Translation.valueType) locals data env ctx.locals index ft out := by
  rcases List.mem_append.mp ordinary with base | numeric
  · exact state.ordinary_base ops law embedding metadata localsMatch next advance inbounds out sourceBound bodyBound opcode base byte accepted
  · obtain ⟨op, rfl⟩ := integer_opcode_of_mem numeric
    obtain ⟨values, changed⟩ := state.numeric ops law embedding next advance inbounds out op sourceBound bodyBound byte accepted
    exact changed.point

theorem StructuredReaderCompilerPoint.ordinary {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types locals data env ctx index ft st}
    (embedding : LinearEmbedding locals emit)
    (point : StructuredReaderCompilerPoint jumpTables emit initial before types (env.func_types.val.map Translation.Environment.funcType) (ft.results.val.map Translation.valueType) locals data env ctx.locals index ft st)
    (metadata : FunctionParameterSlots initial env)
    (localsMatch : initial.function.locals = ctx.locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (opcode : U8) (ordinary : opcode ∈ readerOrdinaryOpcodes)
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index opcode before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPoint jumpTables emit initial after types (env.func_types.val.map Translation.Environment.funcType) (ft.results.val.map Translation.valueType) locals data env ctx.locals index ft out := by
  obtain ⟨parents, current, savedParents, savedCurrent, state⟩ := point
  exact state.ordinary ops law embedding metadata localsMatch next advance inbounds out sourceBound bodyBound opcode ordinary byte accepted
end Itasca.Compiler

end OrdinaryCompilation
