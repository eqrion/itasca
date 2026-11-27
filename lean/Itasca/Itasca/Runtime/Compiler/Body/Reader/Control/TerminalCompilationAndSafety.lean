import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchContracts
import Itasca.Runtime.Compiler.Body.Control.BranchesAndDormantEntry
import Itasca.Runtime.Compiler.Local.Callbacks.MetadataPreservation
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CallbackRetention
import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchAndTerminalEffects
import Itasca.Runtime.Compiler.Local.Capacity.EmissionGrowth
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Body.Reader.Control.StackPrefixes
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchAndScopeEffects
import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.Compiler.Body.Reader.Scalar.ScalarEffects
import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTable
import Itasca.Body.Visitor.ReachedTableLoop
import Itasca.Body.Visitor.BrTable
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchAndCallSafety
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Relations.Control.ReachedControlSafety
import Itasca.Runtime.Compiler.Body.Reader.Safety.Run
import Itasca.Body.Trace.ControlRecords
import Itasca.Runtime.Compiler.Local.Relations.Operations.TerminalAndPairSafety
import Itasca.Body.Control.Frame
import Itasca.Runtime.Compiler.Body.Relations.CallbackReadiness
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchEntry
import Itasca.Runtime.Compiler.Body.Relations.Table.BranchTableTables
import Itasca.Runtime.Compiler.Local.Capacity.AuxiliaryGrowth
import Itasca.Runtime.Compiler.Body.Reader.Replay.OrdinaryEffects
import Itasca.Binary.Scalar.MemoryMeaning
import Itasca.Body.Trace.BytesDispatch
import Itasca.Visitor.BodyReplay
import Itasca.Runtime.Compiler.Local.Capacity.ControlAvailability
import Itasca.Runtime.Compiler.Body.Control.StructuredPrefixes

/-!
Proofs for Runtime / Compiler / Body / Reader / Control.

This module collects TerminalCompilationAndSafety, SafetyAndReturnAcceptance.
Each section documents its contracts and consumers.
-/

/-! ## TerminalCompilationAndSafety -/

section

open Itasca.Representation

/-!
# Terminal Compilation And Safety

Terminal instructions complete their compiler transitions while preserving reader safety. Return and other terminal cases consume the corresponding source-bound premises.
-/

/-! ## TerminalCompilation -/

section

/-!
Return and unreachable source-prefix transitions and structured compilation. Terminal reader states retain their distinct control-flow effects.
-/

/-! ## Structured Compiler Prefix Return -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredCompilerPrefix.return_live {jumpTables : List Aeneas.Std.U32} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (state : code.OpIterState) (consumed : position < state.pos.val)
    (reachable : before.reachable = true)
    (body : runtime.compiler.Frame) (bodyFrame : before.frames.val[0]? = some body)
    (resultWidth : body.results.val = slots returns)
    (front : List valtype) (input : Body.Stack.stackTypes raw = front ++ returns)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
      ops before state = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance .RETURN)
      state.vals.val state.pos.val ∧ after.reachable = false := by
  obtain ⟨_, retained⟩ := invariant.live reachable
  have layout := retained.layout
  rw [input] at layout
  have bounded : slots (compilerLocals before) + slots front < 2^32 := by
    have bound := before.height.hBounds
    change before.height.val < 2^32 at bound
    rw [layout.height, slots_append] at bound
    omega
  let source : U32 := UScalar.ofNatCore (slots (compilerLocals before) + slots front) bounded
  have sourcePosition : source.val = slots (compilerLocals before) + slots front := rfl
  have height : before.height.val = source.val + body.results.val := by
    rw [layout.height, slots_append, sourcePosition, resultWidth]
    omega
  have effect := callback_return ops law before state body source reachable bodyFrame height codeFits sourceFits coordinateFits
  rw [accepted, WP.spec_ok] at effect
  obtain ⟨dead, code, _, _⟩ := effect rfl
  have ordinary := compiler_return_ordinary_result ops law before after state (.Ok ()) accepted
  have sources := compiler_return_sources ops law before after state accepted
  have cursor := compiler_return_cursor ops law before after state accepted
  refine ⟨?_, dead⟩
  apply invariant.terminate reachable dead ordinary (emitted := .Return source body.results) _ code sources consumed (by rw [cursor])
  rw [input]
  exact .return_ front source body.results (by simpa only [retained.localsEq] using sourcePosition) resultWidth

theorem StructuredCompilerPrefix.return_dead {jumpTables : List Aeneas.Std.U32} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (state : code.OpIterState) (consumed : position < state.pos.val)
    (dead : before.reachable = false)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
      ops before state = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance .RETURN)
      state.vals.val state.pos.val ∧ after.reachable = false := by
  have sources := compiler_return_sources ops law before after state accepted
  have cursor := compiler_return_cursor ops law before after state accepted
  have ordinary := compiler_return_ordinary_result ops law before after state (.Ok ()) accepted
  rw [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return.dead ops before state dead] at accepted
  have frame := compiler_observe_frame ops law before state
  rw [accepted, WP.spec_ok] at frame
  change ObserveFrame before after at frame
  have deadAfter : after.reachable = false := by rw [frame]; exact dead
  have code : after.function.code = before.function.code := by rw [frame]
  exact ⟨invariant.skip .RETURN dead deadAfter ordinary code sources consumed (by rw [cursor]), deadAfter⟩
end Itasca.Compiler

end

/-! ## Structured Compiler Prefix Unreachable -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Computation

theorem StructuredCompilerPrefix.unreachable {jumpTables : List Aeneas.Std.U32} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (state : code.OpIterState)
    (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
      ops before state = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance .UNREACHABLE)
      state.vals.val state.pos.val ∧ after.reachable = false := by
  have sources := compiler_unreachable_sources ops law before after state accepted
  have cursor := compiler_unreachable_cursor ops law before after state accepted
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable.inv ops before after state (.Ok ()) accepted with
  | @emitted middle _ _ reachable emitted observed =>
    have emittedMetadata := compiler_emit_ordinary_result ops before middle .Unreachable (.Ok ()) emitted
    have observedMetadata := compiler_observe_ordinary_result ops law {middle with reachable := false} after state (.Ok ()) observed
    have ordinary : CompilerOrdinaryStable before after := emittedMetadata.trans (by
      exact ⟨observedMetadata.metadata, observedMetadata.capacity⟩)
    have frame := compiler_observe_frame ops law {middle with reachable := false} state
    rw [observed, WP.spec_ok] at frame
    change ObserveFrame {middle with reachable := false} after at frame
    have code := compiler_emit_code_success ops law before middle .Unreachable emitted
    have codeFinal : after.function.code.val = before.function.code.val ++ [.Unreachable] := by rw [frame]; exact code
    have dead : after.reachable = false := by rw [frame]
    exact ⟨invariant.terminate reachable dead ordinary (.unreachable _) codeFinal sources consumed (by rw [cursor]), dead⟩
  | dead dead observed =>
    have ordinary := compiler_observe_ordinary_result ops law before after state (.Ok ()) observed
    have frame := compiler_observe_frame ops law before state
    rw [observed, WP.spec_ok] at frame
    change ObserveFrame before after at frame
    have deadAfter : after.reachable = false := by rw [frame]; exact dead
    have unchanged : after.function.code = before.function.code := by rw [frame]
    exact ⟨invariant.skip .UNREACHABLE dead deadAfter ordinary unchanged sources consumed (by rw [cursor]), deadAfter⟩
end Itasca.Compiler

end

/-! ## Structured Reader Prefix Return -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_return {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions (p.ft.results.val.map Translation.valueType)
      locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 15#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 15#u8 before = .ok (.Ok (), out, after)) :
    Body.ReaderPost p out.core .RETURN true [] ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions (p.ft.results.val.map Translation.valueType)
        locals parents (current.advance .RETURN) out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨callback, read, values, post⟩ := reader_return p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have consumed : p.start.val < out.core.pos.val := by have position := p.pos; have span := post.span; omega
  refine ⟨post, ?_⟩
  by_cases reachable : before.reachable = true
  · obtain ⟨frame, found, resultWidth⟩ := reader_root_frame p before invariant.frames same
    obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
    obtain ⟨front, input⟩ := reader_return_stack st out env index p.ft.results.val outer p.current.vals
      (by simp [Body.resolve, p.signature]) vals (by simpa [Body.Control.base, controls] using base)
      (invariant.known reachable) (by simpa [Body.Control.polymorphic, controls] using monomorphic reachable) read
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact invariant.return_live ops law out.core consumed reachable frame found resultWidth front input
      codeFits sourceFits coordinateFits callback
  · exact invariant.return_dead ops law out.core consumed (Bool.eq_false_iff.mpr reachable) callback

end Itasca.Compiler

end

/-! ## Structured Reader Prefix Unreachable -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_unreachable {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_UNREACHABLE)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_UNREACHABLE before = .ok (.Ok (), out, after)) :
    Body.ReaderPost p out.core .UNREACHABLE true [] ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance .UNREACHABLE)
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_UNREACHABLE before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨callback, values, post⟩ := reader_unreachable p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core byte run
  have consumed : p.start.val < out.core.pos.val := by have position := p.pos; have span := post.span; omega
  exact ⟨post, invariant.unreachable ops law out.core consumed callback⟩

end Itasca.Compiler

end

/-! ## Structured Reader Compiler Terminal -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerState.unreachable {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_UNREACHABLE)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index code.OP_UNREACHABLE before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerState jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.UNREACHABLE)) savedParents
      (savedCurrent.advance (.plain (.UNREACHABLE)) (.UNREACHABLE)
        true []) := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨post, compiled, dead⟩ := structured_reader_prefix_unreachable p ops law initial before after out ctx rfl
    state.compiled byte accepted
  exact state.advance next advance inbounds post
    (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) compiled (by simp [dead])

theorem StructuredReaderCompilerState.return_ {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions (ft.results.val.map Translation.valueType) locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_RETURN)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index code.OP_RETURN before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerState jumpTables emit initial after types functions (ft.results.val.map Translation.valueType) locals data env ctx.locals index ft out
      parents (current.advance (.RETURN)) savedParents
      (savedCurrent.advance (.plain (.RETURN)) (.RETURN)
        true []) := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨post, compiled, dead⟩ := structured_reader_prefix_return p ops law initial before after out ctx
    state.compiled state.sources state.reach.current sourceBound bodyBound
      (by simpa only [p, ReaderBoundary.pending, global_simps] using byte) (by simpa only [global_simps] using accepted)
  exact state.advance next advance inbounds post
    (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) compiled (by simp [dead])

end Itasca.Compiler

end

end

/-! ## BranchTableSafety -/

section

/-!
Normal return while collecting and reading br_table labels.

Main declarations: `TableCollecting`.
-/

attribute [local step] Itasca.code.check_suffix.spec
namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body.Visitor
set_option maxRecDepth 4096

theorem reader_table_label (st : code.BodyState) (data : Slice U8)
    (aligned : st.blocks.val.length = st.core.ctrls.val.length) :
    code.read_label_info st data ⦃ out => ∀ depth types, out.1 = .Ok (depth,types) →
      out.2.core.vals = st.core.vals ∧ out.2.core.ctrls = st.core.ctrls ∧
      Binary.Leb128.Decoded data st.core.pos depth out.2.core.pos ∧ depth.val < st.core.ctrls.val.length ⦄ := by
  unfold code.read_label_info
  step with reader.read_u32_leb.spec data st.core.pos as ⟨result,decoded⟩
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨depth,next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry]
    step with code.label.spec {core := {st.core with pos := next}} depth aligned as ⟨result,looked⟩
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok types =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
      intro actual view equal
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj equal)
      refine ⟨trivial,trivial,decoded,?_⟩
      by_contra outside
      simp [Body.labelAt, show ¬depth.val < st.core.ctrls.val.length from outside] at looked

structure TableCollecting {A} (before current : runtime.compiler.FunctionCompiler A)
    (state : code.BodyState) : Prop where
  unchanged : ∃ budget buffer, current = {before with budget,table_depths := buffer}
  targets : ∀depth∈current.table_depths.val, depth.val < before.frames.val.length
  room : before.function.code.val.length + 2*current.table_depths.val.length + 3 ≤ 3*state.core.pos.val
  position : state.core.pos.val ≤ Itasca.limits.MAX_MODULE_BYTES.val
  frames : before.frames.val.length = state.core.ctrls.val.length
  shape : Body.Control.Shape state.core

private theorem table_check_total (st : code.BodyState) (env : metadata.Env)
    (types : signature.ResultType) (arity : Option Usize) (shape : Body.Control.Shape st.core) :
    tableCheck st env types arity ⦃ _ => True ⦄ := by
  unfold tableCheck
  step with signature.ResultType.len.spec types env
  split
  · simp
  · cases arity <;> step*

theorem TableCollecting.read {A} {before current : runtime.compiler.FunctionCompiler A}
    {state next : code.BodyState} {data : Slice U8} {depth : U32} {types}
    (held : TableCollecting before current state) (bounded : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (read : code.read_label_info state data = .ok (.Ok (depth,types),next)) :
    TableCollecting before current next ∧ depth.val < before.frames.val.length ∧
      before.function.code.val.length + 2*current.table_depths.val.length + 5 ≤ 3*next.core.pos.val := by
  have spec := reader_table_label state data (by simp)
  rw [read,WP.spec_ok] at spec
  obtain ⟨values,controls,decoded,depthBound⟩ := spec depth types rfl
  dsimp only at values controls decoded depthBound
  obtain ⟨progress,endBound⟩ := decoded.span
  have room := held.room
  refine ⟨⟨held.unchanged,held.targets,by omega,by omega,?_,?_⟩,?_,by omega⟩
  · simpa [controls] using held.frames
  · exact ⟨by simpa [controls] using held.shape.ordered,by simpa [controls,values] using held.shape.bounded⟩
  · simpa [held.frames] using depthBound

theorem TableCollecting.label {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {before current : runtime.compiler.FunctionCompiler A} {state : code.BodyState} {depth : U32}
    (held : TableCollecting before current state) (depthBound : depth.val < before.frames.val.length)
    (extra : before.function.code.val.length + 2*current.table_depths.val.length + 5 ≤ 3*state.core.pos.val) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label ops current state.core depth
      ⦃ out => out.1 = .Ok () → TableCollecting before out.2 state ⦄ := by
  have words : 2^32-1 ≤ Usize.max := by scalar_tac
  have position := held.position
  norm_num [limits.MAX_MODULE_BYTES] at position
  obtain ⟨⟨status,after⟩,called,_⟩ := WP.spec_imp_exists
    (compiler_table_label_total ops law current state.core depth (by omega))
  rw [called,WP.spec_ok]
  intro accepted
  dsimp only at accepted ⊢
  subst status
  obtain ⟨allocation,buffer,rfl,bufferEq⟩ := compiler_table_label_success ops law current after state.core depth called
  obtain ⟨oldBudget,oldBuffer,currentEq⟩ := held.unchanged
  refine ⟨?_,?_,?_,held.position,held.frames,held.shape⟩
  · exact ⟨allocation,buffer,by simp [currentEq]⟩
  · intro value member
    rw [bufferEq] at member
    rcases List.mem_append.mp member with member | member
    · exact held.targets value member
    · simpa using (List.mem_singleton.mp member ▸ depthBound)
  · simp only [bufferEq,List.length_append,List.length_singleton]
    omega

theorem compiler_table_rest_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current : runtime.compiler.FunctionCompiler A)
    (state : code.BodyState) (env : metadata.Env) (count index depth : U32)
    (types : signature.ResultType) (arity : Option Usize)
    (held : TableCollecting before current state) (bound : index.val ≤ count.val)
    (depthBound : depth.val < before.frames.val.length)
    (aligned : SourceAligned before) (fixups : FixupBudget before.frames.val before.function.code.val.length)
    (tables : before.function.jump_tables.val.length ≤ before.function.code.val.length)
    (coordinate : before.function.body_start.val + before.next_source.val ≤ Usize.max) :
    tableRest (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) state env count index depth types arity
      current ⦃ result => match result with
        | .done out => out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val
        | .cont next => next.2.2.2.val ≤ count.val ∧ index.val < next.2.2.2.val ∧
          TableCollecting before next.2.1 ⟨next.1⟩ ⦄ := by
  unfold tableRest
  step with table_check_total state env types arity held.shape as ⟨status,_⟩
  cases status with
  | Err error => simp
  | Ok nextArity =>
    simp only
    by_cases last : index = count
    · simp only [last,↓reduceIte]
      step with code.mark_unreachable_total state.core held.shape as ⟨marked,_⟩
      have room := held.room
      have position := held.position
      have words : 2^32-1 ≤ Usize.max := by scalar_tac
      norm_num [limits.MAX_MODULE_BYTES] at position
      obtain ⟨allocation,buffer,currentEq⟩ := held.unchanged
      step with compiler_br_table_total ops law current marked depth types
        (by simpa [SourceAligned,currentEq] using aligned) (by simpa [currentEq] using held.targets)
        (by simpa [currentEq] using depthBound) (by simpa [currentEq] using fixups)
        (by simp only [currentEq] at room ⊢; omega)
        (by simpa [currentEq] using tables) (by simpa [currentEq] using coordinate) as ⟨reply,after,observed⟩
      cases reply <;> simp_all [code.visit]
    · simp only [last,↓reduceIte]
      step with UScalar.add_spec (x := index) (y := 1#u32) (by
        have ne : index.val ≠ count.val := fun h => last (UScalar.eq_of_val_eq h)
        scalar_tac) as ⟨next,advance⟩
      refine ⟨by scalar_tac,by scalar_tac,held⟩

theorem compiler_table_body_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current : runtime.compiler.FunctionCompiler A)
    (state : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (count index : U32) (arity : Option Usize)
    (held : TableCollecting before current state)
    (bound : index.val ≤ count.val) (bounded : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (aligned : SourceAligned before) (fixups : FixupBudget before.frames.val before.function.code.val.length)
    (tables : before.function.jump_tables.val.length ≤ before.function.code.val.length)
    (coordinate : before.function.body_start.val + before.next_source.val ≤ Usize.max) :
    tableBody (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env count state current
      arity index ⦃ result => match result with
        | .done out => out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val
        | .cont next => next.2.2.2.val ≤ count.val ∧ index.val < next.2.2.2.val ∧
          TableCollecting before next.2.1 ⟨next.1⟩ ⦄ := by
  unfold tableBody
  obtain ⟨⟨status,next⟩,read,_⟩ := WP.spec_imp_exists (reader_table_label state data (by simp))
  rw [read]
  cases status with
  | Err error => simp
  | Ok pair =>
    obtain ⟨depth,types⟩ := pair
    obtain ⟨fresh,target,extra⟩ := held.read bounded read
    simp only [bind_ok,Std.uncurry]
    by_cases last : index = count
    · simp only [bne_iff_ne,last,ne_eq,not_true_eq_false,Bool.false_eq_true,↓reduceIte]
      simpa only [last] using compiler_table_rest_total ops law before current next env count index depth types arity
        fresh bound target aligned fixups tables coordinate
    · simp only [bne_iff_ne,last,ne_eq,not_false_eq_true,↓reduceIte]
      obtain ⟨⟨reply,after⟩,called,kept⟩ := WP.spec_imp_exists (fresh.label ops law target extra)
      rw [called]
      cases reply with
      | Err error => simp [code.visit]
      | Ok unitValue =>
        cases unitValue
        simp only [bind_ok,Std.uncurry,code.visit]
        exact compiler_table_rest_total ops law before after next env count index depth types arity
          (kept rfl) bound target aligned fixups tables coordinate

theorem compiler_table_reader_loop_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current : runtime.compiler.FunctionCompiler A)
    (state : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (count index : U32) (arity : Option Usize)  (held : TableCollecting before current state)
    (bound : index.val ≤ count.val) (bounded : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (aligned : SourceAligned before) (fixups : FixupBudget before.frames.val before.function.code.val.length)
    (tables : before.function.jump_tables.val.length ≤ before.function.code.val.length)
    (coordinate : before.function.body_start.val + before.next_source.val ≤ Usize.max) :
    code.branch_table_with_loop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      state.core data env current count arity index ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  exact code.branch_table_with_loop.total_on _ data env count
    (fun state current _ _ => TableCollecting before current state)
    (fun state current => ObservedStack current state.core.vals.val)
    (by intro state current arity index bound held
        apply WP.spec_mono (compiler_table_body_total ops law before current state data env
          count index arity held bound bounded aligned fixups tables coordinate)
        intro result ready
        cases result <;> exact ready)
    state current arity index bound held

theorem compiler_table_reader_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (shape : Body.Control.Shape state.core) (bounded : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (frameCount : compiler.frames.val.length = state.core.ctrls.val.length)
    (empty : compiler.table_depths.val = [])
    (room : compiler.function.code.val.length+3 ≤ 3*state.core.pos.val)
    (aligned : SourceAligned compiler) (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (tables : compiler.function.jump_tables.val.length ≤ compiler.function.code.val.length)
    (coordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      state data env compiler ⦃ out => out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  unfold code.branch_table_with
  step with reader.read_u32_leb.spec data state.core.pos as ⟨status,decoded⟩
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨count,next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry]
    obtain ⟨progress,endBound⟩ := decoded.span
    step with code.pop_with_type.total {state.core with pos := next} .I32
      (show Body.Control.Shape {state.core with pos := next} from ⟨shape.ordered,shape.bounded⟩)
      as ⟨status,popped,shape',controls,position,_,_⟩
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok selector =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry]
      apply compiler_table_reader_loop_total ops law compiler compiler ⟨popped⟩ data env count 0#u32 none _ (by simp) bounded aligned fixups tables coordinate
      refine ⟨⟨compiler.budget,compiler.table_depths,rfl⟩,by simp [empty],?_,?_,?_,shape'⟩
      · simp only [empty,List.length_nil,Nat.mul_zero,Nat.add_zero,position]
        omega
      · simp only [position]
        omega
      · simpa [controls] using frameCount

end Itasca.Compiler

end

/-! ## BranchSafety -/

section

/-!
Normal return of branch reader callbacks.

Main declarations: `compiler_branch_reader_total`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body Itasca.Visitor.Trace
set_option maxRecDepth 4096

theorem compiler_branch_reader_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : code.BodyState) (data : Slice U8) (env : metadata.Env) (conditional : Bool)
    (shape : Body.Control.Shape state.core)
    (aligned : state.blocks.val.length = state.core.ctrls.val.length)
    (frames : compiler.frames.val.length = state.blocks.val.length)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (pcBound : compiler.function.code.val.length+3 < 2^32)
    (codeFits : compiler.function.code.val.length+3 ≤ Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length+3 ≤ Usize.max)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    CallbackTrace.bodyRun (code.branch_info state data env conditional)
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      (fun pair => if conditional then .br_if pair.1 pair.2 else .br pair.1 pair.2) compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  apply reader_body_run_reached _ _ _ compiler (fun s c => ObservedStack c s.core.vals.val)
  · exact WP.spec_mono (code.branch_info.total state data env conditional shape aligned) (by simp)
  · intro out pair read
    obtain ⟨depth,view⟩ := pair
    have selected := reader_branch_info_selected state data env conditional depth view out aligned read
    have bound : depth.val < state.blocks.val.length := by
      by_contra no
      simp [Body.labelAt] at selected
      omega
    have depthFits : depth.val < compiler.frames.val.length := by omega
    cases conditional with
    | false =>
      exact compiler_br_callback_total ops law compiler out.core depth view depthFits fixups
        (by omega) (by omega) coordinate
    | true =>
      exact compiler_br_if_callback_total ops law compiler out.core depth view depthFits fixups
        pcBound codeFits sourceFits coordinate
end Itasca.Compiler

end

/-! ## CloseSafety -/

section

/-!
Normal return of scope-closing reader callbacks.

Main declarations: `StructuredCompilerPrefix.close_reader_total`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body Itasca.Visitor.Trace
set_option maxRecDepth 4096

theorem StructuredCompilerPrefix.close_reader_total {jumpTables : List U32} {A}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial compiler types functions returns locals parents current raw position)
    (bounded : position ≤ limits.MAX_MODULE_BYTES.val)
    (state : code.BodyState) (env : metadata.Env) (isElse : Bool)
    (shape : Body.Control.Shape state.core)
    (aligned : state.blocks.val.length = state.core.ctrls.val.length)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (coordinate : compiler.function.body_start.val+state.core.pos.val ≤ Usize.max)
    (emitCoordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    CallbackTrace.bodyRun (code.end_frame_info state env isElse)
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      (fun pair => if isElse then .else_ pair.2 else .end_ pair.1 pair.2) compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  have effect := code.end_frame_info.total state env isElse shape aligned
  apply reader_body_run_reached _ _ _ compiler (fun s c => ObservedStack c s.core.vals.val)
  · exact WP.spec_mono effect (by simp)
  · intro out pair read
    have data := effect
    rw [read,WP.spec_ok] at data
    dsimp only at data
    obtain ⟨kind,bt⟩ := pair
    cases isElse with
    | false =>
      apply invariant.end_total ops law bounded out.core kind bt _ emitCoordinate
      simpa only [data.2.2.2] using coordinate
    | true => exact invariant.else_total ops law bounded fixups out.core bt emitCoordinate
end Itasca.Compiler

end

/-! ## ReturnSafety -/

section

/-!
Normal return of a return reader callback.

Main declarations: `compiler_return_reader_total`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem compiler_return_reader_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : code.BodyState) (env : metadata.Env) (index : U32) (shape : Body.Control.Shape state.core)
    (bodyFrame : compiler.reachable = true → 0 < compiler.frames.val.length)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    Body.CallbackTrace.bodyRun (Body.returnStep state env index)
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) (fun _ => .return_) compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  apply reader_body_run_reached _ _ _ compiler (fun s c => ObservedStack c s.core.vals.val)
  · exact WP.spec_mono (Body.CallbackTrace.return_position state env index shape) (by simp)
  · intro out value read
    exact compiler_on_return_total ops law compiler out.core bodyFrame codeFits sourceFits coordinate
end Itasca.Compiler

end

end

/-! ## SafetyAndReturnAcceptance -/

section

open Itasca.Representation

/-!
# Safety And Return Acceptance

Control safety supplies the reader and compiler bounds used by return acceptance. The return case connects its terminal source effect to the retained control state.
-/

/-! ## ControlSafety -/

section

/-!
Normal return of structured control reader dispatch.

Main declarations: `StructuredReaderCompilerState.control_total`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerState.control_total {A}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {jumpTables emit types functions returns locals data env sourceLocals index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerState jumpTables emit initial compiler types functions returns locals
      data env sourceLocals index ft st parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val < data.length)
    (ctx : code.Context) (opcode : U8) (covered : opcode.val ∈ [2,3,4,5,11,12,13,15])
    (signatures : SignatureSequence compiler.signatures.val env.types.val)
    (observed : ObservedStack compiler st.core.vals.val)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (bodyBound : initial.function.body_start.val+data.length ≤ Usize.max) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with core := {st.core with pos := next}} data env ctx index opcode compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  let pending := state.boundary.pending next advance inbounds
  have ready := state.compiled.control_ready data.length next.val state.boundary.source_bound
    (by omega) (by omega) bodyBound
  have bounded : st.core.pos.val ≤ limits.MAX_MODULE_BYTES.val :=
    (by omega : st.core.pos.val ≤ data.length).trans state.boundary.source_bound
  have frameCount : compiler.frames.val.length = st.blocks.val.length := by
    simpa using state.frames_length
  simp only [List.mem_cons,List.not_mem_nil,or_false] at covered
  rcases covered with h | h | h | h | h | h | h | h
  · have equal : opcode = 2#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Body.CallbackTrace.dispatch_block]
    exact compiler_enter_reader_total ops law compiler pending .block (.inl rfl) signatures observed
      ready.emittedCoordinate (by have := ready.pc; omega) (by have := ready.code; omega)
      (by have := ready.sources; omega) ready.maps ready.frames
  · have equal : opcode = 3#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Body.CallbackTrace.dispatch_loop]
    exact compiler_enter_reader_total ops law compiler pending .loop (.inr (.inl rfl)) signatures observed
      ready.emittedCoordinate (by have := ready.pc; omega) (by have := ready.code; omega)
      (by have := ready.sources; omega) ready.maps ready.frames
  · have equal : opcode = 4#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Body.CallbackTrace.dispatch_if]
    exact compiler_enter_reader_total ops law compiler pending .then_ (.inr (.inr rfl)) signatures observed
      ready.emittedCoordinate (by have := ready.pc; omega) (by have := ready.code; omega)
      (by have := ready.sources; omega) ready.maps ready.frames
  · have equal : opcode = 5#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Body.CallbackTrace.dispatch_else]
    exact state.compiled.close_reader_total ops law bounded _ env true
      pending.opened.shape.core pending.opened.shape.aligned fixups ready.coordinate ready.emittedCoordinate
  · have equal : opcode = 11#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Body.CallbackTrace.dispatch_end]
    exact state.compiled.close_reader_total ops law bounded _ env false
      pending.opened.shape.core pending.opened.shape.aligned fixups ready.coordinate ready.emittedCoordinate
  · have equal : opcode = 12#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Body.CallbackTrace.dispatch_br]
    exact compiler_branch_reader_total ops law compiler _ data env false pending.opened.shape.core
      pending.opened.shape.aligned frameCount fixups ready.pc ready.code ready.sources ready.emittedCoordinate
  · have equal : opcode = 13#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Body.CallbackTrace.dispatch_br_if]
    exact compiler_branch_reader_total ops law compiler _ data env true pending.opened.shape.core
      pending.opened.shape.aligned frameCount fixups ready.pc ready.code ready.sources ready.emittedCoordinate
  · have equal : opcode = 15#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Body.CallbackTrace.dispatch_return]
    exact compiler_return_reader_total ops law compiler _ env index pending.opened.shape.core
      (fun _ => ready.nonempty) (by have := ready.code; omega) (by have := ready.sources; omega) ready.emittedCoordinate
end Itasca.Compiler

end

/-! ## BranchTableLedger -/

section

/-!
Auxiliary allocation accounting for br_table compilation.

Main declarations: `compiler_br_table_auxiliary_growth` and `reader_table_ledger`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem compiler_br_table_auxiliary_growth {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) (fallback : U32) (types : signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types = .ok (.Ok (),after)) : AuxiliaryGrowth before after := by
  obtain ⟨targets,tables⟩ := compiler_br_table_tables ops law before after state fallback types accepted
  have counts := congrArg (fun t : CompilerTables => (t.indirect.length,t.simd.length,t.constants.length)) tables
  simp only [CompilerTables.ofFunction,CompilerTables.append,List.append_nil,Prod.mk.injEq] at counts
  have growth : before.function.code.val.length ≤ after.function.code.val.length := by
    by_cases live : before.reachable = true
    · obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,bound⟩ :=
        compiler_br_table_production ops law before after state fallback types live accepted
      omega
    · obtain ⟨_,code,_⟩ := compiler_br_table_dead_effect ops law before after state fallback types
        (Bool.eq_false_iff.mpr live) accepted
      simp [code]
  unfold AuxiliaryGrowth
  omega

theorem reader_table_ledger {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 14#u8 before = .ok (.Ok (),final,after)) :
    AuxiliaryGrowth before after ∧ FixupBudget after.frames.val after.function.code.val.length := by
  rw [Body.CallbackTrace.dispatch_br_table] at accepted
  obtain ⟨_,_,_,_,_,fallback,types,_,_,allocation,buffer,_,_,_,_,_,_,_,callback⟩ :=
    compiler_read_br_table ops law before after st final data env accepted
  exact ⟨compiler_br_table_auxiliary_growth ops law {before with budget := allocation, table_depths := buffer} after final.core fallback types callback,
    compiler_br_table_fixup_budget ops law {before with budget := allocation, table_depths := buffer} after final.core fallback types budget callback⟩
end Itasca.Compiler

end

/-! ## ControlLedger -/

section

/-!
Allocation accounting for control reader steps.

Main declarations: `reader_control_ledger`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_control_ledger {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32) (opcode : U8)
    (covered : opcode.val ∈ [2,3,4,5,11,12,13,14,15])
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index opcode before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after ∧ FixupBudget after.frames.val after.function.code.val.length := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at covered
  rcases covered with h | h | h | h | h | h | h | h | h
  · obtain rfl : opcode = 2#u8 := UScalar.eq_of_val_eq h
    have effects := reader_control_effects ops law before after st out data env ctx index _ (by first | exact .inl (by unfold ScopeOpcode; decide) | exact .inr (.inl rfl) | exact .inr (.inr rfl)) accepted
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
  · obtain rfl : opcode = 3#u8 := UScalar.eq_of_val_eq h
    have effects := reader_control_effects ops law before after st out data env ctx index _ (by first | exact .inl (by unfold ScopeOpcode; decide) | exact .inr (.inl rfl) | exact .inr (.inr rfl)) accepted
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
  · obtain rfl : opcode = 4#u8 := UScalar.eq_of_val_eq h
    have effects := reader_control_effects ops law before after st out data env ctx index _ (by first | exact .inl (by unfold ScopeOpcode; decide) | exact .inr (.inl rfl) | exact .inr (.inr rfl)) accepted
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
  · obtain rfl : opcode = 5#u8 := UScalar.eq_of_val_eq h
    have effects := reader_control_effects ops law before after st out data env ctx index _ (by first | exact .inl (by unfold ScopeOpcode; decide) | exact .inr (.inl rfl) | exact .inr (.inr rfl)) accepted
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
  · obtain rfl : opcode = 11#u8 := UScalar.eq_of_val_eq h
    have effects := reader_control_effects ops law before after st out data env ctx index _ (by first | exact .inl (by unfold ScopeOpcode; decide) | exact .inr (.inl rfl) | exact .inr (.inr rfl)) accepted
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
  · obtain rfl : opcode = 12#u8 := UScalar.eq_of_val_eq h
    have effects := reader_control_effects ops law before after st out data env ctx index _ (by first | exact .inl (by unfold ScopeOpcode; decide) | exact .inr (.inl rfl) | exact .inr (.inr rfl)) accepted
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
  · obtain rfl : opcode = 13#u8 := UScalar.eq_of_val_eq h
    have effects := reader_control_effects ops law before after st out data env ctx index _ (by first | exact .inl (by unfold ScopeOpcode; decide) | exact .inr (.inl rfl) | exact .inr (.inr rfl)) accepted
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
  · obtain rfl : opcode = 14#u8 := UScalar.eq_of_val_eq h
    exact reader_table_ledger ops law before after st out data env ctx index budget (by simpa only [global_simps] using accepted)
  · obtain rfl : opcode = 15#u8 := UScalar.eq_of_val_eq h
    have effects := reader_return_effects ops law before after st out data env ctx index (by simpa only [global_simps] using accepted)
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
end Itasca.Compiler

end

/-! ## BranchTableDecodePrefix -/

section

/-!
Independently decoded table labels remaining at a reader boundary. The scratch labels are an exact prefix of the source list, indexed by callbacks.

Main declarations: `TableDecodePrefix` and `TableDecodeRead`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Independently decoded table labels remaining at a reader boundary. The
scratch labels are an exact prefix of the source list, indexed by callbacks. -/
structure TableDecodePrefix (data : Slice U8) (all : List U32) (finish : Usize)
    (index : Nat) (state : code.OpIterState) (depths : List U32) : Prop where
  length : depths.length = index
  suffix : ∃ tail, all = depths ++ tail ∧ Body.BrTable.LabelsDecoded data state.pos tail finish

/-- A label has been read but its callback has not yet appended it. Keeping
its value in the relation prevents arbitrary event arguments from replacing
source-decoded targets. -/
structure TableDecodeRead (data : Slice U8) (all : List U32) (finish : Usize)
    (index : Nat) (state : code.OpIterState) (depths : List U32) (depth : U32) : Prop where
  length : depths.length = index
  suffix : ∃ tail, all = depths ++ depth :: tail ∧ Body.BrTable.LabelsDecoded data state.pos tail finish

/-- Each independently decoded label consumes at least one source byte. -/
theorem table_labels_length_span {data start depths finish}
    (decoded : Body.BrTable.LabelsDecoded data start depths finish) :
    start.val + depths.length ≤ finish.val := by
  induction decoded with
  | nil => simp
  | snoc prior label ih =>
    have span := label.span
    simp only [List.length_append,List.length_singleton]
    omega

theorem TableDecodePrefix.initial {data all finish} (state : code.OpIterState)
    (decoded : Body.BrTable.LabelsDecoded data state.pos all finish) :
    TableDecodePrefix data all finish 0 state [] := by
  exact ⟨rfl,all,by simp,decoded⟩

/-- The actual successful reader fixes both the next target and byte cursor
by uniqueness of independent unsigned LEB128 decoding. -/
theorem TableDecodePrefix.read {data all finish index depths depth ts out} {state : code.BodyState}
    (held : TableDecodePrefix data all finish index state.core depths)
    (remaining : index < all.length)
    (read : code.read_label_info state data = .ok (.Ok (depth,ts),out)) :
    TableDecodeRead data all finish index out.core depths depth := by
  obtain ⟨tail,whole,decoded⟩ := held.suffix
  cases tail with
  | nil =>
    have length := congrArg List.length whole
    simp only [List.length_append,List.length_nil,Nat.add_zero] at length
    have prefixLength := held.length
    omega
  | cons first tail =>
    obtain ⟨middle,head,rest⟩ := Body.BrTable.LabelsDecoded.cons_iff.mp decoded
    have actual := reader_table_label state data (by simp)
    rw [read,WP.spec_ok] at actual
    obtain ⟨_,_,bytes,_⟩ := actual depth ts rfl
    dsimp only at bytes
    obtain ⟨rfl,position⟩ := bytes.unique head
    exact ⟨held.length,tail,whole,by simpa only [position] using rest⟩

/-- The successful callback appends exactly the depth just read. -/
theorem TableDecodeRead.collect {data all finish index state depths depth}
    (held : TableDecodeRead data all finish index state depths depth) :
    TableDecodePrefix data all finish (index+1) state (depths++[depth]) := by
  obtain ⟨tail,whole,decoded⟩ := held.suffix
  refine ⟨by simp [held.length],tail,?_,decoded⟩
  simpa [List.append_assoc] using whole

/-- At the separately decoded fallback, all remaining targets have been
accounted for. The vector labels followed by this fallback are exactly the
independent source target list. -/
theorem TableDecodeRead.complete {data all finish index state depths depth}
    (held : TableDecodeRead data all finish index state depths depth)
    (count : all.length = index+1) : all = depths++[depth] := by
  obtain ⟨tail,whole,decoded⟩ := held.suffix
  have length := congrArg List.length whole
  simp only [List.length_append,List.length_cons] at length
  have prefixLength := held.length
  have empty : tail.length = 0 := by omega
  simpa only [List.length_eq_zero_iff.mp empty] using whole

/-- After reading the separately encoded fallback, the cursor is the source
end of the entire table immediate. -/
theorem TableDecodeRead.cursor {data all finish index state depths depth}
    (held : TableDecodeRead data all finish index state depths depth)
    (count : all.length = index+1) : state.pos = finish := by
  obtain ⟨tail,whole,decoded⟩ := held.suffix
  have length := congrArg List.length whole
  simp only [List.length_append,List.length_cons] at length
  have prefixLength := held.length
  have empty : tail = [] := List.length_eq_zero_iff.mp (by omega)
  subst tail
  exact (decoded.unique .nil rfl).2.symm

end Itasca.Compiler

end

/-! ## ReachedReturnAcceptance -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace
set_option maxRecDepth 4096

/-- Source return typing and the retained root frame discharge the actual
return callback's width check, including multi-value and vector results. -/
theorem reached_return_available {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (source : code.OpVisitor V) (before after : V) (out : code.BodyState) (ctx : code.Context)
    {emit types functions locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial compiler
      types functions (p.ft.results.val.map Translation.valueType) locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (demand : CallbackDemand compiler out.core bound)
    (reference : code.step_profile source st data env ctx index 15#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 15#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨frame,found,resultWidth⟩ := reader_root_frame p compiler invariant.frames same
  rw [Body.CallbackTrace.dispatch_return] at reference ⊢
  refine Body.CallbackTrace.bodyRun.accepted_lift_on _ source
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) _ before after compiler out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro value read _
  cases value
  have height : compiler.reachable = true → frame.results.val ≤ compiler.height.val := by
    intro live
    obtain ⟨_,outer,_,_,base,_,controls,_,values⟩ := p.opened
    obtain ⟨front,input⟩ := reader_return_stack st out env index p.ft.results.val outer p.current.vals
      (by simp [Body.resolve,p.signature]) values (by simpa [Body.Control.base,controls] using base)
      (invariant.known live) (by simpa [Body.Control.polymorphic,controls] using monomorphic live) read
    have layout := (invariant.live live).2.layout
    rw [input] at layout
    rw [resultWidth,layout.height,slots_append]
    omega
  exact compiler_return_available ops bound available compiler out.core demand frame (fun _ => found) height

end Itasca.Compiler

end

end
