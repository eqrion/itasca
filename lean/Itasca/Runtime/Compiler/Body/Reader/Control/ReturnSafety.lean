import Itasca.Runtime.Compiler.Local.Lowering.Control.UnreachableContracts
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixOpenDormant
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Itasca.Runtime.Compiler.Local.Lowering.Control.LoweringTrap
import Itasca.Runtime.Compiler.Local.Capacity.EmissionGrowth
import Itasca.Runtime.Compiler.Local.Relations.Control.KnownControlStack
import Itasca.Runtime.Compiler.Body.Reader.Control.ReturnStack
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlKind
import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Unreachable
import Itasca.Runtime.Compiler.Body.Reader.Replay.BulkAndSaturatingAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPreserved
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableCallbackSafety
import Itasca.Wasm2.Visitor.ReachedTableLoop
import Itasca.Wasm2.Visitor.Total
import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileSafety
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallExclusions
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Relations.Control.ReachedControlSafety
import Itasca.Runtime.Compiler.Body.Reader.Safety.Run
import Itasca.Wasm2.Trace.ControlRecords
import Itasca.Runtime.Compiler.Local.Relations.Operations.PairSafety
import Itasca.Wasm2.Control.Total

/-!
Sections, each formerly its own module: TerminalCompilation, BranchTableSafetyWasm2, BranchSafety, CloseSafety, ReturnSafety.
-/

/-! ## TerminalCompilation -/

section

/-!
Return and unreachable source-prefix transitions and structured compilation. Terminal reader states retain their distinct control-flow effects.
-/

/-! ## Structured Compiler Prefix Return -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredCompilerPrefix.return_live {jumpTables : List Aeneas.Std.U32} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (state : code.OpIterState) (consumed : position < state.pos.val)
    (reachable : before.reachable = true)
    (body : runtime.compiler.Frame) (bodyFrame : before.frames.val[0]? = some body)
    (resultWidth : body.results.val = slots returns)
    (front : List valtype) (input : Sequence.stackTypes raw = front ++ returns)
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
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return, dead, Bool.false_eq_true, ↓reduceIte] at accepted
  have frame := compiler_observe_frame ops law before state
  rw [accepted, WP.spec_ok] at frame
  change ObserveFrame before after at frame
  have deadAfter : after.reachable = false := by rw [frame]; exact dead
  have code : after.function.code = before.function.code := by rw [frame]
  exact ⟨invariant.skip .RETURN dead deadAfter ordinary code sources consumed (by rw [cursor]), deadAfter⟩
end Itasca.Runtime.Compiler

end

/-! ## Structured Compiler Prefix Unreachable -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts

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
end Itasca.Runtime.Compiler

end

/-! ## Structured Reader Prefix Return -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_return_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions (p.ft.results.val.map Translate.valueType)
      locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 15#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 15#u8 before = .ok (.Ok (), out, after)) :
    Wasm2.ReaderPost p out.core .RETURN true [] ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions (p.ft.results.val.map Translate.valueType)
        locals parents (current.advance .RETURN) out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨callback, read, values, post⟩ := reader_return_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have consumed : p.start.val < out.core.pos.val := by have position := p.pos; have span := post.span; omega
  refine ⟨post, ?_⟩
  by_cases reachable : before.reachable = true
  · obtain ⟨frame, found, resultWidth⟩ := reader_root_frame_wasm2 p before invariant.frames same
    obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
    obtain ⟨front, input⟩ := reader_return_stack_wasm2 st out env index p.ft.results.val outer p.current.vals
      (by simp [Wasm2.resolve, p.signature]) vals (by simpa [Control.base, controls] using base)
      (invariant.known reachable) (by simpa [Control.polymorphic, controls] using monomorphic reachable) read
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact invariant.return_live ops law out.core consumed reachable frame found resultWidth front input
      codeFits sourceFits coordinateFits callback
  · exact invariant.return_dead ops law out.core consumed (Bool.eq_false_iff.mpr reachable) callback

end Itasca.Runtime.Compiler

end

/-! ## Structured Reader Prefix Unreachable -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_unreachable_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_UNREACHABLE)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_UNREACHABLE before = .ok (.Ok (), out, after)) :
    Wasm2.ReaderPost p out.core .UNREACHABLE true [] ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance .UNREACHABLE)
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_UNREACHABLE before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨callback, values, post⟩ := reader_unreachable_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core byte run
  have consumed : p.start.val < out.core.pos.val := by have position := p.pos; have span := post.span; omega
  exact ⟨post, invariant.unreachable ops law out.core consumed callback⟩

end Itasca.Runtime.Compiler

end

/-! ## Structured Reader Compiler Terminal -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.unreachable {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_UNREACHABLE)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index code.OP_UNREACHABLE before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.UNREACHABLE)) savedParents
      (savedCurrent.advance (.plain (.UNREACHABLE)) (.UNREACHABLE)
        true []) := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨post, compiled, dead⟩ := structured_reader_prefix_unreachable_wasm2 p ops law initial before after out ctx rfl
    state.compiled byte accepted
  exact state.advance next advance inbounds post
    (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])

theorem StructuredReaderCompilerStateWasm2.return_ {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_RETURN)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index code.OP_RETURN before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft out
      parents (current.advance (.RETURN)) savedParents
      (savedCurrent.advance (.plain (.RETURN)) (.RETURN)
        true []) := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨post, compiled, dead⟩ := structured_reader_prefix_return_wasm2 p ops law initial before after out ctx
    state.compiled state.sources state.reach.current sourceBound bodyBound
      (by simpa only [p, ReaderBoundaryWasm2.pending, global_simps] using byte) (by simpa only [global_simps] using accepted)
  exact state.advance next advance inbounds post
    (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])

end Itasca.Runtime.Compiler

end

end

/-! ## BranchTableSafetyWasm2 -/

section

/-!
Normal return while collecting and reading br_table labels.

Main declarations: `TableCollecting`. A direct consumer is `Compiler.Body.Reader.Control.BranchTableDecodePrefix`.
-/

attribute [local step] Itasca.code.check_suffix.spec
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2.Visitor
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem reader_table_label_wasm2 (st : code.BodyState) (data : Slice U8)
    (aligned : st.blocks.val.length = st.core.ctrls.val.length) :
    code.read_label_info st data ⦃ out => ∀ depth types, out.1 = .Ok (depth,types) →
      out.2.core.vals = st.core.vals ∧ out.2.core.ctrls = st.core.ctrls ∧
      Leb128.Decoded data st.core.pos depth out.2.core.pos ∧ depth.val < st.core.ctrls.val.length ⦄ := by
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
      simp [Wasm2.labelAt, show ¬depth.val < st.core.ctrls.val.length from outside] at looked

structure TableCollecting {A} (before current : runtime.compiler.FunctionCompiler A)
    (state : code.BodyState) : Prop where
  unchanged : ∃ budget buffer, current = {before with budget,table_depths := buffer}
  targets : ∀depth∈current.table_depths.val, depth.val < before.frames.val.length
  room : before.function.code.val.length + 2*current.table_depths.val.length + 3 ≤ 3*state.core.pos.val
  position : state.core.pos.val ≤ Itasca.limits.MAX_MODULE_BYTES.val
  frames : before.frames.val.length = state.core.ctrls.val.length
  shape : Control.Shape state.core

private theorem table_check_total (st : code.BodyState) (env : metadata.Env)
    (types : signature.ResultType) (arity : Option Usize) (shape : Control.Shape st.core) :
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
  have spec := reader_table_label_wasm2 state data (by simp)
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
  obtain ⟨⟨status,next⟩,read,_⟩ := WP.spec_imp_exists (reader_table_label_wasm2 state data (by simp))
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

theorem compiler_table_reader_wasm2_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (shape : Control.Shape state.core) (bounded : data.length ≤ limits.MAX_MODULE_BYTES.val)
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
      (show Control.Shape {state.core with pos := next} from ⟨shape.ordered,shape.bounded⟩)
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

end Itasca.Runtime.Compiler

end

/-! ## BranchSafety -/

section

/-!
Normal return of branch reader callbacks.

Main declarations: `compiler_branch_reader_total`. A direct consumer is `Compiler.Body.Reader.Control.ControlSafetyWasm2`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem compiler_branch_reader_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : code.BodyState) (data : Slice U8) (env : metadata.Env) (conditional : Bool)
    (shape : Control.Shape state.core)
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
      simp [Wasm2.labelAt] at selected
      omega
    have depthFits : depth.val < compiler.frames.val.length := by omega
    cases conditional with
    | false =>
      exact compiler_br_callback_total ops law compiler out.core depth view depthFits fixups
        (by omega) (by omega) coordinate
    | true =>
      exact compiler_br_if_callback_total ops law compiler out.core depth view depthFits fixups
        pcBound codeFits sourceFits coordinate
end Itasca.Runtime.Compiler

end

/-! ## CloseSafety -/

section

/-!
Normal return of scope-closing reader callbacks.

Main declarations: `StructuredCompilerPrefix.close_reader_total`. A direct consumer is `Compiler.Body.Reader.Control.ControlSafetyWasm2`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem StructuredCompilerPrefix.close_reader_total {jumpTables : List U32} {A}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial compiler types functions returns locals parents current raw position)
    (bounded : position ≤ limits.MAX_MODULE_BYTES.val)
    (state : code.BodyState) (env : metadata.Env) (isElse : Bool)
    (shape : Control.Shape state.core)
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
end Itasca.Runtime.Compiler

end

/-! ## ReturnSafety -/

section

/-!
Normal return of a return reader callback.

Main declarations: `compiler_return_reader_wasm2_total`. A direct consumer is `Compiler.Body.Reader.Control.ControlSafetyWasm2`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem compiler_return_reader_wasm2_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : code.BodyState) (env : metadata.Env) (index : U32) (shape : Control.Shape state.core)
    (bodyFrame : compiler.reachable = true → 0 < compiler.frames.val.length)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    Wasm2.CallbackTrace.bodyRun (Wasm2.returnStep state env index)
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) (fun _ => .return_) compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  apply reader_body_run_reached _ _ _ compiler (fun s c => ObservedStack c s.core.vals.val)
  · exact WP.spec_mono (Wasm2.CallbackTrace.return_position state env index shape) (by simp)
  · intro out value read
    exact compiler_on_return_total ops law compiler out.core bodyFrame codeFits sourceFits coordinate
end Itasca.Runtime.Compiler

end
