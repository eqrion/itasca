import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixTerminal
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackSources
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackCursor
import Itasca.Runtime.Compiler.Local.Lowering.Control.LoweringReturn
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerOrdinaryResults
import Itasca.Runtime.Compiler.Local.Capacity.EmissionGrowth
import Itasca.Runtime.Compiler.Local.Relations.Control.KnownControlStack
import Itasca.Runtime.Compiler.Body.Reader.Control.ReturnStack
import Itasca.Runtime.Compiler.Body.Reader.Control.RootFrame
import Itasca.Runtime.Compiler.Body.Reader.Replay.Span
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Unreachable
import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileAgreement
import Itasca.Runtime.Compiler.Body.Reader.Replay.StructuredState

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
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable at accepted
  split at accepted
  · rename_i reachable
    obtain ⟨⟨result, middle⟩, emitted, observed⟩ := bind_ok_inv _ _ _ accepted
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at observed
    | Ok unit =>
      cases unit
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at observed
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
  · rename_i notReachable
    have dead : before.reachable = false := Bool.eq_false_iff.mpr notReachable
    have ordinary := compiler_observe_ordinary_result ops law before after state (.Ok ()) accepted
    have frame := compiler_observe_frame ops law before state
    rw [accepted, WP.spec_ok] at frame
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
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
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
      st data env ctx index .Wasm2 15#u8 before = .ok (.Ok (), out, after)) :
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
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_UNREACHABLE)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_UNREACHABLE before = .ok (.Ok (), out, after)) :
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
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_UNREACHABLE before = .ok (.Ok (), out, after)) :
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
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_RETURN before = .ok (.Ok (), out, after)) :
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
