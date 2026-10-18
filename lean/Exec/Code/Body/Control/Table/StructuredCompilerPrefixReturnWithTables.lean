import Exec.Code.Body.Control.Table.StructuredCompilerPrefixTerminalWithTables
import Exec.Code.Local.Callbacks.Common.CompilerTerminalMetadata
import Exec.Code.Local.Callbacks.Calls.CallbackSources
import Exec.Code.Local.Callbacks.Calls.CallbackCursor
import Exec.Code.Local.Lowering.Control.LoweringReturn
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredCompilerPrefixWithTables.return_live {jumpTables : List Aeneas.Std.U32} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
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
    StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance .RETURN)
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

theorem StructuredCompilerPrefixWithTables.return_dead {jumpTables : List Aeneas.Std.U32} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (state : code.OpIterState) (consumed : position < state.pos.val)
    (dead : before.reachable = false)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
      ops before state = .ok (.Ok (), after)) :
    StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance .RETURN)
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
end Exec.Code
