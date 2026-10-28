import Exec.Code.Body.Control.Table.StructuredCompilerPrefixCloseBlock
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- END of an unentered child emits no code and restores its parent's
terminal or dormant source cursor without inventing a body certificate. -/
theorem StructuredCompilerPrefix.close_dormant {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child raw position nextRaw nextPosition}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals (parents ++ [parent]) child raw position)
    (unentered : child.entered = false) (dead : after.reachable = false)
    (stable : CompilerStable before after)
    (maps : after.function.controls.val.length = before.function.controls.val.length)
    (frame : runtime.compiler.Frame) (target : U32) (instruction : instr)
    (framesEq : before.frames.val = after.frames.val ++ [frame])
    (positionEq : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = before.function.code.val)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
      (parent.advance instruction) nextRaw nextPosition := by
  classical
  obtain ⟨paired, shape⟩ := invariant.frames.parts after.frames.val frame framesEq
  have frameDead := shape.entered.trans unentered
  obtain ⟨noExit, noFixups⟩ := invariant.dormant frame (by simp [framesEq]) frameDead
  have noGuard : frame.if_pc = none := by
    have guard := shape.guard
    cases form : child.form <;> simpa [form, SourceScope.guardPosition, unentered] using guard
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, stable.fields.2.2.2.2.1]; exact invariant.mode.locals
  let label : LabelTarget := ⟨child.front, child.branchTypes, child.results,
    if frame.kind = .Loop then frame.start_pc else target, target.val, [], [], false, decide (frame.kind = .Loop)⟩
  have future : FrameFuture before.function.code.val.length locals frame label 0#u32 := by
    refine ⟨?_, ?_, ?_, Nat.le_of_eq positionEq.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [frameDead]
    · simp [frameDead]
    · simp [frameDead]
    · intro kind; simpa [label, kind] using Nat.le_of_eq positionEq.symm
    · intro kind; simp [label, kind]
    · intro kind; simp [label, kind]
    · simp [noExit]
    · intro kind notThen; simp [label, kind]
    · simp [noGuard]
  have labelShape : ScopeLabel child label := ⟨rfl, rfl, rfl⟩
  have resolved : after.function.code.val = resolvedCode before.function.code.val (frameGroups frame label 0#u32) := by
    simpa [frameGroups, noGuard, noFixups, resolvedCode, patchCode] using codeEq
  have sites : ∀ other ∈ after.frames.val, FrameSites after.function.code.val other := by
    intro other member
    rw [codeEq]
    exact invariant.mode.sites other (by rw [framesEq]; exact List.mem_append_left _ member)
  have arms := invariant.arms.pop frame label 0#u32 framesEq future labelShape resolved instruction
  have frames := (invariant.frames.pop frame framesEq (fun scope other member previous =>
    previous.transport (by rw [maps]) (by rw [codeEq]) (by rw [codeEq]; exact previous.entryCode))).advance instruction
  have clean : DormantFrames after.frames.val := (framesEq ▸ invariant.dormant).pop
  refine ⟨invariant.metadata.trans stable, frames, invariant.entryChain.pop.advance _, clean,
    invariant.conditions.pop.advance _, (by intro live; simp [dead] at live), ?_, arms, sources.aligned invariant.sources,
    invariant.codeBudget.advance (by simp [codeEq]) consumed,
    (invariant.controlBudget.transport maps (by simp [framesEq])).advance (Nat.le_of_lt consumed), cursor⟩
  cases mode : invariant.mode with
  | live reachable entered retained => simp [unentered] at entered
  | terminal reachable entered retained => simp [unentered] at entered
  | dormant reachable retained =>
    cases parentEntered : parent.entered with
    | false => exact .dormant dead (retained.close_dormant frame label 0#u32 framesEq future labelShape resolved sites localsEq parentEntered instruction)
    | true =>
      exact StructuredPrefixMode.terminal (current := parent.advance instruction) dead (by exact parentEntered)
        (retained.close_terminal frame label 0#u32 framesEq future labelShape resolved sites localsEq parentEntered instruction)
end Itasca.Runtime.Code
