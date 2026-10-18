import Exec.Code.Body.Callbacks.Common.CompilerPrefix
import Exec.Code.Local.Callbacks.Common.CompilerDeadMetadata
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem PrefixMode.sites {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current stack}
    (mode : PrefixMode compiler types functions returns locals parents current stack) :
    ∀ frame ∈ compiler.frames.val, FrameSites compiler.function.code.val frame := by
  cases mode with
  | live _ _ retained => exact retained.sites
  | terminal _ _ retained => exact retained.sites
  | dormant _ retained => exact retained.sites

theorem PrefixMode.locals {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current stack}
    (mode : PrefixMode compiler types functions returns locals parents current stack) :
    compilerLocals compiler = locals := by
  cases mode with
  | live _ _ retained => exact retained.localsEq
  | terminal _ _ retained => exact retained.localsEq
  | dormant _ retained => exact retained.localsEq

/-- A successful ordinary callback in dead code retains the source suffix but
cannot create a new executable continuation. -/
theorem CompilerPrefix.skip {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position nextRaw nextPosition}
    (invariant : CompilerPrefix initial before types functions returns locals parents current raw position)
    (instruction : instr) (dead : before.reachable = false) (deadAfter : after.reachable = false)
    (ordinary : CompilerOrdinaryStable before after) (unchanged : after.function.code = before.function.code)
    (known : ConcreteStack nextRaw)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    CompilerPrefix initial after types functions returns locals parents (current.advance instruction) nextRaw nextPosition := by
  have code : after.function.code.val = before.function.code.val ++ [] := by simpa only [List.append_nil, unchanged]
  have frames := (invariant.frames.extend (congrArg (fun fs => fs.val) ordinary.frames) []
    code (by rw [ordinary.controls])).advance instruction
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by rw [unchanged]; omega
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, ordinary.stable.fields.2.2.2.2.1]
    exact invariant.mode.locals
  refine ⟨invariant.metadata.trans ordinary.stable, frames, invariant.entryChain.advance instruction,
    (by simpa only [ordinary.frames] using invariant.dormant), invariant.conditions.advance instruction, known, ?_,
    invariant.arms.append invariant.mode.sites [] instruction code ordinary.frames,
    sources.aligned invariant.sources, invariant.codeBudget.advance growth consumed,
    (invariant.controlBudget.transport (congrArg (fun maps => maps.val.length) ordinary.controls)
      (by rw [ordinary.frames])).advance (Nat.le_of_lt consumed), cursor⟩
  cases invariant.mode with
  | live reachable _ _ => simp [dead] at reachable
  | terminal _ entered retained =>
    exact .terminal deadAfter entered (retained.skip instruction (congrArg (fun code => code.val) unchanged) ordinary.frames localsEq)
  | dormant _ retained => exact .dormant deadAfter (retained.skip instruction unchanged ordinary.frames localsEq)

end Exec.Code
