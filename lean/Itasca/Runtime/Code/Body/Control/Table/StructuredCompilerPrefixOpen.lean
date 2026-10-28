import Itasca.Runtime.Code.Body.Control.Table.StructuredCompilerPrefix
import Itasca.Runtime.Code.Local.Control.Table.StructuredUniversalOpen
import Itasca.Runtime.Code.Local.Control.Table.StructuredElseFrames
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Exact entry effects preserve the whole retained invariant. The future
exit coordinates stay quantified until the corresponding END or ELSE. -/
theorem StructuredCompilerPrefix.open_plain {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true) (live : after.reachable = true)
    (child : SourceScope) (frame : runtime.compiler.Frame) (emitted : List Bytecode)
    (ordinary : CompilerStable before after)
    (aligned : ScopeFrameStack locals after (parents ++ [current]) child)
    (codeEq : after.function.code.val = before.function.code.val ++ emitted)
    (framesEq : after.frames.val = before.frames.val ++ [frame])
    (maps : after.function.controls.val.length = before.function.controls.val.length + 1)
    (noGuard : frame.if_pc = none) (noBranches : frame.fixups.val = [])
    (clean : DormantFrame frame) (fresh : child.form.isElse = false)
    (childCondition : ScopeCondition locals child)
    (layout : CompilerLayout after (Sequence.stackTypes raw))
    (sourceTypes : SourceStack nextRaw (Sequence.stackTypes raw))
    (childEntered : child.entered = true)
    (entry : child.entry = before.function.code.val.length)
    (body : child.bodyPc = after.function.code.val.length) (source : child.source = [])
    (input : child.input = Sequence.stackTypes raw) (arguments : child.arguments = Sequence.stackTypes raw)
    (sources : SourceProgress before after) (growth : emitted.length ≤ 3)
    (consumed : position < nextPosition) (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals (parents ++ [current]) child nextRaw nextPosition := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, ordinary.fields.2.2.2.2.1]; exact retained.localsEq
  have next := retained.open_plain child frame emitted codeEq framesEq noGuard noBranches localsEq layout
    entered childEntered entry body source input arguments
  have growthEq : after.function.code.val.length ≤ before.function.code.val.length + 3 := by
    rw [codeEq, List.length_append]; omega
  refine ⟨invariant.metadata.trans ordinary, aligned,
    invariant.entryChain.push child (fun _ => entered),
    (by rw [framesEq]; exact invariant.dormant.push frame clean), invariant.conditions.push child childCondition, (fun _ => sourceTypes.concrete),
    .live live childEntered ?_,
    invariant.arms.open_plain retained.sites child frame emitted fresh codeEq framesEq noGuard noBranches,
    sources.aligned invariant.sources, invariant.codeBudget.advance growthEq consumed,
    invariant.controlBudget.enter maps (by simp [framesEq]) consumed, cursor⟩
  simpa only [sourceTypes.decoded] using next

theorem StructuredCompilerPrefix.open_if {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition stack}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true) (live : after.reachable = true)
    (child : SourceScope) (frame : runtime.compiler.Frame) (condition : U32) (site : Usize)
    (sitePosition : site.val = before.function.code.val.length)
    (inputStack : Sequence.stackTypes raw = stack ++ [.I32])
    (ordinary : CompilerStable before after)
    (aligned : ScopeFrameStack locals after (parents ++ [current]) child)
    (codeEq : after.function.code.val = before.function.code.val ++ [.JumpIfZero condition core.num.U32.MAX])
    (framesEq : after.frames.val = before.frames.val ++ [frame])
    (maps : after.function.controls.val.length = before.function.controls.val.length + 1)
    (guardEq : frame.if_pc = some site) (noBranches : frame.fixups.val = [])
    (clean : DormantFrame frame) (fresh : child.form.isElse = false)
    (childCondition : ScopeCondition locals child)
    (layout : CompilerLayout after stack)
    (sourceTypes : SourceStack nextRaw stack)
    (childEntered : child.entered = true)
    (entry : child.entry = before.function.code.val.length)
    (body : child.bodyPc = after.function.code.val.length) (source : child.source = [])
    (input : child.input = stack) (arguments : child.arguments = stack ++ [.I32])
    (sources : SourceProgress before after)
    (consumed : position < nextPosition) (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals (parents ++ [current]) child nextRaw nextPosition := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, ordinary.fields.2.2.2.2.1]; exact retained.localsEq
  have next := (inputStack ▸ retained).open_if child frame condition site sitePosition codeEq framesEq guardEq noBranches localsEq layout
    entered childEntered entry body source input arguments
  have growthEq : after.function.code.val.length ≤ before.function.code.val.length + 3 := by
    rw [codeEq, List.length_append, List.length_singleton]; omega
  refine ⟨invariant.metadata.trans ordinary, aligned,
    invariant.entryChain.push child (fun _ => entered),
    (by rw [framesEq]; exact invariant.dormant.push frame clean), invariant.conditions.push child childCondition, (fun _ => sourceTypes.concrete),
    .live live childEntered ?_,
    invariant.arms.open_if retained.sites child frame condition site fresh sitePosition codeEq framesEq guardEq noBranches,
    sources.aligned invariant.sources, invariant.codeBudget.advance growthEq consumed,
    invariant.controlBudget.enter maps (by simp [framesEq]) consumed, cursor⟩
  simpa only [sourceTypes.decoded] using next

end Itasca.Runtime.Code
