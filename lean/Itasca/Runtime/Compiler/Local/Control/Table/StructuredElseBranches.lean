import Itasca.Runtime.Compiler.Local.Control.Table.StructuredElseEvidence
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalConditional
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseEvidence
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalConditional
namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- A forward branch strengthens only its selected future exit and appends
new resolved instructions; completed ELSE arms remain an exact prefix. -/
theorem StructuredUniversalElse.branch_forward {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current}
    (invariant : StructuredUniversalElse (jumpTables := jumpTables) emit before types functions returns locals parents current)
    (sites : ∀ frame ∈ before.frames.val, FrameSites before.function.code.val frame)
    (frame : runtime.compiler.Frame) (index depth : Nat)
    (dst src count old : U32) (site : Usize) (fixups : alloc.vec.Vec Usize)
    (found : before.frames.val[index]? = some frame)
    (position : index + depth + 1 = before.frames.val.length)
    (sitePosition : site.val = before.function.code.val.length +
      (if count = 0#u32 ∨ src = dst then 0 else 1))
    (appended : fixups.val = frame.fixups.val ++ [site])
    (codeEq : after.function.code.val = before.function.code.val ++ branchInstructions dst src count old)
    (framesEq : after.frames.val = before.frames.val.set index {frame with end_reachable := true, fixups}) :
    StructuredUniversalElse (jumpTables := jumpTables) emit after types functions returns locals parents (current.advance (.BR (.mk_uN depth))) := by
  intro top labels groups plans shape parentShapes
  have order : before.function.code.val.length ≤ after.function.code.val.length := by simp [codeEq]
  obtain ⟨label, earlier, suffix, labelAt, live, priorPlans, grouped⟩ :=
    plans.before_mark fixups framesEq found position
  have oldPlans := priorPlans.before order
  have oldShape : ScopeLabel current top :=
    ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
  have prior := invariant top labels _ oldPlans oldShape parentShapes
  have resolved := resolved_code_new_br before.function.code.val earlier suffix
    ⟨frame.fixups.val, label.target⟩ dst src count old site sitePosition (oldPlans.inside sites)
  rw [grouped, appended, codeEq, resolved]
  exact (prior.extend (branchInstructions dst src count label.target)).advance (.BR (.mk_uN depth))

/-- Conditional forward branches preserve completed-arm certificates for the
same reason, including the emitted transfer/guard pair when needed. -/
theorem StructuredUniversalElse.branch_if_forward {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current}
    (invariant : StructuredUniversalElse (jumpTables := jumpTables) emit before types functions returns locals parents current)
    (sites : ∀ frame ∈ before.frames.val, FrameSites before.function.code.val frame)
    (frame : runtime.compiler.Frame) (index depth : Nat)
    (dst src count old condition resume : U32) (site : Usize) (fixups : alloc.vec.Vec Usize)
    (found : before.frames.val[index]? = some frame)
    (position : index + depth + 1 = before.frames.val.length)
    (sitePosition : site.val = before.function.code.val.length +
      (if count = 0#u32 ∨ src = dst then 0 else 2))
    (appended : fixups.val = frame.fixups.val ++ [site])
    (codeEq : after.function.code.val = before.function.code.val ++ branchIfInstructions dst src count old condition resume)
    (framesEq : after.frames.val = before.frames.val.set index {frame with end_reachable := true, fixups}) :
    StructuredUniversalElse (jumpTables := jumpTables) emit after types functions returns locals parents (current.advance (.BR_IF (.mk_uN depth))) := by
  intro top labels groups plans shape parentShapes
  have order : before.function.code.val.length ≤ after.function.code.val.length := by simp [codeEq]
  obtain ⟨label, earlier, suffix, labelAt, live, priorPlans, grouped⟩ :=
    plans.before_mark fixups framesEq found position
  have oldPlans := priorPlans.before order
  have oldShape : ScopeLabel current top :=
    ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
  have prior := invariant top labels _ oldPlans oldShape parentShapes
  have resolved := resolved_code_new_br_if before.function.code.val earlier suffix
    ⟨frame.fixups.val, label.target⟩ dst src count old condition resume site sitePosition (oldPlans.inside sites)
  rw [grouped, appended, codeEq, resolved]
  exact (prior.extend (branchIfInstructions dst src count label.target condition resume)).advance (.BR_IF (.mk_uN depth))

end Itasca.Runtime.Compiler
