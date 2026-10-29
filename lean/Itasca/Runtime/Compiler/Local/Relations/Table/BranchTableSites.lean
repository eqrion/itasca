import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableBuild
import Itasca.Runtime.Compiler.Local.Control.Control.UniversalBranch
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Newly appended forward holes remain valid instruction sites; unrelated
frame guards and holes remain valid under the exact appended fragment. -/
theorem TableTargetCode.frame_sites {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32}
    (effect : TableTargetCode before after depth)
    (sites : ∀ frame ∈ before.frames.val, FrameSites before.function.code.val frame) :
    ∀ frame ∈ after.frames.val, FrameSites after.function.code.val frame := by
  cases effect with
  | loop index frame source lookup position kind operands code frames =>
    intro current member
    rw [frames] at member
    simpa only [code] using (sites current member).extend (branchInstructions frame.height source frame.params frame.start_pc)
  | forward index frame source fixups site lookup position kind operands code frames appended sitePosition =>
    intro current member
    rw [frames] at member
    rcases List.mem_or_eq_of_mem_set member with previous | rfl
    · simpa only [code] using (sites current previous).extend (branchInstructions frame.height source frame.results core.num.U32.MAX)
    · have valid := sites frame (List.mem_of_getElem? lookup)
      simpa only [code] using valid.add_branch frame.height source frame.results core.num.U32.MAX site fixups appended sitePosition

theorem TableTargetsBuilt.frame_sites {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depths targets : List U32}
    (built : TableTargetsBuilt before after depths targets)
    (sites : ∀ frame ∈ before.frames.val, FrameSites before.function.code.val frame) :
    ∀ frame ∈ after.frames.val, FrameSites after.function.code.val frame := by
  induction built with
  | nil => exact sites
  | cons _ _ _ _ _ _ effect rest ih => exact ih (effect.frame_sites sites)
end Itasca.Runtime.Compiler
