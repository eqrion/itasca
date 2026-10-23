import Exec.Code.Local.Checking.FrameExitSlotBounds
import Exec.Code.Local.Source.TableTransferBounds
import Exec.Code.Local.Relations.Table.BranchTableMetadata

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Each actual table arm records an exit only for its source-bounded result
region. Loop arms retain the existing flags and bounds. -/
theorem compiler_table_branch_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (lookup : before.table_depths.val[index.val]? = some depth)
    (transfers : TableTransferBounds before) (heightFits : before.height.val ≤ before.function.slot_count.val)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  obtain ⟨_,_,_,_,effect⟩ := compiler_table_target_code ops law before after index depth lookup called
  have capacity := (compiler_table_branch_fixed ops law before after index depth lookup called).stable.capacity
  cases effect with
  | loop selected frame source found position kind operands code frames =>
    exact held.retained (congrArg alloc.vec.Vec.val frames) capacity
  | forward selected frame source fixups site found position kind operands code frames appended siteAt =>
    have region := (transfers depth (List.mem_of_getElem? lookup) selected frame found position).1
    have width : frameBranchWidth frame = frame.results := by cases eq : frame.kind <;> simp_all [frameBranchWidth]
    rw [width] at region
    exact held.record selected.val frame fixups frames capacity (by omega)

/-- A finite table run retains all source transfer bounds needed by subsequent
arms and all slot bounds recorded by previous forward exits. -/
theorem TableBranchRun.exit_slots {A : Type} {ops : runtime.platform.Alloc A}
    (law : Platform.AllocCorrect ops) {before after : runtime.compiler.FunctionCompiler A} {index : Nat}
    (run : TableBranchRun ops before index after) (transfers : TableTransferBounds before)
    (heightFits : before.height.val ≤ before.function.slot_count.val) (held : FrameExitSlotBounds before) :
    FrameExitSlotBounds after := by
  induction run with
  | done => exact held
  | @cons before middle after index inside called rest ih =>
    let depth := before.table_depths.val[index.val]
    have lookup : before.table_depths.val[index.val]? = some depth := List.getElem?_eq_getElem inside
    obtain ⟨_,_,_,height,code⟩ := compiler_table_target_code ops law before middle index depth lookup called
    have depths := compiler_table_branch_depths ops before middle index (.Ok ()) called
    have capacity := (compiler_table_branch_fixed ops law before middle index depth lookup called).stable.capacity
    exact ih (transfers.advance code depths height) (by rw [height]; exact heightFits.trans capacity)
      (compiler_table_branch_exit_slots ops law before middle index depth lookup transfers heightFits held called)

/-- The actual dispatch emission and finite target builder retain all branch
exit bounds independently of their final instruction-check certificate. -/
theorem compiler_lower_table_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (transfers : TableTransferBounds before) (heightFits : before.height.val ≤ before.function.slot_count.val)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  obtain ⟨start,len,selector,emitted,_,_,_,emission,run⟩ := compiler_lower_table_success ops law before after called
  have growth := emission.instructionCheckExtends
  obtain ⟨budget,code,sources,frame,appended,_⟩ := emission
  subst emitted
  apply run.exit_slots law _ heightFits (held.retained rfl le_rfl)
  intro depth member index frame found position
  have region := transfers depth member index frame found position
  refine ⟨region.1,fun loop => (region.2 loop).trans ?_⟩
  change before.function.code.length ≤ code.length
  exact growth.code

end Exec.Code
