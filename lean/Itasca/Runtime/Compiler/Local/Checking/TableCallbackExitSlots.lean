import Itasca.Runtime.Compiler.Local.Checking.FrameExitSlotBounds
import Itasca.Runtime.Compiler.Local.Source.TableTransferBounds
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableMetadata
import Itasca.Runtime.Compiler.Local.Checking.BranchCallbackExitSlots

/-!
Exit-slot bounds for br_table targets, the target loop and the compiler callback. The final callback retains both label and branch-table slot requirements.
-/

/-! ## Table Exit Slot Bounds -/

section

namespace Itasca.Runtime.Compiler
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
  have growth := emission.instruction_check_extends
  obtain ⟨budget,code,sources,frame,appended,_⟩ := emission
  subst emitted
  apply run.exit_slots law _ heightFits (held.retained rfl le_rfl)
  intro depth member index frame found position
  have region := transfers depth member index frame found position
  refine ⟨region.1,fun loop => (region.2 loop).trans ?_⟩
  change before.function.code.length ≤ code.length
  exact growth.code

end Itasca.Runtime.Compiler

end

/-! ## Table Callback Exit Slots -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Collecting a table label preserves instruction checks and pending owners. -/
theorem compiler_table_label_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (held : FrameExitSlotBounds before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops before state depth = .ok (.Ok (),after)) : FrameExitSlotBounds after := by
  obtain ⟨budget,depths,frame,_⟩ := compiler_table_label_success ops law before after state depth called
  exact held.retained (by rw [frame]) (by rw [frame])

/-- Lift the source-derived raw table proof through the final default label,
scratch-buffer clearing, and dead-stack observation of the actual callback. -/
theorem compiler_br_table_callback_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (held : FrameExitSlotBounds before)
    (lower : ∀ labeled,
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
        ops before state fallback = .ok (.Ok (),labeled) → labeled.reachable = true → ∀ lowered,
      runtime.compiler.control.FunctionCompiler.lower_table_branches ops labeled = .ok (.Ok (),lowered) →
      FrameExitSlotBounds lowered)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types = .ok (.Ok (),after)) : FrameExitSlotBounds after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table at called
  obtain ⟨⟨result,labeled⟩,labelCalled,rest⟩ := bind_ok_inv _ _ _ called
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok unit =>
    cases unit
    have checked := compiler_table_label_exit_slots ops law before labeled state fallback held labelCalled
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
    split at rest
    · rename_i live
      obtain ⟨⟨result,lowered⟩,lowerCalled,rest⟩ := bind_ok_inv _ _ _ rest
      cases result with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok unit =>
        cases unit
        have loweredChecked := lower labeled labelCalled live lowered lowerCalled
        simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
        obtain ⟨cleared,_,observed⟩ := bind_ok_inv _ _ _ rest
        exact compiler_observe_exit_slots ops law {lowered with reachable := false,table_depths := cleared}
          after state (loweredChecked.retained rfl le_rfl) observed
    · obtain ⟨cleared,_,observed⟩ := bind_ok_inv _ _ _ rest
      exact compiler_observe_exit_slots ops law {labeled with table_depths := cleared}
        after state (checked.retained rfl le_rfl) observed

end Itasca.Runtime.Compiler

end
