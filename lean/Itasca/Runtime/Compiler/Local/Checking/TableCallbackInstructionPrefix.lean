import Itasca.Runtime.Compiler.Local.Checking.NumericInstructionPrefix
import Itasca.Runtime.Compiler.Local.Checking.InstructionAppendEffect
import Itasca.Runtime.Compiler.Local.Source.TableTransferBounds
import Itasca.Runtime.Compiler.Local.Checking.LoopBranchInstructionPrefix
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableSafetyEffects
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableLower
import Itasca.Runtime.Compiler.Local.Relations.Instructions.CoreInstructionAcceptance

/-!
Checked instruction prefixes through br_table lowering. Target-dispatch effects compose through the loop into the callback while retaining existing checked instructions.
-/

/-! ## Instruction Prefix Retained -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Budget, scratch labels, reachability, and operand observations do not
change the checks or owners of stored instructions. -/
theorem CompilerInstructionPrefix.retained {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : CompilerInstructionPrefix before)
    (function : after.function = before.function) (frames : after.frames = before.frames) :
    CompilerInstructionPrefix after := by
  have owners : PendingInstructionSite after = PendingInstructionSite before := by
    funext index
    simp only [PendingInstructionSite,frames]
  simpa only [CompilerInstructionPrefix,function,owners] using held

end Itasca.Runtime.Compiler

end

/-! ## Table Dispatch Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- An emitted dispatch word can be deferred at its exact new position while
every previously stored instruction retains its ordinary prefix check. -/
theorem Emitted.defer_new_instruction {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction : runtime.bytecode.Instr} (emitted : Emitted before after instruction)
    (held : CompilerInstructionPrefix before) :
    CompilerInstructionPrefixExcept after before.function.code.length := by
  have growth := emitted.instruction_check_extends
  have frames : after.frames = before.frames := by
    obtain ⟨budget,code,sources,rfl,_,_⟩ := emitted
    rfl
  have appended : after.function.code.val = before.function.code.val++[instruction] := by
    obtain ⟨budget,code,sources,rfl,appended,_⟩ := emitted
    exact appended
  intro index selected different found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [appended,List.length_append,List.length_singleton] at bound
  change index ≠ before.function.code.val.length at different
  have prior : index < before.function.code.val.length := by omega
  rw [appended,List.getElem?_append_left prior] at found
  apply (held index selected found).grow growth
  intro owned
  simpa only [PendingInstructionSite,frames] using owned

/-- Metadata-only changes preserve all prefix checks from numerical growth and
unchanged ownership. No new instruction obligation is introduced. -/
theorem InstructionAppendEffect.of_unchanged_code {A : Type}
    {before after : runtime.compiler.FunctionCompiler A}
    (growth : InstructionCheckExtends before.function after.function)
    (code : after.function.code = before.function.code) (frames : after.frames = before.frames) :
    InstructionAppendEffect before after := by
  refine ⟨growth,[],by simpa using congrArg alloc.vec.Vec.val code,?_,by simp⟩
  intro index owned
  simpa only [PendingInstructionSite,frames] using owned

/-- The target-row append preceding each actual table stub preserves every
check, including the temporary dispatch exception. Budget state is arbitrary. -/
theorem instruction_append_effect_jump_table {A : Type} (before : runtime.compiler.FunctionCompiler A)
    (budget : runtime.compiler.Budget A) (table : alloc.vec.Vec U32) (target : U32)
    (appended : table.val = before.function.jump_tables.val++[target]) :
    InstructionAppendEffect before {before with budget,function := {before.function with jump_tables := table}} := by
  apply InstructionAppendEffect.of_unchanged_code (before := before)
    (after := {before with budget,function := {before.function with jump_tables := table}}) _ rfl rfl
  refine ⟨le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,?_⟩
  change before.function.jump_tables.val.length ≤ table.val.length
  rw [appended,List.length_append,List.length_singleton]
  omega

end Itasca.Runtime.Compiler

end

/-! ## Table Branch Instruction Effect -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- One actual table arm appends a checked transfer and an owned or backward
jump. Its source transfer interval and allocation room are retained separately
from the temporarily incomplete dispatch instruction. -/
theorem compiler_table_branch_instruction_effect {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (limit : Nat)
    (lookup : before.table_depths.val[index.val]? = some depth)
    (safe : TableLoopSafe before index.val limit) (limitFits : limit ≤ Usize.max)
    (transfers : TableTransferBounds before)
    (heightFits : before.height.val ≤ before.function.slot_count.val)
    (called : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    InstructionAppendEffect before after := by
  obtain ⟨target,budget,table,_,appended,branch⟩ :=
    compiler_table_branch_success ops law before after index depth lookup called
  let staged := {before with budget,function := {before.function with jump_tables := table}}
  change runtime.compiler.control.FunctionCompiler.branch ops staged depth 1#u32 false = .ok (.Ok (),after) at branch
  obtain ⟨selected,frame,source,found,position,operands⟩ :=
    compiler_branch_arguments_success ops staged after depth 1#u32 branch
  have geometry := transfers depth (List.mem_of_getElem? lookup) selected frame found position
  have inside := (List.getElem?_eq_some_iff.mp lookup).1
  have room := safe.room
  have codeFits : before.function.code.val.length+2 ≤ Usize.max := by omega
  have aligned := safe.aligned
  change before.function.source_offsets.val.length = before.function.code.val.length at aligned
  have offsetsFit : before.function.source_offsets.val.length+2 ≤ Usize.max := by omega
  have prepared := instruction_append_effect_jump_table before budget table target appended
  apply prepared.prepend_unchanged rfl
  have sourcePosition : source.val+(frameBranchWidth frame).val+1 = before.height.val := operands
  by_cases loop : frame.kind = .Loop
  · have width : frameBranchWidth frame = frame.params := by simp [frameBranchWidth,loop]
    rw [width] at sourcePosition geometry
    exact compiler_branch_loop_instruction_effect ops law staged after frame selected depth source 1#u32
      found position loop sourcePosition (by omega) (by simpa only [staged] using (show source.val+frame.params.val ≤ before.function.slot_count.val by omega))
      (geometry.2 loop) codeFits offsetsFit safe.coordinate branch
  · have width : frameBranchWidth frame = frame.results := by
      cases kind : frame.kind <;> simp_all [frameBranchWidth]
    rw [width] at sourcePosition geometry
    exact compiler_branch_forward_instruction_effect ops law staged after frame selected depth source 1#u32
      found position loop sourcePosition (by omega) (by simpa only [staged] using (show source.val+frame.results.val ≤ before.function.slot_count.val by omega))
      (safe.fixups.lookup found (by omega)) codeFits offsetsFit safe.coordinate branch

end Itasca.Runtime.Compiler

end

/-! ## Table Loop Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The finite table builder preserves all stored checks except the dispatch
word whose rows are still being constructed. -/
theorem TableBranchRun.instruction_prefix_except {A : Type} {ops : runtime.platform.Alloc A}
    (law : Platform.AllocCorrect ops) {before after : runtime.compiler.FunctionCompiler A}
    {index limit omitted : Nat} (run : TableBranchRun ops before index after)
    (safe : TableLoopSafe before index limit) (limitFits : limit ≤ Usize.max)
    (transfers : TableTransferBounds before)
    (heightFits : before.height.val ≤ before.function.slot_count.val)
    (held : CompilerInstructionPrefixExcept before omitted) :
    CompilerInstructionPrefixExcept after omitted := by
  induction run with
  | done => exact held
  | @cons before middle after index inside called rest ih =>
    let depth := before.table_depths.val[index.val]
    have lookup : before.table_depths.val[index.val]? = some depth := List.getElem?_eq_getElem inside
    have effect := compiler_table_branch_instruction_effect ops law before middle index depth limit
      lookup safe limitFits transfers heightFits called
    obtain ⟨_,_,_,height,code⟩ := compiler_table_target_code ops law before middle index depth lookup called
    have depths := compiler_table_branch_depths ops before middle index (.Ok ()) called
    have capacity := (compiler_table_branch_fixed ops law before middle index depth lookup called).stable.capacity
    apply ih (safe.advance ops law inside called) (transfers.advance code depths height)
    · rw [height]
      exact heightFits.trans capacity
    · exact effect.apply_except omitted held

end Itasca.Runtime.Compiler

end

/-! ## Table Lower Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The actual dispatch and all target stubs establish the complete instruction
prefix. Source stack geometry supplies the selector, and the deferred dispatch
check is discharged against the completed side table. -/
theorem compiler_lower_table_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (stack : List valtype) (layout : CompilerLayout before (stack++[.I32]))
    (aligned : SourceAligned before)
    (depths : ∀ depth ∈ before.table_depths.val, depth.val < before.frames.val.length)
    (fixups : FixupBudget before.frames.val before.function.code.val.length)
    (room : before.function.code.val.length+1+2*before.table_depths.val.length ≤ Usize.max)
    (tables : before.function.jump_tables.val.length ≤ before.function.code.val.length)
    (coordinate : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (nonempty : 0 < before.table_depths.val.length)
    (transfers : TableTransferBounds before)
    (heightFits : before.height.val ≤ before.function.slot_count.val)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  obtain ⟨start,len,selector,emitted,startAt,count,operand,emission,run⟩ :=
    compiler_lower_table_success ops law before after called
  have selected := compiler_operand ops before (stack++[.I32]) layout 1#usize (by decide) (by simp)
  rw [operand,WP.spec_ok] at selected
  obtain ⟨word,equal,wordAt⟩ := selected
  have same : word = selector := core.result.Result.Ok.inj equal.symm
  subst word
  have selectorFits : selector.val+1 ≤ before.function.slot_count.val := by
    have height := layout.height
    simp [offset] at wordAt
    simp only [slots_append,slots, width] at height
    omega
  have deferred := emission.defer_new_instruction held
  have growth := emission.instruction_check_extends
  obtain ⟨targets,built⟩ := run.built law
  simp only [List.drop_zero] at built
  obtain ⟨budget,code,sources,frame,appended,sourceAppend⟩ := emission
  subst emitted
  have codeSize : code.val.length = before.function.code.val.length+1 := by simp [appended]
  have sourceSize : sources.val.length = before.function.source_offsets.val.length+1 := by
    have size := congrArg List.length sourceAppend
    simpa only [List.length_map,List.length_append,List.length_singleton] using size
  have safe : TableLoopSafe {before with budget,function := {before.function with code,source_offsets := sources}} 0 Usize.max := by
    refine ⟨?_,depths,fixups.mono (by change before.function.code.val.length ≤ code.val.length; omega),?_,?_,coordinate⟩
    · change sources.val.length = code.val.length
      rw [sourceSize,codeSize,aligned]
    · change code.val.length+2*(before.table_depths.val.length-0) ≤ Usize.max
      simpa only [codeSize,Nat.sub_zero] using room
    · change before.function.jump_tables.val.length ≤ code.val.length
      omega
  have transfer : TableTransferBounds {before with budget,function := {before.function with code,source_offsets := sources}} := by
    intro depth member index frame found position
    have old := transfers depth member index frame found position
    exact ⟨old.1,fun loop => (old.2 loop).trans (by change before.function.code.val.length ≤ code.val.length; omega)⟩
  have final := run.instruction_prefix_except law safe le_rfl transfer heightFits deferred
  apply final.complete
  intro instruction found
  obtain ⟨fragment,finalCode,_⟩ := built.code_prefix
  have header : after.function.code.val[before.function.code.length]? = some (.JumpTable selector start len) := by
    rw [finalCode,appended,List.append_assoc]
    change (before.function.code.val++(.JumpTable selector start len :: fragment))[before.function.code.val.length]? = _
    simp
  rw [header] at found
  cases Option.some.inj found
  apply CoreInstructionBounds.accepts
  apply CoreInstructionBounds.jumpTable
  · have capacity := (run.fixed law).stable.capacity
    exact selectorFits.trans capacity
  · omega
  · change start.val+len.val ≤ after.function.jump_tables.val.length
    rw [built.tables,List.length_append,built.length]
    change start.val+len.val ≤ before.function.jump_tables.val.length+before.table_depths.val.length
    omega

end Itasca.Runtime.Compiler

end

/-! ## Table Callback Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Collecting a table label preserves instruction checks and pending owners. -/
theorem compiler_table_label_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops before state depth = .ok (.Ok (),after)) : CompilerInstructionPrefix after := by
  obtain ⟨budget,depths,frame,_⟩ := compiler_table_label_success ops law before after state depth called
  exact held.retained (by rw [frame]) (by rw [frame])

/-- Lift the source-derived raw table proof through the final default label,
scratch-buffer clearing, and dead-stack observation of the actual callback. -/
theorem compiler_br_table_callback_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (held : CompilerInstructionPrefix before)
    (lower : ∀ labeled,
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
        ops before state fallback = .ok (.Ok (),labeled) → labeled.reachable = true → ∀ lowered,
      runtime.compiler.control.FunctionCompiler.lower_table_branches ops labeled = .ok (.Ok (),lowered) →
      CompilerInstructionPrefix lowered)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types = .ok (.Ok (),after)) : CompilerInstructionPrefix after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table at called
  obtain ⟨⟨result,labeled⟩,labelCalled,rest⟩ := bind_ok_inv _ _ _ called
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok unit =>
    cases unit
    have checked := compiler_table_label_open_instructions ops law before labeled state fallback held labelCalled
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
        exact compiler_observe_open_instructions ops law {lowered with reachable := false,table_depths := cleared}
          after state (loweredChecked.retained rfl rfl) observed
    · obtain ⟨cleared,_,observed⟩ := bind_ok_inv _ _ _ rest
      exact compiler_observe_open_instructions ops law {labeled with table_depths := cleared}
        after state (checked.retained rfl rfl) observed

end Itasca.Runtime.Compiler

end
