import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrames
import Itasca.Runtime.Compiler.Local.Checking.ScopeInstructionPrefixes
import Itasca.Runtime.Compiler.Local.Source.StartJumpTableBounds
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTable
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableFrames
import Itasca.Runtime.Compiler.Local.Relations.Instructions.InstructionCheckAcceptance
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CallbackRetention
import Itasca.Runtime.Compiler.Local.Callbacks.MetadataPreservation
import Itasca.Runtime.Compiler.Local.Publication.ControlMapPublication
import Itasca.Runtime.Compiler.Local.Relations.Table.ControlTablePreservation

open WebAssembly

/-!
Proofs for Runtime / Compiler / Local / Checking.

This module collects InstructionBounds, ScopeAndRootChecks.
Each section documents its contracts and consumers.
-/

/-! ## InstructionBounds -/

section

/-!
Proofs for Runtime / Compiler / Local / Checking.

This module collects TableCallbackInstructionPrefix, ElseExitSlotBounds.
Each section documents its contracts and consumers.
-/

/-! ## TableCallbackInstructionPrefix -/

section

open Itasca.Representation

/-!
Checked instruction prefixes through br_table lowering. Target-dispatch effects compose through the loop into the callback while retaining existing checked instructions.
-/

/-! ## Instruction Prefix Retained -/

section

namespace Itasca.Compiler
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

end Itasca.Compiler

end

/-! ## Table Dispatch Instruction Prefix -/

section

namespace Itasca.Compiler
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

end Itasca.Compiler

end

/-! ## Table Branch Instruction Effect -/

section

namespace Itasca.Compiler
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

end Itasca.Compiler

end

/-! ## Table Loop Instruction Prefix -/

section

namespace Itasca.Compiler
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

end Itasca.Compiler

end

/-! ## Table Lower Instruction Prefix -/

section

namespace Itasca.Compiler
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

end Itasca.Compiler

end

/-! ## Table Callback Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

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
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table.inv ops before after state fallback types (.Ok ()) called with
  | @live labeled lowered cleared _ _ labelCall live lowerCall clearCall observed =>
    have checked := lower labeled labelCall live lowered lowerCall
    exact compiler_observe_open_instructions ops law {lowered with reachable := false, table_depths := cleared}
      after state (checked.retained rfl rfl) observed
  | @dead labeled cleared _ _ labelCall dead clearCall observed =>
    have checked := compiler_table_label_open_instructions ops law before labeled state fallback held labelCall
    exact compiler_observe_open_instructions ops law {labeled with table_depths := cleared}
      after state (checked.retained rfl rfl) observed

end Itasca.Compiler

end

end

/-! ## ElseExitSlotBounds -/

section

/-! ## ElseCallbackInstructionPrefix -/

section

/-!
Checked instruction prefixes through else patching. OpenInstructionPrefix.append_patch feeds ElseTransition preservation and the completed else callback.
-/

/-! ## Open Instruction Append Patch -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- ELSE appends a possible skip and patches an earlier guard. The two effects
can be checked together even though the guard's new target is the resulting
end rather than the old end. Pending ownership is required only off the patch. -/
theorem OpenInstructionPrefix.append_patch {before after : runtime.bytecode.CompiledFunction}
    {pending next : Nat → Prop} (held : OpenInstructionPrefix before pending)
    (growth : InstructionCheckExtends before after) (sites : List Usize) (target : U32)
    (sitesInside : ∀ site ∈ sites, site.val < before.code.length)
    (fragment : List runtime.bytecode.Instr)
    (code : after.code.val = patchCode (before.code.val++fragment) sites target)
    (inside : target.val ≤ after.code.length)
    (owners : ∀ index, (∀ site ∈ sites, site.val ≠ index) → pending index → next index)
    (fresh : ∀ index instruction, fragment[index]? = some instruction →
      OpenInstructionCheck after next (before.code.length+index) instruction) :
    OpenInstructionPrefix after next := by
  intro index instruction found
  rw [code,patch_code_get] at found
  by_cases prior : index < before.code.val.length
  · split at found
    · rw [List.getElem?_append_left prior] at found
      cases original : before.code.val[index]? with
      | none => simp [original] at found
      | some old =>
        have same : retarget old target = instruction := by simpa [original] using found
        rw [← same]
        exact (held index old original).retarget growth target inside
    · rename_i unpatched
      rw [List.getElem?_append_left prior] at found
      exact (held index instruction found).grow growth (owners index (by simpa using unpatched))
  · have unpatched : ¬ ∃ site ∈ sites, site.val = index := by
      intro selected
      obtain ⟨site,member,equal⟩ := selected
      have bounded := sitesInside site member
      change site.val < before.code.val.length at bounded
      omega
    rw [if_neg unpatched,List.getElem?_append_right (by omega : before.code.val.length ≤ index)] at found
    have checked := fresh (index-before.code.val.length) instruction found
    have same : before.code.length+(index-before.code.val.length) = index := by
      change before.code.val.length+(index-before.code.val.length) = index
      omega
    simpa only [same] using checked

end Itasca.Compiler

end

/-! ## Else Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

private theorem pending_else {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {prior frame guard site condition old noEntry fixups normal}
    (transition : ElseTransition before after prior frame guard site condition old noEntry fixups normal)
    (hasIf : frame.if_pc = some guard) (index : Nat) (different : guard.val ≠ index)
    (owned : PendingInstructionSite before index) : PendingInstructionSite after index := by
  obtain ⟨owner,member,address,position,kind⟩ := owned
  rw [transition.beforeFrames] at member
  rcases List.mem_append.mp member with previous | current
  · refine ⟨owner,?_,address,position,kind⟩
    rw [transition.afterFrames]
    exact List.mem_append_left _ previous
  · have same : owner = frame := by simpa only [List.mem_singleton] using current
    subst owner
    rcases kind with guarded | branch
    · have equal : guard = address := Option.some.inj (hasIf.symm.trans guarded)
      exact False.elim (different (equal ▸ position))
    · refine ⟨{frame with kind := .Else,if_pc := none,end_reachable := frame.end_reachable || normal,fixups},?_,address,position,Or.inr ?_⟩
      · rw [transition.afterFrames]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      · change address ∈ fixups.val
        rw [transition.fixupsEq]
        exact List.mem_append_left _ branch

/-- The actual physical ELSE update checks its new skip, patches the old guard,
and transfers every remaining pending fixup to the updated frame. -/
theorem ElseTransition.instruction_prefix {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {prior frame guard site condition old noEntry fixups normal}
    (transition : ElseTransition before after prior frame guard site condition old noEntry fixups normal)
    (hasIf : frame.if_pc = some guard) (held : CompilerInstructionPrefix before)
    (growth : InstructionCheckExtends before.function after.function) : CompilerInstructionPrefix after := by
  let fragment : List runtime.bytecode.Instr := if normal then [.Jump core.num.U32.MAX] else []
  have guardInside := (List.getElem?_eq_some_iff.mp transition.guardCode).1
  have patch : patchCode (before.function.code.val++fragment) [guard] noEntry =
      (before.function.code.val++fragment).set guard.val (.JumpIfZero condition noEntry) := by
    have found := fetch_extend transition.guardCode fragment
    simp [patchCode,found,retarget]
  refine held.append_patch growth [guard] noEntry ?_ fragment ?_ ?_ ?_ ?_
  · intro selected member
    simp only [List.mem_singleton] at member
    subst selected
    exact guardInside
  · rw [patch]
    exact transition.codeEq
  · change noEntry.val ≤ after.function.code.val.length
    rw [transition.length]
  · intro index unpatched owned
    apply pending_else transition hasIf index (unpatched guard (by simp)) owned
  · intro index instruction found
    cases normal with
    | false => simp [fragment] at found
    | true =>
      cases index with
      | zero =>
        have same : .Jump core.num.U32.MAX = instruction := by simpa [fragment] using found
        rw [← same]
        apply OpenInstructionCheck.jump
        apply Or.inr
        unfold PendingInstructionSite
        rw [transition.afterFrames]
        refine ⟨_,List.mem_append_right _ (List.mem_singleton_self _),site,?_,Or.inr ?_⟩
        · simpa only [Nat.add_zero] using transition.sitePosition
        · change site ∈ fixups.val
          simp [transition.fixupsEq]
      | succ index => simp [fragment] at found

end Itasca.Compiler

end

/-! ## Else Callback Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Actual ELSE preserves all stored instruction checks on live, terminated,
and unentered arms. Guard syntax and physical frame geometry come from the
source prefix; numerical PC room is independent of callback success. -/
theorem compiler_else_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (frames : before.frames.val = prior++[frame])
    (guardCode : ∀ guard, frame.if_pc = some guard → ∃ condition,
      before.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX))
    (unentered : frame.if_pc = none → before.reachable = false)
    (pcBound : before.function.code.val.length+1 ≤ U32.max)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_else_tables ops law before after state bt called)
    (compiler_else_stable_result ops law before after state bt (.Ok ()) called).capacity
    (compiler_else_code_mono ops law before after state bt called)
  cases hasIf : frame.if_pc with
  | none =>
    have effect := compiler_else_unentered ops law before state bt frame prior frames (unentered hasIf) hasIf
    rw [called,WP.spec_ok] at effect
    obtain ⟨_,code,afterFrames⟩ := effect rfl
    refine held.append growth ?_ [] (by simpa using congrArg alloc.vec.Vec.val code) (by simp)
    intro index owned
    obtain ⟨owner,member,site,position,kind⟩ := owned
    rw [frames] at member
    rcases List.mem_append.mp member with previous | current
    · refine ⟨owner,?_,site,position,kind⟩
      rw [afterFrames]
      exact List.mem_append_left _ previous
    · have same : owner = frame := by simpa only [List.mem_singleton] using current
      subst owner
      rcases kind with guard | branch
      · simp [hasIf] at guard
      · refine ⟨{frame with kind := .Else,if_pc := none},?_,site,position,Or.inr branch⟩
        rw [afterFrames]
        exact List.mem_append_right _ (List.mem_singleton_self _)
  | some guard =>
    obtain ⟨condition,original⟩ := guardCode guard hasIf
    obtain ⟨target,fixups,transition⟩ : ∃ target fixups,
        ElseTransition before after prior frame guard (alloc.vec.Vec.len before.function.code)
          condition core.num.U32.MAX target fixups before.reachable := by
      cases live : before.reachable with
      | false =>
        let target : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
        have targetAt : target.val = before.function.code.val.length := rfl
        have effect := compiler_else_dead ops law before state bt frame prior guard condition target frames live hasIf original targetAt
        rw [called,WP.spec_ok] at effect
        obtain ⟨_,code,afterFrames⟩ := effect rfl
        refine ⟨target,frame.fixups,?_⟩
        exact ⟨frames,by simpa using afterFrames,original,rfl,by simpa using targetAt,by simp,by simpa using code⟩
      | true =>
        let target : U32 := UScalar.ofNatCore (before.function.code.val.length+1) (by scalar_tac)
        have targetAt : target.val = before.function.code.val.length+1 := rfl
        obtain ⟨_,code,fixups,appended,afterFrames⟩ := compiler_else_live_success ops law before after state bt frame prior guard
          condition target frames live hasIf original targetAt called
        refine ⟨target,fixups,?_⟩
        exact ⟨frames,by simpa using afterFrames,original,rfl,by simpa using targetAt,by simpa using appended,by simpa using code⟩
    exact transition.instruction_prefix hasIf held growth

end Itasca.Compiler

end

end

/-! ## ElseExitSlotBounds -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- ELSE records the completed THEN arm's result interval, retaining previous
forward exits whether the arm falls through or is already terminated. -/
theorem ElseTransition.exit_slots {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {prior frame guard site condition old noEntry fixups normal}
    (transition : ElseTransition before after prior frame guard site condition old noEntry fixups normal)
    (held : FrameExitSlotBounds before)
    (capacity : before.function.slot_count.val ≤ after.function.slot_count.val)
    (region : normal = true → frame.height.val+frame.results.val ≤ before.function.slot_count.val) :
    FrameExitSlotBounds after := by
  intro selected member live
  rw [transition.afterFrames] at member
  rcases List.mem_append.mp member with previous | current
  · exact (held selected (by rw [transition.beforeFrames]; exact List.mem_append_left _ previous) live).trans capacity
  · have same : selected = {frame with kind := .Else,if_pc := none,end_reachable := frame.end_reachable || normal,fixups} := by
      simpa only [List.mem_singleton] using current
    subst selected
    change (frame.end_reachable || normal) = true at live
    by_cases prior : frame.end_reachable = true
    · exact (held frame (by simp [transition.beforeFrames]) prior).trans capacity
    · have dead : frame.end_reachable = false := Bool.eq_false_iff.mpr prior
      have current : normal = true := by simpa [dead] using live
      exact (region current).trans capacity

/-- Actual ELSE retains recorded exit-slot regions and accounts for a normal
THEN exit using the independently typed source result interval. -/
theorem compiler_else_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (frames : before.frames.val = prior++[frame])
    (guardCode : ∀ guard, frame.if_pc = some guard → ∃ condition,
      before.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX))
    (unentered : frame.if_pc = none → before.reachable = false)
    (normal : before.reachable = true → frame.height.val+frame.results.val ≤ before.function.slot_count.val)
    (pcBound : before.function.code.val.length+1 ≤ U32.max)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  have capacity := (compiler_else_stable_result ops law before after state bt (.Ok ()) called).capacity
  cases hasIf : frame.if_pc with
  | none =>
    have effect := compiler_else_unentered ops law before state bt frame prior frames (unentered hasIf) hasIf
    rw [called,WP.spec_ok] at effect
    obtain ⟨_,code,afterFrames⟩ := effect rfl
    intro selected member live
    rw [afterFrames] at member
    rcases List.mem_append.mp member with previous | current
    · exact (held selected (by rw [frames]; exact List.mem_append_left _ previous) live).trans capacity
    · have same : selected = {frame with kind := .Else,if_pc := none} := by simpa only [List.mem_singleton] using current
      subst selected
      exact (held frame (by simp [frames]) live).trans capacity
  | some guard =>
    obtain ⟨condition,original⟩ := guardCode guard hasIf
    obtain ⟨target,fixups,transition⟩ : ∃ target fixups,
        ElseTransition before after prior frame guard (alloc.vec.Vec.len before.function.code)
          condition core.num.U32.MAX target fixups before.reachable := by
      cases live : before.reachable with
      | false =>
        let target : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
        have targetAt : target.val = before.function.code.val.length := rfl
        have effect := compiler_else_dead ops law before state bt frame prior guard condition target frames live hasIf original targetAt
        rw [called,WP.spec_ok] at effect
        obtain ⟨_,code,afterFrames⟩ := effect rfl
        refine ⟨target,frame.fixups,?_⟩
        exact ⟨frames,by simpa using afterFrames,original,rfl,by simpa using targetAt,by simp,by simpa using code⟩
      | true =>
        let target : U32 := UScalar.ofNatCore (before.function.code.val.length+1) (by scalar_tac)
        have targetAt : target.val = before.function.code.val.length+1 := rfl
        obtain ⟨_,code,fixups,appended,afterFrames⟩ := compiler_else_live_success ops law before after state bt frame prior guard
          condition target frames live hasIf original targetAt called
        refine ⟨target,fixups,?_⟩
        exact ⟨frames,by simpa using afterFrames,original,rfl,by simpa using targetAt,by simpa using appended,by simpa using code⟩
    exact transition.exit_slots held capacity normal

end Itasca.Compiler

end

end

end

/-! ## ScopeAndRootChecks -/

section

/-!
# Scope And Root Checks

Pending instructions and scope closure satisfy compiler checks. Root-slot facts connect local scope checks to complete function compilation.
-/

/-! ## PendingInstructionClose -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Exact pending sites owned by one physical frame. IF guards are patched
before its ordinary forward-branch fixups. -/
def frameInstructionSites (frame : runtime.compiler.Frame) : List Usize :=
  frame.if_pc.toList++frame.fixups.val

/-- Once all sites of the popped frame have been patched, any remaining
pending instruction still has an owner in the retained physical frame stack. -/
theorem pending_instruction_pop {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (frame : runtime.compiler.Frame) (rest : alloc.vec.Vec runtime.compiler.Frame)
    (beforeFrames : before.frames.val = rest.val++[frame]) (afterFrames : after.frames = rest)
    (index : Nat) (unpatched : ∀ site ∈ frameInstructionSites frame, site.val ≠ index)
    (owned : PendingInstructionSite before index) : PendingInstructionSite after index := by
  obtain ⟨owner,member,site,position,kind⟩ := owned
  rw [beforeFrames] at member
  rcases List.mem_append.mp member with remaining | closing
  · exact ⟨owner,by simpa only [afterFrames] using remaining,site,position,kind⟩
  · have same : owner = frame := by simpa only [List.mem_singleton] using closing
    subst owner
    have selected : site ∈ frameInstructionSites frame := by
      rcases kind with guard | branch
      · simp [frameInstructionSites,guard]
      · exact List.mem_append_right _ branch
    exact False.elim (unpatched site selected position)

/-- Popping and patching a complete frame preserves checks of every stored
instruction, including instructions skipped by source reachability. -/
theorem compiler_instruction_prefix_close {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : CompilerInstructionPrefix before) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (beforeFrames : before.frames.val = rest.val++[frame]) (afterFrames : after.frames = rest)
    (growth : InstructionCheckExtends before.function after.function)
    (code : after.function.code.val = patchCode before.function.code.val (frameInstructionSites frame) target)
    (inside : target.val ≤ after.function.code.length) : CompilerInstructionPrefix after :=
  held.patch growth (frameInstructionSites frame) target code inside
    (pending_instruction_pop frame rest beforeFrames afterFrames)

end Itasca.Compiler

end

/-! ## ScopeCloseInstructionPrefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Actual nested END patches all sites of its closing frame, removes that
owner, and preserves every instruction's local check. Function-root END also
emits an epilogue and is treated separately. -/
theorem compiler_scope_close_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (geometry : ScopeCloseGeometry before) (mode : ScopeCloseMode geometry)
    (nonBody : geometry.frame.kind ≠ .Body) (maps : ControlMapPublication before)
    (coordinateFits : before.function.body_start.val+state.pos.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_end_tables ops law before after state kind bt called)
    (compiler_end_stable_result ops law before after state kind bt (.Ok ()) called).capacity
    (compiler_end_code_mono ops law before after state kind bt called)
  have inside : geometry.target.val ≤ after.function.code.length := by
    change geometry.target.val ≤ after.function.code.val.length
    rw [geometry.position]
    exact growth.code
  have mapFits : geometry.frame.map.val < before.function.controls.val.length := by
    apply maps.owners
    simp [activeControlMaps,geometry.frames]
  have canonical : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state .Block .Empty =
      .ok (.Ok (),after) := called
  cases mode with
  | unguarded noIf codeFits sourceFits emitCoordinateFits =>
    have effect := close_scope_effect ops law before state geometry.frame geometry.rest geometry.target
      geometry.frames nonBody noIf geometry.position geometry.branches mapFits coordinateFits
    rw [canonical,WP.spec_ok] at effect
    obtain ⟨frames,_,code,_⟩ := effect rfl
    apply compiler_instruction_prefix_close held geometry.frame geometry.rest geometry.target geometry.frames frames growth _ inside
    simpa only [frameInstructionSites,noIf,Option.toList_none,List.nil_append] using code
  | guarded guard condition old _ hasIf guardCode =>
    have effect := close_guarded_map_effect ops law before state geometry.frame geometry.rest geometry.target geometry.frames
      guard condition old nonBody hasIf guardCode geometry.position geometry.branches mapFits coordinateFits
    rw [canonical,WP.spec_ok] at effect
    obtain ⟨frames,code,_⟩ := effect rfl
    have patched : patchCode before.function.code.val [guard] geometry.target =
        before.function.code.val.set guard.val (.JumpIfZero condition geometry.target) := by
      simp [patchCode,guardCode,retarget]
    apply compiler_instruction_prefix_close held geometry.frame geometry.rest geometry.target geometry.frames frames growth _ inside
    rw [frameInstructionSites,hasIf]
    simp only [Option.toList_some]
    rw [patch_code_append_sites,patched]
    exact code

end Itasca.Compiler

end

/-! ## ScopeCloseExitSlots -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Actual nested END removes its frame while retaining slot bounds of every
outer forward exit, including guarded scope closure. -/
theorem compiler_scope_close_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (geometry : ScopeCloseGeometry before) (mode : ScopeCloseMode geometry)
    (nonBody : geometry.frame.kind ≠ .Body) (maps : ControlMapPublication before)
    (coordinateFits : before.function.body_start.val+state.pos.val ≤ Usize.max)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  have capacity := (compiler_end_stable_result ops law before after state kind bt (.Ok ()) called).capacity
  have mapFits : geometry.frame.map.val < before.function.controls.val.length := by
    apply maps.owners
    simp [activeControlMaps,geometry.frames]
  have canonical : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state .Block .Empty =
      .ok (.Ok (),after) := called
  cases mode with
  | unguarded noIf codeFits sourceFits emitCoordinateFits =>
    have effect := close_scope_effect ops law before state geometry.frame geometry.rest geometry.target
      geometry.frames nonBody noIf geometry.position geometry.branches mapFits coordinateFits
    rw [canonical,WP.spec_ok] at effect
    obtain ⟨frames,_,code,_⟩ := effect rfl
    exact held.pop geometry.frame (by rw [frames]; exact geometry.frames) capacity
  | guarded guard condition old _ hasIf guardCode =>
    have effect := close_guarded_map_effect ops law before state geometry.frame geometry.rest geometry.target geometry.frames
      guard condition old nonBody hasIf guardCode geometry.position geometry.branches mapFits coordinateFits
    rw [canonical,WP.spec_ok] at effect
    obtain ⟨frames,code,_⟩ := effect rfl
    exact held.pop geometry.frame (by rw [frames]; exact geometry.frames) capacity

end Itasca.Compiler

end

/-! ## ScopeEntryExitSlots -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Actual scope entry retains previous result bounds and introduces a frame
with no recorded forward exit, in both live and dormant source code. -/
theorem compiler_scope_entry_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (geometry : ScopeEntryGeometry before state bt) (mode : ScopeEntryMode geometry kind)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  have capacity := (compiler_enter_stable_result ops law before after state kind bt (.Ok ()) called).capacity
  cases mode with
  | block live position =>
    have effect := enter_block ops law before state geometry.ctrl geometry.prior bt geometry.signature geometry.pc
      geometry.controls geometry.selected geometry.valuesFit geometry.heightFits geometry.sourceFits position
      geometry.mapsFit geometry.framesFit live
    rw [called,WP.spec_ok] at effect
    obtain ⟨code,_,height,source,_,_,frames,_⟩ := effect rfl
    exact held.push _ frames rfl capacity
  | loop live position codeFits offsetsFit =>
    have effect := enter_loop ops law before state geometry.ctrl geometry.prior bt geometry.signature geometry.pc
      geometry.controls geometry.selected geometry.valuesFit geometry.heightFits geometry.sourceFits position codeFits offsetsFit
      geometry.mapsFit geometry.framesFit live
    rw [called,WP.spec_ok] at effect
    obtain ⟨code,_,height,source,_,_,frames,_⟩ := effect rfl
    exact held.push _ frames rfl capacity
  | if_ stack layout live position codeFits offsetsFit =>
    have effect := enter_if ops law before state geometry.ctrl geometry.prior bt geometry.signature geometry.pc
      stack layout codeFits offsetsFit geometry.controls geometry.selected geometry.valuesFit geometry.heightFits
      geometry.sourceFits position geometry.mapsFit geometry.framesFit live
    rw [called,WP.spec_ok] at effect
    obtain ⟨_,condition,height,source,conditionPosition,code,_,_,frames,_⟩ := effect rfl
    exact held.push _ frames rfl capacity
  | dead kind dormant position =>
    have effect := enter_dead ops law before state geometry.ctrl geometry.prior kind bt geometry.signature geometry.pc
      geometry.controls geometry.selected geometry.valuesFit geometry.heightFits geometry.sourceFits position
      geometry.mapsFit geometry.framesFit dormant
    rw [called,WP.spec_ok] at effect
    obtain ⟨code,_,height,source,_,_,frames,_⟩ := effect rfl
    exact held.push _ frames rfl capacity

end Itasca.Compiler

end

/-! ## RootInstructionPublication -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Patching the last frame and appending a checked epilogue discharges every
pending branch obligation. Earlier resolved end targets become strict because
the actual code vector grows. -/
theorem compiler_instruction_root_publish {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : CompilerInstructionPrefix before) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (beforeFrames : before.frames.val = rest.val++[frame]) (afterFrames : after.frames = rest)
    (closed : rest.val = []) (growth : InstructionCheckExtends before.function after.function)
    (fragment : List runtime.bytecode.Instr)
    (code : after.function.code.val = patchCode before.function.code.val (frameInstructionSites frame) target++fragment)
    (nonempty : 0 < fragment.length) (inside : target.val < after.function.code.length)
    (fresh : ∀ instruction ∈ fragment,
      runtime.bytecode.CompiledFunction.instruction_valid after.function instruction = .ok true) :
    CheckedInstructionPrefix after.function := by
  have strict : before.function.code.length < after.function.code.length := by
    change before.function.code.val.length < after.function.code.val.length
    rw [code,List.length_append,patch_code_length]
    omega
  intro instruction member
  rw [code] at member
  rcases List.mem_append.mp member with old | new
  · obtain ⟨index,bound,found⟩ := List.getElem_of_mem old
    have fetched : (patchCode before.function.code.val (frameInstructionSites frame) target)[index]? = some instruction := by
      simp [List.getElem?_eq_getElem bound,found]
    rw [patch_code_get] at fetched
    split at fetched
    · cases original : before.function.code.val[index]? with
      | none => simp [original] at fetched
      | some prior =>
        have same : retarget prior target = instruction := by simpa [original] using fetched
        rw [← same]
        exact (held index prior original).retarget_accepts growth target inside
    · rename_i unchanged
      have old := held index instruction fetched
      have noOwner : PendingInstructionSite before index → False := by
        intro owned
        have remaining := pending_instruction_pop frame rest beforeFrames afterFrames index (by simpa using unchanged) owned
        obtain ⟨owner,member,_⟩ := remaining
        rw [afterFrames,closed] at member
        cases member
      have checked : OpenInstructionCheck before.function (fun _ => False) index instruction :=
        old.grow (.refl _) noOwner
      exact checked.publish growth strict
  · exact fresh instruction new

end Itasca.Compiler

end

/-! ## RootCloseInstructionPrefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- The actual final END patches the root frame and emits a checked return.
Source result layout bounds the epilogue. No final checker success or completed
function instruction certificate is assumed. -/
theorem compiler_root_close_checked_instructions_of_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (geometry : ScopeCloseGeometry before) (body : geometry.frame.kind = .Body)
    (closed : geometry.rest.val = []) (noIf : geometry.frame.if_pc = none)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (emitCoordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (coordinateFits : before.function.body_start.val+state.pos.val ≤ Usize.max)
    (maps : ControlMapPublication before) (held : CompilerInstructionPrefix before)
    (returnFits : geometry.frame.height.val+
      (if scopeExitLive before.reachable geometry.frame then geometry.frame.results else 0#u32).val ≤ after.function.slot_count.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (),after)) :
    CheckedInstructionPrefix after.function := by
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_end_tables ops law before after state kind bt called)
    (compiler_end_stable_result ops law before after state kind bt (.Ok ()) called).capacity
    (compiler_end_code_mono ops law before after state kind bt called)
  have mapFits : geometry.frame.map.val < before.function.controls.val.length := by
    apply maps.owners
    simp [activeControlMaps,geometry.frames]
  have canonical : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state .Block .Empty =
      .ok (.Ok (),after) := called
  have effect := close_function_effect ops law before state geometry.frame geometry.rest geometry.target geometry.frames body noIf
    geometry.position geometry.branches mapFits coordinateFits codeFits sourceFits emitCoordinateFits
  rw [canonical,WP.spec_ok] at effect
  obtain ⟨frames,reachable,code,_⟩ := effect rfl
  apply compiler_instruction_root_publish held geometry.frame geometry.rest geometry.target geometry.frames frames closed growth
    [.Return geometry.frame.height (if scopeExitLive before.reachable geometry.frame then geometry.frame.results else 0#u32)]
    (by simpa only [frameInstructionSites,noIf,Option.toList_none,List.nil_append] using code) (by simp)
  · change geometry.target.val < after.function.code.val.length
    rw [code,List.length_append,patch_code_length,List.length_singleton,geometry.position]
    omega
  · intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    exact (CoreInstructionBounds.return_ returnFits).accepts

end Itasca.Compiler

end

/-! ## FunctionStartExitSlots -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Actual fresh construction and function-start introduce only the root frame,
whose forward-exit flag is initially clear. -/
theorem compiler_start_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (signatures : Slice runtime.compiler.Signature)
    (functionSlots : Slice U32) (budget : runtime.compiler.Budget A) (batchStart : Usize)
    (initial started : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (signature : runtime.compiler.Signature)
    (bodyBegin bodyEnd : Usize)
    (lookup : signatures.val[typeIndex.val]? = some signature)
    (beginFits : batchStart.val+bodyBegin.val ≤ Usize.max)
    (endFits : batchStart.val+bodyEnd.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (begun : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial ctx typeIndex bodyBegin bodyEnd = .ok (.Ok (),started)) : FrameExitSlotBounds started := by
  have newPost := compiler_new ops signatures functionSlots budget batchStart
  rw [created,WP.spec_ok] at newPost
  obtain ⟨layout,emptyLocals,emptyOperands,emptyMaps,emptyFrames,emptyCode,reachable,sigs,widths,coordinate⟩ := newPost
  have startPost := compiler_function_start_raw ops law initial ctx typeIndex signature bodyBegin bodyEnd
    (by simpa only [sigs] using lookup) (by simpa only [coordinate] using beginFits)
    (by simpa only [coordinate] using endFits) emptyLocals layout emptyOperands
    (by simp [emptyMaps]; scalar_tac) (by simp [emptyFrames]; scalar_tac)
  rw [begun,WP.spec_ok] at startPost
  obtain ⟨_,_,frames,_⟩ := startPost rfl
  intro frame member live
  rw [frames,emptyFrames,List.nil_append] at member
  have same := List.mem_singleton.mp member
  subst frame
  simp at live

end Itasca.Compiler

end

end
