import Itasca.Runtime.Compiler.Local.Capacity.CallbackCapacity
import Itasca.Runtime.Compiler.Local.Capacity.BranchAvailability
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableFrames
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableArguments
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableSafetyEffects
import Itasca.Runtime.Compiler.Local.Capacity.AuxiliaryAvailability
import Itasca.Runtime.Compiler.Local.Lowering.Control.LoweringBranchIf
import Itasca.Runtime.Compiler.Local.Capacity.BranchLabelAvailability
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableMetadata

/-!
Availability of br_table compilation, from one target through the target loop and final callback. Width and growth certificates preserve capacity across each collected label.
-/

/-! ## Callback Capacity Growth -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- A bounded internal lowering step consumes its numeric allowance without
requiring a single-emission shape. This applies to branch-table stubs, whose
fixup updates and optional copies have separate checked structural effects. -/
theorem CallbackCapacity.after_growth {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {state bound count amount} (capacity : CallbackCapacity before state bound (count+amount))
    (code : after.function.code.length ≤ before.function.code.length+amount)
    (sources : after.function.source_offsets.length ≤ before.function.source_offsets.length+amount)
    (localsSame : after.function.local_slots = before.function.local_slots)
    (coordinate : after.function.body_start.val+after.next_source.val ≤ Usize.max)
    (effect : CompilationBudgetEffect before.budget after.budget
      (fun counter => if counter = .instructions then amount else 0)) :
    CallbackCapacity after state bound count := by
  have used := (effect.counts .instructions).2
  simp only [ChargeCounter.used,↓reduceIte] at used
  have limits := effect.limits
  rcases capacity with ⟨pc,codeCapacity,sourceCapacity,codeReserve,sourceReserve,_,instructions,operands,slots⟩
  refine ⟨by omega,by omega,by omega,by omega,by omega,coordinate,?_,operands,?_⟩
  · rw [limits]
    omega
  · rw [localsSame]
    exact slots

end Itasca.Runtime.Code

end

/-! ## Table Branch Availability -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- One actual branch-table stub publishes a dispatch target and accepts its
selector-dropping branch from source widths and independently bounded storage.
Only its at-most-two instructions consume compilation budget. -/
theorem compiler_table_branch_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 2)
    (index frameIndex : Usize) (depth : U32) (frame : runtime.compiler.Frame)
    (depthAt : compiler.table_depths.val[index.val]? = some depth)
    (frameAt : compiler.frames.val[frameIndex.val]? = some frame)
    (position : frameIndex.val + depth.val + 1 = compiler.frames.val.length)
    (widthFits : (match frame.kind with | .Loop => frame.params | _ => frame.results).val + 1 ≤ compiler.height.val)
    (tableCapacity : compiler.function.jump_tables.length < Usize.max)
    (tableReserve : compiler.function.jump_tables.length+1 ≤ bound)
    (fixupsCapacity : frame.fixups.length < Usize.max)
    (fixupsReserve : frame.fixups.length+1 ≤ bound) :
    runtime.compiler.control.FunctionCompiler.table_branch ops compiler index ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 2 else 0) ⦄ := by
  unfold runtime.compiler.control.FunctionCompiler.table_branch
  step with compiler_pc_available ops compiler (by have room := capacity.pc; omega)
    as ⟨status,current,same,pc,accepted,_⟩
  subst current
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available compiler.budget compiler.function.jump_tables pc
    tableCapacity tableReserve as ⟨status,budget,table,accepted,same,_⟩
  subst status budget
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  have inside := (List.getElem?_eq_some_iff.mp depthAt).1
  step as ⟨actual,found⟩
  have same : actual = depth := found.trans (List.getElem?_eq_some_iff.mp depthAt).2
  subst actual
  rw [(List.getElem?_eq_some_iff.mp depthAt).2]
  let staged := {compiler with function := {compiler.function with jump_tables := table}}
  have stagedCapacity : CallbackCapacity staged state bound 2 :=
    ⟨capacity.pc,capacity.codeCapacity,capacity.sourceCapacity,capacity.codeReserve,capacity.sourceReserve,
      capacity.coordinate,capacity.instructions,capacity.operands,capacity.slots⟩
  exact compiler_unconditional_branch_available ops law bound available staged state stagedCapacity frame frameIndex depth 1#u32
    frameAt position widthFits fixupsCapacity fixupsReserve

end Itasca.Runtime.Code

end

/-! ## Table Branch Widths -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Independent branch widths for the retained table labels. Only labels
actually named by the table must have operands in the current stack. -/
def TableWidthsFit {A : Type} (compiler : runtime.compiler.FunctionCompiler A) : Prop :=
  ∀ depth ∈ compiler.table_depths.val, ∀ (index : Usize) (frame : runtime.compiler.Frame),
    compiler.frames.val[index.val]? = some frame →
    index.val + depth.val + 1 = compiler.frames.val.length →
    (frameBranchWidth frame).val + 1 ≤ compiler.height.val

/-- Forward relocations change no source label's argument width. -/
theorem TableTargetCode.widths {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {depth} (effect : TableTargetCode before after depth) :
    after.frames.val.map frameBranchWidth = before.frames.val.map frameBranchWidth := by
  cases effect with
  | loop _ _ _ _ _ _ _ _ frames => rw [frames]
  | forward index frame source fixups site lookup position kind operands code frames appended sitePosition =>
    rw [frames,List.map_set]
    have selected : (before.frames.val.map frameBranchWidth)[index.val]? = some (frameBranchWidth frame) := by
      simp only [List.getElem?_map,lookup,Option.map_some]
    have bound := (List.getElem?_eq_some_iff.mp selected).1
    have same := (List.getElem?_eq_some_iff.mp selected).2
    change (before.frames.val.map frameBranchWidth).set index.val (frameBranchWidth frame) = _
    rw [← same]
    exact List.set_getElem_self bound

/-- The source operand condition survives every checked table stub, including
updates to a label subsequently targeted again by another arm. -/
theorem TableWidthsFit.advance {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {chosen} (fits : TableWidthsFit before) (effect : TableTargetCode before after chosen)
    (depths : after.table_depths = before.table_depths) (height : after.height = before.height) :
    TableWidthsFit after := by
  intro depth member index frame lookup position
  have frameBound := (List.getElem?_eq_some_iff.mp lookup).1
  have oldBound : index.val < before.frames.val.length := by rw [effect.frame_length] at frameBound; exact frameBound
  let old := before.frames.val[index.val]
  have oldLookup : before.frames.val[index.val]? = some old := List.getElem?_eq_getElem oldBound
  have widths := congrArg (fun values => values[index.val]?) effect.widths
  simp only [List.getElem?_map,lookup,oldLookup,Option.map_some,Option.some.injEq] at widths
  have memberBefore : depth ∈ before.table_depths.val := by simpa only [depths] using member
  have beforePosition : index.val + depth.val + 1 = before.frames.val.length := by
    rw [effect.frame_length] at position
    exact position
  rw [height,widths]
  exact fits depth memberBefore index old oldLookup beforePosition

end Itasca.Runtime.Code

end

/-! ## Table Loop Availability -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- The complete table-stub lowering loop accepts from independent source
widths and demand for the remaining labels. Actual successful intermediate
steps establish the existing code, fixup, and metadata invariants internally. -/
theorem compiler_table_loop_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (index : Usize) (inside : index.val ≤ compiler.table_depths.val.length) (limit : Nat)
    (safe : TableLoopSafe compiler index.val limit) (widths : TableWidthsFit compiler)
    (capacity : CallbackCapacity compiler state bound (2*(compiler.table_depths.val.length-index.val))) :
    runtime.compiler.control.FunctionCompiler.lower_table_branches_loop ops compiler index (.Ok ()) ⦃ out =>
      ∃ after, out = compilerSnapshot after (.Ok ()) ∧
        CompilationBudgetEffect compiler.budget after.budget
          (fun counter => if counter = .instructions then 2*(compiler.table_depths.val.length-index.val) else 0) ⦄ := by
  unfold runtime.compiler.control.FunctionCompiler.lower_table_branches_loop
  apply loop.spec_decr_nat (fun p => compiler.table_depths.val.length-p.2.1.val)
    (fun p => index.val ≤ p.2.1.val ∧ p.2.1.val ≤ compiler.table_depths.val.length ∧ p.2.2 = .Ok () ∧
      p.1.table_depths = compiler.table_depths ∧ TableLoopSafe p.1 p.2.1.val limit ∧ TableWidthsFit p.1 ∧
      CallbackCapacity p.1 state bound (2*(compiler.table_depths.val.length-p.2.1.val)) ∧
      CompilationBudgetEffect compiler.budget p.1.budget
        (fun counter => if counter = .instructions then 2*(p.2.1.val-index.val) else 0))
  · rintro ⟨current,i,result⟩ ⟨lower,upper,rfl,depths,heldSafe,heldWidths,heldCapacity,effect⟩
    dsimp only at lower upper depths heldSafe heldWidths heldCapacity effect
    unfold runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.body
    simp only
    split
    · rename_i more
      have currentInside : i.val < current.table_depths.val.length := by scalar_tac
      have originalInside : i.val < compiler.table_depths.val.length := by simpa only [depths] using currentInside
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      let depth := current.table_depths.val[i.val]
      have depthAt : current.table_depths.val[i.val]? = some depth := List.getElem?_eq_getElem currentInside
      have depthBound := heldSafe.depths depth (List.mem_of_getElem? depthAt)
      let frameIndex := Usize.ofNatCore (current.frames.val.length-depth.val-1)
        (by have maximum := (alloc.vec.Vec.len current.frames).hBounds
            change current.frames.val.length < 2^UScalarTy.Usize.numBits at maximum; omega)
      have frameBound : frameIndex.val < current.frames.val.length := by
        change current.frames.val.length-depth.val-1 < current.frames.val.length
        omega
      let frame := current.frames.val[frameIndex.val]
      have frameAt : current.frames.val[frameIndex.val]? = some frame := List.getElem?_eq_getElem frameBound
      have position : frameIndex.val+depth.val+1 = current.frames.val.length := by
        change current.frames.val.length-depth.val-1+depth.val+1 = current.frames.val.length
        omega
      have widthFits := heldWidths depth (List.mem_of_getElem? depthAt) frameIndex frame frameAt position
      have primitiveCapacity : CallbackCapacity current state bound 2 := heldCapacity.mono (by omega)
      have codeCapacity := primitiveCapacity.codeCapacity
      have codeReserve := primitiveCapacity.codeReserve
      simp only [alloc.vec.Vec.length] at codeCapacity codeReserve
      have tables := heldSafe.tables
      have fixups := heldSafe.fixups frame (List.mem_of_getElem? frameAt)
      obtain ⟨⟨status,next⟩,called,accepted,stepEffect⟩ := WP.spec_imp_exists
        (compiler_table_branch_available ops law bound available current state primitiveCapacity i frameIndex depth frame
          depthAt frameAt position widthFits (by change current.function.jump_tables.val.length < Usize.max; omega)
          (by change current.function.jump_tables.val.length+1 ≤ bound; omega)
          (by change frame.fixups.val.length < Usize.max; omega)
          (by change frame.fixups.val.length+1 ≤ bound; omega))
      dsimp only at accepted stepEffect
      subst status
      rw [called]
      simp only [uncurry_apply_pair,bind_ok]
      step as ⟨nextIndex,increment⟩
      have progress : nextIndex.val = i.val+1 := by scalar_tac
      have nextSafe := heldSafe.advance ops law currentInside called
      have nextDepths := compiler_table_branch_depths ops current next i (.Ok ()) called
      obtain ⟨target,_,_,height,codeEffect⟩ := compiler_table_target_code ops law current next i depth depthAt called
      have nextWidths := heldWidths.advance codeEffect nextDepths height
      have fixed := (compiler_table_branch_fixed ops law current next i depth depthAt called).stable.fields
      have growth := compiler_table_branch_growth ops law current next i (.Ok ()) called
      have sourceGrowth : next.function.source_offsets.length ≤ current.function.source_offsets.length+2 := by
        change next.function.source_offsets.val.length ≤ current.function.source_offsets.val.length+2
        rw [nextSafe.aligned,heldSafe.aligned]
        exact growth
      have coordinate : next.function.body_start.val+next.next_source.val ≤ Usize.max := nextSafe.coordinate
      have countEq : 2*(compiler.table_depths.val.length-i.val) =
          2*(compiler.table_depths.val.length-(i.val+1))+2 := by omega
      rw [countEq] at heldCapacity
      have nextCapacity := heldCapacity.after_growth (by simpa only [alloc.vec.Vec.length] using growth)
        sourceGrowth fixed.2.2.2.2.2.2.1 coordinate stepEffect
      refine ⟨?_,?_,nextDepths.trans depths,?_,nextWidths,?_,?_,?_⟩
      · omega
      · omega
      · simpa only [progress] using nextSafe
      · simpa only [progress] using nextCapacity
      · have combined := effect.trans stepEffect
        exact combined.weaken (by intro counter; cases counter <;> simp <;> omega)
      · omega
    · rename_i stop
      have done : i.val = compiler.table_depths.val.length := by
        have currentDone : current.table_depths.val.length ≤ i.val := by scalar_tac
        rw [depths] at currentDone
        omega
      simp only [WP.spec_ok]
      refine ⟨current,rfl,?_⟩
      simpa only [done] using effect
  · refine ⟨Nat.le_refl _,inside,rfl,rfl,safe,widths,capacity,?_⟩
    simpa using CompilationBudgetEffect.refl compiler.budget

end Itasca.Runtime.Code

end

/-! ## Table Lower Availability -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Complete raw branch-table lowering accepts the dispatcher and all stubs.
The conservative instruction demand is one plus twice the number of labels;
all allocator requests are bounded independently of compiler success. -/
theorem compiler_lower_table_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound (2*compiler.table_depths.val.length+1))
    (aligned : SourceAligned compiler)
    (depthsValid : ∀ depth ∈ compiler.table_depths.val, depth.val < compiler.frames.val.length)
    (widths : TableWidthsFit compiler)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (tables : compiler.function.jump_tables.val.length ≤ compiler.function.code.val.length)
    (depthCount : compiler.table_depths.length ≤ U32.max) (selector : U32)
    (selectorAt : compiler.before.val[compiler.before.val.length-1]? = some selector) :
    runtime.compiler.control.FunctionCompiler.lower_table_branches ops compiler ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 2*compiler.table_depths.val.length+1 else 0) ⦄ := by
  unfold runtime.compiler.control.FunctionCompiler.lower_table_branches
  step with bounded_index_available (alloc.vec.Vec.len compiler.function.jump_tables)
    (by have room := capacity.pc; simp only [alloc.vec.Vec.length] at room; change compiler.function.jump_tables.val.length ≤ U32.max; omega)
    as ⟨status,start,accepted,_⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with bounded_index_available (alloc.vec.Vec.len compiler.table_depths) depthCount as ⟨status,length,accepted,_⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with compiler_condition ops compiler selector selectorAt as ⟨status,accepted⟩
  subst status
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with compiler_emit_available_effect ops bound available compiler state (capacity.one (by omega))
    (.JumpTable selector start length) as ⟨status,emitted,accepted,emission,emitEffect⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  have remaining : CallbackCapacity emitted state bound (2*compiler.table_depths.val.length) :=
    capacity.after_emission emission emitEffect
  obtain ⟨budget,code,sources,rfl,codeEq,sourcesEq⟩ := emission
  have size : code.val.length = compiler.function.code.val.length+1 := by simp [codeEq]
  have sourceSize : sources.val.length = compiler.function.source_offsets.val.length+1 := by
    have lengths := congrArg List.length sourcesEq
    simpa only [List.length_map,List.length_append,List.length_singleton] using lengths
  let next := {compiler with budget,function := {compiler.function with code,source_offsets := sources}}
  have safe : TableLoopSafe next 0 Usize.max := by
    refine ⟨?_,depthsValid,fixups.mono (by dsimp [next]; omega),?_,?_,capacity.coordinate⟩
    · change sources.val.length = code.val.length
      rw [sourceSize,size,aligned]
    · change code.val.length + 2*(compiler.table_depths.val.length-0) ≤ Usize.max
      have room := capacity.codeCapacity
      simp only [alloc.vec.Vec.length] at room
      simp only [Nat.sub_zero]
      omega
    · change compiler.function.jump_tables.val.length ≤ code.val.length
      omega
  have nextWidths : TableWidthsFit next := widths
  have nextCapacity : CallbackCapacity next state bound (2*(next.table_depths.val.length-(0#usize).val)) := by
    simpa [next] using remaining
  step with compiler_table_loop_available ops law bound available next state 0#usize (by simp) Usize.max
    safe nextWidths nextCapacity
    as ⟨s,params,finalBudget,batch,function,frames,reach,source,before,height,offsets,depths,result,after,same,effect⟩
  simp only [compilerSnapshot,Prod.mk.injEq] at same
  rcases same with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  simp only [WP.spec_ok,true_and]
  exact (emitEffect.trans effect).weaken (by intro counter; cases counter <;> simp [next] <;> omega)

end Itasca.Runtime.Code

end

/-! ## Branch Table Availability -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Actual br_table accepts all collected labels plus the fallback. The
source bounds cover every target; temporary storage and both charged resources
have independent numeric demand. Dead paths still charge the fallback label. -/
theorem compiler_on_br_table_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (fallback : U32) (resultType : Itasca.signature.ResultType) (selector : U32)
    (capacity : CallbackCapacity compiler state bound (2*(compiler.table_depths.val.length+1)+1))
    (branchRoom : compiler.budget.branches.val < compiler.budget.limits.max_branch_table_entries.val)
    (scratchCapacity : compiler.table_depths.length < Usize.max)
    (scratchReserve : compiler.table_depths.length+1 ≤ bound)
    (depthCount : compiler.table_depths.val.length+1 ≤ U32.max)
    (aligned : compiler.reachable = true → SourceAligned compiler)
    (depthsValid : compiler.reachable = true → ∀ depth ∈ compiler.table_depths.val ++ [fallback],
      depth.val < compiler.frames.val.length)
    (widths : compiler.reachable = true → ∀ depth ∈ compiler.table_depths.val ++ [fallback],
      ∀ (index : Usize) (frame : runtime.compiler.Frame), compiler.frames.val[index.val]? = some frame →
        index.val+depth.val+1 = compiler.frames.val.length → (frameBranchWidth frame).val+1 ≤ compiler.height.val)
    (fixups : compiler.reachable = true → FixupBudget compiler.frames.val compiler.function.code.val.length)
    (tables : compiler.reachable = true → compiler.function.jump_tables.val.length ≤ compiler.function.code.val.length)
    (selectorAt : compiler.reachable = true → compiler.before.val[compiler.before.val.length-1]? = some selector) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table ops compiler state fallback resultType ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => match counter with
          | .instructions => 2*(compiler.table_depths.val.length+1)+1 | .branches => 1 | _ => 0) ⦄ := by
  obtain ⟨⟨status,labeled⟩,labelCalled,accepted,labelEffect,_⟩ := WP.spec_imp_exists
    (compiler_branch_label_available ops bound available compiler state fallback branchRoom scratchCapacity scratchReserve)
  dsimp only at accepted labelEffect
  subst status
  obtain ⟨budget,depths,frame,depthsEq⟩ := compiler_table_label_success ops law compiler labeled state fallback labelCalled
  subst labeled
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
  rw [labelCalled]
  simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  have lengthEq : depths.val.length = compiler.table_depths.val.length+1 := by simp [depthsEq]
  have limitsSame : budget.limits = compiler.budget.limits := labelEffect.limits
  have instructionsSame : budget.instructions = compiler.budget.instructions := labelEffect.uncharged .instructions (by decide)
  let staged := {compiler with budget,table_depths := depths}
  by_cases live : compiler.reachable = true
  · rw [if_pos live]
    have stagedCapacity : CallbackCapacity staged state bound (2*depths.val.length+1) := by
      refine ⟨?_,?_,?_,?_,?_,capacity.coordinate,?_,capacity.operands,capacity.slots⟩
      · simpa only [staged,lengthEq] using capacity.pc
      · simpa only [staged,lengthEq] using capacity.codeCapacity
      · simpa only [staged,lengthEq] using capacity.sourceCapacity
      · simpa only [staged,lengthEq] using capacity.codeReserve
      · simpa only [staged,lengthEq] using capacity.sourceReserve
      · change budget.instructions.val+(2*depths.val.length+1) ≤ budget.limits.max_instructions.val
        rw [instructionsSame,limitsSame,lengthEq]
        exact capacity.instructions
    have stagedDepths : ∀ depth ∈ staged.table_depths.val, depth.val < staged.frames.val.length := by
      simpa only [staged,depthsEq] using depthsValid live
    have stagedWidths : TableWidthsFit staged := by
      simpa only [TableWidthsFit,staged,depthsEq] using widths live
    obtain ⟨⟨status,lowered⟩,lowerCalled,accepted,lowerEffect⟩ := WP.spec_imp_exists
      (compiler_lower_table_available ops law bound available staged state stagedCapacity (aligned live)
        stagedDepths stagedWidths (fixups live) (tables live)
        (by change depths.val.length ≤ U32.max; omega) selector (selectorAt live))
    dsimp only at accepted lowerEffect
    subst status
    rw [lowerCalled]
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with runtime_clear lowered.table_depths as ⟨cleared,_⟩
    have fixed := (compiler_lower_table_fixed ops law staged lowered lowerCalled).stable.fields
    have localsSame := fixed.2.2.2.2.2.2.1
    have slotsFit : lowered.function.local_slots.val+2*state.vals.length ≤ U32.max := by
      rw [localsSame]; exact capacity.slots
    apply WP.spec_mono (compiler_observe_available_budget ops bound available
      {lowered with reachable := false,table_depths := cleared} state capacity.operands slotsFit)
    intro out post
    rw [post.2]
    exact ⟨post.1,(labelEffect.trans lowerEffect).weaken
      (by intro counter; cases counter <;> simp [staged,lengthEq])⟩
  · rw [if_neg live]
    step with runtime_clear depths as ⟨cleared,_⟩
    let observed := {compiler with budget,table_depths := cleared}
    apply WP.spec_mono (compiler_observe_available_budget ops bound available observed state capacity.operands capacity.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,labelEffect.weaken (by intro counter; cases counter <;> simp)⟩

end Itasca.Runtime.Code

end
