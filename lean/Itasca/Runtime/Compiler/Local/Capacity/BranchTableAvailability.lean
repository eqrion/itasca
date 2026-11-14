import Itasca.Runtime.Compiler.Local.Callbacks.Control.BranchTableCallbacks
import Itasca.Runtime.Compiler.Local.Lowering.Control.TableBranchContracts
import Itasca.Runtime.Compiler.Local.Capacity.CallAvailability
import Itasca.Runtime.Compiler.Local.Capacity.UnreachableAvailability
import Itasca.Runtime.Compiler.Local.Lowering.Control.LoweringTrap
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableFrames
import Itasca.Runtime.Compiler.Local.Relations.Table.ControlTablePreservation
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableSafetyEffects
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Control.BranchCallbacks

/-!
Sections, each formerly its own module: BranchAvailability, BranchTableAvailability.
-/

/-! ## BranchAvailability -/

section

/-!
Allocator availability for forward and loop branches, composed into the branch callback availability theorem.
-/

/-! ## Branch Forward Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Nonelided forward branches accept with two instruction units and one
independently bounded fixup append, for every non-loop label kind. -/
theorem branch_transfer_forward_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 2)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (nonempty : frame.results ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.results.val + skip.val = compiler.height.val)
    (fixupsCapacity : frame.fixups.length < Usize.max)
    (fixupsReserve : frame.fixups.length + 1 ≤ bound) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 2 else 0) ⦄ := by
  have width : branchWidth frame = frame.results := by
    cases kind : frame.kind <;> simp only [branchWidth, kind]
    exact False.elim (forward kind)
  have no : ¬ (branchWidth frame = 0#u32 ∨ source = frame.height) := by
    rw [width]
    exact fun choice => choice.elim nonempty different
  have count : branchInstructionCount false frame source = 2 := by
    simp only [branchInstructionCount, if_neg no, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false]
  have demand : BranchDemand compiler frame bound 2 := {
    pc := capacity.pc, code := capacity.codeCapacity, sources := capacity.sourceCapacity
    codeReserve := capacity.codeReserve, sourceReserve := capacity.sourceReserve
    coordinate := capacity.coordinate, instructions := capacity.instructions
    fixups := fun _ => fixupsCapacity, fixupsReserve := fun _ => fixupsReserve }
  have ready : false = true → ∃ condition,
      runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok condition) := by
    intro impossible
    cases impossible
  apply WP.spec_mono (runtime.compiler.control.FunctionCompiler.branch.available ops bound available
    compiler depth skip false ⟨index, frame, lookup, position⟩ source
    (by simpa only [width] using sourcePosition) ready (by simpa only [count] using demand))
  intro output effect
  have budget := effect.2.compilation
  exact ⟨effect.1, by simpa only [count] using budget⟩

/-- Elided forward transfers still publish a bounded fixup and one jump. -/
theorem branch_elided_forward_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 1)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (elided : frame.results = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.results.val + skip.val = compiler.height.val)
    (fixupsCapacity : frame.fixups.length < Usize.max)
    (fixupsReserve : frame.fixups.length + 1 ≤ bound) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  have width : branchWidth frame = frame.results := by
    cases kind : frame.kind <;> simp only [branchWidth, kind]
    exact False.elim (forward kind)
  have count : branchInstructionCount false frame source = 1 := by
    simp only [branchInstructionCount, width, if_pos elided]
  have demand : BranchDemand compiler frame bound 1 := {
    pc := capacity.pc, code := capacity.codeCapacity, sources := capacity.sourceCapacity
    codeReserve := capacity.codeReserve, sourceReserve := capacity.sourceReserve
    coordinate := capacity.coordinate, instructions := capacity.instructions
    fixups := fun _ => fixupsCapacity, fixupsReserve := fun _ => fixupsReserve }
  have ready : false = true → ∃ condition,
      runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok condition) := by
    intro impossible
    cases impossible
  apply WP.spec_mono (runtime.compiler.control.FunctionCompiler.branch.available ops bound available
    compiler depth skip false ⟨index, frame, lookup, position⟩ source
    (by simpa only [width] using sourcePosition) ready (by simpa only [count] using demand))
  intro output effect
  have budget := effect.2.compilation
  exact ⟨effect.1, by simpa only [count] using budget⟩

/-- Every unconditional forward branch accepts from its source result width,
with at most two instructions and no other budget charge. -/
theorem compiler_branch_forward_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 2)
    (frame : runtime.compiler.Frame) (index : Usize) (depth skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (widthFits : frame.results.val + skip.val ≤ compiler.height.val)
    (fixupsCapacity : frame.fixups.length < Usize.max)
    (fixupsReserve : frame.fixups.length + 1 ≤ bound) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 2 else 0) ⦄ := by
  let source : U32 := UScalar.ofNatCore (compiler.height.val-(frame.results.val+skip.val)) (by scalar_tac)
  have sourcePosition : source.val + frame.results.val + skip.val = compiler.height.val := by
    change compiler.height.val-(frame.results.val+skip.val)+frame.results.val+skip.val = compiler.height.val
    omega
  by_cases elided : frame.results = 0#u32 ∨ source = frame.height
  · apply WP.spec_mono (branch_elided_forward_available ops bound available compiler state (capacity.mono (by decide))
      frame index depth source skip lookup position forward elided sourcePosition fixupsCapacity fixupsReserve)
    intro out post
    exact ⟨post.1,post.2.weaken (by intro counter; cases counter <;> simp)⟩
  · exact branch_transfer_forward_available ops law bound available compiler state capacity frame index depth source skip
      lookup position forward (by intro empty; exact elided (Or.inl empty))
      (by intro same; exact elided (Or.inr same)) sourcePosition fixupsCapacity fixupsReserve

end Itasca.Runtime.Compiler

end

/-! ## Branch Loop Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- A nonelided backward branch accepts with independently reserved capacity
for its transfer and jump. Its source argument coordinates justify arithmetic. -/
theorem branch_transfer_loop_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 2)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop) (nonempty : frame.params ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.params.val + skip.val = compiler.height.val) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 2 else 0) ⦄ := by
  have width : branchWidth frame = frame.params := by
    simp only [branchWidth, kind]
  have no : ¬ (branchWidth frame = 0#u32 ∨ source = frame.height) := by
    rw [width]
    exact fun choice => choice.elim nonempty different
  have count : branchInstructionCount false frame source = 2 := by
    simp only [branchInstructionCount, if_neg no, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false]
  have demand : BranchDemand compiler frame bound 2 := {
    pc := capacity.pc, code := capacity.codeCapacity, sources := capacity.sourceCapacity
    codeReserve := capacity.codeReserve, sourceReserve := capacity.sourceReserve
    coordinate := capacity.coordinate, instructions := capacity.instructions
    fixups := fun different => False.elim (different kind)
    fixupsReserve := fun different => False.elim (different kind) }
  have ready : false = true → ∃ condition,
      runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok condition) := by
    intro impossible
    cases impossible
  apply WP.spec_mono (runtime.compiler.control.FunctionCompiler.branch.available ops bound available
    compiler depth skip false ⟨index, frame, lookup, position⟩ source
    (by simpa only [width] using sourcePosition) ready (by simpa only [count] using demand))
  intro output effect
  have budget := effect.2.compilation
  exact ⟨effect.1, by simpa only [count] using budget⟩

/-- Empty and identity loop transfers elide the copy and need only the jump. -/
theorem branch_elided_loop_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 1)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop) (elided : frame.params = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.params.val + skip.val = compiler.height.val) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  have width : branchWidth frame = frame.params := by
    simp only [branchWidth, kind]
  have count : branchInstructionCount false frame source = 1 := by
    simp only [branchInstructionCount, width, if_pos elided]
  have demand : BranchDemand compiler frame bound 1 := {
    pc := capacity.pc, code := capacity.codeCapacity, sources := capacity.sourceCapacity
    codeReserve := capacity.codeReserve, sourceReserve := capacity.sourceReserve
    coordinate := capacity.coordinate, instructions := capacity.instructions
    fixups := fun different => False.elim (different kind)
    fixupsReserve := fun different => False.elim (different kind) }
  have ready : false = true → ∃ condition,
      runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok condition) := by
    intro impossible
    cases impossible
  apply WP.spec_mono (runtime.compiler.control.FunctionCompiler.branch.available ops bound available
    compiler depth skip false ⟨index, frame, lookup, position⟩ source
    (by simpa only [width] using sourcePosition) ready (by simpa only [count] using demand))
  intro output effect
  have budget := effect.2.compilation
  exact ⟨effect.1, by simpa only [count] using budget⟩

/-- Every unconditional backward branch accepts from its source parameter
width, with at most two instructions and no other budget charge. -/
theorem compiler_branch_loop_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 2)
    (frame : runtime.compiler.Frame) (index : Usize) (depth skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop) (widthFits : frame.params.val + skip.val ≤ compiler.height.val) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 2 else 0) ⦄ := by
  let source : U32 := UScalar.ofNatCore (compiler.height.val-(frame.params.val+skip.val)) (by scalar_tac)
  have sourcePosition : source.val + frame.params.val + skip.val = compiler.height.val := by
    change compiler.height.val-(frame.params.val+skip.val)+frame.params.val+skip.val = compiler.height.val
    omega
  by_cases elided : frame.params = 0#u32 ∨ source = frame.height
  · apply WP.spec_mono (branch_elided_loop_available ops bound available compiler state (capacity.mono (by decide))
      frame index depth source skip lookup position kind elided sourcePosition)
    intro out post
    exact ⟨post.1,post.2.weaken (by intro counter; cases counter <;> simp)⟩
  · exact branch_transfer_loop_available ops law bound available compiler state capacity frame index depth source skip
      lookup position kind (by intro empty; exact elided (Or.inl empty))
      (by intro same; exact elided (Or.inr same)) sourcePosition

end Itasca.Runtime.Compiler

end

/-! ## Branch Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Raw unconditional branching accepts for every label kind and depth. The
source width bound excludes arithmetic rejection; reserves pay for fixups. -/
theorem compiler_unconditional_branch_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 2)
    (frame : runtime.compiler.Frame) (index : Usize) (depth skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (widthFits : (match frame.kind with | .Loop => frame.params | _ => frame.results).val + skip.val ≤ compiler.height.val)
    (fixupsCapacity : frame.fixups.length < Usize.max)
    (fixupsReserve : frame.fixups.length + 1 ≤ bound) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 2 else 0) ⦄ := by
  by_cases loopEntry : frame.kind = .Loop
  · exact compiler_branch_loop_available ops law bound available compiler state capacity frame index depth skip
      lookup position loopEntry (by simpa only [loopEntry] using widthFits)
  · have resultsFit : frame.results.val + skip.val ≤ compiler.height.val := by
      cases kindEq : frame.kind
      all_goals first | exact False.elim (loopEntry kindEq) | simpa only [kindEq] using widthFits
    exact compiler_branch_forward_available ops law bound available compiler state capacity frame index depth skip
      lookup position loopEntry resultsFit fixupsCapacity fixupsReserve

/-- The actual br callback composes available raw branching and dead-stack
observation. Accepted primitive equations are constructed inside this proof. -/
theorem compiler_on_br_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 2)
    (frame : runtime.compiler.Frame) (index : Usize) (depth : U32) (resultType : Itasca.signature.ResultType)
    (lookup : compiler.reachable = true → compiler.frames.val[index.val]? = some frame)
    (position : compiler.reachable = true → index.val + depth.val + 1 = compiler.frames.val.length)
    (widthFits : compiler.reachable = true →
      (match frame.kind with | .Loop => frame.params | _ => frame.results).val ≤ compiler.height.val)
    (fixupsCapacity : frame.fixups.length < Usize.max)
    (fixupsReserve : frame.fixups.length + 1 ≤ bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops compiler state depth resultType ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 2 else 0) ⦄ := by
  have ready : compiler.reachable = true → BranchCallbackReady ops compiler depth false bound := by
    intro live
    let selected : BranchSelection compiler depth := ⟨index, frame, lookup live, position live⟩
    have width : (branchWidth frame).val ≤ compiler.height.val := by
      change (match frame.kind with | .Loop => frame.params | _ => frame.results).val ≤ compiler.height.val
      exact widthFits live
    let source : U32 := UScalar.ofNatCore (compiler.height.val - (branchWidth frame).val) (by scalar_tac)
    have sourcePosition : source.val + (branchWidth frame).val = compiler.height.val := by
      change compiler.height.val - (branchWidth frame).val + (branchWidth frame).val = compiler.height.val
      omega
    have countBound : branchInstructionCount false frame source ≤ 2 := by
      unfold branchInstructionCount
      split <;> simp
    have base : BranchCapacity compiler bound (branchInstructionCount false frame source) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, capacity.coordinate, ?_⟩
      · have h := capacity.pc; omega
      · have h := capacity.codeCapacity; omega
      · have h := capacity.sourceCapacity; omega
      · have h := capacity.codeReserve; omega
      · have h := capacity.sourceReserve; omega
      · have h := capacity.instructions; omega
    have demand : BranchDemand compiler frame bound (branchInstructionCount false frame source) := {
      toBranchCapacity := base
      fixups := fun _ => fixupsCapacity
      fixupsReserve := fun _ => fixupsReserve }
    refine ⟨selected, source, ?_, ?_, demand⟩
    · simpa [branchCallbackSkip] using sourcePosition
    · intro impossible
      cases impossible
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br.available
    ops bound available compiler state depth resultType ready capacity.operands capacity.slots)
  intro out post
  rcases out with ⟨status, after⟩
  rcases post with ⟨statusEq, callbackBudget⟩
  subst status
  obtain ⟨used, budgetEq, lower, upper⟩ := callbackBudget.bounds
  refine ⟨rfl, ?_⟩
  rw [budgetEq]
  exact CompilationBudgetEffect.of_counter .instructions compiler.budget used 2 lower upper

end Itasca.Runtime.Compiler

end

end

/-! ## BranchTableAvailability -/

section

/-!
Availability of br_table compilation, from one target through the target loop and final callback. Width and growth certificates preserve capacity across each collected label.
-/

/-! ## Callback Capacity Growth -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## Table Branch Availability -/

section

namespace Itasca.Runtime.Compiler
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
  apply runtime.compiler.control.FunctionCompiler.table_branch.available ops bound available compiler index depth depthAt
    (by have room := capacity.pc; simp only [alloc.vec.Vec.length] at room; omega) tableCapacity tableReserve
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 2 else 0))
  intro table
  let staged := {compiler with function := {compiler.function with jump_tables := table}}
  have stagedCapacity : CallbackCapacity staged state bound 2 :=
    ⟨capacity.pc, capacity.codeCapacity, capacity.sourceCapacity, capacity.codeReserve, capacity.sourceReserve,
      capacity.coordinate, capacity.instructions, capacity.operands, capacity.slots⟩
  exact compiler_unconditional_branch_available ops law bound available staged state stagedCapacity frame frameIndex depth 1#u32
    frameAt position widthFits fixupsCapacity fixupsReserve

end Itasca.Runtime.Compiler

end

/-! ## Table Branch Widths -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## Table Loop Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

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
  apply runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.spec ops
    (fun current position status => index.val ≤ position ∧ position ≤ compiler.table_depths.val.length ∧ status = .Ok () ∧
      current.table_depths = compiler.table_depths ∧ TableLoopSafe current position limit ∧ TableWidthsFit current ∧
      CallbackCapacity current state bound (2*(compiler.table_depths.val.length-position)) ∧
      CompilationBudgetEffect compiler.budget current.budget
        (fun counter => if counter = .instructions then 2*(position-index.val) else 0)) _
    ?_ ?_ compiler index (.Ok ()) ?_
  · intro current i held currentInside
    obtain ⟨lower, upper, _, depths, heldSafe, heldWidths, heldCapacity, effect⟩ := held
    have originalInside : i.val < compiler.table_depths.val.length := by simpa only [depths] using currentInside
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
    apply WP.exists_imp_spec ⟨(.Ok (), next), called, ?_⟩
    refine ⟨by omega, by omega, rfl, nextDepths.trans depths, nextSafe, nextWidths, nextCapacity, ?_⟩
    have combined := effect.trans stepEffect
    exact combined.weaken (by
      intro counter
      cases counter <;> simp only [reduceCtorEq, ite_true, ite_false] <;> omega)
  · intro current position status held finished
    obtain ⟨lower, upper, rfl, depths, heldSafe, heldWidths, heldCapacity, effect⟩ := held
    have done : position = compiler.table_depths.val.length := by
      rcases finished with outside | impossible
      · rw [depths] at outside
        omega
      · exact False.elim (impossible rfl)
    refine ⟨current, rfl, ?_⟩
    simpa only [done] using effect
  · refine ⟨Nat.le_refl _, inside, rfl, rfl, safe, widths, capacity, ?_⟩
    simpa only [Nat.sub_self, Nat.mul_zero, ite_self] using CompilationBudgetEffect.refl compiler.budget

end Itasca.Runtime.Compiler

end

/-! ## Table Lower Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

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
  obtain ⟨answer, selectorReady, same⟩ := WP.spec_imp_exists (compiler_condition ops compiler selector selectorAt)
  rw [same] at selectorReady
  have one := capacity.one (by omega)
  have demand : LowerTableDemand compiler bound := by
    refine ⟨⟨one.pc, one.codeCapacity, one.sourceCapacity, one.codeReserve, one.sourceReserve,
      one.coordinate, one.instruction⟩, ?_, depthCount⟩
    have room := capacity.pc
    change compiler.function.jump_tables.val.length ≤ U32.max
    simp only [alloc.vec.Vec.length] at room
    omega
  apply runtime.compiler.control.FunctionCompiler.lower_table_branches.available ops bound available compiler selector selectorReady demand
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 2*compiler.table_depths.val.length+1 else 0))
  intro start length emitted exactEmission
  have emitEffect : CompilationBudgetEffect compiler.budget emitted.budget
      (fun counter => if counter = .instructions then 1 else 0) := by
    apply BranchBudget.compilation
    obtain ⟨used, code, sources, rfl, charged, _, _⟩ := exactEmission
    exact ⟨used, rfl, charged⟩
  have emission := exactEmission.emitted
  have remaining : CallbackCapacity emitted state bound (2*compiler.table_depths.val.length) :=
    capacity.after_emission emission emitEffect
  obtain ⟨budget,code,sources,rfl,codeEq,sourcesEq⟩ := emission
  have size : code.val.length = compiler.function.code.val.length+1 := by
    simp only [codeEq, List.length_append, List.length_singleton]
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
    simpa only [next, UScalar.ofNatCore_val_eq, Nat.sub_zero] using remaining
  apply WP.spec_mono (compiler_table_loop_available ops law bound available next state 0#usize
    (by simp only [UScalar.ofNatCore_val_eq, Nat.zero_le]) Usize.max safe nextWidths nextCapacity)
  intro output effect
  obtain ⟨after, same, effect⟩ := effect
  rw [same]
  refine ⟨rfl, ?_⟩
  exact (emitEffect.trans effect).weaken (by
    intro counter
    cases counter <;> simp only [next, reduceCtorEq, ite_true, ite_false, UScalar.ofNatCore_val_eq, Nat.sub_zero] <;> omega)

end Itasca.Runtime.Compiler

end

/-! ## Branch Table Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

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
  obtain ⟨⟨status, labeled⟩, labelCalled, accepted, labelEffect, _⟩ := WP.spec_imp_exists
    (compiler_branch_label_available ops bound available compiler state fallback branchRoom scratchCapacity scratchReserve)
  dsimp only at accepted labelEffect
  subst status
  obtain ⟨budget, depths, frame, depthsEq⟩ := compiler_table_label_success ops law compiler labeled state fallback labelCalled
  subst labeled
  have lengthEq : depths.val.length = compiler.table_depths.val.length + 1 := by
    rw [depthsEq, List.length_append, List.length_singleton]
  have limitsSame : budget.limits = compiler.budget.limits := labelEffect.limits
  have instructionsSame : budget.instructions = compiler.budget.instructions := labelEffect.uncharged .instructions (by decide)
  let staged := {compiler with budget, table_depths := depths}
  let post := fun (labeled lowered : runtime.compiler.FunctionCompiler A) =>
    CompilationBudgetEffect labeled.budget lowered.budget
      (fun counter => if counter = .instructions then 2 * (compiler.table_depths.val.length + 1) + 1 else 0)
  have lowerReady : ∀ labeled,
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label ops compiler state fallback = .ok (.Ok (), labeled) →
      labeled.reachable = true → runtime.compiler.control.FunctionCompiler.lower_table_branches ops labeled
        ⦃ (status, after) => status = .Ok () ∧ post labeled after ∧ after.function.local_slots = compiler.function.local_slots ⦄ := by
    intro labeled actual live
    have same : labeled = staged := (Prod.mk.inj (Result.ok.injEq.mp (actual.symm.trans labelCalled))).2
    subst labeled
    have liveBefore : compiler.reachable = true := live
    have stagedCapacity : CallbackCapacity staged state bound (2 * depths.val.length + 1) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, capacity.coordinate, ?_, capacity.operands, capacity.slots⟩
      · simpa only [staged, lengthEq] using capacity.pc
      · simpa only [staged, lengthEq] using capacity.codeCapacity
      · simpa only [staged, lengthEq] using capacity.sourceCapacity
      · simpa only [staged, lengthEq] using capacity.codeReserve
      · simpa only [staged, lengthEq] using capacity.sourceReserve
      · change budget.instructions.val + (2 * depths.val.length + 1) ≤ budget.limits.max_instructions.val
        rw [instructionsSame, limitsSame, lengthEq]
        exact capacity.instructions
    have stagedDepths : ∀ depth ∈ staged.table_depths.val, depth.val < staged.frames.val.length := by
      simpa only [staged, depthsEq] using depthsValid liveBefore
    have stagedWidths : TableWidthsFit staged := by
      simpa only [TableWidthsFit, staged, depthsEq] using widths liveBefore
    obtain ⟨⟨status, lowered⟩, lowerCalled, accepted, lowerEffect⟩ := WP.spec_imp_exists
      (compiler_lower_table_available ops law bound available staged state stagedCapacity (aligned liveBefore)
        stagedDepths stagedWidths (fixups liveBefore) (tables liveBefore)
        (by change depths.val.length ≤ U32.max; omega) selector (selectorAt liveBefore))
    dsimp only at accepted lowerEffect
    subst status
    have fixed := (compiler_lower_table_fixed ops law staged lowered lowerCalled).stable.fields
    refine WP.exists_imp_spec ⟨(.Ok (), lowered), lowerCalled, rfl, ?_, fixed.2.2.2.2.2.2.1⟩
    simpa only [post, staged, lengthEq] using lowerEffect
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table.available
    ops bound available compiler state fallback resultType branchRoom scratchCapacity scratchReserve
    capacity.operands capacity.slots post lowerReady)
  rintro ⟨status, after⟩ ⟨accepted, labeled, actual, effect⟩
  have same : labeled = staged := (Prod.mk.inj (Result.ok.injEq.mp (actual.symm.trans labelCalled))).2
  subst labeled
  refine ⟨accepted, ?_⟩
  by_cases live : compiler.reachable = true
  · simp only [staged, live, ite_true] at effect
    obtain ⟨lowered, lowerEffect, budgetEq⟩ := effect
    rw [budgetEq]
    exact (labelEffect.trans lowerEffect).weaken (by
      intro counter
      cases counter <;> simp only [reduceCtorEq, ite_true, ite_false] <;> omega)
  · simp only [staged, live, ite_false] at effect
    rw [effect]
    exact labelEffect.weaken (by
      intro counter
      cases counter <;> simp only [reduceCtorEq, ite_true, ite_false] <;> omega)

end Itasca.Runtime.Compiler

end

end
