import Exec.Code.Local.Capacity.BranchAvailability

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
