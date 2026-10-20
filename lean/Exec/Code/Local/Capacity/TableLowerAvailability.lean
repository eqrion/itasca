import Exec.Code.Local.Capacity.TableLoopAvailability
import Exec.Code.Local.Capacity.AuxiliaryAvailability
import Exec.Code.Local.Lowering.Control.LoweringBranchIf

namespace Exec.Code
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
    runtime.compiler.FunctionCompiler.lower_table_branches ops compiler ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 2*compiler.table_depths.val.length+1 else 0) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.lower_table_branches
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

end Exec.Code
