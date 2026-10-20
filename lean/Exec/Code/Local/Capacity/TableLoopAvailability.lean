import Exec.Code.Local.Capacity.TableBranchAvailability
import Exec.Code.Local.Capacity.TableBranchWidths
import Exec.Code.Local.Capacity.CallbackCapacityGrowth
import Exec.Code.Local.Relations.Table.BranchTableSafetyEffects

namespace Exec.Code
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
    runtime.compiler.FunctionCompiler.lower_table_branches_loop ops compiler index (.Ok ()) ⦃ out =>
      ∃ after, out = compilerSnapshot after (.Ok ()) ∧
        CompilationBudgetEffect compiler.budget after.budget
          (fun counter => if counter = .instructions then 2*(compiler.table_depths.val.length-index.val) else 0) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.lower_table_branches_loop
  apply loop.spec_decr_nat (fun p => compiler.table_depths.val.length-p.2.1.val)
    (fun p => index.val ≤ p.2.1.val ∧ p.2.1.val ≤ compiler.table_depths.val.length ∧ p.2.2 = .Ok () ∧
      p.1.table_depths = compiler.table_depths ∧ TableLoopSafe p.1 p.2.1.val limit ∧ TableWidthsFit p.1 ∧
      CallbackCapacity p.1 state bound (2*(compiler.table_depths.val.length-p.2.1.val)) ∧
      CompilationBudgetEffect compiler.budget p.1.budget
        (fun counter => if counter = .instructions then 2*(p.2.1.val-index.val) else 0))
  · rintro ⟨current,i,result⟩ ⟨lower,upper,rfl,depths,heldSafe,heldWidths,heldCapacity,effect⟩
    dsimp only at lower upper depths heldSafe heldWidths heldCapacity effect
    unfold runtime.compiler.FunctionCompiler.lower_table_branches_loop.body
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

end Exec.Code
