import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSkipSafety
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableCallback
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableSafetyEffects
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericSafety

/-!
Normal return of br_table compilation, from one target through the target loop and lowering to the compiler callback.
-/

/-! ## Branch Table Safety -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

@[step] theorem compiler_table_branch_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (index frameIndex : Usize) (depth : U32) (frame : runtime.compiler.Frame)
    (depthAt : compiler.table_depths.val[index.val]? = some depth)
    (frameAt : compiler.frames.val[frameIndex.val]? = some frame)
    (position : frameIndex.val + depth.val + 1 = compiler.frames.val.length)
    (tableFits : compiler.function.jump_tables.val.length < Usize.max)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length + 2 ≤ Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length + 2 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.table_branch ops compiler index ⦃ _ => True ⦄ := by
  unfold runtime.compiler.control.FunctionCompiler.table_branch
  step with compiler_pc ops compiler as ⟨status,current,_,_,budget,same⟩
  subst current
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pc =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with budget_push ops law budget compiler.function.jump_tables pc tableFits as
      ⟨status,budget,table,effect⟩
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok unit =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      have inside := (List.getElem?_eq_some_iff.mp depthAt).1
      step as ⟨actual,found⟩
      have same : actual = depth := found.trans (List.getElem?_eq_some_iff.mp depthAt).2
      subst actual
      rw [(List.getElem?_eq_some_iff.mp depthAt).2]
      exact compiler_branch_skip_total ops law
        {compiler with budget,function := {compiler.function with jump_tables := table}}
        frame frameIndex depth 1#u32 frameAt position fixupsFit codeFits sourceFits coordinateFits

private theorem charge_branch_total {A} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A) :
    runtime.compiler.Budget.charge ops budget .BranchTableEntries ⦃ _ => True ⦄ := by
  simp only [runtime.compiler.Budget.charge]
  split
  · simp [runtime.compiler.Budget.reject]
  · step

@[step] theorem compiler_table_label_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32)
    (fits : compiler.table_depths.val.length < Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops compiler state depth ⦃ _ => True ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
  step with charge_branch_total ops compiler.budget as ⟨status,budget⟩
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok unit =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with budget_push ops law budget compiler.table_depths depth fits
end Itasca.Runtime.Code

end

/-! ## Branch Table Loop Safety -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

@[step] theorem compiler_table_loop_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (limit : Nat) (limitFits : limit ≤ Usize.max)
    (held : status = .Ok () → TableLoopSafe compiler index.val limit) :
    runtime.compiler.control.FunctionCompiler.lower_table_branches_loop ops compiler index status ⦃ _ => True ⦄ := by
  unfold runtime.compiler.control.FunctionCompiler.lower_table_branches_loop
  apply loop.spec_decr_nat (fun p => Usize.max - p.2.1.val)
    (fun p => p.2.2 = .Ok () → TableLoopSafe p.1 p.2.1.val limit)
  · rintro ⟨current,i,result⟩ safe
    dsimp only at safe
    unfold runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.body
    simp only
    split
    · rename_i more
      have inside : i.val < current.table_depths.val.length := by scalar_tac
      cases result with
      | Err error => simp [core.result.Result.is_ok,WP.spec_ok]
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
        have held := safe rfl
        let depth := current.table_depths.val[i.val]
        have depthAt : current.table_depths.val[i.val]? = some depth := by simp [depth,inside]
        have depthBound := held.depths depth (List.mem_of_getElem? depthAt)
        let frameIndex := Usize.ofNatCore (current.frames.val.length - depth.val - 1)
          (by have h := (alloc.vec.Vec.len current.frames).hBounds; change current.frames.val.length < 2^UScalarTy.Usize.numBits at h; omega)
        have frameBound : frameIndex.val < current.frames.val.length := by
          change current.frames.val.length - depth.val - 1 < current.frames.val.length
          omega
        let frame := current.frames.val[frameIndex.val]
        have frameAt : current.frames.val[frameIndex.val]? = some frame := by simp [frame,frameBound]
        have position : frameIndex.val + depth.val + 1 = current.frames.val.length := by
          change current.frames.val.length - depth.val - 1 + depth.val + 1 = current.frames.val.length
          omega
        have room := held.room
        have codeFits : current.function.code.val.length + 2 ≤ Usize.max := by omega
        have sourceFits : current.function.source_offsets.val.length + 2 ≤ Usize.max := by
          rw [held.aligned]; exact codeFits
        have tableFits : current.function.jump_tables.val.length < Usize.max := by
          have := held.tables; omega
        obtain ⟨⟨result,next⟩,called,_⟩ := WP.spec_imp_exists
          (compiler_table_branch_total ops law current i frameIndex depth frame depthAt frameAt position
            tableFits (held.fixups.lookup frameAt (by omega)) codeFits sourceFits held.coordinate)
        rw [called]
        simp only [bind_ok]
        step as ⟨nextIndex,increment⟩
        refine ⟨?_,by scalar_tac⟩
        intro accepted
        have exactCall : runtime.compiler.control.FunctionCompiler.table_branch ops current i = .ok (.Ok (),next) := by
          simpa only [accepted] using called
        have advanced := held.advance ops law inside exactCall
        have progress : nextIndex.val = i.val+1 := by scalar_tac
        simpa only [progress] using advanced
    · simp [WP.spec_ok]
  · exact held
end Itasca.Runtime.Code

end

/-! ## Branch Table Lower Safety -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

@[step] theorem compiler_lower_table_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (aligned : SourceAligned compiler)
    (depths : ∀ depth ∈ compiler.table_depths.val, depth.val < compiler.frames.val.length)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (room : compiler.function.code.val.length + 1 + 2*compiler.table_depths.val.length ≤ Usize.max)
    (tables : compiler.function.jump_tables.val.length ≤ compiler.function.code.val.length)
    (coordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.lower_table_branches ops compiler ⦃ _ => True ⦄ := by
  unfold runtime.compiler.control.FunctionCompiler.lower_table_branches
  step as ⟨startResult,_⟩
  cases startResult with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok start =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step as ⟨lengthResult,_⟩
    cases lengthResult with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok length =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      step with compiler_operand_total ops compiler 1#usize as ⟨operandResult,_⟩
      cases operandResult with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok selector =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
        step with compiler_emit ops law compiler (.JumpTable selector start length)
          (by omega) (by rw [aligned]; omega) coordinate as ⟨status,emitted,effect⟩
        cases status with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok unit =>
          cases unit
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
          obtain ⟨budget,code,sources,rfl,codeEq,sourcesEq⟩ := effect rfl
          have size : code.val.length = compiler.function.code.val.length+1 := by simp [codeEq]
          have sourceSize : sources.val.length = compiler.function.source_offsets.val.length+1 := by
            have := congrArg List.length sourcesEq
            simpa only [List.length_map,List.length_append,List.length_singleton] using this
          let next := {compiler with budget,function := {compiler.function with code,source_offsets := sources}}
          have safe : TableLoopSafe next 0 Usize.max := by
            refine ⟨?_,depths,fixups.mono (by dsimp [next]; omega),?_,?_,coordinate⟩
            · change sources.val.length = code.val.length
              rw [sourceSize,size,aligned]
            · change code.val.length + 2*(compiler.table_depths.val.length-0) ≤ Usize.max
              simpa only [size,Nat.sub_zero] using room
            · change compiler.function.jump_tables.val.length ≤ code.val.length
              omega
          step with compiler_table_loop_total ops law next 0#usize (.Ok ()) Usize.max (Nat.le_refl _) (fun _ => safe)
end Itasca.Runtime.Code

end

/-! ## Branch Table Callback Safety -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

@[step] theorem compiler_br_table_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (aligned : SourceAligned compiler)
    (depths : ∀ depth ∈ compiler.table_depths.val, depth.val < compiler.frames.val.length)
    (fallbackBound : fallback.val < compiler.frames.val.length)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (room : compiler.function.code.val.length + 1 + 2*(compiler.table_depths.val.length+1) ≤ Usize.max)
    (tables : compiler.function.jump_tables.val.length ≤ compiler.function.code.val.length)
    (coordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops compiler state fallback types ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  obtain ⟨⟨status,labeled⟩,called,_⟩ := WP.spec_imp_exists
    (compiler_table_label_total ops law compiler state fallback (by omega))
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
  rw [called]
  simp only [bind_ok]
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok unit =>
    cases unit
    obtain ⟨budget,labels,rfl,labelsEq⟩ := compiler_table_label_success ops law compiler labeled state fallback called
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    split
    · step with compiler_lower_table_total ops law {compiler with budget,table_depths := labels}
        aligned (by
          intro depth member
          rw [labelsEq] at member
          rcases List.mem_append.mp member with member | member
          · exact depths depth member
          · simp only [List.mem_singleton] at member
            subst depth
            exact fallbackBound)
        fixups (by simpa only [labelsEq,List.length_append,List.length_singleton] using room)
        tables coordinate as ⟨status,lowered⟩
      cases status with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok unit =>
        cases unit
        simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
        step with runtime_clear lowered.table_depths as ⟨cleared,_⟩
        exact compiler_observe_stack ops law {lowered with reachable := false,table_depths := cleared} state
    · step with runtime_clear labels as ⟨cleared,_⟩
      exact compiler_observe_stack ops law {compiler with budget,table_depths := cleared} state
end Itasca.Runtime.Code

end
