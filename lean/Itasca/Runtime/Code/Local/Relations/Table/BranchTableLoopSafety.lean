import Itasca.Runtime.Code.Local.Relations.Table.BranchTableSafety
import Itasca.Runtime.Code.Local.Relations.Table.BranchTableSafetyEffects
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
