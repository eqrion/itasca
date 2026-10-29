import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSuccessControls
import Itasca.Runtime.Compiler.Local.Publication.ControlMapPublication

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

private theorem frame_owner_restore (vector : alloc.vec.Vec runtime.compiler.Frame) (index : Usize)
    (value : runtime.compiler.Frame) (restore : runtime.compiler.Frame → alloc.vec.Vec runtime.compiler.Frame)
    (accepted : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice runtime.compiler.Frame)
      vector index = .ok (value,restore)) :
    ∀ replacement, replacement.map = value.map →
      (restore replacement).val.map (fun frame => frame.map.val) = vector.val.map (fun frame => frame.map.val) := by
  rw [alloc.vec.Vec.index_mut_slice_index] at accepted
  unfold alloc.vec.Vec.index_mut_usize at accepted
  obtain ⟨selected,read,accepted⟩ := bind_ok_inv _ _ _ accepted
  have selectedEq := (Prod.mk.inj (Result.ok.injEq.mp accepted)).1
  have restoreEq := (Prod.mk.inj (Result.ok.injEq.mp accepted)).2
  subst selected
  unfold alloc.vec.Vec.index_usize at read
  split at read
  · simp at read
  next found lookup =>
    have same : found = value := Result.ok.injEq.mp read
    subst found
    have bound := (List.getElem?_eq_some_iff.mp lookup).1
    have atIndex := (List.getElem?_eq_some_iff.mp lookup).2
    intro replacement owner
    rw [← restoreEq,alloc.vec.Vec.set_val_eq,List.map_set,owner,← atIndex]
    have mapped : (vector.val.map (fun frame => frame.map.val))[index.val]'(by simpa using bound) = vector.val[index.val].map.val := by
      rw [List.getElem_map]
    rw [← mapped]
    exact List.set_getElem_self (by simpa using bound)

macro "owners_effect " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | have ownerRestore := frame_owner_restore _ _ _ _ $h
  | metadata_effect $h using $ops, $law)
macro "owners_close" : tactic => `(tactic|
  first | rfl | simp_all only [activeControlMaps, compilerOrdinaryMetadata, compilerMetadata,
    snapshotCompiler,Prod.mk.injEq])
macro "owners_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (owners_effect $h using $ops, $law; owners_close)
  | solve | (sources_terminal $h; simp only [Result.ok.injEq,Prod.mk.injEq] at $h:ident; obtain ⟨_, output⟩ := $h; cases output; owners_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | (fail_if_no_progress simp only [Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame,bind_ok,bind_tc_ok] at $h:ident)
  | (sources_nonterminal $h
     obtain ⟨value,called,rest⟩ := bind_ok_inv _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue,secondValue⟩)
     | skip
     try owners_effect called using $ops, $law
     try simp only [uncurry_apply_pair] at $h:ident)
  | sources_split $h)

/-- Branches change frame flags and fixups while retaining each map owner. -/
theorem compiler_branch_map_owners {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status,after)) :
    activeControlMaps after = activeControlMaps before := by
  cases conditional <;>
    simp only [runtime.compiler.control.FunctionCompiler.branch,Bool.false_eq_true,ite_false,ite_true] at accepted <;>
    repeat' owners_step accepted using ops, law

end Itasca.Runtime.Code
