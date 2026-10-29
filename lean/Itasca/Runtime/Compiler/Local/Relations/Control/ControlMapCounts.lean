import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerMetadataTactic
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private theorem vector_restore {T : Type} (vector : alloc.vec.Vec T) (index : Usize)
    (value : T) (restore : T → alloc.vec.Vec T)
    (accepted : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice T) vector index = .ok (value, restore)) :
    restore = fun value => vector.set index value := by
  rw [alloc.vec.Vec.index_mut_slice_index] at accepted
  unfold alloc.vec.Vec.index_mut_usize at accepted
  obtain ⟨selected, _, accepted⟩ := bind_ok_inv _ _ _ accepted
  exact (Prod.mk.inj (Result.ok.injEq.mp accepted)).2.symm

macro "maps_effect " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | have restoreEq := vector_restore _ _ _ _ $h
  | metadata_effect $h using $ops, $law)
macro "maps_close" : tactic => `(tactic|
  first | rfl | simp_all only [compilerOrdinaryMetadata, compilerMetadata, snapshotCompiler,
    Prod.mk.injEq, alloc.vec.Vec.set_val_eq, List.length_set])
macro "maps_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (maps_effect $h using $ops, $law; maps_close)
  | solve | (sources_terminal $h; simp only [Result.ok.injEq, Prod.mk.injEq] at $h:ident; obtain ⟨_, output⟩ := $h; cases output; maps_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | (sources_nonterminal $h
     obtain ⟨value, called, rest⟩ := bind_ok_inv _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue, secondValue⟩)
     | skip
     try maps_effect called using $ops, $law
     try simp only [uncurry_apply_pair] at $h:ident)
  | sources_split $h)

theorem compiler_end_map_count {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (status, after)) :
    after.function.controls.val.length = before.function.controls.val.length := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end at accepted
  repeat' maps_step accepted using ops, law

theorem compiler_else_map_count {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (status, after)) :
    after.function.controls.val.length = before.function.controls.val.length := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else at accepted
  simp only [core.option.Option.take] at accepted
  repeat' maps_step accepted using ops, law
end Itasca.Runtime.Compiler
