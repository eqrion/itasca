import Itasca.Runtime.Code.Local.Callbacks.Common.CompilerOrdinaryResults
import Itasca.Runtime.Code.Local.Callbacks.Common.CompilerFixupMetadata
import Mathlib.Tactic.FailIfNoProgress
import Mathlib.Tactic.Rename
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

open Lean Meta Elab Tactic in
elab "metadata_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  let some functionName := lhs.getAppFn.constName? | throwError "not a named helper"
  let tac ← match functionName with
    | ``runtime.compiler.FunctionCompiler.observe =>
      `(tactic| have effect := compiler_observe_ordinary_result $ops $law _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.emit =>
      `(tactic| have effect := compiler_emit_ordinary_result $ops _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.copy =>
      `(tactic| have effect := compiler_copy_ordinary_result $ops _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.pair =>
      `(tactic| have effect := compiler_pair_ordinary_result $ops _ _ _ _ _ $h)
    | ``runtime.compiler.lower.FunctionCompiler.finish_op =>
      `(tactic| have effect := compiler_finish_op_ordinary_result $ops $law _ _ _ _ _ $h)
    | ``runtime.compiler.simd.FunctionCompiler.simd_op => do
      let theoremName := mkIdent `Itasca.Runtime.Code.compiler_simd_ordinary_result
      `(tactic| have effect := $theoremName $ops $law _ _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.pc => do
      let theoremName := mkIdent `Itasca.Runtime.Code.compiler_pc_ordinary_result
      `(tactic| have effect := $theoremName $ops _ _ _ $h)
    | ``runtime.compiler.control.FunctionCompiler.patch => do
      let theoremName := mkIdent `Itasca.Runtime.Code.compiler_patch_ordinary_result
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0 => do
      let theoremName := mkIdent `Itasca.Runtime.Code.compiler_fixups_ordinary_result
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1 => do
      let theoremName := mkIdent `Itasca.Runtime.Code.compiler_fixups_after_if_ordinary_result
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ _ $h)
    | _ => throwError "not a compiler helper"
  evalTactic tac
  evalTactic (← `(tactic| have metadataEq := effect.metadata))
  evalTactic (← `(tactic| have capacity := effect.capacity))

macro "metadata_close" : tactic => `(tactic|
  (constructor
   · first | rfl | simp_all only [compilerOrdinaryMetadata, compilerMetadata, snapshotCompiler, Prod.mk.injEq]
   · try simp_all only [compilerOrdinaryMetadata, compilerMetadata, snapshotCompiler, Prod.mk.injEq]
     try omega))

macro "metadata_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (metadata_effect $h using $ops, $law; metadata_close)
  | solve | (simp only [Result.ok.injEq, Prod.mk.injEq] at $h:ident; obtain ⟨_, output⟩ := $h; cases output; metadata_close)
  | (obtain ⟨value, called, rest⟩ := bind_ok_inv _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue, secondValue⟩)
     | skip
     try metadata_effect called using $ops, $law
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | split at $h:ident)

end Itasca.Runtime.Code
