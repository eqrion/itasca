import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableBoundary
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- Function entry and local declarations preserve branch-table scratch and code buffers. -/
def CompilerTableEntryMetadata {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  (after.table_depths, after.function.jump_tables, after.function.code) =
    (before.table_depths, before.function.jump_tables, before.function.code)

theorem CompilerTableEntryMetadata.trans {A : Type} {before middle after : runtime.compiler.FunctionCompiler A}
    (first : CompilerTableEntryMetadata before middle) (second : CompilerTableEntryMetadata middle after) :
    CompilerTableEntryMetadata before after := Eq.trans second first

open Lean Meta Elab Tactic in
elab "table_entry_metadata_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  if lhs.getAppFn.constName? = some ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop then
    let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_locals_table_entry_metadata
    evalTactic (← `(tactic| have effect := $theoremName $ops $law _ _ _ _ _ $h))
  else
    throwError "not local declaration loop"

macro "table_entry_metadata_close" : tactic => `(tactic|
  (first | rfl | (simp_all [CompilerTableEntryMetadata, snapshotCompiler, source_unit_eq])))
macro "table_entry_metadata_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; table_entry_metadata_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (table_entry_metadata_effect $h using $ops, $law; table_entry_metadata_close)
  | solve | (sources_terminal $h; have output := (Prod.mk.inj (Result.ok.injEq.mp $h)).2; cases output; table_entry_metadata_close)
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
     try table_entry_metadata_effect called using $ops, $law
     try clear called
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | sources_split $h)

theorem compiler_add_local_table_entry_metadata {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (ty : Itasca.types.ValueType) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.add_local ops before ty = .ok (status, after)) :
    CompilerTableEntryMetadata before after := by
  unfold runtime.compiler.FunctionCompiler.add_local at accepted
  repeat' table_entry_metadata_step accepted using ops, law
theorem compiler_locals_table_entry_metadata {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (ctx : Itasca.code.Context) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop
      ops before ctx index status = .ok output) :
    CompilerTableEntryMetadata before (snapshotCompiler output) := by
  generalize measure : Usize.max - index.val = n
  induction n using Nat.strong_induction_on generalizing before index status with
  | h n ih =>
    unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop at accepted
    rw [loop] at accepted
    simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop.body,
      bind_ok] at accepted
    split at accepted
    · cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at accepted
        subst output
        rfl
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at accepted
        obtain ⟨site, _, rest⟩ := bind_ok_inv _ _ _ accepted
        obtain ⟨⟨result, middle⟩, patched, tail⟩ := bind_ok_inv _ _ _ rest
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := bind_ok_inv _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < n := by scalar_tac
        have tail' : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop
            ops middle ctx nextIndex result = .ok output := by
          simpa only [uncurry_apply_pair, bind_ok,
            runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop,
            runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop.body,
            core.result.Result.is_ok] using tail
        exact (compiler_add_local_table_entry_metadata ops law before middle site result patched).trans
          (ih _ smaller middle nextIndex result tail' rfl)
    · simp only [bind_ok, Result.ok.injEq] at accepted
      subst output
      rfl


theorem compiler_function_start_table_entry_metadata {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (start finish : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops before ctx typeIndex start finish = .ok (status, after)) :
    CompilerTableEntryMetadata before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start at accepted
  repeat' table_entry_metadata_step accepted using ops, law

theorem compiler_new_table_boundary {A : Type} (ops : runtime.platform.Alloc A)
    (signatures : Slice runtime.compiler.Signature) (functionSlots : Slice U32)
    (budget : runtime.compiler.Budget A) (batchStart : Usize) :
    runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart ⦃ out =>
      CompilerTableBoundary out ⦄ := by
  simp only [runtime.compiler.FunctionCompiler.new, WP.spec_ok]
  exact CompilerTableBoundary.empty rfl rfl

theorem compiler_function_start_table_boundary {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (start finish : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (boundary : CompilerTableBoundary before)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops before ctx typeIndex start finish = .ok (status, after)) :
    CompilerTableBoundary after := by
  have fields := compiler_function_start_table_entry_metadata ops law before after ctx typeIndex start finish status accepted
  simp only [CompilerTableEntryMetadata, Prod.mk.injEq] at fields
  exact boundary.preserved fields.1 fields.2.1 (by rw [fields.2.2])

end Itasca.Runtime.Compiler
