import Itasca.Runtime.Code.Local.Relations.Table.TableSources
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
/-- Exact finite callback trace of the target loop. This intermediate execution
witness is eliminated when producing the final syntax-only table certificate. -/
inductive TableBranchRun {A : Type} (ops : runtime.platform.Alloc A) :
    runtime.compiler.FunctionCompiler A → Nat → runtime.compiler.FunctionCompiler A → Prop where
  | done (compiler) (index) (finished : compiler.table_depths.val.length ≤ index) :
      TableBranchRun ops compiler index compiler
  | cons {before middle after} (index : Usize)
      (inside : index.val < before.table_depths.val.length)
      (called : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),middle))
      (rest : TableBranchRun ops middle (index.val+1) after) :
      TableBranchRun ops before index.val after

theorem compiler_table_loop_trace {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.control.FunctionCompiler.lower_table_branches_loop
      ops before index status = .ok output) :
    snapshotStatus output = .Ok () →
      status = .Ok () ∧ TableBranchRun ops before index.val (snapshotCompiler output) := by
  intro successful
  generalize measure : Usize.max - index.val = n
  induction n using Nat.strong_induction_on generalizing before index status with
  | h n ih =>
    unfold runtime.compiler.control.FunctionCompiler.lower_table_branches_loop at accepted
    rw [loop] at accepted
    simp only [runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.body,
      bind_ok] at accepted
    split at accepted
    · rename_i inside
      have indexBound : index.val < before.table_depths.val.length := by scalar_tac
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at accepted
        subst output
        simp [snapshotStatus] at successful
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at accepted
        obtain ⟨⟨result, middle⟩, patched, tail⟩ := bind_ok_inv _ _ _ accepted
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := bind_ok_inv _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < n := by scalar_tac
        have tail' : runtime.compiler.control.FunctionCompiler.lower_table_branches_loop
            ops middle nextIndex result = .ok output := by
          simpa only [uncurry_apply_pair, bind_ok,
            runtime.compiler.control.FunctionCompiler.lower_table_branches_loop,
            runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.body,
            core.result.Result.is_ok] using tail
        obtain ⟨resultOk, restSources⟩ := ih _ smaller middle nextIndex result tail' rfl
        subst result
        exact ⟨rfl, .cons index indexBound patched (by simpa only [progress] using restSources)⟩
    · simp only [bind_ok, Result.ok.injEq] at accepted
      subst output
      exact ⟨successful, .done _ _ (by scalar_tac)⟩

end Itasca.Runtime.Code
