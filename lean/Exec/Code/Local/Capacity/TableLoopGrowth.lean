import Exec.Code.Local.Capacity.TableGrowth
import Exec.Code.Local.Relations.Table.TableDepths
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
theorem compiler_table_loop_growth {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.lower_table_branches_loop
      ops before index status = .ok output) :
    (snapshotCompiler output).table_depths = before.table_depths ∧
      (snapshotCompiler output).function.code.val.length ≤ before.function.code.val.length +
        2 * (before.table_depths.val.length - index.val) := by
  generalize measure : Usize.max - index.val = n
  induction n using Nat.strong_induction_on generalizing before index status with
  | h n ih =>
    unfold runtime.compiler.FunctionCompiler.lower_table_branches_loop at accepted
    rw [loop] at accepted
    simp only [runtime.compiler.FunctionCompiler.lower_table_branches_loop.body,
      bind_ok] at accepted
    split at accepted
    · rename_i inside
      have indexBound : index.val < before.table_depths.val.length := by scalar_tac
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at accepted
        subst output
        exact ⟨rfl, by simp only [snapshotCompiler]; omega⟩
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
        have tail' : runtime.compiler.FunctionCompiler.lower_table_branches_loop
            ops middle nextIndex result = .ok output := by
          simpa only [uncurry_apply_pair, bind_ok,
            runtime.compiler.FunctionCompiler.lower_table_branches_loop,
            runtime.compiler.FunctionCompiler.lower_table_branches_loop.body,
            core.result.Result.is_ok] using tail
        have depths := compiler_table_branch_depths ops before middle index result patched
        have growth := compiler_table_branch_growth ops law before middle index result patched
        obtain ⟨finalDepths, finalGrowth⟩ := ih _ smaller middle nextIndex result tail' rfl
        refine ⟨finalDepths.trans depths, ?_⟩
        rw [depths] at finalGrowth
        omega
    · simp only [bind_ok, Result.ok.injEq] at accepted
      subst output
      exact ⟨rfl, by simp only [snapshotCompiler]; omega⟩

end Exec.Code
