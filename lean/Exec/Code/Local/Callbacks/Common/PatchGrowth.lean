import Exec.Code.Local.Callbacks.Common.CompilerFixupMetadata
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
private theorem code_update_length {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (pc : Usize) (instruction : runtime.bytecode.Instr)
    (result status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : Result.ok (result, {before with function := {before.function with
      code := before.function.code.set pc instruction}}) = Result.ok (status, after)) :
    after.function.code.val.length = before.function.code.val.length := by
  have same := (Prod.mk.inj (Result.ok.injEq.mp accepted)).2
  subst after
  simp

theorem compiler_patch_code_length {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (pc : Usize) (target : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.patch ops before pc target = .ok (status, after)) :
    after.function.code.val.length = before.function.code.val.length := by
  unfold runtime.compiler.control.FunctionCompiler.patch at accepted
  obtain ⟨⟨instruction, restore⟩, indexed, rest⟩ := bind_ok_inv _ _ _ accepted
  rw [alloc.vec.Vec.index_mut_slice_index] at indexed
  unfold alloc.vec.Vec.index_mut_usize at indexed
  obtain ⟨value, _, indexed⟩ := bind_ok_inv _ _ _ indexed
  have restoreEq := (Prod.mk.inj (Result.ok.injEq.mp indexed)).2
  subst restore
  cases instruction <;> exact code_update_length before after pc _ _ status rest
theorem compiler_fixups_code_length {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
      ops before sites target index status = .ok output) :
    (snapshotCompiler output).function.code.val.length = before.function.code.val.length := by
  generalize measure : Usize.max - index.val = n
  induction n using Nat.strong_induction_on generalizing before index status with
  | h n ih =>
    unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0 at accepted
    rw [loop] at accepted
    simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0.body,
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
        have tail' : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
            ops middle sites target nextIndex result = .ok output := by
          simpa only [uncurry_apply_pair, bind_ok,
            runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0,
            runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0.body,
            core.result.Result.is_ok] using tail
        exact (ih _ smaller middle nextIndex result tail' rfl).trans
          (compiler_patch_code_length ops before middle site target result patched)
    · simp only [bind_ok, Result.ok.injEq] at accepted
      subst output
      rfl

theorem compiler_fixups_after_if_code_length {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1
      ops before sites target index status = .ok output) :
    (snapshotCompiler output).function.code.val.length = before.function.code.val.length :=
  compiler_fixups_code_length ops before sites target index status output accepted
end Exec.Code
