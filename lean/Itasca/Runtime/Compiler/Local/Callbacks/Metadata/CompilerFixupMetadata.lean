import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerPatchMetadata

/-!
Compiler snapshots and metadata effects of branch fixups.

Main declarations: `CompilerSnapshot` and `snapshotCompiler`. A direct consumer is `Compiler.Local.Callbacks.CodeGrowth.PatchGrowth`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts

abbrev CompilerSnapshot (A : Type) :=
  Slice runtime.compiler.Signature × Slice U32 × runtime.compiler.Budget A × Usize ×
  runtime.bytecode.CompiledFunction × alloc.vec.Vec runtime.compiler.Frame × Bool × Usize ×
  alloc.vec.Vec U32 × U32 × alloc.vec.Vec U32 × alloc.vec.Vec U32 ×
  core.result.Result Unit Itasca.error.VisitError

def snapshotCompiler {A : Type} (output : CompilerSnapshot A) : runtime.compiler.FunctionCompiler A :=
  let (signatures, functionSlots, budget, batchStart, function, frames, reachable,
    nextSource, operands, height, offsets, depths, _) := output
  ⟨signatures, functionSlots, budget, batchStart, function, frames, reachable,
    nextSource, operands, height, offsets, depths⟩

theorem compiler_fixups_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
      ops before sites target index status = .ok output) :
    CompilerOrdinaryStable before (snapshotCompiler output) := by
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
        exact .refl _
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
        exact (compiler_patch_ordinary_result ops before middle site target result patched).trans
          (ih _ smaller middle nextIndex result tail' rfl)
    · simp only [bind_ok, Result.ok.injEq] at accepted
      subst output
      exact .refl _

theorem compiler_fixups_after_if_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1
      ops before sites target index status = .ok output) :
    CompilerOrdinaryStable before (snapshotCompiler output) :=
  compiler_fixups_ordinary_result ops before sites target index status output accepted
end Itasca.Runtime.Code
