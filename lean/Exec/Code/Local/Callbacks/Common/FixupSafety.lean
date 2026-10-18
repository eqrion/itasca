import Exec.Code.Local.Relations.Control.ControlSafety
import Exec.Code.Local.Callbacks.Common.CompilerFixupMetadata

/-! Fixup loops return normally under address bounds, including an existing
error or a patch to a non-branch. No branch-layout certificate is required. -/
namespace Exec.Code
open Aeneas Aeneas.Std

@[step] theorem compiler_fixups_total {A} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (inside : ∀ site ∈ sites.val, site.val < compiler.function.code.val.length) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
      ops compiler sites target index status ⦃ out =>
      (snapshotCompiler out).function.code.val.length = compiler.function.code.val.length ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
  apply loop.spec_decr_nat (fun p => sites.val.length - p.2.1.val)
    (fun p => p.1.function.code.val.length = compiler.function.code.val.length)
  · rintro ⟨current, i, result⟩ length
    dsimp only at length
    unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0.body
    simp only
    split
    · rename_i more
      have bound : i.val < sites.val.length := by scalar_tac
      cases result with
      | Err error => simp [core.result.Result.is_ok, snapshotCompiler, WP.spec_ok, length]
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step as ⟨site, found⟩
        have siteInside : site.val < current.function.code.val.length := by
          rw [length, found]
          exact inside _ (List.getElem_mem _)
        step with compiler_patch_total ops current site target siteInside as ⟨status1, nextCompiler, sameLength⟩
        step as ⟨nextIndex, increment⟩
        exact ⟨sameLength.trans length, by scalar_tac⟩
    · simp [WP.spec_ok, snapshotCompiler, length]
  · rfl

@[step] theorem compiler_fixups_after_if_total {A} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (inside : ∀ site ∈ sites.val, site.val < compiler.function.code.val.length) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1
      ops compiler sites target index status ⦃ out =>
      (snapshotCompiler out).function.code.val.length = compiler.function.code.val.length ⦄ :=
  compiler_fixups_total ops compiler sites target index status inside

end Exec.Code
