import Exec.Code.Local.Callbacks.Calls.CallbackSafety
import Exec.Code.Local.Relations.Control.Control

/-! Normal-return control primitives under raw index bounds. In particular,
patching a non-branch instruction returns an ordinary compiler error. -/
namespace Exec.Code
open Aeneas Aeneas.Std

@[step] theorem block_signature_total (signatures : Slice runtime.compiler.Signature)
    (bt : Itasca.signature.BlockType)
    (indexFits : ∀ index, bt = .TypeIndex index → index.val < signatures.val.length) :
    runtime.compiler.control.block_signature signatures bt ⦃ _ => True ⦄ := by
  cases bt with
  | Empty => simp [runtime.compiler.control.block_signature, WP.spec_ok]
  | Value ty =>
    unfold runtime.compiler.control.block_signature
    step with compiler_width ty
  | TypeIndex index =>
    have inside := indexFits index rfl
    have max := signatures.property
    unfold runtime.compiler.control.block_signature
    step as ⟨cast, castValue⟩
    step

private theorem patch_result_total {A} (before : runtime.compiler.FunctionCompiler A)
    (pc : Usize) (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError) :
    Result.ok (status, {before with function := {before.function with
      code := before.function.code.set pc instruction}}) ⦃ out =>
      out.2.function.code.val.length = before.function.code.val.length ⦄ := by
  simp [WP.spec_ok]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
@[step] theorem compiler_patch_total {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (pc : Usize) (target : U32)
    (inside : pc.val < compiler.function.code.val.length) :
    runtime.compiler.control.FunctionCompiler.patch ops compiler pc target ⦃ out =>
      out.2.function.code.val.length = compiler.function.code.val.length ⦄ := by
  obtain ⟨⟨instruction, back⟩, call, found, backEq⟩ :=
    WP.spec_imp_exists (alloc.vec.Vec.index_mut_usize_spec compiler.function.code pc inside)
  rw [runtime.compiler.control.FunctionCompiler.patch, alloc.vec.Vec.index_mut_slice_index,
    call, bind_ok]
  rw [backEq]
  cases instruction <;> exact patch_result_total compiler pc _ _

end Exec.Code
