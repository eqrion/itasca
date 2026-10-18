import Exec.Code.Local.Relations.Table.BranchTableSkip
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def frameBranchWidth (frame : runtime.compiler.Frame) : U32 :=
  match frame.kind with | .Loop => frame.params | _ => frame.results

private theorem vec_read_success {T : Type} (vector : alloc.vec.Vec T) (index : Usize) (value : T)
    (accepted : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T) vector index = .ok value) :
    vector.val[index.val]? = some value := by
  change alloc.vec.Vec.index_usize vector index = .ok value at accepted
  unfold alloc.vec.Vec.index_usize at accepted
  split at accepted
  · simp [Result.fail] at accepted
  · rename_i found exact
    cases Result.ok_injective accepted
    exact exact

private theorem checked_add_success (a b out : U32)
    (called : lift (U32.checked_add a b) = .ok (some out)) :
    out.val = a.val + b.val := by
  have spec : lift (U32.checked_add a b)
      ⦃ result => ∀ value, result = some value → value.val = a.val + b.val ⦄ := by
    step as ⟨result,facts⟩
    cases result <;> simp_all
  rw [called,WP.spec_ok] at spec
  exact spec out rfl

private theorem checked_sub_success (a b out : U32)
    (called : lift (U32.checked_sub a b) = .ok (some out)) :
    out.val + b.val = a.val := by
  have spec : lift (U32.checked_sub a b)
      ⦃ result => ∀ value, result = some value → value.val + b.val = a.val ⦄ := by
    step as ⟨result,facts⟩
    cases result <;> simp_all
  rw [called,WP.spec_ok] at spec
  exact spec out rfl

/-- Successful branch lowering itself establishes the selected frame and exact
operand interval; no separate depth or subtraction safety premise is needed. -/
theorem compiler_branch_arguments_success {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (depth skip : U32)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip false = .ok (.Ok (),after)) :
    ∃ (index : Usize) (frame : runtime.compiler.Frame) (source : U32),
      before.frames.val[index.val]? = some frame ∧
      index.val + depth.val + 1 = before.frames.val.length ∧
      source.val + (frameBranchWidth frame).val + skip.val = before.height.val := by
  unfold runtime.compiler.control.FunctionCompiler.branch at accepted
  obtain ⟨last,lastCall,rest⟩ := bind_ok_inv _ _ _ accepted
  obtain ⟨converted,convertedCall,rest⟩ := bind_ok_inv _ _ _ rest
  obtain ⟨index,indexCall,rest⟩ := bind_ok_inv _ _ _ rest
  obtain ⟨frame,frameCall,rest⟩ := bind_ok_inv _ _ _ rest
  have lookup := vec_read_success before.frames index frame frameCall
  have lastEq := UScalar.sub_equiv (alloc.vec.Vec.len before.frames) 1#usize
  rw [lastCall] at lastEq
  simp at lastEq
  have convertedEq : converted = UScalar.cast .Usize depth := (Result.ok_injective convertedCall).symm
  have indexEq := UScalar.sub_equiv last converted
  rw [indexCall] at indexEq
  simp at indexEq
  clear accepted
  have position : index.val + depth.val + 1 = before.frames.val.length := by
    subst converted
    have bound := depth.hmax
    have castEq : (UScalar.cast .Usize depth).val = depth.val := by scalar_tac
    rw [castEq] at indexEq
    scalar_tac
  cases kindEq : frame.kind
  all_goals
    simp only [kindEq,bind_ok,Bool.false_eq_true,ite_false,ite_true] at rest
    obtain ⟨total,totalCall,rest⟩ := bind_ok_inv _ _ _ rest
    cases total with
    | none => simp [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | some total =>
      simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
      obtain ⟨source,sourceCall,rest⟩ := bind_ok_inv _ _ _ rest
      cases source with
      | none => simp [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | some source =>
        clear rest
        have sum := checked_add_success skip (frameBranchWidth frame) total (by
          simpa only [frameBranchWidth,kindEq] using totalCall)
        have sub := checked_sub_success before.height total source sourceCall
        refine ⟨index,frame,source,lookup,position,?_⟩
        omega
end Exec.Code
