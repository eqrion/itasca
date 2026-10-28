import Itasca.Runtime.Code.Local.Relations.Calls.IndirectCallLowering
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- An indirect call's table selector is the final i32 operand; its argument
base is determined by the source parameters, including two-word vectors. -/
theorem indirect_call_arithmetic {A : Type}
    (compiler : runtime.compiler.FunctionCompiler A) (front params : List valtype)
    (signature : runtime.compiler.Signature)
    (layout : CompilerLayout compiler ((front ++ params) ++ [.I32]))
    (parameterWidth : signature.param_slots.val = slots params) :
    ∃ total base : U32,
      U32.checked_add signature.param_slots 1#u32 = some total ∧
      U32.checked_sub compiler.height total = some base ∧
      base.val = slots (compilerLocals compiler) + slots front := by
  have height : compiler.height.val = slots (compilerLocals compiler) + slots front + slots params + 1 := by
    simpa [slots_append,slots,width,Nat.add_assoc] using layout.height
  have addSpec := U32.checked_add_bv_spec signature.param_slots 1#u32
  cases added : U32.checked_add signature.param_slots 1#u32 with
  | none =>
    simp only [added] at addSpec
    have bound := compiler.height.hBounds
    scalar_tac
  | some total =>
    simp only [added] at addSpec
    have subSpec := U32.checked_sub_bv_spec compiler.height total
    cases subtracted : U32.checked_sub compiler.height total with
    | none =>
      simp only [subtracted] at subSpec
      scalar_tac
    | some base =>
      simp only [subtracted] at subSpec
      refine ⟨total,base,rfl,subtracted,?_⟩
      scalar_tac

theorem indirect_call_operand {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (front params : List valtype)
    (layout : CompilerLayout compiler ((front ++ params) ++ [.I32])) :
    ∃ index : U32, runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok index) ∧
      index.val = slots (compilerLocals compiler) + slots front + slots params := by
  obtain ⟨r,read,index,rfl,position⟩ := WP.spec_imp_exists
    (compiler_operand ops compiler _ layout 1#usize (by decide) (by change 1 ≤ _; simp only [List.length_append,List.length_singleton]; omega))
  refine ⟨index,read,?_⟩
  have take : (((front ++ params) ++ [valtype.I32]).take (((front ++ params) ++ [valtype.I32]).length - 1)) = front ++ params := by
    rw [List.length_append, List.length_singleton, Nat.add_sub_cancel]
    exact List.take_left
  change index.val = slots (compilerLocals compiler) + offset ((front ++ params) ++ [valtype.I32]) (((front ++ params) ++ [valtype.I32]).length - 1) at position
  simpa only [offset, take, slots_append, Nat.add_assoc] using position
end Itasca.Runtime.Code
