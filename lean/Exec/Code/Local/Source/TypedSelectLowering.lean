import Exec.Code.Local.Relations.Common.SelectOperands
import Exec.Code.Local.Source.TypedSelectEmission
namespace Exec.Code
open Aeneas Aeneas.Std
@[step] theorem compiler_typed_select_lowered {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (front : List valtype) (ty : valtype)
    (layout : CompilerLayout compiler (front ++ [ty, ty, .I32]))
    (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ [ty])
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 28#u16 0#u32 0#u32 0#u128
      ⦃ out => out.1 = .Ok () → ∃ left right condition : U32,
        left.val = slots (compilerLocals compiler) + slots front ∧
        right.val = left.val + width ty ∧ condition.val = right.val + width ty ∧
        Lowered compiler out.2 (selectInstruction (decide (width ty = 2)) left right condition)
          (front ++ [ty]) ⦄ := by
  obtain ⟨left, right, condition, hl, hr, hc, lp, rp, cp⟩ := select_operands ops compiler front ty layout
  obtain ⟨difference, subtract, differenceVal⟩ := WP.spec_imp_exists
    (UScalar.sub_spec (x := right) (y := left) (by omega))
  have dw : difference.val = width ty := by omega
  have wide : (difference = 2#u32) ↔ width ty = 2 := by
    constructor
    · intro h
      have v : difference.val = 2 := by simpa using congrArg UScalar.val h
      omega
    · intro h; apply UScalar.eq_of_val_eq; simpa [h] using dw
  have dispatch := lower_select_eq ops compiler state left right condition difference true reachable hl hr hc subtract
  simp only [ite_true] at dispatch
  rw [dispatch]
  simp only [wide]
  step with finish_op ops law compiler state types
    (selectInstruction (decide (width ty = 2)) left right condition) _ layout concrete
    codeFits sourceFits coordinateFits as ⟨out, lowered, success⟩
  exact ⟨left, right, condition, lp, rp, cp, by simpa only [typed] using lowered success⟩
@[step] theorem compiler_typed_select_emission {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (C : context) (front : List valtype) (ty : valtype)
    (locals : compilerLocals compiler = C.LOCALS)
    (layout : CompilerLayout compiler (front ++ [ty, ty, .I32]))
    (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ [ty])
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 28#u16 0#u32 0#u32 0#u128
      ⦃ out => out.1 = .Ok () → ∃ emitted,
        Lowered compiler out.2 emitted (front ++ [ty]) ∧
        TypedSelectEmission C (front ++ [ty, ty, .I32]) (.SELECT (some [ty])) [emitted] (front ++ [ty]) ⦄ := by
  apply WP.spec_mono (compiler_typed_select_lowered ops law compiler state types front ty layout reachable concrete typed
    codeFits sourceFits coordinateFits)
  intro out result success
  obtain ⟨left,right,condition,lp,rp,cp,lowered⟩ := result success
  exact ⟨_, lowered, .select front ty left right condition (by simpa only [locals] using lp) rp cp⟩


end Exec.Code
