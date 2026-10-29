import Itasca.Runtime.Compiler.Local.Relations.Global.GlobalLowering
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem compiler_global_get_lowered {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (front : List Itasca.types.ValueType)
    (ty : Itasca.types.ValueType) (index : U32)
    (layout : CompilerLayout compiler (front.map Itasca.Translate.valueType))
    (reachable : compiler.reachable = true)
    (concrete : state.vals.val = (front ++ [ty]).map Itasca.code.StackType.Val)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 35#u16 index 0#u32 0#u128
      ⦃ out => out.1 = .Ok () →
        Lowered compiler out.2
          (globalGetInstruction (decide (width (Itasca.Translate.valueType ty) = 2)) compiler.height index)
          ((front ++ [ty]).map Itasca.Translate.valueType) ⦄ := by
  have top := top_is_v128_shape (alloc.vec.Vec.deref state.vals)
    (front.map Itasca.code.StackType.Val) ty (by simpa [alloc.vec.Vec.deref] using concrete)
  have wide : valueIsVector ty = decide (width (Itasca.Translate.valueType ty) = 2) := by
    cases ty <;> rfl
  rw [lower_global_get_eq ops compiler state index (valueIsVector ty) reachable top, wide]
  exact finish_op ops law compiler state (front ++ [ty]) _ _ layout concrete codeFits sourceFits coordinateFits

@[step] theorem compiler_global_set_lowered {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (front : List valtype) (ty : valtype) (index : U32)
    (layout : CompilerLayout compiler (front ++ [ty]))
    (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 36#u16 index 0#u32 0#u128
      ⦃ out => out.1 = .Ok () → ∃ source : U32,
        source.val = slots (compilerLocals compiler) + slots front ∧
        Lowered compiler out.2 (globalSetInstruction (decide (width ty = 2)) source index) front ⦄ := by
  obtain ⟨source, read, position⟩ := last_operand ops compiler front ty layout
  have height := layout.height
  simp only [slots_append, slots, Nat.add_zero] at height
  obtain ⟨difference, subtract, differenceVal⟩ := WP.spec_imp_exists
    (UScalar.sub_spec (x := compiler.height) (y := source) (by omega))
  have dw : difference.val = width ty := by omega
  have wide : (difference = 2#u32) ↔ width ty = 2 := by
    constructor
    · intro h
      have v : difference.val = 2 := by simpa using congrArg UScalar.val h
      omega
    · intro h; apply UScalar.eq_of_val_eq; simpa [h] using dw
  rw [lower_global_set_eq ops compiler state index source difference reachable read subtract]
  simp only [wide]
  step with finish_op ops law compiler state types
    (globalSetInstruction (decide (width ty = 2)) source index) _ layout concrete
    codeFits sourceFits coordinateFits as ⟨out, lowered, success⟩
  exact ⟨source, position, by simpa only [typed] using lowered success⟩
end Itasca.Runtime.Compiler
