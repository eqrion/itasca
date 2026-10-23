import Exec.Code.Body.Reader.Common.ReaderValues
import Exec.Code.Local.Capacity.FinishBudgetAvailability

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- A source numeric effect and exact reader post supply the live operand
layout before the numeric callback runs, including extension opcodes. -/
theorem ReaderPostWasm2.numeric_available {data env locals index st out instruction values}
    {p : Wasm2.Pending data env .Wasm2 locals index st}
    (post : ReaderPostWasm2 p out instruction p.current.ctrl.polymorphic_base values)
    {input : List types.ValueType} {output : types.ValueType}
    (effect : StackSemantics.NumericEffect p.current.ctrl.polymorphic_base p.current.vals input output values)
    {A : Type} (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (demand : CallbackDemand compiler out bound)
    (op : Abs.Numeric.Instruction)
    (inputs : input.map Translate.valueType = List.replicate op.arity (integerType op.input))
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val)) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler out (integerOpcode op) 0#u32 0#u32 0#u128 ⦃ result =>
      result.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget result.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · rw [monomorphic live] at effect
    obtain ⟨old,new⟩ := post.values
    obtain ⟨front,_,oldTypes,_⟩ := numeric_full_stack_types (known live) old new effect
    rw [inputs] at oldTypes
    have layout := wholeLayout live
    rw [oldTypes] at layout
    exact compiler_numeric_available_effect ops bound available compiler out demand front op (fun _ => layout)
  · exact compiler_numeric_available_effect ops bound available compiler out demand [] op
      (fun impossible => False.elim (live impossible))

/-- A source numeric effect and exact reader post supply the live operand
layout before the float callback runs, including extension opcodes. -/
theorem ReaderPostWasm2.float_available {data env locals index st out instruction values}
    {p : Wasm2.Pending data env .Wasm2 locals index st}
    (post : ReaderPostWasm2 p out instruction p.current.ctrl.polymorphic_base values)
    {input : List types.ValueType} {output : types.ValueType}
    (effect : StackSemantics.NumericEffect p.current.ctrl.polymorphic_base p.current.vals input output values)
    {A : Type} (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (demand : CallbackDemand compiler out bound)
    (op : Abs.Float.Instruction)
    (inputs : input.map Translate.valueType = List.replicate op.arity (valtype_numtype op.input))
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val)) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler out (floatOpcode op) 0#u32 0#u32 0#u128 ⦃ result =>
      result.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget result.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · rw [monomorphic live] at effect
    obtain ⟨old,new⟩ := post.values
    obtain ⟨front,_,oldTypes,_⟩ := numeric_full_stack_types (known live) old new effect
    rw [inputs] at oldTypes
    have layout := wholeLayout live
    rw [oldTypes] at layout
    exact compiler_float_available_effect ops bound available compiler out demand front op (fun _ => layout)
  · exact compiler_float_available_effect ops bound available compiler out demand [] op
      (fun impossible => False.elim (live impossible))

end Exec.Code
