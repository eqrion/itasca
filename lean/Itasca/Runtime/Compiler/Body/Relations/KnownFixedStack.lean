import Itasca.Runtime.Compiler.Local.Relations.Stacks.ConcretePops
import Itasca.Runtime.Compiler.Body.Reader.StackValues
import Itasca.Body.LoopDispatch

/-!
Fixed signatures preserve concrete operands even when the control frame is polymorphic; this follows from actual pop/push behavior.

Main declarations: `read_fixed_known` and `fixed_effect_types`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Computation

/-- Fixed signatures preserve concrete operands even when the control frame is
polymorphic; this follows from actual pop/push behavior. -/
theorem read_fixed_known (st out : code.OpIterState) (outer segment : List code.StackType)
    (inputs : List wasm_types.ValueType) (output : Option wasm_types.ValueType)
    (values : st.vals.val = outer ++ segment) (base : (Body.Control.base st).val = outer.length)
    (size : st.vals.val.length < Usize.max) (known : ConcreteStack st.vals.val)
    (accepted : Body.Simd.readFixed st inputs output = .ok (.Ok (),out)) :
    ConcreteStack out.vals.val := by
  induction inputs generalizing st segment with
  | nil =>
    cases output with
    | none =>
      simp only [Body.Simd.readFixed,Result.ok.injEq,Prod.mk.injEq,true_and] at accepted
      subst out; exact known
    | some type =>
      obtain ⟨after,pushed,afterValues,_,_⟩ := WP.spec_imp_exists (code.push_val.spec st (.Val type) size)
      simp only [Body.Simd.readFixed,pushed,bind_ok,Result.ok.injEq,Prod.mk.injEq,true_and] at accepted
      subst out
      rw [afterValues]
      exact concrete_stack_append.mpr ⟨known,by simp [ConcreteStack]⟩
  | cons type inputs ih =>
    unfold Body.Simd.readFixed at accepted
    obtain ⟨⟨result,middle⟩,popped,rest⟩ := bind_ok_inv _ _ _ accepted
    cases result with
    | Err error => simp [uncurry_apply_pair] at rest
    | Ok value =>
      obtain ⟨tail,controls,position,vals,shrink,nextKnown⟩ :=
        pop_with_type_known st middle outer segment type (.Ok value) values base known popped
      have fits : middle.vals.val.length < Usize.max := by
        simp only [vals,values,List.length_append] at *
        omega
      have middleBase : (Body.Control.base middle).val = outer.length := by
        simpa only [Body.Control.base,controls] using base
      apply ih middle tail vals middleBase fits nextKnown
      simpa only [uncurry_apply_pair] using rest

/-- A live fixed signature exposes exact source input/output lists once the actual
reader has preserved concrete stack entries. -/
theorem fixed_effect_types {before after : List code.StackType} {inputs output}
    (known : ConcreteStack before)
    (effect : Body.Simd.FixedEffect false before inputs output after) :
    ∃ front, Body.Stack.stackTypes before = front ++ Body.Simd.inputTypes inputs ∧
      Body.Stack.stackTypes after = front ++ Body.Simd.outputTypes output := by
  obtain ⟨front,afterTypes,realized⟩ := effect _ (Body.Stack.realizes_default false after)
  exact ⟨front,(realized_concrete_types known realized).symm,afterTypes⟩

end Itasca.Compiler
