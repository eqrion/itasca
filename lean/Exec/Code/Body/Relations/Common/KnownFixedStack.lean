import Exec.Code.Local.Relations.Common.KnownNumericStack
import Exec.Code.Body.Reader.Common.ReaderStacks
import Itasca.Wasm2.FixedOperands
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts

/-- Fixed signatures preserve concrete operands even when the control frame is
polymorphic; this follows from actual pop/push behavior. -/
theorem readFixed_known (st out : code.OpIterState) (outer segment : List code.StackType)
    (inputs : List types.ValueType) (output : Option types.ValueType)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length)
    (size : st.vals.val.length < Usize.max) (known : ConcreteStack st.vals.val)
    (accepted : Wasm2.Simd.readFixed st inputs output = .ok (.Ok (),out)) :
    ConcreteStack out.vals.val := by
  induction inputs generalizing st segment with
  | nil =>
    cases output with
    | none =>
      simp only [Wasm2.Simd.readFixed,Result.ok.injEq,Prod.mk.injEq,true_and] at accepted
      subst out; exact known
    | some type =>
      obtain ⟨after,pushed,afterValues,_,_⟩ := WP.spec_imp_exists (code.push_val.spec st (.Val type) size)
      simp only [Wasm2.Simd.readFixed,pushed,bind_ok,Result.ok.injEq,Prod.mk.injEq,true_and] at accepted
      subst out
      rw [afterValues]
      exact concreteStack_append.mpr ⟨known,by simp [ConcreteStack]⟩
  | cons type inputs ih =>
    unfold Wasm2.Simd.readFixed at accepted
    obtain ⟨⟨result,middle⟩,popped,rest⟩ := bind_ok_inv _ _ _ accepted
    cases result with
    | Err error => simp [uncurry_apply_pair] at rest
    | Ok value =>
      obtain ⟨tail,controls,position,vals,shrink,nextKnown⟩ :=
        pop_with_type_known st middle outer segment type (.Ok value) values base known popped
      have fits : middle.vals.val.length < Usize.max := by
        simp only [vals,values,List.length_append] at *
        omega
      have middleBase : (Control.base middle).val = outer.length := by
        simpa only [Control.base,controls] using base
      apply ih middle tail vals middleBase fits nextKnown
      simpa only [uncurry_apply_pair] using rest

/-- A live fixed signature exposes exact source input/output lists once the actual
reader has preserved concrete stack entries. -/
theorem fixed_effect_types {before after : List code.StackType} {inputs output}
    (known : ConcreteStack before)
    (effect : Wasm2.Simd.FixedEffect false before inputs output after) :
    ∃ front, Sequence.stackTypes before = front ++ Wasm2.Simd.inputTypes inputs ∧
      Sequence.stackTypes after = front ++ Wasm2.Simd.outputTypes output := by
  obtain ⟨front,afterTypes,realized⟩ := effect _ (Sequence.realizes_default false after)
  exact ⟨front,(realized_concrete_types known realized).symm,afterTypes⟩

end Itasca.Runtime.Code
