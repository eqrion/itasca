import Exec.Code.Body.Reader.Control.ReaderReturn
import Exec.Code.Body.Reader.Common.ReaderStacks
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

private theorem return_stack_suffix {before outer segment rest : List code.StackType} {results : List valtype}
    (values : before = outer ++ segment) (known : ConcreteStack before)
    (transfer : ∀ ts, Sequence.Realizes false rest ts → Sequence.Realizes false segment (ts ++ results)) :
    ∃ front, Sequence.stackTypes before = front ++ results := by
  have segmentKnown := (concreteStack_append.mp (values ▸ known)).2
  have types := realized_concrete_types segmentKnown (transfer _ (Sequence.realizes_default false rest))
  refine ⟨Sequence.stackTypes outer ++ Sequence.stackTypes rest, ?_⟩
  simpa [Sequence.stackTypes, values, List.map_append, List.append_assoc] using
    congrArg (Sequence.stackTypes outer ++ ·) types.symm

theorem reader_return_stack_wasm2 (st out : code.BodyState) (env : module.Env) (index : U32)
    (results : List types.ValueType) (outer segment : List code.StackType)
    (resolved : Wasm2.resolve env (.Type index .Results) = some results)
    (values : st.core.vals.val = outer ++ segment) (base : (Control.base st.core).val = outer.length)
    (known : ConcreteStack st.core.vals.val) (mono : Control.polymorphic st.core = false)
    (accepted : Wasm2.returnStep st env index = .ok (.Ok (), out)) :
    ∃ front, Sequence.stackTypes st.core.vals.val = front ++ results.map Translate.valueType := by
  obtain ⟨⟨result, middle⟩, popped, _, _, rest, _, _, transfer⟩ := WP.spec_imp_exists
    (code.pop_results.realizes st.core env (.Type index .Results) results outer segment resolved values base)
  cases result with
  | Err error => simp [Wasm2.returnStep, popped] at accepted
  | Ok unit =>
    have effect := transfer rfl
    try dsimp only at effect
    rw [mono] at effect
    exact return_stack_suffix values known effect

theorem reader_return_stack_wasm1 (st out : code.OpIterState) (ctx : code.Context)
    (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length)
    (known : ConcreteStack st.vals.val) (mono : Control.polymorphic st = false)
    (accepted : code.read_return st ctx = .ok (.Ok (), out)) :
    ∃ front, Sequence.stackTypes st.vals.val = front ++ ctx.results.val.map Translate.valueType := by
  obtain ⟨⟨result, middle⟩, popped, _, _, rest, _, _, transfer⟩ := WP.spec_imp_exists
    (code.pop_types.realizes st outer segment (alloc.vec.Vec.deref ctx.results) values base)
  cases result with
  | Err error => simp [code.read_return, popped, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok unit =>
    dsimp only at transfer
    rw [mono] at transfer
    apply return_stack_suffix (rest := rest) values known
    simpa [alloc.vec.Vec.deref] using transfer
end Exec.Code
