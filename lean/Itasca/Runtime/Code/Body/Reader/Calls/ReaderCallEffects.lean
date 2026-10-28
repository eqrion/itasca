import Itasca.Runtime.Code.Body.Reader.Calls.ReaderWasm2Call
import Itasca.Runtime.Code.Body.Reader.Common.ReaderValues
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Actual direct-call metadata lookup and parameter/result stack transfer. -/
theorem reader_call_info_effect (st out : code.BodyState) (data : Slice U8) (env : module.Env)
    (index : U32) (outer segment : List code.StackType)
    (values : st.core.vals.val = outer ++ segment) (base : (Control.base st.core).val = outer.length)
    (accepted : code.call_info st data env = .ok (.Ok index, out)) :
    ∃ (ft : types.FuncType) (rest : List code.StackType),
      env.func_types.val[index.val]? = some ft ∧
      out.core.vals.val = outer ++ (rest ++ ft.results.val.map code.StackType.Val) ∧
      (∀ ts, Sequence.Realizes (Control.polymorphic st.core) rest ts →
        Sequence.Realizes (Control.polymorphic st.core) segment (ts ++ ft.params.val.map Translate.valueType)) := by
  obtain ⟨⟨result, state⟩, read, sameValues, controls, post⟩ := WP.spec_imp_exists (code.take_index.spec st.core data)
  dsimp only at sameValues controls post
  cases result with
  | Err error => simp [code.call_info, read, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok idx =>
    by_cases bound : idx.val < env.func_types.val.length
    · have indexBound : (UScalar.cast .Usize idx).val < env.func_types.val.length := by simpa using bound
      obtain ⟨ft, indexed, lookup⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec env.func_types (UScalar.cast .Usize idx) indexBound)
      obtain ⟨⟨reply, after⟩, applied, effect⟩ := WP.spec_imp_exists
        (code.apply_func_type.realizes state ft outer segment (by simpa [sameValues] using values)
          (by simpa [Control.base, controls] using base))
      cases reply with
      | Err error => simp [code.call_info, read, lift, Nat.not_le_of_gt bound, indexed, applied,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
      | Ok unit =>
        cases unit
        obtain ⟨_, _, _, _, rest, afterValues, _, transfer⟩ := effect rfl
        dsimp only at afterValues transfer
        simp [code.call_info, read, lift, Nat.not_le_of_gt bound, indexed, applied,
          core.result.Result.Insts.CoreOpsTry.branch] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        refine ⟨ft, rest, ?_, afterValues, ?_⟩
        · simpa [List.getElem?_eq_getElem bound] using congrArg some lookup.symm
        · simpa [Control.polymorphic, controls] using transfer
    · simp [code.call_info, read, lift, Nat.le_of_not_gt bound,
        core.result.Result.Insts.CoreOpsTry.branch] at accepted

/-- Live calls determine complete concrete operand stacks from their exact
parameter/result transfer, without assuming a compiler stack effect. -/
theorem call_full_stack_types {before after outer segment rest : List code.StackType}
    (params results : List types.ValueType)
    (known : ConcreteStack before) (old : before = outer ++ segment)
    (new : after = outer ++ (rest ++ results.map code.StackType.Val))
    (transfer : ∀ ts, Sequence.Realizes false rest ts →
      Sequence.Realizes false segment (ts ++ params.map Translate.valueType)) :
    ∃ front : List types.ValueType,
      Sequence.stackTypes before = front.map Translate.valueType ++ params.map Translate.valueType ∧
      after = (front ++ results).map code.StackType.Val := by
  have both := concreteStack_append.mp (old ▸ known)
  have restKnown := concrete_stack_transfer both.2 transfer
  obtain ⟨outerTypes, outerConcrete⟩ := (concreteStack_iff outer).mp both.1
  obtain ⟨restTypes, restConcrete⟩ := (concreteStack_iff rest).mp restKnown
  have segmentTypes := realized_concrete_types both.2 (transfer _ (Sequence.realizes_default false rest))
  refine ⟨outerTypes ++ restTypes, ?_, ?_⟩
  · have whole := congrArg (Sequence.stackTypes outer ++ ·) segmentTypes.symm
    simpa [old, outerConcrete, restConcrete, Sequence.stackTypes, List.map_map,
      Function.comp_def, List.append_assoc] using whole
  · simp [new, outerConcrete, restConcrete, List.append_assoc]

end Itasca.Runtime.Code
