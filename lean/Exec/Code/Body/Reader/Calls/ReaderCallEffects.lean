import Exec.Code.Body.Reader.Calls.ReaderWasm2Call
import Exec.Code.Body.Reader.Common.ReaderValues
namespace Exec.Code
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

theorem reader_call_effect_wasm1 (st out : code.OpIterState) (data : Slice U8) (env : module.Env)
    (index : U32) (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length)
    (capacity : st.vals.val.length < Usize.max)
    (accepted : code.read_call st data env = .ok (.Ok index, out)) :
    ∃ (ft : types.FuncType) (rest : List code.StackType),
      env.func_types.val[index.val]? = some ft ∧
      out.vals.val = outer ++ (rest ++ ft.results.val.map code.StackType.Val) ∧
      (∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
        Sequence.Realizes (Control.polymorphic st) segment (ts ++ ft.params.val.map Translate.valueType)) := by
  obtain ⟨⟨result, state⟩, read, sameValues, controls, post⟩ := WP.spec_imp_exists (code.take_index.spec st data)
  dsimp only at sameValues controls post
  cases result with
  | Err error => simp [code.read_call, read, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok idx =>
    by_cases bound : idx.val < env.func_types.val.length
    · have indexBound : (UScalar.cast .Usize idx).val < env.func_types.val.length := by simpa using bound
      obtain ⟨ft, indexed, lookup⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec env.func_types (UScalar.cast .Usize idx) indexBound)
      obtain ⟨requirement, checked, resultLimit⟩ := WP.spec_imp_exists
        (code.require_single_result.spec (alloc.vec.Vec.deref ft.results))
      cases requirement with
      | Err error => simp [code.read_call, read, lift, Nat.not_le_of_gt bound, indexed, checked,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
      | Ok unit =>
        obtain ⟨⟨reply, next⟩, popped, _, _, rest, nextValues, shrink, transfer⟩ := WP.spec_imp_exists
          (code.pop_types.realizes state outer segment (alloc.vec.Vec.deref ft.params)
            (by simpa [sameValues] using values) (by simpa [Control.base, controls] using base))
        dsimp only at nextValues shrink transfer
        cases reply with
        | Err error => simp [code.read_call, read, lift, Nat.not_le_of_gt bound, indexed, checked, popped,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
        | Ok unit =>
          have resultLength : ft.results.val.length ≤ 1 := by simpa [alloc.vec.Vec.deref] using resultLimit
          have fits : next.vals.val.length + (alloc.vec.Vec.deref ft.results).val.length ≤ Usize.max := by
            simp only [nextValues, values, List.length_append, alloc.vec.Vec.deref] at *
            omega
          obtain ⟨finalState, pushed, finalValues, _, _⟩ := WP.spec_imp_exists
            (code.push_types.spec next (alloc.vec.Vec.deref ft.results) fits)
          simp [code.read_call, read, lift, Nat.not_le_of_gt bound, indexed, checked, popped, pushed,
            core.result.Result.Insts.CoreOpsTry.branch] at accepted
          obtain ⟨rfl, rfl⟩ := accepted
          refine ⟨ft, rest, ?_, ?_, ?_⟩
          · simpa [List.getElem?_eq_getElem bound] using congrArg some lookup.symm
          · simpa [nextValues, List.append_assoc, alloc.vec.Vec.deref] using finalValues
          · simpa [Control.polymorphic, controls, alloc.vec.Vec.deref] using transfer
    · simp [code.read_call, read, lift, Nat.le_of_not_gt bound,
        core.result.Result.Insts.CoreOpsTry.branch] at accepted

end Exec.Code
