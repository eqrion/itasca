import Itasca.Body.End
import Itasca.Body.StackSemantics

open Aeneas Aeneas.Std

namespace Itasca

def EndResult (st : code.OpIterState) (cs : List code.Ctrl) (c : code.Ctrl)
    (outer segment : List code.StackType)
    (r : core.result.Result (code.LabelKind × code.BlockType) error.OpError × code.OpIterState) : Prop :=
  r.2.pos = st.pos ∧
    match r.1 with
    | .Err _ => True
    | .Ok (kind, bt) => kind = c.kind ∧ bt = c.block_type ∧
        r.2.ctrls.val = cs ∧
        r.2.vals.val = outer ++ (Control.results c.block_type).map code.StackType.Val ∧
        Sequence.Realizes c.polymorphic_base segment (Control.resultTypes c.block_type) ∧
        (c.kind = .Then → c.block_type = .Empty)

private theorem read_end_not_then (st : code.OpIterState) (cs : List code.Ctrl)
    (c : code.Ctrl) (outer segment : List code.StackType)
    (hctrls : st.ctrls.val = cs ++ [c]) (hvals : st.vals.val = outer ++ segment)
    (hbase : c.value_stack_base.val = outer.length) (hkind : c.kind ≠ .Then)
    (hsize : st.vals.val.length + 1 ≤ Usize.max) :
    code.read_end st ⦃ EndResult st cs c outer segment ⦄ := by
  obtain ⟨rs, hrs, hrsv⟩ := WP.spec_imp_exists (code.block_results.spec c.block_type)
  obtain ⟨⟨res, popped⟩, hpop, hpc, hpp, rest, hpv, hrest, hsem⟩ := WP.spec_imp_exists
    (code.pop_types.realizes st outer segment (alloc.vec.Vec.deref rs) hvals
      (by simp [Control.base, hctrls, hbase]))
  dsimp only at hpc hpp hpv hrest hsem
  have ht : code.is_then c.kind = .ok false := by
    cases hk : c.kind <;> simp_all [code.is_then]
  have hn : alloc.vec.Vec.len st.ctrls ≠ 0#usize := by scalar_tac
  unfold code.read_end
  simp only [hn, ↓reduceIte]
  step
  step
  have heq : frame = c := by simp_all
  rw [heq, hrs]
  simp only [bind_ok, ht, Bool.false_eq_true, ↓reduceIte]
  cases res with
  | Err e =>
    simp [hpop, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, EndResult, hpp]
  | Ok u =>
    cases u
    by_cases hlen : popped.vals.val.length = c.value_stack_base.val
    · have hnil : rest = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp only [hpv, List.length_append, hbase] at hlen
        omega
      have hreal : Sequence.Realizes c.polymorphic_base segment (Control.resultTypes c.block_type) := by
        have hp := hsem [] (by simpa [hnil, Sequence.stackTypes] using Sequence.realizes_default (Control.polymorphic st) [])
        simpa [Control.polymorphic, hctrls, alloc.vec.Vec.deref, hrsv, Control.resultTypes] using hp
      have hcap : popped.vals.val.length + rs.val.length ≤ Usize.max := by
        have hrslen : rs.val.length ≤ 1 := by rw [hrsv]; cases c.block_type <;> simp [Control.results]
        simp only [hvals, List.length_append] at hsize
        simp only [hpv, List.length_append]
        omega
      simp [hpop, core.result.Result.Insts.CoreOpsTry.branch, hlen]
      step*
      all_goals simp_all [EndResult, alloc.vec.Vec.deref]
    · simp [hpop, core.result.Result.Insts.CoreOpsTry.branch, hlen, EndResult, hpp]

/-- Totality and successful-exit typing for every operand shape, including mixed Bot values. -/
@[step]
theorem code.read_end.realizes (st : code.OpIterState) (cs : List code.Ctrl)
    (c : code.Ctrl) (outer segment : List code.StackType)
    (hctrls : st.ctrls.val = cs ++ [c]) (hvals : st.vals.val = outer ++ segment)
    (hbase : c.value_stack_base.val = outer.length)
    (hsize : st.vals.val.length + 1 ≤ Usize.max) :
    code.read_end st ⦃ EndResult st cs c outer segment ⦄ := by
  by_cases hk : c.kind = .Then
  · cases hbt : c.block_type with
    | Empty =>
      by_cases hlen : st.vals.val.length = c.value_stack_base.val
      · obtain ⟨⟨res, st'⟩, hr, hok, hc, hv, hp⟩ := WP.spec_imp_exists
          (code.read_end.empty st cs c hctrls hbt hlen)
        dsimp only at hok hc hv hp
        have hnil : segment = [] := by
          apply List.eq_nil_of_length_eq_zero
          simp only [hvals, List.length_append, hbase] at hlen
          omega
        rw [hr, WP.spec_ok]
        simp [EndResult, hok, hc, hv, hp, hbt, hvals, hnil,
          Control.results, Control.resultTypes, Sequence.Realizes]
      · obtain ⟨_, hr, rfl⟩ := WP.spec_imp_exists
          (code.read_end.empty_mismatch st cs c hctrls hbt hlen)
        simp [hr, EndResult]
    | Value t =>
      obtain ⟨_, hr, rfl⟩ := WP.spec_imp_exists
        (code.read_end.then_result st cs c t hctrls hk hbt)
      simp [hr, EndResult]
  · exact read_end_not_then st cs c outer segment hctrls hvals hbase hk hsize

def ElseResult (st : code.OpIterState) (cs : List code.Ctrl) (c : code.Ctrl)
    (outer segment : List code.StackType)
    (r : core.result.Result code.BlockType error.OpError × code.OpIterState) : Prop :=
  r.2.pos = st.pos ∧
    match r.1 with
    | .Err _ => True
    | .Ok bt => c.kind = .Then ∧ bt = c.block_type ∧
        r.2.ctrls.val = cs ++ [{ c with kind := .Else, polymorphic_base := false }] ∧
        r.2.vals.val = outer ∧
        Sequence.Realizes c.polymorphic_base segment (Control.resultTypes c.block_type)

/-- Every successful else delimiter closes the then arm and resets the frame for its else arm. -/
@[step]
theorem code.read_else.realizes (st : code.OpIterState) (cs : List code.Ctrl)
    (c : code.Ctrl) (outer segment : List code.StackType)
    (hctrls : st.ctrls.val = cs ++ [c]) (hvals : st.vals.val = outer ++ segment)
    (hbase : c.value_stack_base.val = outer.length) :
    code.read_else st ⦃ ElseResult st cs c outer segment ⦄ := by
  obtain ⟨rs, hrs, hrsv⟩ := WP.spec_imp_exists (code.block_results.spec c.block_type)
  obtain ⟨⟨res, popped⟩, hpop, hpc, hpp, rest, hpv, hrest, hsem⟩ := WP.spec_imp_exists
    (code.pop_types.realizes st outer segment (alloc.vec.Vec.deref rs) hvals
      (by simp [Control.base, hctrls, hbase]))
  dsimp only at hpc hpp hpv hrest hsem
  have hn : alloc.vec.Vec.len st.ctrls ≠ 0#usize := by scalar_tac
  unfold code.read_else
  simp only [hn, ↓reduceIte]
  step
  step
  have heq : frame = c := by simp_all
  rw [heq]
  by_cases hk : c.kind = .Then
  · simp only [code.is_then, hk, bind_ok, ↓reduceIte, hrs]
    cases res with
    | Err e =>
      simp [hpop, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ElseResult, hpp]
    | Ok u =>
      cases u
      by_cases hlen : popped.vals.val.length = c.value_stack_base.val
      · have hnil : rest = [] := by
          apply List.eq_nil_of_length_eq_zero
          simp only [hpv, List.length_append, hbase] at hlen
          omega
        have hreal : Sequence.Realizes c.polymorphic_base segment (Control.resultTypes c.block_type) := by
          have hp := hsem [] (by simpa [hnil, Sequence.stackTypes] using
            Sequence.realizes_default (Control.polymorphic st) [])
          simpa [Control.polymorphic, hctrls, alloc.vec.Vec.deref, hrsv, Control.resultTypes] using hp
        simp [hpop, core.result.Result.Insts.CoreOpsTry.branch, hlen]
        have hi : i.val = cs.length := by simpa [hctrls] using i_post
        step*
        all_goals simp_all [ElseResult, alloc.vec.Vec.set]
      · simp [hpop, core.result.Result.Insts.CoreOpsTry.branch, hlen, ElseResult, hpp]
  · have ht : code.is_then c.kind = .ok false := by
      cases hk' : c.kind <;> simp_all [code.is_then]
    simp [ht, ElseResult]

/-- The if reader may reject an operand, but a successful pop retains the consumed i32
in the backwards typing relation used to suspend its parent frame. -/
@[step]
theorem code.read_if.from_block_type (st : code.OpIterState) (data : Slice U8)
    (bt : code.BlockType) (next : Usize) (outer segment : List code.StackType)
    (hread : code.read_block_type data st.pos = .ok (.Ok (bt, next)))
    (hvals : st.vals.val = outer ++ segment) (hbase : (Control.base st).val = outer.length)
    (hsize : st.ctrls.val.length < Usize.max) :
    code.read_if st data ⦃ r => r.2.pos = next ∧
      match r.1 with
      | .Err _ => True
      | .Ok result => result = bt ∧ ∃ rest,
          r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length ∧
          r.2.ctrls.val = st.ctrls.val ++ [Control.frame r.2 .Then bt] ∧
          ∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
            Sequence.Realizes (Control.polymorphic st) segment (ts ++ [.I32]) ⦄ := by
  obtain ⟨⟨res, popped⟩, hpop, hc, hp, rest, hv, hlen, hsem⟩ := WP.spec_imp_exists
    (code.pop_with_type.realizes { st with pos := next } outer segment .I32 hvals hbase)
  dsimp only at hc hp hv hlen hsem
  cases res with
  | Err e =>
    simp [code.read_if, hread, hpop, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hp]
  | Ok t =>
    obtain ⟨st', hpush, hcs, hvs, hps⟩ := WP.spec_imp_exists
      (code.push_ctrl.spec popped .Then bt (by simpa [hc] using hsize))
    have hr : code.read_if st data = .ok (.Ok bt, st') := by
      simp [code.read_if, hread, hpop, hpush, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hr, WP.spec_ok]
    refine ⟨hps.trans hp, rfl, rest, ?_, hlen, ?_, ?_⟩
    · simpa [hvs] using hv
    · simpa [hc, Control.frame, hvs] using hcs
    · simpa [Control.polymorphic, Translate.valueType] using hsem.2

end Itasca
