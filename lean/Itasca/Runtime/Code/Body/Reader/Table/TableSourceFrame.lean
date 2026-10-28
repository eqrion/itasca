import Itasca.Runtime.Code.Body.Reader.Table.TableLoopReaderReplay
import Itasca.Runtime.Code.Body.Reader.Table.ReaderTableSafetyWasm2

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Independent source table loops retain operands and controls until their
single final unreachable transformation. This describes the source reader,
without any compiler-success or target callback assumption. -/
theorem source_table_loop_frame {V : Type} (source : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (profile : ValidationProfile) (count index : U32)
    (arity : Option Usize) (first : signature.ResultType)
    (st : code.OpIterState) (out : code.BodyState) (before after : V)
    (bounded : index.val ≤ count.val)
    (reference : code.branch_table_with_loop source st data env profile before count arity first index =
      .ok (.Ok (),out,after)) :
    ∃ last, last.vals = st.vals ∧ last.ctrls = st.ctrls ∧ code.mark_unreachable last = .ok out.core := by
  let related := fun (_ : Nat) (state : code.OpIterState) (left right : V) =>
    state.vals = st.vals ∧ state.ctrls = st.ctrls ∧ left = right
  let readRelated := fun (_ : Nat) (state : code.OpIterState) (_ : U32) (_ : signature.ResultType) (left right : V) =>
    state.vals = st.vals ∧ state.ctrls = st.ctrls ∧ left = right
  let post := fun (final : code.BodyState) (_ _ : V) =>
    ∃ last, last.vals = st.vals ∧ last.ctrls = st.ctrls ∧ code.mark_unreachable last = .ok final.core
  have readMoves : ∀ (i : U32) (state : code.BodyState) left right depth ts next,
      i.val ≤ count.val → related i.val state.core left right →
      code.read_label_info state data = .ok (.Ok (depth,ts),next) →
      readRelated i.val next.core depth ts left right := by
    intro i state left right depth ts next _ held read
    have actual := reader_table_label_wasm2 state data (by simp)
    rw [read,WP.spec_ok] at actual
    obtain ⟨values,controls,_,_⟩ := actual depth ts rfl
    exact ⟨values.trans held.1,controls.trans held.2.1,held.2.2⟩
  obtain ⟨targetAfter,_,retained⟩ := table_loop_reader_accepted_replay source source related readRelated post
    data env profile count readMoves
    (by
      intro i state left right depth ts next _ held called
      obtain ⟨values,controls,rfl⟩ := held
      rw [called,WP.spec_ok]
      exact ⟨rfl,values,controls,rfl⟩)
    (by
      intro state left right marked depth ts next held mark called
      obtain ⟨values,controls,rfl⟩ := held
      rw [called,WP.spec_ok]
      exact ⟨rfl,state.core,values,controls,mark⟩)
    index bounded arity first st out before after before ⟨rfl,rfl,rfl⟩ reference
  exact retained

/-- Source frame preservation and the independently decoded final cursor fix
the final marked state uniquely, including unreachable operand truncation. -/
theorem source_table_loop_marked {V : Type} (source : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (profile : ValidationProfile) (count index : U32)
    (arity : Option Usize) (first : signature.ResultType)
    (st : code.OpIterState) (out : code.BodyState) (before after : V)
    (bounded : index.val ≤ count.val) (shape : Control.Shape st)
    (reference : code.branch_table_with_loop source st data env profile before count arity first index =
      .ok (.Ok (),out,after))
    (state marked : code.OpIterState) (values : state.vals = st.vals) (controls : state.ctrls = st.ctrls)
    (position : state.pos = out.core.pos) (mark : code.mark_unreachable state = .ok marked) :
    marked = out.core := by
  obtain ⟨last,lastValues,lastControls,lastMark⟩ := source_table_loop_frame source data env profile count index arity first
    st out before after bounded reference
  have lastShape : Control.Shape last :=
    ⟨by simpa only [lastControls] using shape.ordered,
      by simpa only [lastControls,lastValues] using shape.bounded⟩
  have lastSpec := code.mark_unreachable_total last lastShape
  rw [lastMark,WP.spec_ok] at lastSpec
  have sameValues := values.trans lastValues.symm
  have sameControls := controls.trans lastControls.symm
  have samePosition := position.trans lastSpec.2.2.1
  have same : state = last := by
    cases state
    cases last
    simp_all only [code.OpIterState.mk.injEq]
  rw [same,lastMark] at mark
  simpa only [Result.ok.injEq] using mark.symm

end Itasca.Runtime.Code
