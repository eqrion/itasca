import Exec.Code.Body.Reader.Table.TableLoopReaderReplay

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Leaf obligations for replay of one decoded branch table. Label capacity is
required only below the decoded count; the final callback sees the full count. -/
structure TableReaderReplay {V W : Type}
    (source : code.OpVisitor V) (target : code.OpVisitor W)
    (related : Nat → code.OpIterState → V → W → Prop)
    (readRelated : Nat → code.OpIterState → U32 → signature.ResultType → V → W → Prop)
    (post : code.BodyState → V → W → Prop)
    (data : Slice U8) (env : module.Env) (count : U32) : Prop where
  readMoves : ∀ (index : U32) (st : code.BodyState) before compiler depth ts out,
    index.val ≤ count.val → related index.val st.core before compiler → code.read_label_info st data = .ok (.Ok (depth,ts),out) →
    readRelated index.val out.core depth ts before compiler
  label : ∀ (index : U32) st before compiler depth ts after,
    index.val < count.val → readRelated index.val st depth ts before compiler →
    source.on_br_table_label before st depth = .ok (.Ok (),after) →
    target.on_br_table_label compiler st depth ⦃ result => result.1 = .Ok () ∧ related (index.val+1) st after result.2 ⦄
  finish : ∀ (st : code.BodyState) before compiler marked depth ts after,
    readRelated count.val st.core depth ts before compiler → code.mark_unreachable st.core = .ok marked →
    source.on_br_table before marked depth ts = .ok (.Ok (),after) →
    target.on_br_table compiler marked depth ts ⦃ result => result.1 = .Ok () ∧
      post {st with core := marked} after result.2 ⦄

/-- Replays the actual complete Wasm 2 branch-table reader, including count
and selector decoding. Preparation is needed only for the count and state
actually decoded by the independently accepted reference. -/
theorem table_reader_accepted_replay {V W : Type}
    (source : code.OpVisitor V) (target : code.OpVisitor W)
    (related : Nat → code.OpIterState → V → W → Prop)
    (readRelated : Nat → code.OpIterState → U32 → signature.ResultType → V → W → Prop)
    (post : code.BodyState → V → W → Prop)
    (data : Slice U8) (env : module.Env) (st out : code.BodyState)
    (before after : V) (compiler : W)
    (prepared : ∀ count first state value,
      reader.read_u32_leb data st.core.pos = .ok (.Ok (count,first)) →
      code.pop_with_type {st.core with pos := first} .I32 = .ok (.Ok value,state) →
      related 0 state before compiler ∧ TableReaderReplay source target related readRelated post data env count)
    (reference : code.branch_table_with source st data env before = .ok (.Ok (),out,after)) :
    code.branch_table_with target st data env compiler ⦃ result => result.1 = .Ok () ∧
      result.2.1 = out ∧ post out after result.2.2 ⦄ := by
  unfold code.branch_table_with at reference ⊢
  obtain ⟨read,readCalled,reference⟩ := ResultFacts.bind_ok_inv _ _ _ reference
  rw [readCalled]
  cases read with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at reference
  | Ok pair =>
    obtain ⟨count,first⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at reference ⊢
    obtain ⟨⟨reply,state⟩,popCalled,reference⟩ := ResultFacts.bind_ok_inv _ _ _ reference
    rw [popCalled]
    cases reply with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at reference
    | Ok value =>
      simp only [bind_ok,Std.uncurry] at reference ⊢
      obtain ⟨held,callbacks⟩ := prepared count first state value readCalled popCalled
      obtain ⟨targetAfter,targetCalled,retained⟩ := table_loop_reader_accepted_replay source target related readRelated post
        data env count callbacks.readMoves callbacks.label callbacks.finish 0#u32 (by simp) none state out
        before after compiler held reference
      apply WP.exists_imp_spec
      exact ⟨(.Ok (),out,targetAfter),targetCalled,rfl,rfl,retained⟩

end Exec.Code
