import Exec.Code.Local.Capacity.ReaderAcceptance
import Itasca.Wasm2.Trace.ControlRefinement

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2.Visitor
set_option maxRecDepth 4096

/-- Successful table iterations either continue or finish with acceptance. -/
def TableFlowAccepted {V : Type} :
    ControlFlow (code.OpIterState × V × Option Usize × signature.ResultType × U32)
      (core.result.Result Unit error.OpError × code.BodyState × V) → Prop
  | .cont _ => True
  | .done (reply,_,_) => reply = .Ok ()

/-- Table iteration correspondence retains the exact reader state and cursor,
with separate relations at continuation and final callback boundaries. -/
def TableFlowRelated {V W : Type}
    (related : Nat → code.OpIterState → V → W → Prop) (post : code.BodyState → V → W → Prop)
    (source : ControlFlow (code.OpIterState × V × Option Usize × signature.ResultType × U32)
      (core.result.Result Unit error.OpError × code.BodyState × V))
    (target : ControlFlow (code.OpIterState × W × Option Usize × signature.ResultType × U32)
      (core.result.Result Unit error.OpError × code.BodyState × W)) : Prop :=
  tableObserve target = tableObserve source ∧
    match source with
    | .cont (st,before,_,_,index) => related index.val st before (tableVisitor target)
    | .done (_,st,before) => post st before (tableVisitor target)

/-- Replays only the final hook actually reached by an independently accepted
suffix check. Unrelated or rejected target callbacks are not assumptions. -/
theorem table_rest_accepted_replay {V W : Type}
    (source : code.OpVisitor V) (target : code.OpVisitor W)
    (related : Nat → code.OpIterState → V → W → Prop)
    (readRelated : Nat → code.OpIterState → U32 → signature.ResultType → V → W → Prop)
    (post : code.BodyState → V → W → Prop)
    (count : U32)
    (finish : ∀ (st : code.BodyState) before compiler marked depth ts after,
      readRelated count.val st.core depth ts before compiler → code.mark_unreachable st.core = .ok marked →
      source.on_br_table before marked depth ts = .ok (.Ok (),after) →
      target.on_br_table compiler marked depth ts ⦃ result => result.1 = .Ok () ∧
        post {st with core := marked} after result.2 ⦄)
    (st : code.BodyState) (env : module.Env) (index depth : U32) (ts : signature.ResultType)
    (bounded : index.val ≤ count.val)
    (arity : Option Usize) (first : signature.ResultType) (before : V) (compiler : W)
    (held : if index = count then readRelated index.val st.core depth ts before compiler
      else related (index.val+1) st.core before compiler)
    (flow) (accepted : TableFlowAccepted flow)
    (reference : tableRest source st env count index depth ts arity first before = .ok flow) :
    ∃ out, tableRest target st env count index depth ts arity first compiler = .ok out ∧
      TableFlowRelated related post flow out := by
  unfold tableRest at reference ⊢
  obtain ⟨check,checked,reference⟩ := ResultFacts.bind_ok_inv _ _ _ reference
  rw [checked]
  cases check with
  | Err error =>
    simp only [Result.ok.injEq] at reference
    subst flow
    simp [TableFlowAccepted] at accepted
  | Ok nextArity =>
    simp only [bind_ok] at reference ⊢
    by_cases last : index = count
    · simp only [last,↓reduceIte] at reference ⊢
      obtain ⟨marked,mark,reference⟩ := ResultFacts.bind_ok_inv _ _ _ reference
      rw [mark]
      simp only [bind_ok]
      obtain ⟨⟨reply,after⟩,called,reference⟩ := ResultFacts.bind_ok_inv _ _ _ reference
      cases reply with
      | Err error =>
        simp [code.visit,Std.uncurry] at reference
        subst flow
        simp [TableFlowAccepted] at accepted
      | Ok unit =>
        cases unit
        simp [code.visit,Std.uncurry] at reference
        subst flow
        obtain ⟨⟨reply,targetAfter⟩,targetCalled,ok,retained⟩ := WP.spec_imp_exists
          (finish st before compiler marked depth ts after (by simpa only [last,↓reduceIte] using held) mark called)
        dsimp only at ok retained
        subst reply
        refine ⟨.done (.Ok (),{st with core := marked},targetAfter),?_,?_⟩
        · simp [targetCalled,code.visit,Std.uncurry]
        · exact ⟨rfl,retained⟩
    · simp only [last,↓reduceIte] at reference ⊢
      obtain ⟨next,increment,reference⟩ := ResultFacts.bind_ok_inv _ _ _ reference
      simp only [Result.ok.injEq] at reference
      subst flow
      have nextEq : next.val = index.val+1 := by
        have addition := UScalar.add_spec (x := index) (y := 1#u32)
        have max := index.hmax
        have different : index.val ≠ count.val := fun same => last (UScalar.eq_of_val_eq same)
        have countMax := count.hmax
        have checked := addition (by scalar_tac)
        rw [increment,WP.spec_ok] at checked
        simpa using checked
      exact ⟨.cont (st.core,compiler,nextArity,first,next),by simp [increment],rfl,
        by simpa only [nextEq,last,↓reduceIte,tableVisitor] using held⟩

/-- Replays the actual label read and optional label hook of one accepted
Wasm 2 table iteration, retaining source state at each callback boundary. -/
theorem table_body_accepted_replay {V W : Type}
    (source : code.OpVisitor V) (target : code.OpVisitor W)
    (related : Nat → code.OpIterState → V → W → Prop)
    (readRelated : Nat → code.OpIterState → U32 → signature.ResultType → V → W → Prop)
    (post : code.BodyState → V → W → Prop)
    (data : Slice U8) (env : module.Env) (profile : ValidationProfile) (count : U32)
    (readMoves : ∀ (index : U32) (st : code.BodyState) before compiler depth ts out,
      index.val ≤ count.val → related index.val st.core before compiler → code.read_label_info st data = .ok (.Ok (depth,ts),out) →
      readRelated index.val out.core depth ts before compiler)
    (label : ∀ (index : U32) st before compiler depth ts after,
      index.val < count.val → readRelated index.val st depth ts before compiler → source.on_br_table_label before st depth = .ok (.Ok (),after) →
      target.on_br_table_label compiler st depth ⦃ result => result.1 = .Ok () ∧ related (index.val+1) st after result.2 ⦄)
    (finish : ∀ (st : code.BodyState) before compiler marked depth ts after,
      readRelated count.val st.core depth ts before compiler → code.mark_unreachable st.core = .ok marked →
      source.on_br_table before marked depth ts = .ok (.Ok (),after) →
      target.on_br_table compiler marked depth ts ⦃ result => result.1 = .Ok () ∧
        post {st with core := marked} after result.2 ⦄)
    (st : code.BodyState) (before : V) (compiler : W)
    (arity : Option Usize) (first : signature.ResultType) (index : U32)
    (bounded : index.val ≤ count.val)
    (held : related index.val st.core before compiler)
    (flow) (accepted : TableFlowAccepted flow)
    (reference : tableBody source data env profile count st before arity first index = .ok flow) :
    ∃ out, tableBody target data env profile count st compiler arity first index = .ok out ∧
      TableFlowRelated related post flow out := by
  unfold tableBody at reference ⊢
  obtain ⟨⟨read,out⟩,readCalled,reference⟩ := ResultFacts.bind_ok_inv _ _ _ reference
  rw [readCalled]
  cases read with
  | Err error =>
    simp at reference
    subst flow
    simp [TableFlowAccepted] at accepted
  | Ok pair =>
    obtain ⟨depth,ts⟩ := pair
    have readHeld := readMoves index st before compiler depth ts out bounded held readCalled
    simp only [bind_ok,Std.uncurry] at reference ⊢
    obtain ⟨check,checked,reference⟩ := ResultFacts.bind_ok_inv _ _ _ reference
    rw [checked]
    cases check with
    | Err error =>
      simp at reference
      subst flow
      simp [TableFlowAccepted] at accepted
    | Ok _ =>
    simp only [bind_ok] at reference ⊢
    by_cases last : index = count
    · simp only [last,bne_self_eq_false,Bool.false_eq_true,if_false] at reference ⊢
      exact table_rest_accepted_replay source target related readRelated post count finish out env count depth ts (by omega) arity _
        before compiler (by simpa [last] using readHeld) flow accepted reference
    · simp only [bne_iff_ne,if_pos last] at reference ⊢
      obtain ⟨⟨reply,after⟩,called,reference⟩ := ResultFacts.bind_ok_inv _ _ _ reference
      cases reply with
      | Err error =>
        simp [code.visit,Std.uncurry] at reference
        subst flow
        simp [TableFlowAccepted] at accepted
      | Ok unit =>
        cases unit
        simp only [code.visit,bind_ok,Std.uncurry] at reference
        obtain ⟨⟨reply,targetAfter⟩,targetCalled,ok,retained⟩ := WP.spec_imp_exists
          (label index out.core before compiler depth ts after
            (by have different : index.val ≠ count.val := fun same => last (UScalar.eq_of_val_eq same); omega)
            readHeld called)
        dsimp only at ok retained
        subst reply
        rw [targetCalled]
        simp only [code.visit,bind_ok,Std.uncurry]
        exact table_rest_accepted_replay source target related readRelated post count finish out env index depth ts bounded arity _
          after targetAfter (by simpa only [last,↓reduceIte] using retained) flow accepted reference

/-- Replay the entire Wasm 2 label loop from an independently accepted run.
Only reached successful label and final callbacks need available target
implementations. It does not require universal compiler visitor acceptance. -/
theorem table_loop_reader_accepted_replay {V W : Type}
    (source : code.OpVisitor V) (target : code.OpVisitor W)
    (related : Nat → code.OpIterState → V → W → Prop)
    (readRelated : Nat → code.OpIterState → U32 → signature.ResultType → V → W → Prop)
    (post : code.BodyState → V → W → Prop)
    (data : Slice U8) (env : module.Env) (profile : ValidationProfile) (count : U32)
    (readMoves : ∀ (index : U32) (st : code.BodyState) before compiler depth ts out,
      index.val ≤ count.val → related index.val st.core before compiler → code.read_label_info st data = .ok (.Ok (depth,ts),out) →
      readRelated index.val out.core depth ts before compiler)
    (label : ∀ (index : U32) st before compiler depth ts after,
      index.val < count.val → readRelated index.val st depth ts before compiler → source.on_br_table_label before st depth = .ok (.Ok (),after) →
      target.on_br_table_label compiler st depth ⦃ result => result.1 = .Ok () ∧ related (index.val+1) st after result.2 ⦄)
    (finish : ∀ (st : code.BodyState) before compiler marked depth ts after,
      readRelated count.val st.core depth ts before compiler → code.mark_unreachable st.core = .ok marked →
      source.on_br_table before marked depth ts = .ok (.Ok (),after) →
      target.on_br_table compiler marked depth ts ⦃ result => result.1 = .Ok () ∧
        post {st with core := marked} after result.2 ⦄)
    (index : U32) (bounded : index.val ≤ count.val) (arity : Option Usize)
    (first : signature.ResultType) (st : code.OpIterState) (out : code.BodyState) (before after : V) (compiler : W)
    (held : related index.val st before compiler)
    (reference : code.branch_table_with_loop source st data env profile before count arity first
      index = .ok (.Ok (),out,after)) :
    ∃ targetAfter, code.branch_table_with_loop target st data env profile compiler count arity first
      index =
      .ok (.Ok (),out,targetAfter) ∧ post out after targetAfter := by
  generalize measure : count.val-index.val = remaining
  induction remaining using Nat.strong_induction_on generalizing st before compiler index arity first with
  | h remaining ih =>
    unfold code.branch_table_with_loop at reference ⊢
    rw [loop] at reference ⊢
    simp only [tableBody_eq source data env profile count ⟨st⟩ before arity first index] at reference
    simp only [tableBody_eq target data env profile count ⟨st⟩ compiler arity first index]
    obtain ⟨flow,called,tail⟩ := ResultFacts.bind_ok_inv _ _ _ reference
    have accepted : TableFlowAccepted flow := by
      cases flow with
      | cont next => trivial
      | done result =>
        obtain ⟨reply,final,last⟩ := result
        simp only [Result.ok.injEq,Prod.mk.injEq] at tail
        exact tail.1
    obtain ⟨targetFlow,targetCalled,agreement,retained⟩ := table_body_accepted_replay source target
      related readRelated post data env profile count readMoves label finish ⟨st⟩ before compiler arity first index
      bounded held flow accepted called
    rw [targetCalled]
    cases flow with
    | done result =>
      obtain ⟨reply,final,last⟩ := result
      simp only [Result.ok.injEq,Prod.mk.injEq] at tail
      obtain ⟨rfl,rfl,rfl⟩ := tail
      cases targetFlow with
      | cont next => simp [tableObserve] at agreement
      | done result =>
        obtain ⟨reply,final,targetAfter⟩ := result
        simp only [tableObserve,ControlFlow.done.injEq,Prod.mk.injEq] at agreement
        obtain ⟨rfl,rfl⟩ := agreement
        exact ⟨targetAfter,by simp,retained⟩
    | cont following =>
      obtain ⟨next,before',arity',first',index'⟩ := following
      have progress := tableBody.cont_progress source data env profile count ⟨st⟩ before arity first
        index next before' arity' first' index' bounded called
      cases targetFlow with
      | done result => simp [tableObserve] at agreement
      | cont following =>
        obtain ⟨next',compiler',arity'',first'',index''⟩ := following
        simp only [tableObserve,ControlFlow.cont.injEq,Prod.mk.injEq] at agreement
        obtain ⟨rfl,rfl,rfl,rfl⟩ := agreement
        obtain ⟨targetAfter,targetTail,retained'⟩ := ih (count.val-index''.val) (by omega)
          index'' progress.2 arity'' first'' next' before' compiler' retained tail rfl
        exact ⟨targetAfter,by simpa only [bind_ok,code.branch_table_with_loop] using targetTail,retained'⟩

end Itasca.Runtime.Code
