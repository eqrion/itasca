import Itasca.Support.Result
import Itasca.Visitor.VisitorEvents
import Itasca.Binary.WasmBinaryComplete
import Itasca.Visitor.VisitorErasure
import Itasca.Visitor.VisitorTraceBytes
import Itasca.Visitor.VisitorRecording

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

/-- A bounded label's independent bytes and the unchanged stacks visible to
its callback. The callback observes the cursor after the complete label. -/
structure LabelRead (data : Slice U8) (st : code.OpIterState) (depth : U32)
    (target : code.Ctrl) (next : code.OpIterState) : Prop where
  vals : next.vals = st.vals
  ctrls : next.ctrls = st.ctrls
  decoded : Leb128.Decoded data st.pos depth next.pos
  bound : depth.val < st.ctrls.val.length
  target_eq : target = st.ctrls.val[st.ctrls.val.length - 1 - depth.val]'(by have := bound; omega)

/-- A failed label lookup makes no callback. Unknown labels consume their
complete immediate; malformed LEBs leave the public state cursor unchanged. -/
def LabelFailure (data : Slice U8) (st : code.OpIterState) (error : error.OpError)
    (next : code.OpIterState) : Prop :=
  next.vals = st.vals ∧ next.ctrls = st.ctrls ∧
    ((Leb128.Rejected data st.pos error ∧ next.pos = st.pos) ∨
      (error = .UnknownLabel ∧ ∃ depth, Leb128.Decoded data st.pos depth next.pos ∧
        st.ctrls.val.length ≤ depth.val))

/-- Declarative label-vector protocol. The observations include the final
rejected hook, and include an accepted hook before a target merge fails.
No constructor mentions an implementation reader or dispatcher. -/
inductive LabelRun (data : Slice U8) (count : Nat) :
    code.OpIterState → Nat → Option code.BlockType → List Observation →
      core.result.Result (Option code.BlockType) error.OpError → code.OpIterState → Prop where
  | done (st : code.OpIterState) (expect : Option code.BlockType) :
      LabelRun data count st count expect [] (.Ok expect) st
  | label_error {st i expect e next} : i < count → LabelFailure data st e next →
      LabelRun data count st i expect [] (.Err e) next
  | visitor_error {st i expect depth target next} (e : error.VisitError) : i < count →
      LabelRead data st depth target next →
      LabelRun data count st i expect [⟨.op next (.br_table_label depth), .Err e⟩] (.Err (.Visitor e)) next
  | target_error {st i expect depth target next} : i < count →
      LabelRead data st depth target next →
      expect ≠ none → expect ≠ some (Control.targetBlockType target) →
      LabelRun data count st i expect [⟨.op next (.br_table_label depth), .Ok ()⟩] (.Err .TypeMismatch) next
  | next {st i expect depth target next observations result final} : i < count →
      LabelRead data st depth target next →
      (expect = none ∨ expect = some (Control.targetBlockType target)) →
      LabelRun data count next (i + 1) (some (Control.targetBlockType target)) observations result final →
      LabelRun data count st i expect (⟨.op next (.br_table_label depth), .Ok ()⟩ :: observations) result final

/-- Byte provenance of precisely the observed labels, with one state snapshot
per callback. The last observation may reject, or precede a failing merge. -/
inductive LabelPrefix (data : Slice U8) : code.OpIterState →
    List Observation → List U32 → code.OpIterState → Prop where
  | nil (st : code.OpIterState) : LabelPrefix data st [] [] st
  | cons {st depth target next observations depths final} (outcome : VisitResult) :
      LabelRead data st depth target next → LabelPrefix data next observations depths final →
      LabelPrefix data st (⟨.op next (.br_table_label depth), outcome⟩ :: observations) (depth :: depths) final

theorem LabelPrefix.length {data st observations depths final}
    (h : LabelPrefix data st observations depths final) : observations.length = depths.length := by
  induction h <;> simp_all

theorem LabelPrefix.stacks {data st observations depths final}
    (h : LabelPrefix data st observations depths final) : final.vals = st.vals ∧ final.ctrls = st.ctrls := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ hread _ ih => exact ⟨ih.1.trans hread.vals, ih.2.trans hread.ctrls⟩

theorem LabelPrefix.decoded {data st observations depths final}
    (h : LabelPrefix data st observations depths final) : BrTable.LabelsDecoded data st.pos depths final.pos := by
  induction h with
  | nil => exact .nil
  | cons _ hread _ ih =>
      exact (BrTable.LabelsDecoded.snoc .nil hread.decoded).append ih

theorem LabelPrefix.labelsAt {data st observations depths final}
    (h : LabelPrefix data st observations depths final) :
    LabelsAt data st.pos observations depths final.pos := by
  induction h with
  | nil => exact .nil _
  | cons outcome hread _ ih => exact .cons hread.decoded ih

/-- Every observed label is in range, including the one immediately before
an accepted callback's target-type mismatch. -/
theorem LabelPrefix.bounded {data st observations depths final}
    (h : LabelPrefix data st observations depths final) :
    ∀ depth ∈ depths, depth.val < st.ctrls.val.length := by
  induction h with
  | nil => simp
  | cons _ hread _ ih =>
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hread.bound
      · simpa [hread.ctrls] using ih d hd

/-- The event list is always a decoded, bounded vector prefix. A later bad
label may move the final cursor without adding an observation. -/
theorem LabelRun.prefix {data count st i expect observations result final}
    (h : LabelRun data count st i expect observations result final) :
    ∃ depths last, LabelPrefix data st observations depths last ∧
      i + depths.length ≤ count := by
  induction h with
  | done st expect => exact ⟨[], st, .nil st, by simp⟩
  | label_error hi _ => exact ⟨[], _, .nil _, by simpa using Nat.le_of_lt hi⟩
  | visitor_error e hi hr => exact ⟨[_], _, .cons (.Err e) hr (.nil _), by simp; omega⟩
  | target_error hi hr _ _ => exact ⟨[_], _, .cons (.Ok ()) hr (.nil _), by simp; omega⟩
  | next hi hr _ _ ih =>
      obtain ⟨depths, last, hp, hc⟩ := ih
      exact ⟨_ :: depths, last, .cons (.Ok ()) hr hp, by simp only [List.length_cons]; omega⟩

theorem LabelRun.accepted {data count st i expect observations result final}
    (h : LabelRun data count st i expect observations (.Ok result) final) :
    ∃ depths, LabelPrefix data st observations depths final ∧
      i + depths.length = count ∧ ∀ observation ∈ observations, observation.outcome = .Ok () := by
  generalize heq : core.result.Result.Ok result = outcome at h
  induction h with
  | done st expect => exact ⟨[], .nil st, by simp, by simp⟩
  | label_error => cases heq
  | visitor_error => cases heq
  | target_error => cases heq
  | next hi hr _ _ ih =>
      obtain ⟨depths, hp, hc, ho⟩ := ih heq
      exact ⟨_ :: depths, .cons (.Ok ()) hr hp, by simp only [List.length_cons]; omega,
        by simpa using ho⟩

theorem LabelRun.outcomes {data count st i expect observations result final}
    (h : LabelRun data count st i expect observations result final) :
    Outcomes observations (match result with | .Ok _ => .Ok () | .Err e => .Err e) := by
  induction h with
  | done => exact .empty _
  | label_error => exact .empty _
  | visitor_error e _ _ => exact .single _ (.Err e)
  | target_error => exact .of_accepted (by simp [AllAccepted]) _
  | @next st i expect depth target next observations result final _ _ _ _ ih =>
      cases result <;> exact ih.prepend (before := [⟨.op next (.br_table_label depth), .Ok ()⟩])
        (by simp [AllAccepted])

/-- Provenance of an unfinished table's callbacks, beginning after its opcode.
Only observed vector entries appear here; the default label is never a hook. -/
def TablePrefix (data : Slice U8) (st : code.OpIterState)
    (observations : List Observation) : Prop :=
  ∃ count first depths last, Leb128.Decoded data st.pos count first ∧
    LabelPrefix data { st with pos := first } observations depths last ∧
    depths.length ≤ count.val

/-- The complete vector and default immediate associated with an accepted
table handler. The closing callback is emitted separately by the dispatcher. -/
def TableAccepted (data : Slice U8) (st : code.OpIterState)
    (observations : List Observation) (fallback : U32) (final : code.OpIterState) : Prop :=
  ∃ count first depths last, Leb128.Decoded data st.pos count first ∧
    LabelPrefix data { st with pos := first } observations depths last ∧
    depths.length = count.val ∧ Leb128.Decoded data last.pos fallback final.pos ∧
    AllAccepted observations

def TableResult (data : Slice U8) (st : code.OpIterState) (observations : List Observation)
    (result : core.result.Result (U32 × code.BlockType) error.OpError)
    (final : code.OpIterState) : Prop :=
  match result with
  | .Err e => (observations = [] ∨ TablePrefix data st observations) ∧ Outcomes observations (.Err e)
  | .Ok (fallback, _) => TableAccepted data st observations fallback final

end Itasca.VisitorTrace

namespace Itasca.VisitorTrace

private theorem merge_error (expect : Option code.BlockType) (bt : code.BlockType) (e : error.OpError)
    (h : code.merge_target expect bt = .ok (.Err e)) :
    e = .TypeMismatch ∧ expect ≠ none ∧ expect ≠ some bt := by
  cases expect with
  | none => simp [code.merge_target] at h
  | some previous =>
    obtain ⟨equal, he, heq⟩ := WP.spec_imp_exists (code.BlockType.eq_spec bt previous)
    cases equal with
    | false =>
      have hne : bt ≠ previous := by intro h; have := heq.mpr h; cases this
      simp [code.merge_target, he] at h
      exact ⟨h.symm, by simp, by simpa [eq_comm] using hne⟩
    | true => simp [code.merge_target, he] at h

end Itasca.VisitorTrace

namespace Itasca

/-- Every ordinary return of the actual label loop has the independent trace
protocol above. The recording premise covers rejecting hooks as well as
accepting hooks, and no global visitor termination premise is required. -/
theorem code.read_table_labels_loop.trace {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List VisitorTrace.Observation)
    (records : ∀ v s depth reply v', visitor.on_br_table_label v s depth = .ok (reply, v') →
      observe v' = observe v ++ [⟨.op s (.br_table_label depth), reply⟩])
    (st : code.OpIterState) (data : Slice U8) (count i : U32) (v : V)
    (expect : Option code.BlockType) (hi : i.val ≤ count.val)
    (result : core.result.Result (Option code.BlockType) error.OpError)
    (final : code.OpIterState) (v' : V)
    (h : code.read_table_labels_loop visitor st data count v expect i = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      VisitorTrace.LabelRun data count.val st i.val expect observations result final := by
  generalize hn : count.val - i.val = n
  induction n using Nat.strong_induction_on generalizing st i v expect with
  | h n ih =>
    unfold code.read_table_labels_loop at h
    rw [loop] at h
    simp only [code.read_table_labels_loop.body] at h
    by_cases heq : i = count
    · simp [heq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨[], by simp, by simpa [heq] using VisitorTrace.LabelRun.done (data := data) (count := count.val) st expect⟩
    · have hlt : i.val < count.val := by
        have hne : i.val ≠ count.val := fun he => heq (UScalar.eq_of_val_eq he)
        omega
      simp only [heq, ↓reduceIte] at h
      obtain ⟨⟨res, s⟩, hread, hv, hc, hpost⟩ := WP.spec_imp_exists (code.read_label.spec st data)
      dsimp only at hv hc hpost
      rw [hread] at h
      cases res with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨[], by simp, .label_error hlt ⟨hv, hc, hpost⟩⟩
      | Ok pair =>
        obtain ⟨depth, target⟩ := pair
        obtain ⟨hd, hb, ht⟩ := hpost
        have hlabel : VisitorTrace.LabelRead data st depth target s := ⟨hv, hc, hd, hb, ht⟩
        simp [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_assoc] at h
        obtain ⟨⟨reply, w⟩, hhook, htail⟩ := ResultFacts.bind_ok_inv _ _ _ h
        have hrecord := records v s depth reply w hhook
        cases reply with
        | Err e =>
          simp [code.visit,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at htail
          obtain ⟨rfl, rfl, rfl⟩ := htail
          exact ⟨_, hrecord, .visitor_error e hlt hlabel⟩
        | Ok u =>
          cases u
          obtain ⟨bt, hbt, hbtval⟩ := WP.spec_imp_exists (code.branch_target_bt.spec target)
          obtain ⟨merged, hm, hmerge⟩ := WP.spec_imp_exists (code.merge_target.spec expect bt)
          cases merged with
          | Err e =>
            obtain ⟨rfl, hnone, hdiff⟩ := VisitorTrace.merge_error expect bt e hm
            simp [code.visit, hbt, hm,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at htail
            obtain ⟨rfl, rfl, rfl⟩ := htail
            exact ⟨_, hrecord, .target_error hlt hlabel hnone (by simpa [hbtval] using hdiff)⟩
          | Ok common =>
            obtain ⟨hcommon, hcompatible⟩ := hmerge common rfl
            subst common
            obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
              (UScalar.add_spec (x := i) (y := 1#u32) (by scalar_tac))
            simp [code.visit, hbt, hm, hj] at htail
            have hrec : code.read_table_labels_loop visitor s data count w (some bt) j =
                .ok (result, final, v') := by
              simpa [code.read_table_labels_loop, code.read_table_labels_loop.body, code.visit,
                core.result.Result.Insts.CoreOpsTry.branch] using htail
            obtain ⟨observations, hobs, hrun⟩ := ih (count.val - j.val) (by scalar_tac)
              s j w (some bt) (by scalar_tac) hrec rfl
            refine ⟨⟨.op s (.br_table_label depth), .Ok ()⟩ :: observations, ?_, ?_⟩
            · simpa [List.append_assoc] using hobs.trans (congrArg (· ++ observations) hrecord)
            · apply VisitorTrace.LabelRun.next hlt hlabel
                (by simpa [hbtval] using hcompatible)
              simpa [hbtval, show j.val = i.val + 1 by scalar_tac] using hrun

/-- The public vector reader starts with counter zero and no expected target. -/
theorem code.read_table_labels.trace {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List VisitorTrace.Observation)
    (records : ∀ v s depth reply v', visitor.on_br_table_label v s depth = .ok (reply, v') →
      observe v' = observe v ++ [⟨.op s (.br_table_label depth), reply⟩])
    (st : code.OpIterState) (data : Slice U8) (count : U32) (v : V)
    (result : core.result.Result (Option code.BlockType) error.OpError)
    (final : code.OpIterState) (v' : V)
    (h : code.read_table_labels visitor st data count v = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      VisitorTrace.LabelRun data count.val st 0 none observations result final :=
  code.read_table_labels_loop.trace visitor observe records st data count 0#u32 v none
    (by scalar_tac) result final v' h

/-- Every ordinary table-handler return has exactly its observed label prefix.
On success all vector labels and the unobserved default have independent byte
provenance. This also records callbacks preceding later validation failures. -/
theorem code.read_br_table.trace {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List VisitorTrace.Observation) (records : VisitorTrace.Records visitor observe)
    (st : code.OpIterState) (data : Slice U8) (v : V)
    (cs : List code.Ctrl) (c : code.Ctrl) (outer segment : List code.StackType)
    (hctrls : st.ctrls.val = cs ++ [c]) (hvals : st.vals.val = outer ++ segment)
    (hbase : c.value_stack_base.val = outer.length)
    (result : core.result.Result (U32 × code.BlockType) error.OpError)
    (final : code.OpIterState) (v' : V)
    (h : code.read_br_table visitor st data v = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      VisitorTrace.TableResult data st observations result final := by
  obtain ⟨countRes, hcount, hcsem⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
  unfold code.read_br_table at h
  rw [hcount] at h
  cases countRes with
  | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨[], by simp, Or.inl rfl, .empty _⟩
  | Ok pair =>
      obtain ⟨count, first⟩ := pair
      simp [core.result.Result.Insts.CoreOpsTry.branch] at h
      obtain ⟨⟨labelRes, s1, v1⟩, hl, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      obtain ⟨observations, hobs, hrun⟩ := code.read_table_labels.trace visitor observe
        (fun v s depth reply v' hhook => records v (.op s (.br_table_label depth)) reply v' hhook)
        {st with pos := first} data count v labelRes s1 v1 hl
      have hprefix : VisitorTrace.TablePrefix data st observations := by
        obtain ⟨depths, last, hp, hlen⟩ := hrun.prefix
        exact ⟨count, first, depths, last, hcsem, hp, by simpa using hlen⟩
      cases labelRes with
      | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨observations, hobs, Or.inr hprefix, hrun.outcomes⟩
      | Ok expect =>
          obtain ⟨depths, hpref, hlen, hall⟩ := hrun.accepted
          have herror (e : error.OpError) (s : code.OpIterState) :
              VisitorTrace.TableResult data st observations (.Err e) s :=
            ⟨Or.inr hprefix, .of_accepted hall _⟩
          obtain ⟨⟨defaultRes, s2⟩, hdefault, hv2, hc2, hdpost⟩ := WP.spec_imp_exists
            (code.read_label.spec s1 data)
          dsimp only at hv2 hc2 hdpost
          simp [hdefault] at h
          cases defaultRes with
          | Err e =>
              simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact ⟨observations, hobs, herror _ _⟩
          | Ok pair =>
              obtain ⟨fallback, target⟩ := pair
              obtain ⟨hd, _, _⟩ := hdpost
              obtain ⟨bt, hbt, _⟩ := WP.spec_imp_exists (code.branch_target_bt.spec target)
              obtain ⟨merged, hmerge, _⟩ := WP.spec_imp_exists (code.merge_target.spec expect bt)
              simp [hbt, hmerge] at h
              cases merged with
              | Err e =>
                  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
                  obtain ⟨rfl, rfl, rfl⟩ := h
                  exact ⟨observations, hobs, herror _ _⟩
              | Ok common =>
                  have hv : s2.vals.val = outer ++ segment := by simpa [hv2, hpref.stacks.1] using hvals
                  have hb : (Control.base s2).val = outer.length := by
                    simp [Control.base, hc2, hpref.stacks.2, hctrls, hbase]
                  obtain ⟨⟨popRes, s3⟩, hpop, hc3, hp3, rest, hv3, _, _⟩ := WP.spec_imp_exists
                    (code.pop_with_type.realizes s2 outer segment .I32 hv hb)
                  dsimp only at hc3 hp3 hv3
                  simp [hpop] at h
                  cases popRes with
                  | Err e =>
                      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
                      obtain ⟨rfl, rfl, rfl⟩ := h
                      exact ⟨observations, hobs, herror _ _⟩
                  | Ok t =>
                      obtain ⟨rs, hrs, _⟩ := WP.spec_imp_exists (code.block_results.spec common)
                      obtain ⟨⟨argRes, s4⟩, hargs, hc4, hp4, remaining, hv4, _, _⟩ := WP.spec_imp_exists
                        (code.pop_types.realizes s3 outer rest (alloc.vec.Vec.deref rs) hv3
                          (by simpa [Control.base, hc3] using hb))
                      dsimp only at hc4 hp4 hv4
                      simp [hrs, hargs] at h
                      cases argRes with
                      | Err e =>
                          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
                          obtain ⟨rfl, rfl, rfl⟩ := h
                          exact ⟨observations, hobs, herror _ _⟩
                      | Ok u =>
                          have hcs4 : s4.ctrls.val = cs ++ [c] := by
                            simpa [hc4, hc3, hc2, hpref.stacks.2] using hctrls
                          obtain ⟨s5, hm, _, _, _, hp5⟩ := WP.spec_imp_exists
                            (code.mark_unreachable.spec s4 cs c hcs4 (by simp [hv4, hbase]))
                          simp [hm] at h
                          obtain ⟨rfl, rfl, rfl⟩ := h
                          exact ⟨observations, hobs, count, first, depths, s1, hcsem, hpref,
                            by simpa using hlen, by simpa [hp5, hp4, hp3] using hd, hall⟩

end Itasca
