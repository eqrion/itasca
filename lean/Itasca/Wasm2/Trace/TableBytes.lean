import Itasca.Wasm2.Trace.ControlRecords

open Aeneas Aeneas.Std Result ControlFlow

namespace Itasca.MultiValue.CallbackTrace

open VisitorTrace Visitor

/-- A table suffix records only vector labels until the final table callback.
The default target is decoded separately and never emits a label callback. -/
inductive TableSuffix (data : Slice U8) (start : Usize) (remaining : Nat) :
    List Observation → BodyResult → code.OpIterState → Prop where
  | failed {labels depths last final} (e : error.OpError) :
      LabelsAt data start labels depths last → depths.length ≤ remaining →
      Outcomes labels (.Err e) → TableSuffix data start remaining labels (.Err e) final
  | complete {labels depths last fallback final bt reply} :
      LabelsAt data start labels depths last → depths.length = remaining →
      Leb128.Decoded data last fallback final.pos → AllAccepted labels →
      TableSuffix data start remaining
        (labels ++ [⟨.op final (.br_table fallback bt), reply⟩]) (hookResult reply) final

theorem TableSuffix.prepend {data start middle depth remaining observations result final}
    (decoded : Leb128.Decoded data start depth middle.pos)
    (trace : TableSuffix data middle.pos remaining observations result final) :
    TableSuffix data start (remaining + 1)
      (⟨.op middle (.br_table_label depth), .Ok ()⟩ :: observations) result final := by
  cases trace with
  | failed e labels count outcomes =>
    exact .failed e (.cons decoded labels) (by simpa using Nat.add_le_add_right count 1)
      (by simpa using outcomes.prepend (before := [⟨.op middle (.br_table_label depth), .Ok ()⟩]) (by simp [AllAccepted]))
  | complete labels count fallback outcomes =>
    simpa using TableSuffix.complete (.cons (reply := .Ok ()) decoded labels)
      (by simpa using count) fallback (by simpa [AllAccepted] using outcomes)

set_option maxHeartbeats 1500000 in
/-- Ordinary returns of the actual multi-value table loop retain all observed
label bytes, including a rejecting label or a label preceding a suffix error. -/
theorem table_loop_records {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (hs : Control.Shape st.core) (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (count i : U32) (arity : Option Usize) (hi : i.val ≤ count.val)
    (v : V) (result : BodyResult) (final : code.BodyState) (v' : V)
    (run : code.branch_table_with_loop visitor st.core data env v count arity i =
      .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      TableSuffix data st.core.pos (count.val - i.val) observations result final.core := by
  generalize hn : count.val - i.val = n
  induction n using Nat.strong_induction_on generalizing st i arity v with
  | h n ih =>
    unfold code.branch_table_with_loop at run
    rw [loop] at run
    simp only [Visitor.tableBody_eq visitor data env count st v arity i] at run
    obtain ⟨cf, hb, ht⟩ := ResultFacts.bind_ok_inv _ _ _ run
    unfold Visitor.tableBody at hb
    obtain ⟨⟨r, s⟩, hr, hv, hc, hbytes⟩ := WP.spec_imp_exists (code.read_label_info.bytes st data ha)
    rw [hr] at hb
    cases r with
    | Err e =>
      simp only [bind_ok, Std.uncurry, ok.injEq] at hb
      subst cf
      simp only [ok.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl, rfl⟩ := ht
      exact ⟨[], by simp, .failed e (.nil _) (by simp) (.empty _)⟩
    | Ok pair =>
      obtain ⟨depth, ts⟩ := pair
      dsimp only at hv hc
      have hd := hbytes depth ts rfl
      have hs' : Control.Shape s.core :=
        ⟨by simpa [hc] using hs.ordered, by simpa [hc, hv] using hs.bounded⟩
      have ha' : s.blocks.val.length = s.core.ctrls.val.length := by simp [code.BodyState.blocks]
      simp only [bind_ok, Std.uncurry] at hb
      by_cases he : i = count
      · simp only [he, bne_self_eq_false, Bool.false_eq_true, if_false] at hb
        unfold tableRest at hb
        obtain ⟨r, hcheck, hb⟩ := ResultFacts.bind_ok_inv _ _ _ hb
        cases r with
        | Err e =>
          simp only [ok.injEq] at hb
          subst cf
          simp only [ok.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, rfl, rfl⟩ := ht
          exact ⟨[], by simp, .failed e (.nil _) (by simp) (.empty _)⟩
        | Ok nextArity =>
          simp only [↓reduceIte] at hb
          obtain ⟨ois, ho, hb⟩ := ResultFacts.bind_ok_inv _ _ _ hb
          have spec := code.mark_unreachable_total s.core hs'
          rw [ho, WP.spec_ok] at spec
          have hp : ois.pos = s.core.pos := spec.2.2.1
          obtain ⟨⟨reply, w⟩, hh, hb⟩ := ResultFacts.bind_ok_inv _ _ _ hb
          have hlog := records v (.op ois (.br_table depth ts)) reply w hh
          cases reply <;> simp [code.visit, Std.uncurry] at hb
          all_goals subst cf
          all_goals simp only [ok.injEq, Prod.mk.injEq] at ht
          all_goals obtain ⟨rfl, rfl, rfl⟩ := ht
          all_goals refine ⟨_, hlog, ?_⟩
          all_goals apply TableSuffix.complete (labels := []) (depths := []) (last := st.core.pos) (.nil _)
          all_goals first | (simpa [← hn, he]) | (simpa [hp] using hd) | simp [AllAccepted]
      · simp only [bne_iff_ne, if_pos he] at hb
        obtain ⟨⟨reply, w⟩, hh, hb⟩ := ResultFacts.bind_ok_inv _ _ _ hb
        have hlog := records v (.op s.core (.br_table_label depth)) reply w hh
        have hlt : i.val < count.val := by
          have hne : i.val ≠ count.val := fun eq => he (UScalar.eq_of_val_eq eq)
          omega
        cases reply with
        | Err e =>
          simp [code.visit, Std.uncurry] at hb
          subst cf
          simp only [ok.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, rfl, rfl⟩ := ht
          exact ⟨_, hlog, .failed (.Visitor e) (.cons hd (.nil _))
            (by simp; omega) (.single _ (.Err e))⟩
        | Ok u =>
          cases u
          simp only [code.visit, bind_ok, Std.uncurry] at hb
          unfold tableRest at hb
          obtain ⟨r, hcheck, hb⟩ := ResultFacts.bind_ok_inv _ _ _ hb
          cases r with
          | Err e =>
            simp only [ok.injEq] at hb
            subst cf
            simp only [ok.injEq, Prod.mk.injEq] at ht
            obtain ⟨rfl, rfl, rfl⟩ := ht
            exact ⟨_, hlog, .failed e (.cons hd (.nil _)) (by simp; omega)
              (.of_accepted (by simp [AllAccepted]) _)⟩
          | Ok nextArity =>
            simp only [he, if_false] at hb
            obtain ⟨j, hj, hjv⟩ := WP.spec_imp_exists
              (UScalar.add_spec (x := i) (y := 1#u32) (by scalar_tac))
            simp only [hj, bind_ok, ok.injEq] at hb
            subst cf
            have hrec : code.branch_table_with_loop visitor s.core data env w count nextArity j =
                .ok (result, final, v') := ht
            obtain ⟨observations, hobs, htrace⟩ := ih (count.val - j.val) (by scalar_tac)
              s hs' ha' j nextArity (by scalar_tac) w hrec rfl
            refine ⟨⟨.op s.core (.br_table_label depth), .Ok ()⟩ :: observations, ?_, ?_⟩
            · simpa [List.append_assoc] using hobs.trans (congrArg (· ++ observations) hlog)
            · have hn' : count.val - j.val + 1 = n := by scalar_tac
              simpa [hn'] using htrace.prepend hd

end Itasca.MultiValue.CallbackTrace

namespace Itasca.MultiValue.CallbackTrace

open VisitorTrace

theorem labels_decoded {data pos observations depths last}
    (h : LabelsAt data pos observations depths last) :
    BrTable.LabelsDecoded data pos depths last := by
  induction h with
  | nil => exact .nil
  | cons hd _ ih => exact (BrTable.LabelsDecoded.snoc .nil hd).append ih

/-- Table decoding includes its count, every observed vector label, and the
separately decoded default. Operand failures before the loop emit no callbacks. -/
theorem table_records {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe)
    (byte : data.val[p.start.val]'p.inbounds = 0x0e#u8)
    (v : V) (result : BodyResult) (final : code.BodyState) (v' : V)
    (run : code.branch_table_with visitor st data env v = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      StepTrace data p.start observations result final.core := by
  unfold code.branch_table_with at run
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  rw [hr] at run
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
    obtain ⟨rfl, rfl, rfl⟩ := run
    exact ⟨[], by simp, .silent e st.core (.empty _)⟩
  | Ok pair =>
    obtain ⟨count, first⟩ := pair
    have hcount : Leb128.Decoded data st.core.pos count first := hd
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at run
    have shape : Control.Shape {st.core with pos := first} :=
      ⟨p.opened.shape.core.ordered, p.opened.shape.core.bounded⟩
    obtain ⟨⟨r, s⟩, hr, hs, hc, hp, _⟩ := WP.spec_imp_exists
      (code.pop_with_type.total {st.core with pos := first} .I32 shape)
    rw [hr] at run
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
      obtain ⟨rfl, rfl, rfl⟩ := run
      exact ⟨[], by simp, .silent e s (.empty _)⟩
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at run
      obtain ⟨observations, log, trace⟩ := table_loop_records visitor observe records
        ⟨s⟩ data env hs (by simp) count 0#u32 none (by simp) v result final v' run
      have hop : Wasm.BytesAt data p.start [0x0E#u8] st.core.pos :=
        .byte data p.start st.core.pos 0x0E#u8 p.inbounds byte p.pos
      have hpos : s.pos = first := hp
      simp only [hpos] at trace
      change TableSuffix data first count.val observations result final.core at trace
      refine ⟨observations, log, ?_⟩
      cases trace with
      | failed e labels len outcomes =>
        exact .unfinished e ⟨st.core.pos, count, first, _, _, hop, hcount, labels, len⟩ outcomes
      | complete labels len fallback outcomes =>
        refine .complete (.table hop hcount labels len fallback ?_) ?_
        · exact At.plain (Wasm.At.of_br_table count _ _ p.inbounds byte p.pos hcount len
            (labels_decoded labels) fallback)
        · exact (Outcomes.single _ _).prepend outcomes

/-- The table arm of the profile dispatcher returns its handler's exact result. -/
theorem dispatch_br_table {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (v : V) :
    code.step_profile visitor st data env ctx index .Wasm2 0x0e#u8 v =
      code.branch_table_with visitor st data env v := by
  simp [code.step_profile, global_simps,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  conv => rhs; rw [← Std.bind_pure (code.branch_table_with visitor st data env v)]
  congr 1
  funext pair
  obtain ⟨r, s, w⟩ := pair
  cases r <;> simp

end Itasca.MultiValue.CallbackTrace

namespace Itasca.MultiValue.CallbackTrace

open VisitorTrace

theorem step_br_table {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0e#u8) :
    ProfileStepRecords p visitor observe ctx 0x0e#u8 := by
  intro v result final v' run
  rw [dispatch_br_table] at run
  exact table_records p visitor observe records byte v result final v' run

end Itasca.MultiValue.CallbackTrace
