(** * The checker's side of completeness

    Soundness reads the code and asks what it means; completeness reads the
    checker and asks whether the code can follow. Every lemma here is a converse
    of one used by the simulation: [consume] taken apart rather than assembled,
    [c_types_agree] turned back into a pop sequence, the alignment bound read from
    the specification's exponent to the code's comparison.

    The one place the two sides could have disagreed is closed by construction:
    [consume] accepts a pop of any type against a [T_bot] operand while the Rust
    compares value types for equality, but [ValueType] has no bottom, so no
    operand translates to [T_bot] ([Translate.translate_vt_v_not_bot]). An
    operand of unknown type is [StackType::Bot], which carries no value type at
    all. *)

Require Import Primitives.
Import Primitives.
Require Import Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Import Itasca.Aeneas_Specs.
Require Import Itasca.Translate.
Require Import Itasca.OpIter_State.
Require Import Itasca.OpIter_Sim.

From Wasm Require Import datatypes type_checker operations typing.
From mathcomp Require Import ssreflect ssrbool eqtype seq.

(* Same reason as in [OpIter_Sim.v]: mathcomp binds [list] to [seq_scope], so
   [++] would mean [cat] in argument position whatever the ambient scope is, and
   an [app]-keyed rewrite would silently fail to fire. *)
Local Open Scope list_scope.
Local Bind Scope list_scope with list.

(* ================================================================== *)
(** ** Subtyping and [consume], taken apart                            *)
(* ================================================================== *)

Lemma translate_vt_v_inj : forall a b,
  translate_vt_v a = translate_vt_v b -> a = b.
Proof. intros a b H. destruct a; destruct b; try reflexivity; discriminate. Qed.

(** The converse of [translate_st_sub] on the [Val] side: the Rust's equality
    test and [consume]'s subtyping test agree, because the only way subtyping is
    weaker is a [T_bot] operand and no value type translates to one. *)
Lemma vsub_val_eq : forall v vt,
  (translate_vt_v v <t: translate_vt_v vt) = true -> v = vt.
Proof.
  intros v vt H. unfold value_subtyping in H.
  move/orP: H => [H|H]; move/eqP: H => H.
  - apply translate_vt_v_inj. exact H.
  - exfalso. apply (translate_vt_v_not_bot v). exact H.
Qed.

Lemma consume_nil_unr : forall ts, consume <<[], true>> ts = Some <<[], true>>.
Proof. intros ts. destruct ts; reflexivity. Qed.

(** The converse of [consume_cons_split]: a successful multi-type [consume]
    factors through the first type, which is what lets a multi-pop reader take
    its pops one at a time. *)
Lemma consume_cons_inv : forall ct a rest ct2,
  consume ct (a :: rest) = Some ct2 ->
  exists ct1, consume ct [a] = Some ct1 /\ consume ct1 rest = Some ct2.
Proof.
  intros [ts unr] a rest ct2 H. cbn [consume CT_type CT_unr] in H |- *.
  destruct ts as [|t ts'].
  - destruct unr; [|discriminate]. injection H as <-.
    exists <<[], true>>. split; [reflexivity | apply consume_nil_unr].
  - destruct (t <t: a) eqn:Hsub; [|discriminate].
    exists <<ts', unr>>. split; [reflexivity | exact H].
Qed.

(** An empty else-branch agrees only with an empty result type, which is why
    Wasm 1.0 requires an [if] with a result to have an [else] and why
    [read_end] may reject a [Then] frame that has one. The reachable case is
    plain equality; the unreachable one cannot arise, since a frame that
    consumed nothing is not unreachable. *)
Lemma c_types_agree_nil_inv : forall ts,
  c_types_agree <<[], false>> ts = true -> ts = [].
Proof.
  intros ts H. unfold c_types_agree in H. cbn [CT_type CT_unr] in H.
  destruct ts as [|t ts']; [reflexivity | cbn in H; discriminate].
Qed.

(** The converse of [c_types_agree_consume_nil]: what the checker asks of a
    frame's operands at [end] is exactly that popping the results succeeds and
    leaves nothing. Both of [c_types_agree]'s cases work out, the unreachable one
    because [take] stops the comparison at the operands actually present. *)
Lemma consume_of_c_types_agree : forall ts ct,
  c_types_agree ct ts = true -> exists unr, consume ct ts = Some <<[], unr>>.
Proof.
  induction ts as [|a ts IH]; intros [cts cunr] H;
    unfold c_types_agree in H; cbn [CT_type CT_unr] in H.
  - destruct cts as [|t cts']; [exists cunr; reflexivity|].
    exfalso. destruct cunr; cbn in H; discriminate.
  - destruct cts as [|t cts'].
    + destruct cunr; [exists true; reflexivity|]. exfalso. cbn in H. discriminate.
    + cbn [consume CT_type CT_unr]. destruct cunr.
      * cbn [size take values_subtyping all2] in H.
        destruct (t <t: a) eqn:Hsub; [|discriminate].
        apply (IH <<cts', true>>). unfold c_types_agree. cbn [CT_type CT_unr].
        exact H.
      * cbn [values_subtyping all2] in H.
        destruct (t <t: a) eqn:Hsub; [|discriminate].
        apply (IH <<cts', false>>). unfold c_types_agree. cbn [CT_type CT_unr].
        exact H.
Qed.

(** An emptied [checker_type] means an emptied segment, which is what [end]'s
    "nothing above the frame's base" check tests. *)
Lemma translate_vals_nil_inv : forall seg, translate_vals seg = [] -> seg = [].
Proof.
  intros seg H. destruct seg as [|x xs]; [reflexivity|].
  exfalso. apply (f_equal (@List.length _)) in H.
  unfold translate_vals in H. rewrite List.rev_length in H.
  rewrite List.map_length in H. cbn [List.length] in H. discriminate.
Qed.

(* ================================================================== *)
(** ** Popping what the checker consumes                                *)
(* ================================================================== *)

Lemma seg_snoc : forall (l : list opiter_StackType_t),
  l <> [] -> exists l0 x, l = l0 ++ [x].
Proof.
  intros l Hne. destruct (List.exists_last Hne) as [l0 [x Hl]].
  exists l0, x. exact Hl.
Qed.

(** The raw pop succeeds whenever the frame owns an operand or is unreachable,
    which is exactly the case distinction [consume] makes. *)
Lemma pop_stack_type_complete : forall st pre_seg f,
  vec_list st.(opiter_OpIterState_vals) = pre_seg ++ fv_seg f ->
  cur_base_nat st = List.length pre_seg ->
  cur_unr st = (fv_ctrl f).(opiter_Ctrl_polymorphic_base) ->
  (fv_seg f <> [] \/ (fv_ctrl f).(opiter_Ctrl_polymorphic_base) = true) ->
  exists t st', opiter_pop_stack_type st = Ok (Core_result_Result_Ok t, st').
Proof.
  intros st pre_seg f Hsplit Hbase Hunr Hne.
  unfold opiter_pop_stack_type.
  destruct (cur_base_total st) as [base Hcb]. rewrite Hcb. cbn [bind].
  pose proof (cur_base_agrees st base Hcb) as Hba.
  assert (Hbz : to_Z base = Z.of_nat (List.length pre_seg)).
  { assert (Hn : Z.to_nat (to_Z base) = List.length pre_seg).
    { rewrite Hba. exact Hbase. }
    apply (f_equal Z.of_nat) in Hn.
    pose proof (Z2Nat.id (to_Z base) (usize_nonneg base)) as Hid.
    rewrite Hid in Hn. exact Hn. }
  assert (Hlen : Z.of_nat (List.length (vec_list st.(opiter_OpIterState_vals)))
                 = Z.of_nat (List.length pre_seg)
                   + Z.of_nat (List.length (fv_seg f))).
  { rewrite Hsplit. rewrite List.app_length. lia. }
  destruct (fv_seg f) as [|x xs] eqn:Hseg.
  - (* the frame owns nothing, so it has to be unreachable *)
    destruct Hne as [Hne|Hpoly]; [exfalso; apply Hne; reflexivity|].
    assert (Hz : (alloc_vec_Vec_len st.(opiter_OpIterState_vals) s= base) = true).
    { unfold scalar_eqb. apply Z.eqb_eq. rewrite vec_len_spec. rewrite Hbz.
      cbn [List.length] in Hlen. lia. }
    rewrite Hz. cbn beta iota.
    destruct (cur_polymorphic_total st) as [pb Hcp]. rewrite Hcp. cbn [bind].
    pose proof (cur_unr_agrees st pb Hcp) as Hpb.
    assert (Hpbt : pb = true) by (rewrite Hpb; rewrite Hunr; exact Hpoly).
    rewrite Hpbt. eexists. eexists. reflexivity.
  - (* a real pop, which cannot come up empty *)
    assert (Hz : (alloc_vec_Vec_len st.(opiter_OpIterState_vals) s= base)
                 = false).
    { unfold scalar_eqb. apply Z.eqb_neq. rewrite vec_len_spec. rewrite Hbz.
      cbn [List.length] in Hlen. lia. }
    rewrite Hz. cbn beta iota.
    destruct (vec_pop_ok alloc_alloc_Global st.(opiter_OpIterState_vals))
      as [o [v Hpop]].
    rewrite Hpop. cbn [bind].
    pose proof (vec_pop_last alloc_alloc_Global _ o v Hpop) as Hspec.
    destruct (List.rev (vec_list st.(opiter_OpIterState_vals))) as [|y r]
      eqn:Hrev.
    { exfalso. apply (f_equal (@List.length _)) in Hrev.
      rewrite List.rev_length in Hrev. cbn [List.length] in Hrev.
      cbn [List.length] in Hlen. lia. }
    destruct Hspec as [Ho _]. rewrite Ho. eexists. eexists. reflexivity.
Qed.

(** The two shapes a raw pop takes, with the resulting state pinned down so that
    [read_select]'s three pops can be chained. A nonempty segment yields its last
    element; an empty unreachable one yields [Bot] and changes nothing. *)
Lemma pop_stack_type_real : forall st pre_seg f seg0 x,
  vec_list st.(opiter_OpIterState_vals) = pre_seg ++ fv_seg f ->
  cur_base_nat st = List.length pre_seg ->
  cur_unr st = (fv_ctrl f).(opiter_Ctrl_polymorphic_base) ->
  fv_seg f = seg0 ++ [x] ->
  exists st',
    opiter_pop_stack_type st = Ok (Core_result_Result_Ok x, st')
    /\ vec_list st'.(opiter_OpIterState_ctrls)
       = vec_list st.(opiter_OpIterState_ctrls)
    /\ vec_list st'.(opiter_OpIterState_vals) = pre_seg ++ seg0.
Proof.
  intros st pre_seg f seg0 x Hsplit Hbase Hunr Hseg.
  assert (Hne : fv_seg f <> []).
  { rewrite Hseg. destruct seg0; discriminate. }
  destruct (pop_stack_type_complete st pre_seg f Hsplit Hbase Hunr
              (or_introl Hne)) as [t [st' Hps]].
  destruct (pop_stack_type_sim st pre_seg f t st' Hsplit Hbase Hunr Hps)
    as [seg' [Hc [Hv [HL | [HR _]]]]].
  - rewrite Hseg in HL. apply List.app_inj_tail in HL as [Hs Ht].
    rewrite Ht. exists st'. split; [exact Hps|]. split; [exact Hc|].
    rewrite Hv. rewrite Hs. reflexivity.
  - exfalso. rewrite Hseg in HR. destruct seg0; discriminate HR.
Qed.

Lemma pop_stack_type_empty : forall st pre_seg f,
  vec_list st.(opiter_OpIterState_vals) = pre_seg ++ fv_seg f ->
  cur_base_nat st = List.length pre_seg ->
  cur_unr st = (fv_ctrl f).(opiter_Ctrl_polymorphic_base) ->
  fv_seg f = [] ->
  (fv_ctrl f).(opiter_Ctrl_polymorphic_base) = true ->
  opiter_pop_stack_type st
    = Ok (Core_result_Result_Ok Opiter_StackType_Bot, st).
Proof.
  intros st pre_seg f Hsplit Hbase Hunr Hseg Hpoly.
  unfold opiter_pop_stack_type.
  destruct (cur_base_total st) as [base Hcb]. rewrite Hcb. cbn [bind].
  pose proof (cur_base_agrees st base Hcb) as Hba.
  assert (Hz : (alloc_vec_Vec_len st.(opiter_OpIterState_vals) s= base) = true).
  { unfold scalar_eqb. apply Z.eqb_eq. rewrite vec_len_spec.
    rewrite Hsplit. rewrite Hseg. rewrite List.app_nil_r.
    assert (Hn : Z.to_nat (to_Z base) = List.length pre_seg)
      by (rewrite Hba; exact Hbase).
    apply (f_equal Z.of_nat) in Hn.
    rewrite (Z2Nat.id (to_Z base) (usize_nonneg base)) in Hn.
    rewrite Hn. reflexivity. }
  rewrite Hz. cbn beta iota.
  destruct (cur_polymorphic_total st) as [pb Hcp]. rewrite Hcp. cbn [bind].
  pose proof (cur_unr_agrees st pb Hcp) as Hpb.
  assert (Hpbt : pb = true) by (rewrite Hpb; rewrite Hunr; exact Hpoly).
  rewrite Hpbt. reflexivity.
Qed.

(* ================================================================== *)
(** ** The join, backwards                                             *)
(* ================================================================== *)

(** The converse of [join_stack_type_spec]. WasmCert's [value_type_select] treats
    [T_bot] as a wildcard where the Rust compares value types, but neither
    operand can translate to [T_bot], so the two agree on every case. *)
Lemma join_stack_type_complete : forall a b tsup,
  value_type_select (translate_st a) (translate_st b) = Some tsup ->
  exists t, opiter_join_stack_type a b = Ok (Core_result_Result_Ok t).
Proof.
  intros a b tsup H. unfold opiter_join_stack_type.
  destruct a as [va|]; [|eexists; reflexivity].
  destruct b as [vb|]; [|eexists; reflexivity].
  cbn [translate_st] in H.
  destruct va; destruct vb;
    try (vm_compute in H; discriminate H);
    (rewrite vt_eq_spec; cbn [types_ValueType_t_beq]; eexists; reflexivity).
Qed.

(** With a [Bot] on one side the join cannot fail, which is what the three
    exhausted-frame cases of [select] need. *)
Lemma join_stack_type_bot_l_ok : forall b,
  exists t, opiter_join_stack_type Opiter_StackType_Bot b
            = Ok (Core_result_Result_Ok t).
Proof. intros b. exists b. reflexivity. Qed.

Lemma join_stack_type_bot_r_ok : forall a,
  exists t, opiter_join_stack_type a Opiter_StackType_Bot
            = Ok (Core_result_Result_Ok t).
Proof. intros a. destruct a as [va|]; [exists (Opiter_StackType_Val va)
       | exists Opiter_StackType_Bot]; reflexivity. Qed.

(* ================================================================== *)
(** ** [type_update_select], taken apart                               *)
(* ================================================================== *)

Lemma translate_vals_snoc3 : forall s z y x,
  translate_vals (s ++ [z; y; x])
    = translate_st x :: translate_st y :: translate_st z :: translate_vals s.
Proof.
  intros s z y x. unfold translate_vals.
  rewrite List.map_app. rewrite List.rev_app_distr. reflexivity.
Qed.

(** What an accepting [select] tells the reader: the condition is consumable as
    an [i32], and the segment has one of the four shapes [type_update_select]
    splits on. Only the three-or-more case carries a join obligation; the others
    have a [Bot] on one side, where the join cannot fail. *)
Lemma select_disj : forall f ct',
  type_update_select (fv_ct f) None = Some ct' ->
  (exists ct1, consume (fv_ct f) [T_num T_i32] = Some ct1)
  /\ ((exists s z y x, fv_seg f = s ++ [z; y; x]
                       /\ exists t, opiter_join_stack_type y z
                                    = Ok (Core_result_Result_Ok t))
      \/ ((exists y x, fv_seg f = [y; x])
          /\ (fv_ctrl f).(opiter_Ctrl_polymorphic_base) = true)
      \/ ((fv_seg f = [] \/ exists x, fv_seg f = [x])
          /\ (fv_ctrl f).(opiter_Ctrl_polymorphic_base) = true)).
Proof.
  intros f ct' H.
  destruct (@seg_cases _ (fv_seg f)) as
    [Hs | [[x Hs] | [[y [x Hs]] | [s [z [y [x Hs]]]]]]].
  - (* nothing visible *)
    assert (Hct : fv_ct f
             = <<[], (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>>).
    { unfold fv_ct. rewrite Hs. reflexivity. }
    rewrite Hct in H. unfold type_update_select in H.
    cbn [CT_type CT_unr] in H. cbn beta iota in H.
    assert (Hu : (fv_ctrl f).(opiter_Ctrl_polymorphic_base) = true).
    { destruct ((fv_ctrl f).(opiter_Ctrl_polymorphic_base));
        [reflexivity | cbn in H; discriminate H]. }
    split.
    + rewrite Hct. rewrite Hu. exists <<[], true>>. reflexivity.
    + right. right. split; [left; exact Hs | exact Hu].
  - (* only the condition *)
    assert (Hct : fv_ct f
             = <<[translate_st x],
                 (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>>).
    { unfold fv_ct. rewrite Hs. reflexivity. }
    rewrite Hct in H. unfold type_update_select in H.
    cbn [CT_type CT_unr] in H. cbn beta iota in H.
    assert (Hu : (fv_ctrl f).(opiter_Ctrl_polymorphic_base) = true).
    { destruct ((fv_ctrl f).(opiter_Ctrl_polymorphic_base));
        [reflexivity | cbn in H; discriminate H]. }
    rewrite Hu in H. unfold type_update in H.
    destruct (consume <<[translate_st x], true>> [T_num T_i32]) as [ct1|]
      eqn:Hc; [|discriminate H].
    split.
    + rewrite Hct. rewrite Hu. exists ct1. exact Hc.
    + right. right. split; [right; exists x; exact Hs | exact Hu].
  - (* two operands, so the second value comes off Bot *)
    assert (Hct : fv_ct f
             = <<[translate_st x; translate_st y],
                 (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>>).
    { unfold fv_ct. rewrite Hs. reflexivity. }
    rewrite Hct in H. unfold type_update_select in H.
    cbn [CT_type CT_unr] in H. cbn beta iota in H.
    rewrite translate_st_numeric in H. cbn [andb] in H.
    assert (Hu : (fv_ctrl f).(opiter_Ctrl_polymorphic_base) = true).
    { destruct ((fv_ctrl f).(opiter_Ctrl_polymorphic_base));
        [reflexivity | cbn in H; discriminate H]. }
    rewrite Hu in H. unfold type_update in H.
    destruct (consume <<[translate_st x; translate_st y], true>>
                [T_num T_i32; translate_st y]) as [ct1|] eqn:Hc;
      [|discriminate H].
    destruct (consume_cons_inv _ _ _ _ Hc) as [ct2 [Hc2 _]].
    split.
    + rewrite Hct. rewrite Hu. exists ct2. exact Hc2.
    + right. left. split; [exists y, x; exact Hs | exact Hu].
  - (* three or more, so both values are real and have to agree *)
    assert (Hct : fv_ct f
             = <<translate_st x :: translate_st y :: translate_st z
                 :: translate_vals s,
                 (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>>).
    { unfold fv_ct. rewrite Hs. rewrite translate_vals_snoc3. reflexivity. }
    rewrite Hct in H. unfold type_update_select in H.
    cbn [CT_type CT_unr] in H. cbn beta iota in H.
    destruct (value_type_select (translate_st y) (translate_st z)) as [tsup|]
      eqn:Hvs; [|discriminate H].
    unfold type_update in H.
    destruct (consume <<translate_st x :: translate_st y :: translate_st z
                        :: translate_vals s,
                        (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>>
                [T_num T_i32; translate_st y; translate_st z]) as [ct1|] eqn:Hc;
      [|discriminate H].
    destruct (consume_cons_inv _ _ _ _ Hc) as [ct2 [Hc2 _]].
    split.
    + rewrite Hct. exists ct2. exact Hc2.
    + left. exists s, z, y, x. split; [exact Hs|].
      apply (join_stack_type_complete y z tsup Hvs).
Qed.

(** The typed pop succeeds whenever [consume] does. This is the primitive the
    per-reader completeness proofs are built from. *)
Lemma pop_with_type_complete : forall st pre_seg f vt ct',
  vec_list st.(opiter_OpIterState_vals) = pre_seg ++ fv_seg f ->
  cur_base_nat st = List.length pre_seg ->
  cur_unr st = (fv_ctrl f).(opiter_Ctrl_polymorphic_base) ->
  consume (fv_ct f) [translate_vt_v vt] = Some ct' ->
  exists t st', opiter_pop_with_type st vt = Ok (Core_result_Result_Ok t, st').
Proof.
  intros st pre_seg f vt ct' Hsplit Hbase Hunr Hcon.
  assert (Hcase : fv_seg f = [] \/ fv_seg f <> []).
  { destruct (fv_seg f); [left; reflexivity | right; discriminate]. }
  assert (Hdisj : fv_seg f <> []
                  \/ (fv_ctrl f).(opiter_Ctrl_polymorphic_base) = true).
  { destruct Hcase as [Hnil|Hne]; [|left; exact Hne]. right.
    unfold fv_ct in Hcon. rewrite Hnil in Hcon.
    cbn [translate_vals List.map List.rev consume CT_type CT_unr] in Hcon.
    destruct ((fv_ctrl f).(opiter_Ctrl_polymorphic_base));
      [reflexivity | discriminate]. }
  destruct (pop_stack_type_complete st pre_seg f Hsplit Hbase Hunr Hdisj)
    as [t [st0 Hps]].
  unfold opiter_pop_with_type. rewrite Hps. cbn [bind]. rewrite branch_ok.
  cbn [bind].
  destruct t as [v|]; [|eexists; eexists; reflexivity].
  (* a real value came off, so it is the segment's top, and the checker's guard
     forces it to be the expected type *)
  rewrite vt_eq_spec. cbn [bind].
  assert (Hveq : v = vt).
  { destruct (pop_stack_type_ok st _ st0 Hps) as [_ [Hreal | Hbot]];
      [|destruct Hbot as [Hb _]; discriminate Hb].
    destruct Hreal as [prev [Hvals [_ Hne2]]].
    assert (Hsegne : fv_seg f <> []).
    { intros Hz. apply Hne2. rewrite Hbase. rewrite Hsplit. rewrite Hz.
      rewrite List.app_nil_r. reflexivity. }
    destruct (seg_snoc (fv_seg f) Hsegne) as [seg0 [x Hseg]].
    assert (Hx : x = Opiter_StackType_Val v).
    { rewrite Hsplit in Hvals. rewrite Hseg in Hvals.
      rewrite List.app_assoc in Hvals.
      apply List.app_inj_tail in Hvals as [_ Hx]. exact Hx. }
    apply vsub_val_eq.
    unfold fv_ct in Hcon. rewrite Hseg in Hcon.
    rewrite translate_vals_snoc in Hcon.
    cbn [consume CT_type CT_unr] in Hcon.
    rewrite Hx in Hcon. cbn [translate_st] in Hcon.
    destruct (translate_vt_v v <t: translate_vt_v vt) eqn:Hsub;
      [reflexivity | discriminate]. }
  rewrite Hveq. rewrite vt_beq_refl. eexists. eexists. reflexivity.
Qed.

(** What a typed pop leaves behind, recorded so that the pops chain: the
    [consume] step of [pop_with_type_sim] over the resulting segment. *)
Lemma pop_with_type_step : forall st pre_seg f vt t st',
  vec_list st.(opiter_OpIterState_vals) = pre_seg ++ fv_seg f ->
  cur_base_nat st = List.length pre_seg ->
  cur_unr st = (fv_ctrl f).(opiter_Ctrl_polymorphic_base) ->
  opiter_pop_with_type st vt = Ok (Core_result_Result_Ok t, st') ->
  exists seg0,
    vec_list st'.(opiter_OpIterState_ctrls)
      = vec_list st.(opiter_OpIterState_ctrls)
    /\ vec_list st'.(opiter_OpIterState_vals) = pre_seg ++ seg0
    /\ consume (fv_ct f) [translate_vt_v vt]
       = Some <<translate_vals seg0,
                (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>>.
Proof.
  intros st pre_seg f vt t st' Hsplit Hbase Hunr H.
  destruct (pop_with_type_ok st vt t st' H) as [Hraw _].
  destruct (pop_stack_type_sim st pre_seg f t st' Hsplit Hbase Hunr Hraw)
    as [seg0 [Hc0 [Hv0 _]]].
  destruct (pop_with_type_sim st pre_seg f vt t st' Hsplit Hbase Hunr H)
    as [seg1 [_ [Hv1 Hcon]]].
  assert (Hseq : seg0 = seg1).
  { rewrite Hv0 in Hv1. apply List.app_inv_head in Hv1. exact Hv1. }
  exists seg0. split; [exact Hc0|]. split; [exact Hv0|].
  rewrite Hseq. exact Hcon.
Qed.

(** [pop_types]: the completeness counterpart of [pop_types_sim], and the same
    induction on the loop index read the other way. *)
Lemma pop_types_loop_complete : forall n st pre_seg f
                                       (s : slice types_ValueType_t)
                                       (i : usize) ct',
  Z.to_nat (to_Z i) = n ->
  (n <= List.length (vec_list s))%nat ->
  vec_list st.(opiter_OpIterState_vals) = pre_seg ++ fv_seg f ->
  cur_base_nat st = List.length pre_seg ->
  cur_unr st = (fv_ctrl f).(opiter_Ctrl_polymorphic_base) ->
  consume (fv_ct f) (translate_typelist (List.firstn n (vec_list s)))
    = Some ct' ->
  exists st', opiter_pop_types_loop st s i = Ok (Core_result_Result_Ok tt, st').
Proof.
  induction n as [|n IH];
    intros st pre_seg f s i ct' Hi Hlen Hsplit Hbase Hunr Hcon;
    unfold opiter_pop_types_loop; rewrite loop_unfold; cbn beta iota.
  - assert (Hz : (i s= 0%usize) = true).
    { apply scalar_eqb_zero_true. pose proof (usize_nonneg i). lia. }
    rewrite Hz. cbn beta iota. exists st. reflexivity.
  - assert (Hpos : 0 < to_Z i) by (pose proof (usize_nonneg i); lia).
    assert (Hz : (i s= 0%usize) = false) by (apply scalar_eqb_zero_false; lia).
    rewrite Hz. cbn beta iota.
    destruct (usize_sub_1_ok i) as [i2 [Hsub Hi2]]; [lia|].
    rewrite Hsub. cbn [bind]. rewrite slice_index_usize_spec.
    assert (Hidx : Z.to_nat (to_Z i2) = n) by (rewrite Hi2; lia).
    rewrite Hidx.
    destruct (List.nth_error (vec_list s) n) as [vt|] eqn:Hnth.
    2: { exfalso. apply (List.nth_error_None (vec_list s) n) in Hnth. lia. }
    cbn [bind].
    rewrite (firstn_nth_error_snoc n (vec_list s) vt Hnth) in Hcon.
    rewrite translate_typelist_snoc in Hcon.
    destruct (consume_cons_inv (fv_ct f) (translate_vt_v vt) _ ct' Hcon)
      as [ct1 [Hc1 Hc2]].
    destruct (pop_with_type_complete st pre_seg f vt ct1 Hsplit Hbase Hunr Hc1)
      as [t [st0 Hp]].
    rewrite Hp. cbn [bind]. rewrite branch_ok. cbn [bind].
    destruct (pop_with_type_step st pre_seg f vt t st0 Hsplit Hbase Hunr Hp)
      as [seg0 [Hc0 [Hv0 Hcon0]]].
    pose (f0 := {| fv_ctrl := fv_ctrl f;
                   fv_seg := seg0;
                   fv_done := fv_done f; fv_then := fv_then f |}).
    destruct (cur_views_ctrls st st0 Hc0) as [Hb0 Hu0].
    assert (Hct1 : ct1 = fv_ct f0).
    { rewrite Hc1 in Hcon0. injection Hcon0 as Heq. rewrite Heq. reflexivity. }
    apply (IH st0 pre_seg f0 s i2 ct' Hidx ltac:(lia) Hv0
              ltac:(rewrite Hb0; exact Hbase)
              ltac:(rewrite Hu0; exact Hunr)).
    rewrite <- Hct1. exact Hc2.
Qed.

Lemma pop_types_complete : forall st pre_seg f (s : slice types_ValueType_t) ct',
  vec_list st.(opiter_OpIterState_vals) = pre_seg ++ fv_seg f ->
  cur_base_nat st = List.length pre_seg ->
  cur_unr st = (fv_ctrl f).(opiter_Ctrl_polymorphic_base) ->
  consume (fv_ct f) (translate_typelist (vec_list s)) = Some ct' ->
  exists st', opiter_pop_types st s = Ok (Core_result_Result_Ok tt, st').
Proof.
  intros st pre_seg f s ct' Hsplit Hbase Hunr Hcon.
  unfold opiter_pop_types.
  assert (Hlen : Z.to_nat (to_Z (slice_len s)) = List.length (vec_list s)).
  { rewrite slice_len_spec. apply Z_to_nat_of_nat. }
  apply (pop_types_loop_complete (List.length (vec_list s)) st pre_seg f s
           (slice_len s) ct' Hlen (Nat.le_refl _) Hsplit Hbase Hunr).
  rewrite List.firstn_all. exact Hcon.
Qed.

(** [call_indirect]'s inversion lives here rather than with the other
    [check_single_*_inv] lemmas because WasmCert tests the table's element type
    with mathcomp's [==], and [OpIter_Complete.v] does not import ssreflect. *)
Lemma check_single_call_indirect_inv : forall C ts x y ct,
  check_single C (Some ts) (BI_call_indirect x y) = Some ct ->
  exists tabt tn tm ct1,
    lookup_N (tc_tables C) x = Some tabt
    /\ tt_elem_type tabt = T_funcref
    /\ lookup_N (tc_types C) y = Some (Tf tn tm)
    /\ consume ts (T_num T_i32 :: tn) = Some ct1.
Proof.
  intros C ts x y ct H. cbn [check_single] in H.
  destruct (lookup_N (tc_tables C) x) as [tabt|] eqn:Htab; [|discriminate].
  destruct (tt_elem_type tabt == T_funcref) eqn:He; [|discriminate].
  move/eqP: He => He.
  destruct (lookup_N (tc_types C) y) as [tf|] eqn:Hty; [|discriminate].
  destruct tf as [tn tm]. exists tabt, tn, tm.
  unfold type_update in H.
  destruct (consume ts (T_num T_i32 :: tn)) as [ct1|]; [|discriminate].
  exists ct1. split; [reflexivity|]. split; [exact He|].
  split; reflexivity.
Qed.

(* ================================================================== *)
(** ** The alignment bound, read backwards                             *)
(* ================================================================== *)

(** mathcomp's [nat_of_bin] coercion is a binary computation of its own, so it
    has to be related to [N.to_nat] before the specification's exponent bound can
    become the code's [a <= natural] comparison. *)
Lemma nat_of_pos_to_nat : forall p, ssrnat.nat_of_pos p = Pos.to_nat p.
Proof.
  elim => [p IH|p IH|] //=;
    rewrite ssrnat.NatTrec.trecE -ssrnat.addnn IH -ssrnat.plusE.
  - rewrite Pos2Nat.inj_xI. lia.
  - rewrite Pos2Nat.inj_xO. lia.
Qed.

Lemma nat_of_bin_N : forall n : BinNums.N, ssrnat.nat_of_bin n = N.to_nat n.
Proof. case => [|p] //=. apply nat_of_pos_to_nat. Qed.

Lemma pow2_bound_nat : forall a e L : nat,
  Nat.le (Nat.pow 2 a) L -> Nat.lt L (Nat.pow 2 (S e)) -> Nat.le a e.
Proof.
  intros a e L H1 H2.
  destruct (Nat.le_gt_cases a e) as [Hle|Hgt]; [exact Hle|].
  exfalso.
  assert (Hm : Nat.le (Nat.pow 2 (S e)) (Nat.pow 2 a))
    by (apply Nat.pow_le_mono_r; lia).
  lia.
Qed.

(** The access width an alignment exponent is bounded by. *)
Definition align_limit (tp : option packed_type) (nt : number_type) : nat :=
  match tp with
  | None => N.to_nat (tnum_length nt)
  | Some tp' => tp_length tp'
  end.

(** WasmCert bounds [2 ^ a] by the access width; the Rust bounds [a] by the
    natural alignment exponent. At each opcode the width is a literal, so the two
    say the same thing, and the side condition falls to computation. *)
Lemma load_store_align_bound : forall (z : Z) tp nt e,
  0 <= z ->
  load_store_t_bounds (Z.to_N z) tp nt = true ->
  Nat.lt (align_limit tp nt) (Nat.pow 2 (S e)) ->
  z <= Z.of_nat e.
Proof.
  intros z tp nt e Hz H Hb.
  assert (Hle : Nat.le (N.to_nat (Z.to_N z)) e).
  { unfold load_store_t_bounds in H. unfold align_limit in Hb.
    destruct tp as [tp'|].
    - move/andP: H => [H _]. move/andP: H => [H _].
      rewrite !nat_of_bin_N in H. move/ssrnat.leP: H => H.
      apply (pow2_bound_nat _ _ (tp_length tp')); [exact H | exact Hb].
    - rewrite !nat_of_bin_N in H. move/ssrnat.leP: H => H.
      apply (pow2_bound_nat _ _ (N.to_nat (tnum_length nt)));
        [exact H | exact Hb]. }
  rewrite N_to_nat_Z_to_N in Hle. lia.
Qed.

(* ================================================================== *)
(** ** The memory and alignment checks, read backwards                 *)
(* ================================================================== *)

Lemma require_memory_complete : forall module C0 m,
  mems_agree module C0 ->
  lookup_N (tc_mems C0) 0%N = Some m ->
  opiter_require_memory module = Ok (Core_result_Result_Ok tt).
Proof.
  intros module C0 m Hag Hlk. unfold opiter_require_memory.
  rewrite vec_is_empty_spec. cbn [bind].
  assert (Hne : vec_list module.(env_Env_mem_types) <> []).
  { intros Hnil. unfold mems_agree in Hag. rewrite Hnil in Hag.
    cbn [List.map] in Hag. rewrite Hag in Hlk. discriminate. }
  destruct (vec_list module.(env_Env_mem_types)) as [|m0 ms];
    [exfalso; apply Hne; reflexivity | reflexivity].
Qed.

Lemma check_memory_and_alignment_complete : forall module C0 memarg natural m,
  mems_agree module C0 ->
  lookup_N (tc_mems C0) 0%N = Some m ->
  to_Z memarg.(opiter_MemArg_align) <= to_Z natural ->
  opiter_check_memory_and_alignment module memarg natural
    = Ok (Core_result_Result_Ok tt).
Proof.
  intros module C0 memarg natural m Hag Hlk Hle.
  unfold opiter_check_memory_and_alignment.
  rewrite (require_memory_complete module C0 m Hag Hlk). cbn [bind].
  rewrite branch_ok. cbn [bind].
  destruct (memarg.(opiter_MemArg_align) s> natural) eqn:Hgt; [|reflexivity].
  exfalso. apply scalar_gtb_true in Hgt. lia.
Qed.
