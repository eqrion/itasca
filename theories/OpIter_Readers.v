(** * The readers accept what the checker accepts

    One lemma per reader, each the converse of a step lemma: instead of "the
    reader succeeded, so the checker would too", it says "the checker accepts, so
    the reader succeeds". Together with the decoders' completeness in
    [OpIter_Decode.v] these are everything the dispatch needs, because a reader's
    only failure modes are a decode failure, a pop that finds the wrong type, and
    a check the checker also makes.

 *)

Require Import Primitives.
Import Primitives.
Require Import Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Import Itasca.Aeneas_Specs.
Require Import Itasca.Translate.
Require Import Itasca.Spec_Binary.
Require Import Itasca.OpIter_Visit.
Require Import Itasca.OpIter_State.
Require Import Itasca.OpIter_Decode.
Require Import Itasca.OpIter_Sim.
Require Import Itasca.OpIter_Checker.

From Wasm Require Import datatypes numerics type_checker operations typing.

(* Mathcomp is not imported here, so [++] is [List.app] and [rewrite <-] works.
   Binding the type keeps it that way despite mathcomp's own [Bind Scope]. *)
Local Open Scope list_scope.
Local Bind Scope list_scope with list.
Open Scope Z_scope.

Lemma room_fit : forall st, room st -> Z.of_nat (stack_size st) <= usize_max.
Proof. intros st H. unfold room in H. lia. Qed.

Lemma pop_stack_type_fit : forall st r st',
  Z.of_nat (stack_size st) <= usize_max ->
  code_pop_stack_type st = Ok (r, st') ->
  Z.of_nat (stack_size st') <= usize_max.
Proof.
  intros st r st' Hfit Hpop.
  pose proof (pop_stack_type_size st r st' Hpop). lia.
Qed.

Lemma pop_with_type_fit : forall st vt r st',
  Z.of_nat (stack_size st) <= usize_max ->
  code_pop_with_type st vt = Ok (r, st') ->
  Z.of_nat (stack_size st') <= usize_max.
Proof.
  intros st vt r st' Hfit Hpop.
  pose proof (pop_with_type_size st vt r st' Hpop). lia.
Qed.

(* ================================================================== *)
(** ** The readers with no immediates                                   *)
(* ================================================================== *)

Lemma read_unreachable_complete : forall st,
  room st ->
  exists st', code_read_unreachable st = Ok (Core_result_Result_Ok tt, st').
Proof.
  intros st Hroom. unfold code_read_unreachable.
  destruct (mark_unreachable_total st (room_fit st Hroom)) as [st1 Hmu].
  rewrite Hmu. cbn [bind]. exists st1. reflexivity.
Qed.

(** [drop]'s only failure is an exhausted frame that is not unreachable, which is
    exactly when [type_update_drop] returns [None]. *)
Lemma drop_disj : forall f ct',
  type_update_drop (fv_ct f) = Some ct' ->
  fv_seg f <> [] \/ (fv_ctrl f).(code_Ctrl_polymorphic_base) = true.
Proof.
  intros f ct' H.
  assert (Hcase : fv_seg f = [] \/ fv_seg f <> []).
  { destruct (fv_seg f); [left; reflexivity | right; discriminate]. }
  destruct Hcase as [Hnil|Hne]; [|left; exact Hne]. right.
  unfold type_update_drop, fv_ct in H. rewrite Hnil in H.
  cbn [translate_vals List.map List.rev CT_type CT_unr] in H.
  destruct ((fv_ctrl f).(code_Ctrl_polymorphic_base));
    [reflexivity | discriminate].
Qed.

Lemma read_drop_complete : forall C0 st pre f ct',
  Inv C0 st (pre ++ [f]) ->
  type_update_drop (fv_ct f) = Some ct' ->
  room st ->
  exists t st', code_read_drop st = Ok (Core_result_Result_Ok t, st').
Proof.
  intros C0 st pre f ct' Hinv Hdrop Hroom. unfold code_read_drop.
  destruct (Inv_split C0 st pre f Hinv) as [Hbase [Hsplit Hunr]].
  destruct (pop_stack_type_complete st (List.concat (List.map fv_seg pre)) f
              Hsplit Hbase Hunr (room_fit st Hroom)
              (drop_disj f ct' Hdrop)) as [t [st1 Hps]].
  exists t, st1. exact Hps.
Qed.

(* ================================================================== *)
(** ** select                                                          *)
(* ================================================================== *)

(** The plumbing, so the four segment shapes below differ only in how they
    supply the three pops and the join. *)
Lemma read_select_of_pops : forall st t1 st1 t2 st2 t3 st3 t,
  code_pop_with_type st Types_ValueType_I32
    = Ok (Core_result_Result_Ok t1, st1) ->
  code_pop_stack_type st1 = Ok (Core_result_Result_Ok t2, st2) ->
  code_pop_stack_type st2 = Ok (Core_result_Result_Ok t3, st3) ->
  code_join_stack_type t2 t3 = Ok (Core_result_Result_Ok t) ->
  room st ->
  exists st4, code_read_select st = Ok (Core_result_Result_Ok t, st4).
Proof.
  intros st t1 st1 t2 st2 t3 st3 t Hq1 Hq2 Hq3 Hj Hroom.
  destruct (push_val_total st3 t) as [st4 Hpv].
  { apply room_vals.
    pose proof (pop_with_type_size st _ _ st1 Hq1) as Hs1.
    pose proof (pop_stack_type_size st1 _ st2 Hq2) as Hs2.
    pose proof (pop_stack_type_size st2 _ st3 Hq3) as Hs3.
    unfold room in Hroom |- *. lia. }
  exists st4. unfold code_read_select.
  rewrite Hq1. cbn [bind]. rewrite branch_ok. cbn [bind].
  rewrite Hq2. cbn [bind]. rewrite branch_ok. cbn [bind].
  rewrite Hq3. cbn [bind]. rewrite branch_ok. cbn [bind].
  rewrite Hj. cbn [bind]. rewrite branch_ok. cbn [bind].
  rewrite Hpv. cbn [bind]. reflexivity.
Qed.

(** Re-associating a two- or three-element tail, so [List.app_inj_tail]
    applies. *)
Lemma snoc3_split : forall {A} (s : list A) z y x,
  s ++ [z; y; x] = (s ++ [z; y]) ++ [x].
Proof. intros A s z y x. rewrite <- List.app_assoc. reflexivity. Qed.

Lemma snoc2_split : forall {A} (s : list A) z y,
  s ++ [z; y] = (s ++ [z]) ++ [y].
Proof. intros A s z y. rewrite <- List.app_assoc. reflexivity. Qed.

(** The two shapes with nothing below the condition. Both values come off [Bot]
    and the join is [Bot], which is the one way a [Bot] reaches the operand
    stack. *)
Lemma select_no_operands : forall st pre f t1 st1,
  code_pop_with_type st Types_ValueType_I32
    = Ok (Core_result_Result_Ok t1, st1) ->
  cur_base_nat st = List.length (List.concat (List.map fv_seg pre)) ->
  cur_unr st = (fv_ctrl f).(code_Ctrl_polymorphic_base) ->
  vals_list st1.(code_OpIterState_vals)
    = List.concat (List.map fv_seg pre) ++ [] ->
  cur_base_nat st1 = cur_base_nat st ->
  cur_unr st1 = cur_unr st ->
  (fv_ctrl f).(code_Ctrl_polymorphic_base) = true ->
  room st ->
  exists t st', code_read_select st = Ok (Core_result_Result_Ok t, st').
Proof.
  intros st pre f t1 st1 Hq1 Hbase1 Hunr1 Hv2 Hb2 Hu2 Hu Hroom.
  assert (Hq2 : code_pop_stack_type st1
                = Ok (Core_result_Result_Ok Code_StackType_Bot, st1)).
  { apply (pop_stack_type_empty st1 (List.concat (List.map fv_seg pre))
             {| fv_ctrl := fv_ctrl f; fv_seg := [];
                  fv_done := []; fv_then := [] |}).
    - cbn [fv_seg]. exact Hv2.
    - cbn [fv_ctrl]. rewrite Hb2. exact Hbase1.
    - cbn [fv_ctrl]. rewrite Hu2. exact Hunr1.
    - exact (pop_with_type_fit st _ _ st1 (room_fit st Hroom) Hq1).
    - reflexivity.
    - cbn [fv_ctrl]. exact Hu. }
  destruct (join_stack_type_bot_l_ok Code_StackType_Bot) as [t Hj].
  exists t.
  destruct (read_select_of_pops st t1 st1 Code_StackType_Bot st1
              Code_StackType_Bot st1 t Hq1 Hq2 Hq2 Hj Hroom)
    as [st4 Hrd].
  exists st4. exact Hrd.
Qed.

Lemma read_select_complete : forall C0 st pre f ct',
  Inv C0 st (pre ++ [f]) ->
  type_update_select (fv_ct f) None = Some ct' ->
  room st ->
  exists t st', code_read_select st = Ok (Core_result_Result_Ok t, st').
Proof.
  intros C0 st pre f ct' Hinv Hsel Hroom.
  destruct (Inv_split C0 st pre f Hinv) as [Hbase1 [Hsplit1 Hunr1]].
  destruct (select_disj f ct' Hsel) as [[ct1 Hcons] Hshape].
  (* the condition, the one pop the checker types *)
  destruct (pop_with_type_complete st (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 ct1 Hsplit1 Hbase1 Hunr1
              (room_fit st Hroom) Hcons)
    as [t1 [st1 Hq1]].
  destruct (pop_with_type_ok st _ t1 st1 Hq1) as [Hraw1 _].
  destruct (pop_stack_type_sim st (List.concat (List.map fv_seg pre)) f
              t1 st1 Hsplit1 Hbase1 Hunr1 Hraw1) as [seg1 [Hc2 [Hv2 D1]]].
  destruct (cur_views_ctrls st st1 Hc2) as [Hb2 Hu2].
  destruct Hshape as [[s [z [y [x [Hs Hjoin]]]]]
                     |[[[y [x Hs]] Hu]
                     | [[Hs | [x Hs]] Hu]]].
  - (* three or more visible, so both values are real and have to agree *)
    assert (Hseg1 : seg1 = s ++ [z; y]).
    { destruct D1 as [HL | [HR1 _]].
      - rewrite Hs in HL. rewrite snoc3_split in HL.
        apply List.app_inj_tail in HL as [HL _]. symmetry. exact HL.
      - exfalso. rewrite Hs in HR1. destruct s; discriminate HR1. }
    destruct (pop_stack_type_real st1 (List.concat (List.map fv_seg pre))
                {| fv_ctrl := fv_ctrl f; fv_seg := seg1;
                  fv_done := []; fv_then := [] |}
                (s ++ [z]) y) as [st2 [Hq2 [Hc3 Hv3]]].
    { cbn [fv_seg]. exact Hv2. }
    { cbn [fv_ctrl]. rewrite Hb2. exact Hbase1. }
    { cbn [fv_ctrl]. rewrite Hu2. exact Hunr1. }
    { exact (pop_with_type_fit st _ _ st1 (room_fit st Hroom) Hq1). }
    { cbn [fv_seg]. rewrite Hseg1. apply snoc2_split. }
    destruct (cur_views_ctrls st1 st2 Hc3) as [Hb3 Hu3].
    destruct (pop_stack_type_real st2 (List.concat (List.map fv_seg pre))
                {| fv_ctrl := fv_ctrl f; fv_seg := s ++ [z];
                  fv_done := []; fv_then := [] |}
                s z) as [st3 [Hq3 [Hc4 Hv4]]].
    { cbn [fv_seg]. exact Hv3. }
    { cbn [fv_ctrl]. rewrite Hb3. rewrite Hb2. exact Hbase1. }
    { cbn [fv_ctrl]. rewrite Hu3. rewrite Hu2. exact Hunr1. }
    { exact (pop_stack_type_fit st1 (Core_result_Result_Ok y) st2
               (pop_with_type_fit st _ _ st1 (room_fit st Hroom) Hq1) Hq2). }
    { cbn [fv_seg]. reflexivity. }
    destruct Hjoin as [t Hj].
    exists t.
    destruct (read_select_of_pops st t1 st1 y st2 z st3 t Hq1 Hq2 Hq3 Hj
                Hroom) as [st4 Hrd].
    exists st4. exact Hrd.
  - (* exactly two, so the first value comes off Bot and the join keeps the
       second *)
    assert (Hseg1 : seg1 = [y]).
    { destruct D1 as [HL | [HR1 _]].
      - rewrite Hs in HL. change [y; x] with ([y] ++ [x]) in HL.
        apply List.app_inj_tail in HL as [HL _]. symmetry. exact HL.
      - exfalso. rewrite Hs in HR1. discriminate HR1. }
    destruct (pop_stack_type_real st1 (List.concat (List.map fv_seg pre))
                {| fv_ctrl := fv_ctrl f; fv_seg := seg1;
                  fv_done := []; fv_then := [] |}
                [] y) as [st2 [Hq2 [Hc3 Hv3]]].
    { cbn [fv_seg]. exact Hv2. }
    { cbn [fv_ctrl]. rewrite Hb2. exact Hbase1. }
    { cbn [fv_ctrl]. rewrite Hu2. exact Hunr1. }
    { exact (pop_with_type_fit st _ _ st1 (room_fit st Hroom) Hq1). }
    { cbn [fv_seg]. rewrite Hseg1. reflexivity. }
    destruct (cur_views_ctrls st1 st2 Hc3) as [Hb3 Hu3].
    assert (Hq3 : code_pop_stack_type st2
                  = Ok (Core_result_Result_Ok Code_StackType_Bot, st2)).
    { apply (pop_stack_type_empty st2 (List.concat (List.map fv_seg pre))
               {| fv_ctrl := fv_ctrl f; fv_seg := [];
                  fv_done := []; fv_then := [] |}).
      - cbn [fv_seg]. exact Hv3.
      - cbn [fv_ctrl]. rewrite Hb3. rewrite Hb2. exact Hbase1.
      - cbn [fv_ctrl]. rewrite Hu3. rewrite Hu2. exact Hunr1.
      - exact (pop_stack_type_fit st1 (Core_result_Result_Ok y) st2
                 (pop_with_type_fit st _ _ st1 (room_fit st Hroom) Hq1) Hq2).
      - reflexivity.
      - cbn [fv_ctrl]. exact Hu. }
    destruct (join_stack_type_bot_r_ok y) as [t Hj].
    exists t.
    destruct (read_select_of_pops st t1 st1 y st2 Code_StackType_Bot st2 t
                Hq1 Hq2 Hq3 Hj Hroom) as [st4 Hrd].
    exists st4. exact Hrd.
  - (* nothing visible at all *)
    assert (Hseg1 : seg1 = []).
    { destruct D1 as [HL | [_ [HR2 _]]].
      - rewrite Hs in HL. destruct seg1; [reflexivity | discriminate HL].
      - exact HR2. }
    rewrite Hseg1 in Hv2.
    apply (select_no_operands st pre f t1 st1
             Hq1 Hbase1 Hunr1 Hv2 Hb2 Hu2 Hu Hroom).
  - (* only the condition was visible *)
    assert (Hseg1 : seg1 = []).
    { destruct D1 as [HL | [_ [HR2 _]]].
      - rewrite Hs in HL. change [x] with (@nil code_StackType_t ++ [x]) in HL.
        apply List.app_inj_tail in HL as [HL _]. symmetry. exact HL.
      - exact HR2. }
    rewrite Hseg1 in Hv2.
    apply (select_no_operands st pre f t1 st1
             Hq1 Hbase1 Hunr1 Hv2 Hb2 Hu2 Hu Hroom).
Qed.

Lemma read_binary_complete : forall C0 st pre f ty res ct',
  Inv C0 st (pre ++ [f]) ->
  consume (fv_ct f) [translate_vt_v ty; translate_vt_v ty] = Some ct' ->
  room st ->
  exists st', code_read_binary st ty res
                = Ok (Core_result_Result_Ok tt, st').
Proof.
  intros C0 st pre f ty res ct' Hinv Hcon Hroom.
  unfold code_read_binary.
  destruct (Inv_split C0 st pre f Hinv) as [Hbase1 [Hsplit1 Hunr1]].
  destruct (consume_cons_inv (fv_ct f) (translate_vt_v ty)
              [translate_vt_v ty] ct' Hcon) as [ct1 [Hcon1 Hcon2]].
  (* first pop *)
  destruct (pop_with_type_complete st (List.concat (List.map fv_seg pre)) f
              ty ct1 Hsplit1 Hbase1 Hunr1
              (room_fit st Hroom) Hcon1)
    as [t1 [st1 Hp1]].
  rewrite Hp1. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (pop_with_type_sim st (List.concat (List.map fv_seg pre)) f
              ty t1 st1 Hsplit1 Hbase1 Hunr1 Hp1) as [seg1 [Hc2 [Hv2 Hsim1]]].
  (* the frame with the shortened segment, which is what the second pop sees *)
  destruct (cur_views_ctrls st st1 Hc2) as [Hb2 Hu2].
  assert (Hct1 : ct1 = <<translate_vals seg1,
                         (fv_ctrl f).(code_Ctrl_polymorphic_base)>>).
  { pose proof Hsim1 as Hs. rewrite Hcon1 in Hs. injection Hs as Hs. exact Hs. }
  rewrite Hct1 in Hcon2.
  (* second pop *)
  destruct (pop_with_type_complete st1 (List.concat (List.map fv_seg pre))
              {| fv_ctrl := fv_ctrl f; fv_seg := seg1;
                  fv_done := fv_done f; fv_then := fv_then f |}
              ty ct') as [t2 [st2 Hp2]].
  { cbn [fv_seg]. exact Hv2. }
  { cbn [fv_ctrl]. rewrite Hb2. exact Hbase1. }
  { cbn [fv_ctrl]. rewrite Hu2. exact Hunr1. }
  { exact (pop_with_type_fit st _ _ st1 (room_fit st Hroom) Hp1). }
  { cbn [fv_ct fv_seg fv_ctrl]. exact Hcon2. }
  rewrite Hp2. cbn [bind]. rewrite branch_ok. cbn [bind].
  (* the push *)
  destruct (push_val_total st2 (Code_StackType_Val res)) as [st3 Hpv].
  { apply room_vals.
    pose proof (pop_with_type_size st ty _ st1 Hp1) as Hs1.
    pose proof (pop_with_type_size st1 ty _ st2 Hp2) as Hs2.
    unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. exists st3. reflexivity.
Qed.

Lemma read_conversion_complete : forall C0 st pre f from to ct',
  Inv C0 st (pre ++ [f]) ->
  consume (fv_ct f) [translate_vt_v from] = Some ct' ->
  room st ->
  exists st', code_read_conversion st from to
                = Ok (Core_result_Result_Ok tt, st').
Proof.
  intros C0 st pre f from to ct' Hinv Hcon Hroom.
  unfold code_read_conversion.
  destruct (Inv_split C0 st pre f Hinv) as [Hbase1 [Hsplit1 Hunr1]].
  destruct (pop_with_type_complete st (List.concat (List.map fv_seg pre)) f
              from ct' Hsplit1 Hbase1 Hunr1
              (room_fit st Hroom) Hcon)
    as [t1 [st1 Hp1]].
  rewrite Hp1. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (push_val_total st1 (Code_StackType_Val to)) as [st2 Hpv].
  { apply room_vals.
    pose proof (pop_with_type_size st from _ st1 Hp1) as Hs1.
    unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. exists st2. reflexivity.
Qed.

(* ================================================================== *)
(** ** The readers with immediates                                      *)
(* ================================================================== *)

Lemma read_i32_const_complete : forall st data z rest,
  repr_s32 (bytes_from data st.(code_OpIterState_pos)) z rest ->
  room st ->
  exists v st', code_read_i32_const st data
                  = Ok (Core_result_Result_Ok v, st')
                /\ to_Z v = z.
Proof.
  intros st data z rest Hrep Hroom.
  unfold code_read_i32_const.
  destruct (read_s32_leb_complete data st.(code_OpIterState_pos) z rest Hrep)
    as [v [p1 [Hleb [Hval Hrest]]]].
  rewrite Hleb. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (push_val_total
              {| code_OpIterState_vals := st.(code_OpIterState_vals);
                 code_OpIterState_ctrls := st.(code_OpIterState_ctrls);
                 code_OpIterState_pos := p1 |}
              (Code_StackType_Val Types_ValueType_I32)) as [st1 Hpv].
  { cbn [code_OpIterState_vals]. apply room_vals. exact Hroom. }
  rewrite Hpv. cbn [bind]. exists v, st1. split; [reflexivity|].
  exact Hval.
Qed.

Lemma read_f32_const_complete : forall st data z rest,
  repr_bytes_le 4 (bytes_from data st.(code_OpIterState_pos)) z rest ->
  room st ->
  exists v st', code_read_f32_const st data
                  = Ok (Core_result_Result_Ok v, st')
                /\ to_Z v = z.
Proof.
  intros st data z rest Hrep Hroom.
  unfold code_read_f32_const.
  destruct (read_f32_bits_complete data st.(code_OpIterState_pos) z rest Hrep)
    as [v [p1 [Hleb [Hval Hrest]]]].
  rewrite Hleb. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (push_val_total
              {| code_OpIterState_vals := st.(code_OpIterState_vals);
                 code_OpIterState_ctrls := st.(code_OpIterState_ctrls);
                 code_OpIterState_pos := p1 |}
              (Code_StackType_Val Types_ValueType_F32)) as [st1 Hpv].
  { cbn [code_OpIterState_vals]. apply room_vals. exact Hroom. }
  rewrite Hpv. cbn [bind]. exists v, st1. split; [reflexivity|].
  exact Hval.
Qed.

Lemma read_f64_const_complete : forall st data z rest,
  repr_bytes_le 8 (bytes_from data st.(code_OpIterState_pos)) z rest ->
  room st ->
  exists v st', code_read_f64_const st data
                  = Ok (Core_result_Result_Ok v, st')
                /\ to_Z v = z.
Proof.
  intros st data z rest Hrep Hroom.
  unfold code_read_f64_const.
  destruct (read_f64_bits_complete data st.(code_OpIterState_pos) z rest Hrep)
    as [v [p1 [Hleb [Hval Hrest]]]].
  rewrite Hleb. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (push_val_total
              {| code_OpIterState_vals := st.(code_OpIterState_vals);
                 code_OpIterState_ctrls := st.(code_OpIterState_ctrls);
                 code_OpIterState_pos := p1 |}
              (Code_StackType_Val Types_ValueType_F64)) as [st1 Hpv].
  { cbn [code_OpIterState_vals]. apply room_vals. exact Hroom. }
  rewrite Hpv. cbn [bind]. exists v, st1. split; [reflexivity|].
  exact Hval.
Qed.

Lemma read_i64_const_complete : forall st data z rest,
  repr_sN 64 (bytes_from data st.(code_OpIterState_pos)) z rest ->
  room st ->
  exists v st', code_read_i64_const st data
                  = Ok (Core_result_Result_Ok v, st')
                /\ to_Z v = z.
Proof.
  intros st data z rest Hrep Hroom.
  unfold code_read_i64_const.
  destruct (read_s64_leb_complete data st.(code_OpIterState_pos) z rest Hrep)
    as [v [p1 [Hleb [Hval Hrest]]]].
  rewrite Hleb. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (push_val_total
              {| code_OpIterState_vals := st.(code_OpIterState_vals);
                 code_OpIterState_ctrls := st.(code_OpIterState_ctrls);
                 code_OpIterState_pos := p1 |}
              (Code_StackType_Val Types_ValueType_I64)) as [st1 Hpv].
  { cbn [code_OpIterState_vals]. apply room_vals. exact Hroom. }
  rewrite Hpv. cbn [bind]. exists v, st1. split; [reflexivity|].
  exact Hval.
Qed.

(** [block] and [loop] differ only in the kind they push, so the two proofs are
    the same modulo that argument. *)
Lemma read_block_complete : forall st data bb bt rest,
  bytes_from data st.(code_OpIterState_pos) = bb :: rest ->
  blocktype_spec bb = Some bt ->
  room st ->
  exists bt' st', code_read_block st data
                    = Ok (Core_result_Result_Ok bt', st')
                  /\ translate_bt bt' = bt.
Proof.
  intros st data bb bt rest Hbs Hspec Hroom.
  unfold code_read_block.
  destruct (read_block_type_complete data st.(code_OpIterState_pos) bb bt rest
              Hbs Hspec) as [bt' [p1 [Hrbt [Htr Hrest]]]].
  rewrite Hrbt. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (push_ctrl_total
              {| code_OpIterState_vals := st.(code_OpIterState_vals);
                 code_OpIterState_ctrls := st.(code_OpIterState_ctrls);
                 code_OpIterState_pos := p1 |}
              Code_LabelKind_Block bt') as [st1 Hpc].
  { cbn [code_OpIterState_vals].
    pose proof (room_vals st Hroom). lia. }
  { cbn [code_OpIterState_ctrls]. apply room_ctrls. exact Hroom. }
  rewrite Hpc. cbn [bind]. exists bt', st1.
  split; [reflexivity | exact Htr].
Qed.

Lemma read_loop_complete : forall st data bb bt rest,
  bytes_from data st.(code_OpIterState_pos) = bb :: rest ->
  blocktype_spec bb = Some bt ->
  room st ->
  exists bt' st', code_read_loop st data
                    = Ok (Core_result_Result_Ok bt', st')
                  /\ translate_bt bt' = bt.
Proof.
  intros st data bb bt rest Hbs Hspec Hroom.
  unfold code_read_loop.
  destruct (read_block_type_complete data st.(code_OpIterState_pos) bb bt rest
              Hbs Hspec) as [bt' [p1 [Hrbt [Htr Hrest]]]].
  rewrite Hrbt. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (push_ctrl_total
              {| code_OpIterState_vals := st.(code_OpIterState_vals);
                 code_OpIterState_ctrls := st.(code_OpIterState_ctrls);
                 code_OpIterState_pos := p1 |}
              Code_LabelKind_Loop bt') as [st1 Hpc].
  { cbn [code_OpIterState_vals].
    pose proof (room_vals st Hroom). lia. }
  { cbn [code_OpIterState_ctrls]. apply room_ctrls. exact Hroom. }
  rewrite Hpc. cbn [bind]. exists bt', st1.
  split; [reflexivity | exact Htr].
Qed.

(** [if] is [block] plus the condition pop, so it needs the frame the condition
    comes off and the [consume] the checker performed for it. *)
Lemma read_if_complete : forall C0 st pre f data bb bt rest ct',
  Inv C0 st (pre ++ [f]) ->
  bytes_from data st.(code_OpIterState_pos) = bb :: rest ->
  blocktype_spec bb = Some bt ->
  consume (fv_ct f) [T_num T_i32] = Some ct' ->
  room st ->
  exists bt' st', code_read_if st data = Ok (Core_result_Result_Ok bt', st')
                  /\ translate_bt bt' = bt.
Proof.
  intros C0 st pre f data bb bt rest ct' Hinv Hbs Hspec Hcon Hroom.
  unfold code_read_if.
  destruct (read_block_type_complete data st.(code_OpIterState_pos) bb bt rest
              Hbs Hspec) as [bt' [p1 [Hrbt [Htr Hrest]]]].
  rewrite Hrbt. cbn [bind]. rewrite branch_ok. cbn [bind].
  (* the cursor moved past the block type byte; nothing else did *)
  set (st1 := {| code_OpIterState_vals := st.(code_OpIterState_vals);
                 code_OpIterState_ctrls := st.(code_OpIterState_ctrls);
                 code_OpIterState_pos := p1 |}).
  assert (Hinv2 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_fields C0 st st1 _ (eq_refl _) (eq_refl _) Hinv)).
  destruct (Inv_split C0 st1 pre f Hinv2) as [Hbase2 [Hsplit2 Hunr2]].
  destruct (pop_with_type_complete st1 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 ct' Hsplit2 Hbase2 Hunr2
              (room_fit st Hroom) Hcon)
    as [t1 [st2 Hp1]].
  rewrite Hp1. cbn [bind]. rewrite branch_ok. cbn [bind].
  assert (Hroom2 : room st2).
  { apply (room_le st st2); [|exact Hroom].
    pose proof (pop_with_type_size st1 _ _ st2 Hp1) as Hs2.
    assert (Hs1 : stack_size st1 = stack_size st) by reflexivity. lia. }
  destruct (push_ctrl_total st2 Code_LabelKind_Then bt') as [st3 Hpc].
  { pose proof (room_vals st2 Hroom2). lia. }
  { exact (room_ctrls st2 Hroom2). }
  rewrite Hpc. cbn [bind]. exists bt', st3.
  split; [reflexivity | exact Htr].
Qed.

Lemma pop_block_results_complete : forall st pre f bt ct',
  vals_list st.(code_OpIterState_vals) = pre ++ fv_seg f ->
  cur_base_nat st = List.length pre ->
  cur_unr st = (fv_ctrl f).(code_Ctrl_polymorphic_base) ->
  Z.of_nat (stack_size st) <= usize_max ->
  consume (fv_ct f) (translate_typelist (block_results_of bt)) = Some ct' ->
  exists st', code_pop_block_results st bt
                = Ok (Core_result_Result_Ok tt, st').
Proof.
  intros st pre f bt ct' Hsplit Hbase Hunr Hfit Hcon.
  destruct bt as [|vt].
  - exists st. reflexivity.
  - cbn [block_results_of translate_typelist] in Hcon.
    destruct (pop_with_type_complete st pre f vt ct' Hsplit Hbase Hunr
                Hfit Hcon) as [t [st' Hpop]].
    exists st'. unfold code_pop_block_results. rewrite Hpop. cbn [bind].
    rewrite branch_ok. cbn [bind]. reflexivity.
Qed.

(** [else] closes the then-branch, which is [end]'s obligation over the same
    frame, and rewrites it in place rather than popping. The frame must be an
    open then-branch, which the caller learns from the operator stream: only an
    [if] puts an [FO_else] there. *)
Lemma read_else_complete : forall C0 st pre g,
  Inv C0 st (pre ++ [g]) ->
  (fv_ctrl g).(code_Ctrl_kind) = Code_LabelKind_Then ->
  c_types_agree (fv_ct g)
    (translate_typelist (block_results_of (fv_ctrl g).(code_Ctrl_block_type)))
    = true ->
  room st ->
  exists bt st', code_read_else st = Ok (Core_result_Result_Ok bt, st').
Proof.
  intros C0 st pre g Hinv Hkind Hagree Hroom.
  unfold code_read_else.
  assert (Hsnoc : ctrls_list st.(code_OpIterState_ctrls)
                  = List.map fv_ctrl pre ++ [fv_ctrl g]).
  { destruct Hinv as [K1 _]. rewrite K1. rewrite List.map_app. reflexivity. }
  destruct (Inv_split C0 st pre g Hinv) as [Hbase [Hsplit Hunr]].
  assert (Hgbase : Z.to_nat (to_Z (fv_ctrl g).(code_Ctrl_value_stack_base))
                   = List.length (List.concat (List.map fv_seg pre))).
  { unfold cur_base_nat in Hbase.
    rewrite (cur_ctrl_snoc st (List.map fv_ctrl pre) (fv_ctrl g) Hsnoc)
      in Hbase. exact Hbase. }
  destruct (ctrls_stack_len_total st.(code_OpIterState_ctrls)
              ltac:(pose proof (room_ctrls st Hroom); lia)) as [n Hlen].
  rewrite Hlen. cbn [bind].
  assert (Hnz : (n s= 0%usize) = false).
  { unfold scalar_eqb. apply Z.eqb_neq.
    rewrite (ctrls_stack_len_spec _ _ Hlen). rewrite Hsnoc.
    rewrite List.app_length. cbn [List.length].
    assert (H0 : to_Z 0%usize = 0) by reflexivity. lia. }
  rewrite Hnz. cbn beta iota.
  apply scalar_eqb_false in Hnz.
  assert (H0 : to_Z 0%usize = 0) by reflexivity. rewrite H0 in Hnz.
  destruct (usize_sub_1_ok n ltac:(pose proof (usize_nonneg n); lia))
    as [i [Hsub Hival]].
  rewrite Hsub. cbn [bind].
  assert (Hlt : (Z.to_nat (to_Z i)
                 < List.length (ctrls_list st.(code_OpIterState_ctrls)))%nat).
  { rewrite (ctrls_last_index_len st (List.map fv_ctrl pre) (fv_ctrl g)
               n i Hsnoc Hlen Hsub), Hsnoc, List.app_length.
    cbn. lia. }
  destruct (ctrls_stack_get_total _ i Hlt) as [frame Hget].
  rewrite Hget. cbn [bind].
  pose proof (ctrls_stack_get_spec _ i frame Hlt Hget) as Hnth.
  rewrite (ctrls_last_index st (List.map fv_ctrl pre) (fv_ctrl g)
             n i Hsnoc Hlen Hsub) in Hnth.
  injection Hnth as <-.
  cbn [bind].
  (* the frame is an open then-branch, so the guard passes *)
  destruct (is_then_total (fv_ctrl g).(code_Ctrl_kind)) as [bth Hit].
  rewrite Hit. cbn [bind].
  destruct (is_then_spec _ _ Hit) as [[Hbth _] | [_ Hne]];
    [|exfalso; apply Hne; exact Hkind].
  rewrite Hbth. cbn beta iota.
  destruct (consume_of_c_types_agree _ (fv_ct g) Hagree) as [unr Hcon0].
  destruct (pop_block_results_complete st (List.concat (List.map fv_seg pre)) g
              (fv_ctrl g).(code_Ctrl_block_type) <<[], unr>>
              Hsplit Hbase Hunr (room_fit st Hroom) Hcon0)
    as [st1 Hpt].
  rewrite Hpt. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (pop_block_results_sim st (List.concat (List.map fv_seg pre)) g
              (fv_ctrl g).(code_Ctrl_block_type) st1 Hsplit Hbase Hunr Hpt)
    as [seg' [Hc2 [Hv2 Hcon]]].
  assert (Hempty : seg' = []).
  { apply translate_vals_nil_inv.
    pose proof Hcon as Hc'. rewrite Hcon0 in Hc'.
    apply (f_equal (fun o => match o with
                             | Some ct => CT_type ct
                             | None => [] end)) in Hc'.
    cbn in Hc'. symmetry. exact Hc'. }
  rewrite Hempty in Hv2.
  pose proof (pop_block_results_size st _ _ st1 Hpt) as Hsize1.
  destruct (vals_stack_len_total st1.(code_OpIterState_vals)
              ltac:(assert (Hfit1 : Z.of_nat (stack_size st1) <= usize_max)
                      by (apply Nat2Z.inj_le in Hsize1;
                          pose proof (room_fit st Hroom); lia);
                    unfold stack_size in Hfit1;
                    rewrite Nat2Z.inj_add in Hfit1; lia)) as [nv Hvlen].
  rewrite Hvlen. cbn [bind].
  assert (Hne2 : (nv s<> (fv_ctrl g).(code_Ctrl_value_stack_base)) = false).
  { unfold scalar_neqb, scalar_eqb. apply Bool.negb_false_iff. apply Z.eqb_eq.
    rewrite (vals_stack_len_spec _ _ Hvlen). rewrite Hv2. rewrite List.app_nil_r.
    pose proof (usize_nonneg (fv_ctrl g).(code_Ctrl_value_stack_base)). lia. }
  rewrite Hne2. cbn beta iota.
  (* the two in-place rewrites of the frame, as in [step_switch_else] *)
  assert (Hsnoc2 : ctrls_list st1.(code_OpIterState_ctrls)
                   = List.map fv_ctrl pre ++ [fv_ctrl g])
    by (rewrite Hc2; exact Hsnoc).
  assert (Hidxlen : Z.to_nat (to_Z i) = List.length (List.map fv_ctrl pre))
    by (apply (ctrls_last_index_len st (List.map fv_ctrl pre) (fv_ctrl g) n i
                 Hsnoc Hlen Hsub)).
  assert (Hidxlen2 : (Z.to_nat (to_Z i)
                      < List.length (ctrls_list st1.(code_OpIterState_ctrls)))%nat).
  { rewrite Hsnoc2. rewrite List.app_length. cbn [List.length].
    rewrite Hidxlen. lia. }
  set (mid := {| code_Ctrl_kind := Code_LabelKind_Else;
                 code_Ctrl_block_type := (fv_ctrl g).(code_Ctrl_block_type);
                 code_Ctrl_value_stack_base :=
                   (fv_ctrl g).(code_Ctrl_value_stack_base);
                 code_Ctrl_polymorphic_base := false |} : code_Ctrl_t).
  destruct (ctrls_stack_set_total st1.(code_OpIterState_ctrls) i mid Hidxlen2)
    as [cs Hset].
  rewrite Hset. cbn [bind].
  eexists. eexists. reflexivity.
Qed.

Definition read_end_tail (st : code_OpIterState_t) (frame : code_Ctrl_t)
                         (i : usize) :=
  p <- code_pop_block_results st frame.(code_Ctrl_block_type);
  let (r, st1) := p in
  cf <-
    core_result_Result_Insts_CoreOpsTry_traitTryTResultInfallibleE_branch r;
  match cf with
  | Core_ops_control_flow_ControlFlow_Continue _ =>
      n <- code_ValsStack_len st1.(code_OpIterState_vals);
      if n s<> frame.(code_Ctrl_value_stack_base)
      then Ok (Core_result_Result_Err Error_OpError_StackMismatch, st1)
      else
        p2 <- code_CtrlsStack_pop st1.(code_OpIterState_ctrls);
        let (_, cs) := p2 in
        st2 <- code_push_block_results
          {| code_OpIterState_vals := st1.(code_OpIterState_vals);
             code_OpIterState_ctrls := cs;
             code_OpIterState_pos := st1.(code_OpIterState_pos) |}
          frame.(code_Ctrl_block_type);
        Ok (Core_result_Result_Ok
              (frame.(code_Ctrl_kind), frame.(code_Ctrl_block_type)), st2)
  | Core_ops_control_flow_ControlFlow_Break residual =>
      r1 <-
        core_result_Result_Insts_CoreOpsTry_traitFromResidualResultInfallibleE_from_residual
          (code_LabelKind_t * code_BlockType_t)
          (core_convert_From_Blanket error_OpError_t) residual;
      Ok (r1, st1)
  end.

Lemma read_end_tail_complete : forall C0 st pre g i,
  Inv C0 st (pre ++ [g]) ->
  c_types_agree (fv_ct g)
    (translate_typelist (block_results_of (fv_ctrl g).(code_Ctrl_block_type)))
    = true ->
  room st ->
  exists r st', read_end_tail st (fv_ctrl g) i
                  = Ok (Core_result_Result_Ok r, st').
Proof.
  intros C0 st pre g i Hinv Hagree Hroom.
  unfold read_end_tail.
  assert (Hsnoc : ctrls_list st.(code_OpIterState_ctrls)
                  = List.map fv_ctrl pre ++ [fv_ctrl g]).
  { destruct Hinv as [K1 _]. rewrite K1. rewrite List.map_app. reflexivity. }
  destruct (Inv_split C0 st pre g Hinv) as [Hbase [Hsplit Hunr]].
  destruct (consume_of_c_types_agree _ (fv_ct g) Hagree) as [unr Hcon0].
  destruct (pop_block_results_complete st (List.concat (List.map fv_seg pre)) g
              (fv_ctrl g).(code_Ctrl_block_type) <<[], unr>>
              Hsplit Hbase Hunr (room_fit st Hroom) Hcon0)
    as [st1 Hpt].
  rewrite Hpt. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (pop_block_results_sim st (List.concat (List.map fv_seg pre)) g
              (fv_ctrl g).(code_Ctrl_block_type) st1 Hsplit Hbase Hunr Hpt)
    as [seg' [Hc2 [Hv2 Hcon]]].
  assert (Hempty : seg' = []).
  { apply translate_vals_nil_inv.
    pose proof Hcon as Hc'. rewrite Hcon0 in Hc'.
    apply (f_equal (fun o => match o with
                             | Some ct => CT_type ct
                             | None => [] end)) in Hc'.
    cbn in Hc'. symmetry. exact Hc'. }
  rewrite Hempty in Hv2.
  pose proof (pop_block_results_size st _ _ st1 Hpt) as Hsize1.
  destruct (vals_stack_len_total st1.(code_OpIterState_vals)
              ltac:(assert (Hfit1 : Z.of_nat (stack_size st1) <= usize_max)
                      by (apply Nat2Z.inj_le in Hsize1;
                          pose proof (room_fit st Hroom); lia);
                    unfold stack_size in Hfit1;
                    rewrite Nat2Z.inj_add in Hfit1; lia)) as [nv Hvlen].
  rewrite Hvlen. cbn [bind].
  assert (Hne :
    (nv s<> (fv_ctrl g).(code_Ctrl_value_stack_base)) = false).
  { unfold scalar_neqb, scalar_eqb. apply Bool.negb_false_iff. apply Z.eqb_eq.
    rewrite (vals_stack_len_spec _ _ Hvlen). rewrite Hv2.
    rewrite List.app_nil_r.
    assert (Hsnoc_base :
      Z.to_nat (to_Z (fv_ctrl g).(code_Ctrl_value_stack_base))
        = List.length (List.concat (List.map fv_seg pre))).
    { unfold cur_base_nat in Hbase.
      rewrite (cur_ctrl_snoc st (List.map fv_ctrl pre) (fv_ctrl g) Hsnoc)
        in Hbase. exact Hbase. }
    pose proof (usize_nonneg (fv_ctrl g).(code_Ctrl_value_stack_base)). lia. }
  rewrite Hne. cbn beta iota.
  destruct (ctrls_stack_pop_total st1.(code_OpIterState_ctrls))
    as [o [cs Hpop]].
  rewrite Hpop. cbn [bind].
  destruct (push_block_results_total
              {| code_OpIterState_vals := st1.(code_OpIterState_vals);
                 code_OpIterState_ctrls := cs;
                 code_OpIterState_pos := st1.(code_OpIterState_pos) |}
              (fv_ctrl g).(code_Ctrl_block_type)) as [st2 Hpush].
  { cbn [code_OpIterState_vals]. apply room_vals.
    apply (room_le st st1); [exact Hsize1 | exact Hroom]. }
  rewrite Hpush. cbn [bind]. eexists. exists st2. reflexivity.
Qed.

(** [end] is where the checker's [c_types_agree] obligation and the Rust's
    "results popped, nothing else left" check meet. [consume_of_c_types_agree]
    supplies the pops, and the emptiness check follows because the [consume] it
    supplies leaves an empty stack, hence an empty segment.

    Closing a [Then] frame is the [if] whose else-branch is empty, and the
    reader rejects one with a result type. That is not a gap in this direction
    either: the empty else-branch type-checks against [tm] only for [tm = []],
    so the caller has the hypothesis to hand. *)
Lemma read_end_complete : forall C0 st pre g,
  Inv C0 st (pre ++ [g]) ->
  c_types_agree (fv_ct g)
    (translate_typelist (block_results_of (fv_ctrl g).(code_Ctrl_block_type)))
    = true ->
  ((fv_ctrl g).(code_Ctrl_kind) = Code_LabelKind_Then ->
   block_results_of (fv_ctrl g).(code_Ctrl_block_type) = []) ->
  room st ->
  exists r st', code_read_end st = Ok (Core_result_Result_Ok r, st').
Proof.
  intros C0 st pre g Hinv Hagree Hthen Hroom.
  unfold code_read_end.
  assert (Hsnoc : ctrls_list st.(code_OpIterState_ctrls)
                  = List.map fv_ctrl pre ++ [fv_ctrl g]).
  { destruct Hinv as [K1 _]. rewrite K1. rewrite List.map_app. reflexivity. }
  destruct (Inv_split C0 st pre g Hinv) as [Hbase [Hsplit Hunr]].
  assert (Hgbase : Z.to_nat (to_Z (fv_ctrl g).(code_Ctrl_value_stack_base))
                   = List.length (List.concat (List.map fv_seg pre))).
  { unfold cur_base_nat in Hbase.
    rewrite (cur_ctrl_snoc st (List.map fv_ctrl pre) (fv_ctrl g) Hsnoc)
      in Hbase. exact Hbase. }
  (* the frame list is non-empty, so the [n = 0] branch cannot fire *)
  destruct (ctrls_stack_len_total st.(code_OpIterState_ctrls)
              ltac:(pose proof (room_ctrls st Hroom); lia)) as [n Hlen].
  rewrite Hlen. cbn [bind].
  assert (Hnz : (n s= 0%usize) = false).
  { unfold scalar_eqb. apply Z.eqb_neq.
    rewrite (ctrls_stack_len_spec _ _ Hlen). rewrite Hsnoc.
    rewrite List.app_length. cbn [List.length].
    assert (H0 : to_Z 0%usize = 0) by reflexivity. lia. }
  rewrite Hnz. cbn beta iota.
  apply scalar_eqb_false in Hnz.
  assert (H0 : to_Z 0%usize = 0) by reflexivity. rewrite H0 in Hnz.
  destruct (usize_sub_1_ok n ltac:(pose proof (usize_nonneg n); lia))
    as [i [Hsub Hival]].
  rewrite Hsub. cbn [bind].
  assert (Hidxlen : Z.to_nat (to_Z i) = List.length (List.map fv_ctrl pre))
    by (apply (ctrls_last_index_len st (List.map fv_ctrl pre) (fv_ctrl g) n i
                 Hsnoc Hlen Hsub)).
  assert (Hlt : (Z.to_nat (to_Z i)
                 < List.length (ctrls_list st.(code_OpIterState_ctrls)))%nat).
  { rewrite Hsnoc, List.app_length, Hidxlen. cbn. lia. }
  destruct (ctrls_stack_get_total _ i Hlt) as [frame Hget].
  rewrite Hget. cbn [bind].
  pose proof (ctrls_stack_get_spec _ i frame Hlt Hget) as Hnth.
  rewrite (ctrls_last_index st (List.map fv_ctrl pre) (fv_ctrl g)
             n i Hsnoc Hlen Hsub) in Hnth.
  injection Hnth as <-.
  cbn [bind].
  (* the bare-[if] guard, discharged once rather than under each of the two
     copies of the tail the extraction made *)
  destruct (fv_ctrl g).(code_Ctrl_block_type) as [|vt] eqn:Hbt;
    cbn [bind].
  - destruct (is_then_total (fv_ctrl g).(code_Ctrl_kind)) as [bth Hit].
    rewrite Hit. cbn [bind]. destruct bth; cbn [bind];
      pose proof (read_end_tail_complete C0 st pre g i Hinv
                    ltac:(rewrite Hbt; exact Hagree) Hroom)
        as Htail;
      unfold read_end_tail in Htail; rewrite Hbt in Htail; exact Htail.
  - destruct (is_then_total (fv_ctrl g).(code_Ctrl_kind)) as [bth Hit].
    rewrite Hit. cbn [bind]. destruct bth eqn:Hbth.
    + destruct (is_then_spec _ _ Hit) as [[_ Hkind] | [Hbad _]].
      * exfalso. specialize (Hthen Hkind).
        cbn [block_results_of] in Hthen. discriminate.
      * rewrite Hbad in Hbth. discriminate.
    + cbn [bind].
      pose proof (read_end_tail_complete C0 st pre g i Hinv
                    ltac:(rewrite Hbt; exact Hagree) Hroom)
        as Htail.
      unfold read_end_tail in Htail. rewrite Hbt in Htail. exact Htail.
Qed.

(** [br]: the depth the checker looked up is in range and names the frame whose
    types the pops ask for, which is [ctx_at_label_lookup] read backwards. *)
(** The local operators' prologue: the index the specification put there decodes,
    and the lookup that the checker performed succeeds here too. *)
Lemma take_local_complete : forall ctx C0 st data l rest xx,
  locals_agree ctx C0 ->
  repr_u32 (bytes_from data st.(code_OpIterState_pos)) l rest ->
  lookup_N (tc_locals C0) (Z.to_N l) = Some xx ->
  exists idx t st',
    code_take_local st data ctx
      = Ok (Core_result_Result_Ok (idx, t), st')
    /\ to_Z idx = l
    /\ translate_vt_v t = xx.
Proof.
  intros ctx C0 st data l rest xx Hag Hrep Hlk.
  unfold code_take_local.
  destruct (read_u32_leb_complete data st.(code_OpIterState_pos) l rest Hrep)
    as [iv [p1 [Hleb [Hiv Hrest]]]].
  rewrite Hleb. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (local_type_complete ctx C0 iv xx Hag
              (ltac:(rewrite Hiv; exact Hlk))) as [t [Hlt Ht]].
  rewrite Hlt. cbn [bind]. rewrite branch_ok. cbn [bind].
  exists iv, t. eexists. split; [reflexivity|].
  split; [exact Hiv | exact Ht].
Qed.

Lemma read_local_get_complete : forall C0 ctx st pre f data l rest xx,
  Inv C0 st (pre ++ [f]) ->
  locals_agree ctx C0 ->
  repr_u32 (bytes_from data st.(code_OpIterState_pos)) l rest ->
  lookup_N (tc_locals C0) (Z.to_N l) = Some xx ->
  room st ->
  exists idx st',
    code_read_local_get st data ctx = Ok (Core_result_Result_Ok idx, st')
    /\ to_Z idx = l.
Proof.
  intros C0 ctx st pre f data l rest xx Hinv Hag Hrep Hlk Hroom.
  unfold code_read_local_get.
  destruct (take_local_complete ctx C0 st data l rest xx
              Hag Hrep Hlk) as [idx [t [st1 [Htl [Hidx Ht]]]]].
  rewrite Htl. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (take_local_fields st data ctx _ st1 Htl) as [Hv1 Hc1].
  pose proof (take_local_size st data ctx _ st1 Htl) as Hs1.
  destruct (push_val_total st1 (Code_StackType_Val t)) as [st2 Hpv].
  { apply room_vals. unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. exists idx, st2.
  split; [reflexivity | exact Hidx].
Qed.

Lemma read_local_set_complete : forall C0 ctx st pre f data l rest xx ct',
  Inv C0 st (pre ++ [f]) ->
  locals_agree ctx C0 ->
  repr_u32 (bytes_from data st.(code_OpIterState_pos)) l rest ->
  lookup_N (tc_locals C0) (Z.to_N l) = Some xx ->
  consume (fv_ct f) [xx] = Some ct' ->
  room st ->
  exists idx st',
    code_read_local_set st data ctx = Ok (Core_result_Result_Ok idx, st')
    /\ to_Z idx = l.
Proof.
  intros C0 ctx st pre f data l rest xx ct' Hinv Hag Hrep Hlk Hcon Hroom.
  unfold code_read_local_set.
  destruct (take_local_complete ctx C0 st data l rest xx
              Hag Hrep Hlk) as [idx [t [st1 [Htl [Hidx Ht]]]]].
  rewrite Htl. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (take_local_fields st data ctx _ st1 Htl) as [Hv1 Hc1].
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_fields C0 st st1 _ Hv1 Hc1 Hinv)).
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  destruct (pop_with_type_complete st1 (List.concat (List.map fv_seg pre)) f
              t ct' Hsplit1 Hbase1 Hunr1
              (ltac:(pose proof (take_local_size st data ctx _ st1 Htl);
                     pose proof (room_fit st Hroom); lia))
              (ltac:(rewrite Ht; exact Hcon))) as [t1 [st2 Hp1]].
  rewrite Hp1. cbn [bind]. rewrite branch_ok. cbn [bind].
  exists idx, st2. split; [reflexivity|]. exact Hidx.
Qed.

Lemma read_local_tee_complete : forall C0 ctx st pre f data l rest xx ct',
  Inv C0 st (pre ++ [f]) ->
  locals_agree ctx C0 ->
  repr_u32 (bytes_from data st.(code_OpIterState_pos)) l rest ->
  lookup_N (tc_locals C0) (Z.to_N l) = Some xx ->
  consume (fv_ct f) [xx] = Some ct' ->
  room st ->
  exists idx st',
    code_read_local_tee st data ctx = Ok (Core_result_Result_Ok idx, st')
    /\ to_Z idx = l.
Proof.
  intros C0 ctx st pre f data l rest xx ct' Hinv Hag Hrep Hlk Hcon
         Hroom.
  unfold code_read_local_tee.
  destruct (take_local_complete ctx C0 st data l rest xx
              Hag Hrep Hlk) as [idx [t [st1 [Htl [Hidx Ht]]]]].
  rewrite Htl. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (take_local_fields st data ctx _ st1 Htl) as [Hv1 Hc1].
  pose proof (take_local_size st data ctx _ st1 Htl) as Hs1.
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_fields C0 st st1 _ Hv1 Hc1 Hinv)).
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  destruct (pop_with_type_complete st1 (List.concat (List.map fv_seg pre)) f
              t ct' Hsplit1 Hbase1 Hunr1
              (ltac:(pose proof (room_fit st Hroom); lia))
              (ltac:(rewrite Ht; exact Hcon))) as [t1 [st2 Hp1]].
  rewrite Hp1. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (push_val_total st2 (Code_StackType_Val t)) as [st3 Hpv].
  { apply room_vals.
    pose proof (pop_with_type_size st1 t _ st2 Hp1) as Hs2.
    unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. exists idx, st3.
  split; [reflexivity | exact Hidx].
Qed.

(** The global operators' prologue, and the two readers. [global.set]'s extra
    hypothesis is the mutability the checker's [is_mut] tested. *)
Lemma take_global_complete : forall module C0 st data l rest xx,
  globals_agree module C0 ->
  repr_u32 (bytes_from data st.(code_OpIterState_pos)) l rest ->
  lookup_N (tc_globals C0) (Z.to_N l) = Some xx ->
  exists idx g st',
    code_take_global st data module
      = Ok (Core_result_Result_Ok (idx, g), st')
    /\ to_Z idx = l
    /\ translate_globaltype g = xx.
Proof.
  intros module C0 st data l rest xx Hag Hrep Hlk.
  unfold code_take_global.
  destruct (read_u32_leb_complete data st.(code_OpIterState_pos) l rest Hrep)
    as [iv [p1 [Hleb [Hiv Hrest]]]].
  rewrite Hleb. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (global_type_complete module C0 iv xx Hag
              (ltac:(rewrite Hiv; exact Hlk))) as [g [Hgt Hg]].
  rewrite Hgt. cbn [bind]. rewrite branch_ok. cbn [bind].
  exists iv, g. eexists. split; [reflexivity|].
  split; [exact Hiv | exact Hg].
Qed.

Lemma read_global_get_complete : forall C0 module st pre f data l rest xx,
  Inv C0 st (pre ++ [f]) ->
  globals_agree module C0 ->
  repr_u32 (bytes_from data st.(code_OpIterState_pos)) l rest ->
  lookup_N (tc_globals C0) (Z.to_N l) = Some xx ->
  room st ->
  exists idx st',
    code_read_global_get st data module = Ok (Core_result_Result_Ok idx, st')
    /\ to_Z idx = l.
Proof.
  intros C0 module st pre f data l rest xx Hinv Hag Hrep Hlk
         Hroom.
  unfold code_read_global_get.
  destruct (take_global_complete module C0 st data l rest xx
              Hag Hrep Hlk) as [idx [g [st1 [Htg [Hidx Hg]]]]].
  rewrite Htg. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (take_global_fields st data module _ st1 Htg) as [Hv1 Hc1].
  pose proof (take_global_size st data module _ st1 Htg) as Hs1.
  destruct (push_val_total st1
              (Code_StackType_Val g.(types_GlobalType_valtype))) as [st2 Hpv].
  { apply room_vals. unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. exists idx, st2.
  split; [reflexivity | exact Hidx].
Qed.

Lemma read_global_set_complete : forall C0 module st pre f data l rest xx ct',
  Inv C0 st (pre ++ [f]) ->
  globals_agree module C0 ->
  repr_u32 (bytes_from data st.(code_OpIterState_pos)) l rest ->
  lookup_N (tc_globals C0) (Z.to_N l) = Some xx ->
  is_mut xx = true ->
  consume (fv_ct f) [tg_t xx] = Some ct' ->
  room st ->
  exists idx st',
    code_read_global_set st data module = Ok (Core_result_Result_Ok idx, st')
    /\ to_Z idx = l.
Proof.
  intros C0 module st pre f data l rest xx ct' Hinv Hag Hrep Hlk Hmut Hcon
         Hroom.
  unfold code_read_global_set.
  destruct (take_global_complete module C0 st data l rest xx
              Hag Hrep Hlk) as [idx [g [st1 [Htg [Hidx Hg]]]]].
  rewrite Htg. cbn [bind]. rewrite branch_ok. cbn [bind].
  assert (Hvar : g.(types_GlobalType_mutability) = Types_Mut_Var)
    by (apply var_of_is_mut; rewrite Hg; exact Hmut).
  (* [destruct] rewrites [Hvar] too, so the immutable case is a contradiction *)
  destruct (g.(types_GlobalType_mutability)) eqn:Hm; [discriminate|].
  destruct (take_global_fields st data module _ st1 Htg) as [Hv1 Hc1].
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_fields C0 st st1 _ Hv1 Hc1 Hinv)).
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  destruct (pop_with_type_complete st1 (List.concat (List.map fv_seg pre)) f
              g.(types_GlobalType_valtype) ct' Hsplit1 Hbase1 Hunr1
              (ltac:(pose proof (take_global_size st data module _ st1 Htg);
                     pose proof (room_fit st Hroom); lia))
              (ltac:(rewrite <- Hg in Hcon;
                     cbn [tg_t translate_globaltype] in Hcon; exact Hcon)))
    as [t1 [st2 Hp1]].
  rewrite Hp1. cbn [bind]. rewrite branch_ok. cbn [bind].
  exists idx, st2. split; [reflexivity|]. exact Hidx.
Qed.

(** The label lookup: the depth the specification put there decodes, the bounds
    check passes because the checker found a label at that depth, and the frame
    resolved is the one it found. *)
Lemma read_label_complete : forall C0 st fs data l rest target,
  Inv C0 st fs ->
  repr_u32 (bytes_from data st.(code_OpIterState_pos)) l rest ->
  (Z.to_nat l < List.length (ctrls_list st.(code_OpIterState_ctrls)))%nat ->
  List.nth_error (ctrls_list st.(code_OpIterState_ctrls))
    (List.length (ctrls_list st.(code_OpIterState_ctrls)) - 1 - Z.to_nat l)
    = Some target ->
  room st ->
  exists depth st',
    code_read_label st data = Ok (Core_result_Result_Ok (depth, target), st')
    /\ to_Z depth = l
    /\ bytes_from data st'.(code_OpIterState_pos) = rest
    /\ Inv C0 st' fs
    /\ vals_list st'.(code_OpIterState_vals)
       = vals_list st.(code_OpIterState_vals)
    /\ ctrls_list st'.(code_OpIterState_ctrls)
       = ctrls_list st.(code_OpIterState_ctrls).
Proof.
  intros C0 st fs data l rest target Hinv Hrep Hlt Hnth Hroom.
  unfold code_read_label.
  destruct (read_u32_leb_complete data st.(code_OpIterState_pos) l rest Hrep)
    as [dv [p1 [Hleb [Hdv Hrest]]]].
  rewrite Hleb. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (cast_u32_usize_ok dv) as [d [Hcast Hdval]].
  rewrite Hcast. cbn [bind].
  pose proof (u32_nonneg dv) as Hdvnn.
  assert (Hdz : to_Z d = l) by (rewrite Hdval; exact Hdv).
  destruct (ctrls_stack_len_total st.(code_OpIterState_ctrls)
              ltac:(pose proof (room_ctrls st Hroom); lia)) as [n Hlen].
  rewrite Hlen. cbn [bind].
  assert (Hlen1 : to_Z n = Z.of_nat
                      (List.length (ctrls_list st.(code_OpIterState_ctrls))))
    by exact (ctrls_stack_len_spec _ _ Hlen).
  assert (Hge : (d s>= n) = false).
  { apply scalar_lt_geb_false. rewrite Hlen1. rewrite Hdz. lia. }
  rewrite Hge. cbn beta iota.
  destruct (usize_sub_1_ok n)
    as [i [Hsub1 Hival]]; [rewrite Hlen1; lia|].
  rewrite Hsub1. cbn [bind].
  destruct (usize_sub_ok i d) as [i1 [Hsub2 Hi1val]];
    [rewrite Hival; rewrite Hlen1; rewrite Hdz; lia|].
  rewrite Hsub2. cbn [bind].
  assert (Hidx : Z.to_nat (to_Z i1)
                 = (List.length (ctrls_list st.(code_OpIterState_ctrls)) - 1
                    - Z.to_nat l)%nat).
  { rewrite Hi1val. rewrite Hival. rewrite Hlen1. rewrite Hdz. lia. }
  assert (Hidxlt : (Z.to_nat (to_Z i1)
                    < List.length (ctrls_list st.(code_OpIterState_ctrls)))%nat)
    by (rewrite Hidx; lia).
  destruct (ctrls_stack_get_total _ i1 Hidxlt) as [frame Hget].
  rewrite Hget. cbn [bind].
  pose proof (ctrls_stack_get_spec _ i1 frame Hidxlt Hget) as Hget_spec.
  rewrite Hidx, Hnth in Hget_spec. injection Hget_spec as <-.
  exists dv. eexists. split; [reflexivity|]. split; [exact Hdv|].
  cbn [code_OpIterState_vals code_OpIterState_ctrls code_OpIterState_pos].
  split; [exact Hrest|].
  split; [exact Hinv|].
  split; reflexivity.
Qed.

(** The branch operators' prologue is the opcode and then a label. *)
(** [read_label_complete] with the invariant and the stacks transported, which
    is what the two branch operators need of their shared label immediate. *)
Lemma read_label_complete_at :
  forall C0 st fs data l rest target,
  Inv C0 st fs ->
  repr_u32 (bytes_from data st.(code_OpIterState_pos)) l rest ->
  (Z.to_nat l < List.length (ctrls_list st.(code_OpIterState_ctrls)))%nat ->
  List.nth_error (ctrls_list st.(code_OpIterState_ctrls))
    (List.length (ctrls_list st.(code_OpIterState_ctrls)) - 1 - Z.to_nat l)
    = Some target ->
  room st ->
  exists depth st',
    code_read_label st data
      = Ok (Core_result_Result_Ok (depth, target), st')
    /\ to_Z depth = l
    /\ Inv C0 st' fs
    /\ vals_list st'.(code_OpIterState_vals)
       = vals_list st.(code_OpIterState_vals)
    /\ ctrls_list st'.(code_OpIterState_ctrls)
       = ctrls_list st.(code_OpIterState_ctrls).
Proof.
  intros C0 st fs data l rest target Hinv Hrep Hlt Hnth Hroom.
  destruct (read_label_complete C0 st fs data l rest target Hinv Hrep Hlt Hnth
              Hroom)
    as [depth [st' [Hrl [Hdv [_ [Hinv' [Hvl' Hcl']]]]]]].
  exists depth, st'. split; [exact Hrl|]. split; [exact Hdv|].
  split; [exact Hinv'|]. split; [exact Hvl' | exact Hcl'].
Qed.

Lemma read_br_complete :
  forall C0 st pre f data l rest target ct',
  Inv C0 st (pre ++ [f]) ->
  repr_u32 (bytes_from data st.(code_OpIterState_pos)) l rest ->
  (Z.to_nat l < List.length (ctrls_list st.(code_OpIterState_ctrls)))%nat ->
  List.nth_error (ctrls_list st.(code_OpIterState_ctrls))
    (List.length (ctrls_list st.(code_OpIterState_ctrls)) - 1 - Z.to_nat l)
    = Some target ->
  consume (fv_ct f) (translate_typelist (ctrl_target target)) = Some ct' ->
  room st ->
  exists depth bt' st',
    code_read_br st data = Ok (Core_result_Result_Ok (depth, bt'), st')
    /\ to_Z depth = l.
Proof.
  intros C0 st pre f data l rest target ct'
         Hinv Hrep Hlt Hnth Hcon Hroom.
  unfold code_read_br.
  destruct (read_label_complete_at C0 st (pre ++ [f]) data
              l rest target Hinv Hrep Hlt Hnth Hroom)
    as [depth [st1 [Htb [Hdepth [Hinv1 [Hv1 Hc1]]]]]].
  rewrite Htb. cbn [bind]. rewrite branch_ok. cbn [bind].
  rewrite branch_target_bt_spec. cbn [bind].
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase [Hsplit Hunr]].
  assert (Hroom1 : room st1).
  { unfold room, stack_size in *. rewrite Hv1, Hc1. exact Hroom. }
  destruct (pop_block_results_complete st1
              (List.concat (List.map fv_seg pre)) f
              (branch_target_bt_of target) ct' Hsplit Hbase Hunr
              (room_fit st1 Hroom1)
              (ltac:(unfold ctrl_target in Hcon; exact Hcon))) as [st2 Hpt].
  rewrite Hpt. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (mark_unreachable_total st2
              ltac:(pose proof (pop_block_results_size st1 _ _ st2 Hpt) as Hsz;
                     pose proof (room_fit st1 Hroom1);
                     apply Nat2Z.inj_le in Hsz; lia)) as [st3 Hmu].
  rewrite Hmu. cbn [bind]. exists depth, target.(code_Ctrl_block_type), st3.
  split; [reflexivity | exact Hdepth].
Qed.

(** [br_if]: the condition pop and the target pops come from the checker's one
    [consume], split at the head, and the types then go back on. *)
Lemma read_br_if_complete :
  forall C0 st pre f data l rest target ct',
  Inv C0 st (pre ++ [f]) ->
  repr_u32 (bytes_from data st.(code_OpIterState_pos)) l rest ->
  (Z.to_nat l < List.length (ctrls_list st.(code_OpIterState_ctrls)))%nat ->
  List.nth_error (ctrls_list st.(code_OpIterState_ctrls))
    (List.length (ctrls_list st.(code_OpIterState_ctrls)) - 1 - Z.to_nat l)
    = Some target ->
  consume (fv_ct f)
    (T_num T_i32 :: translate_typelist (ctrl_target target)) = Some ct' ->
  room st ->
  exists depth bt' st',
    code_read_br_if st data = Ok (Core_result_Result_Ok (depth, bt'), st')
    /\ to_Z depth = l.
Proof.
  intros C0 st pre f data l rest target ct'
         Hinv Hrep Hlt Hnth Hcon Hroom.
  unfold code_read_br_if.
  destruct (read_label_complete_at C0 st (pre ++ [f]) data
              l rest target Hinv Hrep Hlt Hnth Hroom)
    as [depth [st1 [Htb [Hdepth [Hinv1 [Hvl Hcl]]]]]].
  rewrite Htb. cbn [bind]. rewrite branch_ok. cbn [bind].
  rewrite branch_target_bt_spec. cbn [bind].
  assert (Hroom1 : room st1).
  { unfold room, stack_size in *. rewrite Hvl, Hcl. exact Hroom. }
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  destruct (consume_cons_inv (fv_ct f) (T_num T_i32)
              (translate_typelist (ctrl_target target)) ct' Hcon)
    as [ct1 [Hcon1 Hcon2]].
  (* the condition *)
  destruct (pop_with_type_complete st1 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 ct1 Hsplit1 Hbase1 Hunr1
              (room_fit st1 Hroom1) Hcon1)
    as [t1 [st2 Hp1]].
  rewrite Hp1. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (pop_with_type_sim st1 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 t1 st2 Hsplit1 Hbase1 Hunr1 Hp1)
    as [seg1 [Hc2 [Hv2 Hsim1]]].
  destruct (cur_views_ctrls st1 st2 Hc2) as [Hb2 Hu2].
  assert (Hct1 : ct1 = <<translate_vals seg1,
                         (fv_ctrl f).(code_Ctrl_polymorphic_base)>>).
  { pose proof Hsim1 as Hs. cbn [translate_vt_v] in Hs.
    rewrite Hcon1 in Hs. injection Hs as Hs. exact Hs. }
  rewrite Hct1 in Hcon2.
  (* the target's types, on the frame with the shortened segment *)
  destruct (pop_block_results_complete st2
              (List.concat (List.map fv_seg pre))
              {| fv_ctrl := fv_ctrl f; fv_seg := seg1;
                  fv_done := fv_done f; fv_then := fv_then f |}
              (branch_target_bt_of target) ct'
              (ltac:(cbn [fv_seg]; exact Hv2))
              (ltac:(cbn [fv_ctrl]; rewrite Hb2; exact Hbase1))
              (ltac:(cbn [fv_ctrl]; rewrite Hu2; exact Hunr1))
              (ltac:(exact (pop_with_type_fit st1 _ _ st2
                               (room_fit st1 Hroom1) Hp1)))
              (ltac:(cbn [fv_ct fv_seg fv_ctrl];
                     unfold ctrl_target in Hcon2; exact Hcon2)))
    as [st3 Hpt].
  rewrite Hpt. cbn [bind]. rewrite branch_ok. cbn [bind].
  (* and back on: the condition pop paid for the push *)
  destruct (push_block_results_total st3 (branch_target_bt_of target))
    as [st4 Hpush].
  { apply room_vals. apply (room_le st st3); [|exact Hroom].
    pose proof (pop_with_type_size st1 _ _ st2 Hp1) as Hs2.
    pose proof (pop_block_results_size st2 _ _ st3 Hpt) as Hs3.
    unfold stack_size in Hs2, Hs3 |- *. rewrite Hvl, Hcl in Hs2. lia. }
  rewrite Hpush. cbn [bind].
  exists depth, target.(code_Ctrl_block_type), st4.
  split; [reflexivity | exact Hdepth].
Qed.

(** [br_table]'s label vector, in the completeness direction: the specification's
    label list decodes, every entry resolves because the checker found a label at
    that depth, and the running block type is the one they share.

    The loop's running value starts unset and is only ever set to [common], which
    is what the disjunction in the hypothesis and the conclusion says. *)
Lemma read_table_labels_loop_complete :
  forall n V (inst : code_OpVisitor_t V) v C0 st fs data ls rest count i expect
         common,
  hooks_accept inst ->
  Inv C0 st fs ->
  to_Z i + Z.of_nat n = to_Z count ->
  repr_u32_rep n (bytes_from data st.(code_OpIterState_pos)) ls rest ->
  List.Forall (fun d => depth_target st d common) ls ->
  (expect = None \/ expect = Some common) ->
  room st ->
  exists res st' v',
    code_read_table_labels_loop inst st data count v expect i
      = Ok (Core_result_Result_Ok res, st', v')
    /\ (res = None \/ res = Some common)
    /\ bytes_from data st'.(code_OpIterState_pos) = rest
    /\ Inv C0 st' fs
    /\ vals_list st'.(code_OpIterState_vals)
       = vals_list st.(code_OpIterState_vals)
    /\ ctrls_list st'.(code_OpIterState_ctrls)
       = ctrls_list st.(code_OpIterState_ctrls).
Proof.
  induction n as [|n IH];
    intros V inst v C0 st fs data ls rest count i expect common
           Hacc Hinv Hn Hrep Hall Hexp Hroom;
    unfold code_read_table_labels_loop; rewrite loop_unfold; cbn beta iota.
  - (* the count is exhausted, so the guard fires and nothing was read *)
    inversion Hrep; subst.
    assert (Heq : (i s= count) = true)
      by (unfold scalar_eqb; apply Z.eqb_eq; cbn in Hn; lia).
    rewrite Heq. cbn beta iota.
    exists expect, st, v. split; [reflexivity|]. split; [exact Hexp|].
    split; [reflexivity|]. split; [exact Hinv|].
    split; reflexivity.
  - inversion Hrep as [|n0 bs0 d mid0 ls0 rest0 Hd Hrest Hn0 Hbs0 Hls Hrest'];
      subst.
    assert (Heq : (i s= count) = false)
      by (unfold scalar_eqb; apply Z.eqb_neq; cbn in Hn; lia).
    rewrite Heq. cbn beta iota.
    (* the head label resolves, because the checker found one at that depth *)
    inversion Hall as [|d0 ls1 Hhead Htail]; subst.
    destruct Hhead as [c [Hlt [Hnth Hbtc]]].
    destruct (read_label_complete C0 st fs data d mid0 c Hinv Hd Hlt Hnth Hroom)
      as [depth [st1 [Hrl [Hdv [Hbytes1 [Hinv1 [Hv1 Hc1]]]]]]].
    rewrite Hrl. cbn [bind]. rewrite branch_ok. cbn [bind].
    (* the per-label hook accepts, since the consumer accepts every operator *)
    destruct (label_hook_accept V inst v st1 depth Hacc) as [vh Hhk].
    rewrite Hhk. cbn [bind code_visit]. rewrite branch_ok. cbn [bind].
    rewrite branch_target_bt_spec. cbn [bind]. rewrite Hbtc.
    rewrite (merge_target_same expect common Hexp). cbn [bind].
    rewrite branch_ok. cbn [bind].
    (* [i] is below the count, so the increment cannot overflow *)
    pose proof (u32_bounds i) as Hib. pose proof (u32_bounds count) as Hcb.
    destruct (u32_add_ok i 1%u32) as [i1 [Hadd Hi1]].
    { assert (H1 : to_Z 1%u32 = 1) by reflexivity. rewrite H1. cbn in Hn. lia. }
    rewrite Hadd. cbn [bind].
    rewrite <- Hbytes1 in Hrest.
    destruct (IH V inst vh C0 st1 fs data ls0 rest count i1 (Some common) common
                Hacc Hinv1
                (ltac:(assert (H1 : to_Z 1%u32 = 1) by reflexivity;
                       rewrite Hi1; rewrite H1; cbn in Hn; lia))
                Hrest
                (List.Forall_impl _
                   (fun d' Hd' => depth_target_ctrls st st1 d' common Hc1 Hd')
                   Htail)
                (or_intror eq_refl)
                (ltac:(unfold room, stack_size in *;
                       rewrite Hv1, Hc1; exact Hroom)))
      as [res [st' [v' [Hloop [Hres [Hb' [Hinv' [Hv' Hc']]]]]]]].
    exists res, st', v'. split; [exact Hloop|]. split; [exact Hres|].
    split; [exact Hb'|]. split; [exact Hinv'|].
    split; [rewrite Hv'; exact Hv1 | rewrite Hc'; exact Hc1].
Qed.

Lemma read_table_labels_complete :
  forall V (inst : code_OpVisitor_t V) v C0 st fs data ls rest count common,
  hooks_accept inst ->
  Inv C0 st fs ->
  repr_u32_rep (Z.to_nat (to_Z count))
               (bytes_from data st.(code_OpIterState_pos)) ls rest ->
  List.Forall (fun d => depth_target st d common) ls ->
  room st ->
  exists res st' v',
    code_read_table_labels inst st data count v
      = Ok (Core_result_Result_Ok res, st', v')
    /\ (res = None \/ res = Some common)
    /\ bytes_from data st'.(code_OpIterState_pos) = rest
    /\ Inv C0 st' fs
    /\ vals_list st'.(code_OpIterState_vals)
       = vals_list st.(code_OpIterState_vals)
    /\ ctrls_list st'.(code_OpIterState_ctrls)
       = ctrls_list st.(code_OpIterState_ctrls).
Proof.
  intros V inst v C0 st fs data ls rest count common Hacc Hinv Hrep Hall Hroom.
  unfold code_read_table_labels.
  apply (read_table_labels_loop_complete (Z.to_nat (to_Z count)) V inst v C0 st
           fs data ls rest count 0%u32 None common Hacc Hinv
           (ltac:(assert (H0 : to_Z 0%u32 = 0) by reflexivity; rewrite H0;
                  rewrite Z2Nat.id by apply u32_nonneg; reflexivity))
           Hrep Hall (or_introl eq_refl) Hroom).
Qed.

(** [br_table]: [br]'s effect after an [i32], with the vector and the default
    label read first. Every label names a frame with the same branch target, so
    the running comparison never fails and the reader returns that target. *)
Lemma read_br_table_complete :
  forall V (inst : code_OpVisitor_t V) v C0 st pre f data ls x mid rest common
         ct',
  hooks_accept inst ->
  Inv C0 st (pre ++ [f]) ->
  repr_vec_u32 (bytes_from data st.(code_OpIterState_pos)) ls mid ->
  repr_u32 mid x rest ->
  List.Forall (fun d => depth_target st d common) (ls ++ [x]) ->
  consume (fv_ct f)
    (T_num T_i32 :: translate_typelist (block_results_of common)) = Some ct' ->
  room st ->
  exists dflt st' v',
    code_read_br_table inst st data v
      = Ok (Core_result_Result_Ok (dflt, common), st', v').
Proof.
  intros V inst v C0 st pre f data ls x mid rest common ct'
         Hacc Hinv Hvec Hdef Hall Hcon Hroom.
  apply List.Forall_app in Hall. destruct Hall as [Hallls Hallx].
  inversion Hallx as [|x0 nil0 Hxt _]; subst.
  unfold code_read_br_table.
  assert (Hvl1 : vals_list st.(code_OpIterState_vals)
                 = vals_list st.(code_OpIterState_vals))
    by reflexivity.
  assert (Hcl1 : ctrls_list st.(code_OpIterState_ctrls)
                 = ctrls_list st.(code_OpIterState_ctrls))
    by reflexivity.
  assert (Hinv1 : Inv C0 st (pre ++ [f]))
    by (apply (Inv_fields C0 st st _ Hvl1 Hcl1 Hinv)).
  (* the count, then the vector *)
  inversion Hvec as [bs0 n mid0 ls0 rest0 Hn Hrep]; subst.
  destruct (read_u32_leb_complete data st.(code_OpIterState_pos) n mid0 Hn)
    as [count [p1 [Hleb [Hcv Hmid0]]]].
  rewrite Hleb. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (read_table_labels_complete V inst v C0
              {| code_OpIterState_vals := st.(code_OpIterState_vals);
                 code_OpIterState_ctrls := st.(code_OpIterState_ctrls);
                 code_OpIterState_pos := p1
              |} (pre ++ [f]) data ls mid count common Hacc
              (Inv_fields C0 st _ _ eq_refl eq_refl Hinv1)
              (ltac:(cbn [code_OpIterState_pos]; rewrite Hcv;
                     rewrite Hmid0; exact Hrep))
              (List.Forall_impl _
                 (fun d Hd => depth_target_ctrls st _ d common Hcl1 Hd)
                 Hallls)
              (ltac:(unfold room, stack_size; cbn; exact Hroom)))
    as [res [st1 [v1 [Htl [Hres [Hb2 [Hinv2 [Hv2 Hc2]]]]]]]].
  rewrite Htl. cbn [bind]. rewrite branch_ok. cbn [bind].
  assert (Hcl2 : ctrls_list st1.(code_OpIterState_ctrls)
                 = ctrls_list st.(code_OpIterState_ctrls))
    by (rewrite Hc2; exact Hcl1).
  assert (Hroom1 : room st1).
  { unfold room, stack_size in *. rewrite Hv2, Hc2. exact Hroom. }
  (* the default label *)
  destruct Hxt as [c [Hlt [Hnth Hbtc]]].
  rewrite <- Hcl2 in Hlt, Hnth.
  destruct (read_label_complete C0 st1 (pre ++ [f]) data x rest c Hinv2
              (ltac:(rewrite Hb2; exact Hdef)) Hlt Hnth Hroom1)
    as [depth [st2 [Hrl [_ [_ [Hinv3 [Hv3 Hc3]]]]]]].
  rewrite Hrl. cbn [bind]. rewrite branch_ok. cbn [bind].
  rewrite branch_target_bt_spec. cbn [bind]. rewrite Hbtc.
  rewrite (merge_target_same res common Hres). cbn [bind].
  rewrite branch_ok. cbn [bind].
  assert (Hroom2 : room st2).
  { unfold room, stack_size in *. rewrite Hv3, Hc3. exact Hroom1. }
  assert (Hsnoc : ctrls_list st2.(code_OpIterState_ctrls)
                  = List.map fv_ctrl pre ++ [fv_ctrl f])
    by (destruct Hinv3 as [K1 _]; rewrite K1; rewrite List.map_app;
        reflexivity).
  destruct (Inv_split C0 st2 pre f Hinv3) as [Hbase [Hsplit Hunr]].
  destruct (consume_cons_inv (fv_ct f) (T_num T_i32)
              (translate_typelist (block_results_of common)) ct' Hcon)
    as [ct1 [Hcon1 Hcon2]].
  (* the index *)
  destruct (pop_with_type_complete st2 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 ct1 Hsplit Hbase Hunr
              (room_fit st2 Hroom2) Hcon1)
    as [t1 [st3 Hp1]].
  rewrite Hp1. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (pop_with_type_sim st2 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 t1 st3 Hsplit Hbase Hunr Hp1)
    as [seg1 [Hc4 [Hv4 Hsim1]]].
  destruct (cur_views_ctrls st2 st3 Hc4) as [Hb4 Hu4].
  assert (Hct1 : ct1 = <<translate_vals seg1,
                         (fv_ctrl f).(code_Ctrl_polymorphic_base)>>).
  { pose proof Hsim1 as Hs. cbn [translate_vt_v] in Hs.
    rewrite Hcon1 in Hs. injection Hs as Hs. exact Hs. }
  rewrite Hct1 in Hcon2.
  (* the target's types, then the truncation *)
  destruct (pop_block_results_complete st3
              (List.concat (List.map fv_seg pre))
              {| fv_ctrl := fv_ctrl f; fv_seg := seg1;
                  fv_done := fv_done f; fv_then := fv_then f |}
              common ct'
              (ltac:(cbn [fv_seg]; exact Hv4))
              (ltac:(cbn [fv_ctrl]; rewrite Hb4; exact Hbase))
              (ltac:(cbn [fv_ctrl]; rewrite Hu4; exact Hunr))
              (ltac:(exact (pop_with_type_fit st2 _ _ st3
                               (room_fit st2 Hroom2) Hp1)))
              (ltac:(cbn [fv_ct fv_seg fv_ctrl]; exact Hcon2)))
    as [st4 Hpt].
  rewrite Hpt. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (mark_unreachable_total st4
              ltac:(pose proof (pop_block_results_size st3 _ _ st4 Hpt)
                       as Hsz2;
                     apply Nat2Z.inj_le in Hsz2;
                     pose proof (pop_with_type_fit st2 _ _ st3
                       (room_fit st2 Hroom2) Hp1); lia)) as [st5 Hmu].
  rewrite Hmu. cbn [bind]. exists depth, st5. eexists. reflexivity.
Qed.

Lemma read_reserved_zero_complete : forall st data rest,
  bytes_from data st.(code_OpIterState_pos) = 0 :: rest ->
  exists st',
    code_read_reserved_zero st data = Ok (Core_result_Result_Ok tt, st')
    /\ bytes_from data st'.(code_OpIterState_pos) = rest
    /\ vals_list st'.(code_OpIterState_vals)
       = vals_list st.(code_OpIterState_vals)
    /\ ctrls_list st'.(code_OpIterState_ctrls)
       = ctrls_list st.(code_OpIterState_ctrls).
Proof.
  intros st data rest Hbytes. unfold code_read_reserved_zero.
  destruct (read_byte_complete data st.(code_OpIterState_pos) 0 rest Hbytes)
    as [b [p [Hrb [Hb Hrest]]]].
  rewrite Hrb. cbn [bind]. rewrite branch_ok. cbn [bind].
  assert (Hz : (b s<> 0%u8) = false).
  { unfold scalar_neqb, scalar_eqb. apply Bool.negb_false_iff.
    apply Z.eqb_eq. rewrite Hb. reflexivity. }
  rewrite Hz. cbn beta iota. eexists.
  split; [reflexivity|]. cbn [code_OpIterState_pos].
  split; [exact Hrest|]. split; reflexivity.
Qed.


(** The two call operators. [take_index] reads the index, the arity guard passes
    because the context is a Wasm 1.0 one, and the pops and pushes are the
    callee's signature. *)
Lemma take_index_complete : forall st data l rest,
  repr_u32 (bytes_from data st.(code_OpIterState_pos)) l rest ->
  exists idx st',
    code_take_index st data = Ok (Core_result_Result_Ok idx, st')
    /\ to_Z idx = l
    /\ bytes_from data st'.(code_OpIterState_pos) = rest
    /\ vals_list st'.(code_OpIterState_vals)
       = vals_list st.(code_OpIterState_vals)
    /\ ctrls_list st'.(code_OpIterState_ctrls)
       = ctrls_list st.(code_OpIterState_ctrls).
Proof.
  intros st data l rest Hrep. unfold code_take_index.
  destruct (read_u32_leb_complete data st.(code_OpIterState_pos) l rest Hrep)
    as [iv [p1 [Hleb [Hiv Hrest]]]].
  rewrite Hleb. cbn [bind]. rewrite branch_ok. cbn [bind].
  exists iv. eexists. split; [reflexivity|]. split; [exact Hiv|].
  cbn [code_OpIterState_vals code_OpIterState_ctrls code_OpIterState_pos].
  split; [exact Hrest|]. split; reflexivity.
Qed.

Lemma read_call_complete : forall C0 module st pre f data l rest tn tm ct',
  Inv C0 st (pre ++ [f]) ->
  funcs_agree module C0 -> funcs_wasm10 module ->
  repr_u32 (bytes_from data st.(code_OpIterState_pos)) l rest ->
  lookup_N (tc_funcs C0) (Z.to_N l) = Some (Tf tn tm) ->
  consume (fv_ct f) tn = Some ct' ->
  room st ->
  exists idx st',
    code_read_call st data module = Ok (Core_result_Result_Ok idx, st')
    /\ to_Z idx = l.
Proof.
  intros C0 module st pre f data l rest tn tm ct'
         Hinv Hag Hw10 Hrep Hlk Hcon Hroom.
  unfold code_read_call.
  destruct (take_index_complete st data l rest Hrep)
    as [idx [st1 [Hti [Hidx [_ [Hv1 Hc1]]]]]].
  rewrite Hti. cbn [bind]. rewrite branch_ok. cbn [bind].
  pose proof (take_index_size st data _ st1 Hti) as Hs1.
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_fields C0 st st1 _ Hv1 Hc1 Hinv)).
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  destruct (ft_lookup_complete module.(module_Env_func_types) (tc_funcs C0) idx
              (Tf tn tm) Hag (ltac:(rewrite Hidx; exact Hlk)))
    as [i [ft [Hcast [_ [Hge [Hidxv [Hin Hft]]]]]]].
  rewrite Hcast. cbn [bind]. rewrite Hge. rewrite Hidxv. cbn [bind].
  pose proof (Hw10 ft Hin) as Hlen. unfold ft_results_wasm10 in Hlen.
  repeat rewrite vec_deref_spec.
  rewrite (require_single_result_intro _ Hlen). cbn [bind].
  rewrite branch_ok. cbn [bind].
  (* [translate_ft] is the pair of translated lists, so the checker's [tn] and
     [tm] are the parameter and result lists of the type the code found *)
  assert (Htn : translate_typelist (vec_list ft.(types_FuncType_params)) = tn)
    by (injection Hft as Ha _; exact Ha).
  assert (Htm : translate_typelist (vec_list ft.(types_FuncType_results)) = tm)
    by (injection Hft as _ Hb2; exact Hb2).
  destruct (pop_types_complete st1 (List.concat (List.map fv_seg pre)) f
              ft.(types_FuncType_params) ct' Hsplit1 Hbase1 Hunr1
              (ltac:(pose proof (room_fit st Hroom); lia))
              (ltac:(rewrite Htn; exact Hcon))) as [st2 Hpt].
  rewrite Hpt. cbn [bind]. rewrite branch_ok. cbn [bind].
  pose proof (pop_types_size st1 _ _ st2 Hpt) as Hs2.
  destruct (push_types_total st2 ft.(types_FuncType_results)) as [st3 Hpu].
  { assert (Hb3 : (List.length (vals_list st2.(code_OpIterState_vals))
                   + List.length (vec_list ft.(types_FuncType_results))
                   <= stack_size st + 1)%nat).
    { unfold stack_size in Hs1, Hs2 |- *. lia. }
    apply (proj1 (Nat2Z.inj_le _ _)) in Hb3.
    rewrite Nat2Z.inj_add in Hb3. rewrite Nat2Z.inj_add in Hb3.
    unfold room in Hroom. lia. }
  rewrite Hpu. cbn [bind]. exists idx, st3.
  split; [reflexivity | exact Hidx].
Qed.

Lemma read_call_indirect_complete :
  forall C0 module st pre f data l rest tabt tn tm ct',
  Inv C0 st (pre ++ [f]) ->
  types_agree module C0 -> tables_agree module C0 -> types_wasm10 module ->
  repr_u32 (bytes_from data st.(code_OpIterState_pos)) l
           (0 :: rest) ->
  lookup_N (tc_tables C0) 0%N = Some tabt ->
  lookup_N (tc_types C0) (Z.to_N l) = Some (Tf tn tm) ->
  consume (fv_ct f) (T_num T_i32 :: tn) = Some ct' ->
  room st ->
  exists idx st',
    code_read_call_indirect st data module
      = Ok (Core_result_Result_Ok idx, st')
    /\ to_Z idx = l.
Proof.
  intros C0 module st pre f data l rest tabt tn tm ct'
         Hinv Hty Htab Hw10 Hrep Htlk Hlk Hcon Hroom.
  unfold code_read_call_indirect.
  destruct (take_index_complete st data l (0 :: rest)
              Hrep) as [idx [st1 [Hti [Hidx [Hrest [Hv1 Hc1]]]]]].
  rewrite Hti. cbn [bind]. rewrite branch_ok. cbn [bind].
  pose proof (take_index_size st data _ st1 Hti) as Hs1.
  destruct (read_reserved_zero_complete st1 data rest Hrest)
    as [st2 [Hrz [_ [Hv2 Hc2]]]].
  rewrite Hrz. cbn [bind]. rewrite branch_ok. cbn [bind].
  pose proof (read_reserved_zero_size st1 data _ st2 Hrz) as Hs2.
  assert (Hinv2 : Inv C0 st2 (pre ++ [f])).
  { apply (Inv_fields C0 st st2 _ (ltac:(rewrite Hv2; exact Hv1))
             (ltac:(rewrite Hc2; exact Hc1)) Hinv). }
  destruct (Inv_split C0 st2 pre f Hinv2) as [Hbase2 [Hsplit2 Hunr2]].
  (* the table the checker found is one the context has, so it is not empty *)
  rewrite vec_is_empty_spec. cbn [bind].
  assert (Hne : vec_list module.(module_Env_table_types) <> []).
  { intros Hnil. unfold tables_agree in Htab. rewrite Hnil in Htab.
    rewrite Htab in Htlk. discriminate. }
  destruct (vec_list module.(module_Env_table_types)) as [|t0 ts] eqn:Hts;
    [exfalso; apply Hne; reflexivity|].
  destruct (ft_lookup_complete module.(module_Env_types) (tc_types C0) idx
              (Tf tn tm) Hty (ltac:(rewrite Hidx; exact Hlk)))
    as [i [ft [Hcast [_ [Hge [Hidxv [Hin Hft]]]]]]].
  rewrite Hcast. cbn [bind]. rewrite Hge. rewrite Hidxv. cbn [bind].
  pose proof (Hw10 ft Hin) as Hlen. unfold ft_results_wasm10 in Hlen.
  repeat rewrite vec_deref_spec.
  rewrite (require_single_result_intro _ Hlen). cbn [bind].
  rewrite branch_ok. cbn [bind].
  assert (Htn : translate_typelist (vec_list ft.(types_FuncType_params)) = tn)
    by (injection Hft as Ha _; exact Ha).
  destruct (consume_cons_inv (fv_ct f) (T_num T_i32) tn ct' Hcon)
    as [ct1 [Hcon1 Hcon2]].
  (* the table index *)
  destruct (pop_with_type_complete st2 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 ct1 Hsplit2 Hbase2 Hunr2
              (ltac:(pose proof (room_fit st Hroom); lia)) Hcon1)
    as [t3 [st3 Hpw]].
  rewrite Hpw. cbn [bind]. rewrite branch_ok. cbn [bind].
  pose proof (pop_with_type_size st2 _ _ st3 Hpw) as Hs3.
  destruct (pop_with_type_sim st2 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 t3 st3 Hsplit2 Hbase2 Hunr2 Hpw)
    as [seg1 [Hc3 [Hv3 Hsim1]]].
  destruct (cur_views_ctrls st2 st3 Hc3) as [Hb3 Hu3].
  assert (Hct1 : ct1 = <<translate_vals seg1,
                         (fv_ctrl f).(code_Ctrl_polymorphic_base)>>).
  { pose proof Hsim1 as Hs. cbn [translate_vt_v] in Hs.
    rewrite Hcon1 in Hs. injection Hs as Hs. exact Hs. }
  rewrite Hct1 in Hcon2.
  (* then the parameters, on the frame with the shortened segment *)
  destruct (pop_types_complete st3 (List.concat (List.map fv_seg pre))
              {| fv_ctrl := fv_ctrl f; fv_seg := seg1;
                  fv_done := fv_done f; fv_then := fv_then f |}
              ft.(types_FuncType_params) ct'
              (ltac:(cbn [fv_seg]; exact Hv3))
              (ltac:(cbn [fv_ctrl]; rewrite Hb3; exact Hbase2))
              (ltac:(cbn [fv_ctrl]; rewrite Hu3; exact Hunr2))
              (ltac:(pose proof (pop_with_type_fit st2 _ _ st3
                                  ltac:(pose proof (room_fit st Hroom); lia)
                                  Hpw) as Hfit3; exact Hfit3))
              (ltac:(cbn [fv_ct fv_seg fv_ctrl]; rewrite Htn; exact Hcon2)))
    as [st4 Hpt].
  rewrite Hpt. cbn [bind]. rewrite branch_ok. cbn [bind].
  pose proof (pop_types_size st3 _ _ st4 Hpt) as Hs4.
  destruct (push_types_total st4 ft.(types_FuncType_results)) as [st5 Hpu].
  { assert (Hb5 : (List.length (vals_list st4.(code_OpIterState_vals))
                   + List.length (vec_list ft.(types_FuncType_results))
                   <= stack_size st + 1)%nat).
    { unfold stack_size in Hs1, Hs2, Hs3, Hs4 |- *. lia. }
    apply (proj1 (Nat2Z.inj_le _ _)) in Hb5.
    rewrite Nat2Z.inj_add in Hb5. rewrite Nat2Z.inj_add in Hb5.
    unfold room in Hroom. lia. }
  rewrite Hpu. cbn [bind]. exists idx, st5.
  split; [reflexivity | exact Hidx].
Qed.

(** [return]: the same shape as [br], with the result list coming from the
    context. Nothing is pushed, so no room hypothesis and no bottom-freeness
    obligation beyond what the pops preserve. *)
Lemma read_return_complete : forall C0 ctx st pre f ct',
  Inv C0 st (pre ++ [f]) ->
  consume (fv_ct f)
    (match ctx.(code_Context_results) with
     | None => []
     | Some vt => [translate_vt_v vt]
     end) = Some ct' ->
  room st ->
  exists st',
    code_read_return st ctx = Ok (Core_result_Result_Ok tt, st').
Proof.
  intros C0 ctx st pre f ct' Hinv Hcon Hroom.
  unfold code_read_return.
  assert (Hsnoc : ctrls_list st.(code_OpIterState_ctrls)
                  = List.map fv_ctrl pre ++ [fv_ctrl f]).
  { destruct Hinv as [K1 _]. rewrite K1. rewrite List.map_app. reflexivity. }
  destruct (Inv_split C0 st pre f Hinv) as [Hbase [Hsplit Hunr]].
  destruct ctx.(code_Context_results) as [vt|] eqn:Hresults; cbn [bind] in *.
  all:
  destruct (pop_block_results_complete st (List.concat (List.map fv_seg pre)) f
              (match ctx.(code_Context_results) with
               | None => Code_BlockType_Empty
               | Some vt => Code_BlockType_Value vt
               end) ct' Hsplit Hbase Hunr (room_fit st Hroom)
              ltac:(rewrite Hresults; exact Hcon))
    as [st1 Hpt].
  all: rewrite Hresults in Hpt; rewrite Hpt; cbn [bind];
       rewrite branch_ok; cbn [bind].
  all:
  destruct (mark_unreachable_total st1
              ltac:(pose proof (pop_block_results_size st _ _ st1 Hpt) as Hsz;
                     apply Nat2Z.inj_le in Hsz;
                     pose proof (room_fit st Hroom); lia)) as [st2 Hmu].
  all: rewrite Hmu; cbn [bind]; exists st2; reflexivity.
Qed.

(** [load] and [store]: the memarg decodes because the specification says so, the
    memory lookup and the alignment check are the ones the checker already made,
    and the pops come from its [consume]. *)
(** [memory.size] and [memory.grow]: the reserved byte is where the
    specification says, and the memory the checker looked up is the one the
    context has. *)
Lemma read_memory_size_complete : forall C0 module st pre f data m rest,
  Inv C0 st (pre ++ [f]) ->
  bytes_from data st.(code_OpIterState_pos) = 0 :: rest ->
  mems_agree module C0 ->
  lookup_N (tc_mems C0) 0%N = Some m ->
  room st ->
  exists st',
    code_read_memory_size st data module = Ok (Core_result_Result_Ok tt, st').
Proof.
  intros C0 module st pre f data m rest Hinv Hbytes Hag Hlk Hroom.
  unfold code_read_memory_size.
  destruct (read_reserved_zero_complete st data rest Hbytes)
    as [st1 [Hrz [_ [Hv2 Hc2]]]].
  rewrite Hrz. cbn [bind]. rewrite branch_ok. cbn [bind].
  pose proof (read_reserved_zero_size st data _ st1 Hrz) as Hs1.
  rewrite (require_memory_complete module C0 m Hag Hlk). cbn [bind].
  rewrite branch_ok. cbn [bind].
  destruct (push_val_total st1 (Code_StackType_Val Types_ValueType_I32))
    as [st2 Hpv].
  { apply room_vals. unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. exists st2. reflexivity.
Qed.

Lemma read_memory_grow_complete : forall C0 module st pre f data m rest ct',
  Inv C0 st (pre ++ [f]) ->
  bytes_from data st.(code_OpIterState_pos) = 0 :: rest ->
  mems_agree module C0 ->
  lookup_N (tc_mems C0) 0%N = Some m ->
  consume (fv_ct f) [T_num T_i32] = Some ct' ->
  room st ->
  exists st',
    code_read_memory_grow st data module = Ok (Core_result_Result_Ok tt, st').
Proof.
  intros C0 module st pre f data m rest ct'
         Hinv Hbytes Hag Hlk Hcon Hroom.
  unfold code_read_memory_grow.
  destruct (read_reserved_zero_complete st data rest Hbytes)
    as [st1 [Hrz [_ [Hv2 Hc2]]]].
  rewrite Hrz. cbn [bind]. rewrite branch_ok. cbn [bind].
  assert (Hinv2 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_fields C0 st st1 _ Hv2 Hc2 Hinv)).
  pose proof (read_reserved_zero_size st data _ st1 Hrz) as Hs1.
  rewrite (require_memory_complete module C0 m Hag Hlk). cbn [bind].
  rewrite branch_ok. cbn [bind].
  destruct (Inv_split C0 st1 pre f Hinv2) as [Hbase2 [Hsplit2 Hunr2]].
  destruct (pop_with_type_complete st1 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 ct' Hsplit2 Hbase2 Hunr2
              (ltac:(pose proof (room_fit st Hroom); lia)) Hcon)
    as [t3 [st2 Hp3]].
  rewrite Hp3. cbn [bind]. rewrite branch_ok. cbn [bind].
  pose proof (pop_with_type_size st1 _ _ st2 Hp3) as Hs2.
  destruct (push_val_total st2 (Code_StackType_Val Types_ValueType_I32))
    as [st3 Hpv].
  { apply room_vals. unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. exists st3. reflexivity.
Qed.

Lemma read_load_complete :
  forall C0 st pre f data module ty natural a o rest m0 ct',
  Inv C0 st (pre ++ [f]) ->
  repr_memarg (bytes_from data st.(code_OpIterState_pos)) (a, o) rest ->
  mems_agree module C0 ->
  lookup_N (tc_mems C0) 0%N = Some m0 ->
  a <= to_Z natural ->
  consume (fv_ct f) [translate_vt_v Types_ValueType_I32] = Some ct' ->
  room st ->
  exists m st', code_read_load st data module ty natural
                  = Ok (Core_result_Result_Ok m, st')
                /\ to_Z m.(code_MemArg_align) = a
                /\ to_Z m.(code_MemArg_offset) = o.
Proof.
  intros C0 st pre f data module ty natural a o rest m0 ct'
         Hinv Hrep Hmems Hlk Hal Hcon Hroom.
  unfold code_read_load.
  (* the immediates *)
  destruct (read_memarg_complete st data a o rest Hrep) as [m [st1 [Hma [Hmal
              [Hmof Hmrest]]]]].
  rewrite Hma. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (read_memarg_state st data m st1 Hma) as [Hmv Hmc].
  pose proof (read_memarg_size st data _ st1 Hma) as Hs1.
  assert (Hinv2 : Inv C0 st1 (pre ++ [f])).
  { apply (Inv_fields C0 st st1 _); [rewrite Hmv | rewrite Hmc |];
      try reflexivity. exact Hinv. }
  (* memory and alignment *)
  rewrite (check_memory_and_alignment_complete module C0 m natural m0 Hmems Hlk
             (ltac:(rewrite Hmal; exact Hal))).
  cbn [bind]. rewrite branch_ok. cbn [bind].
  (* the address pop *)
  destruct (Inv_split C0 st1 pre f Hinv2) as [Hbase [Hsplit Hunr]].
  destruct (pop_with_type_complete st1 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 ct' Hsplit Hbase Hunr
              (ltac:(pose proof (room_fit st Hroom); lia)) Hcon)
    as [t [st2 Hpop]].
  rewrite Hpop. cbn [bind]. rewrite branch_ok. cbn [bind].
  pose proof (pop_with_type_size st1 Types_ValueType_I32 _ st2 Hpop) as Hs2.
  (* the push *)
  destruct (push_val_total st2 (Code_StackType_Val ty)) as [st3 Hpv].
  { apply room_vals. unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. exists m, st3. split; [reflexivity|].
  split; [exact Hmal|]. exact Hmof.
Qed.

Lemma read_store_complete :
  forall C0 st pre f data module ty natural a o rest m0 ct',
  Inv C0 st (pre ++ [f]) ->
  repr_memarg (bytes_from data st.(code_OpIterState_pos)) (a, o) rest ->
  mems_agree module C0 ->
  lookup_N (tc_mems C0) 0%N = Some m0 ->
  a <= to_Z natural ->
  consume (fv_ct f) [translate_vt_v ty; translate_vt_v Types_ValueType_I32]
    = Some ct' ->
  room st ->
  exists m st', code_read_store st data module ty natural
                  = Ok (Core_result_Result_Ok m, st')
                /\ to_Z m.(code_MemArg_align) = a
                /\ to_Z m.(code_MemArg_offset) = o.
Proof.
  intros C0 st pre f data module ty natural a o rest m0 ct'
         Hinv Hrep Hmems Hlk Hal Hcon Hroom.
  unfold code_read_store.
  destruct (read_memarg_complete st data a o rest Hrep) as [m [st1 [Hma [Hmal
              [Hmof Hmrest]]]]].
  rewrite Hma. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (read_memarg_state st data m st1 Hma) as [Hmv Hmc].
  pose proof (read_memarg_size st data _ st1 Hma) as Hs1.
  assert (Hinv2 : Inv C0 st1 (pre ++ [f])).
  { apply (Inv_fields C0 st st1 _); [rewrite Hmv | rewrite Hmc |];
      try reflexivity. exact Hinv. }
  rewrite (check_memory_and_alignment_complete module C0 m natural m0 Hmems Hlk
             (ltac:(rewrite Hmal; exact Hal))).
  cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (Inv_split C0 st1 pre f Hinv2) as [Hbase [Hsplit Hunr]].
  destruct (consume_cons_inv (fv_ct f) (translate_vt_v ty)
              [translate_vt_v Types_ValueType_I32] ct' Hcon)
    as [ct1 [Hcon1 Hcon2]].
  (* the stored value *)
  destruct (pop_with_type_complete st1 (List.concat (List.map fv_seg pre)) f
              ty ct1 Hsplit Hbase Hunr
              (ltac:(pose proof (room_fit st Hroom); lia)) Hcon1)
    as [t1 [st2 Hp1]].
  rewrite Hp1. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (pop_with_type_sim st1 (List.concat (List.map fv_seg pre)) f
              ty t1 st2 Hsplit Hbase Hunr Hp1) as [seg1 [Hc3 [Hv3 Hsim1]]].
  destruct (cur_views_ctrls st1 st2 Hc3) as [Hb3 Hu3].
  assert (Hct1 : ct1 = <<translate_vals seg1,
                         (fv_ctrl f).(code_Ctrl_polymorphic_base)>>).
  { pose proof Hsim1 as Hs. rewrite Hcon1 in Hs. injection Hs as Hs. exact Hs. }
  rewrite Hct1 in Hcon2.
  (* the address *)
  destruct (pop_with_type_complete st2 (List.concat (List.map fv_seg pre))
              {| fv_ctrl := fv_ctrl f; fv_seg := seg1;
                  fv_done := fv_done f; fv_then := fv_then f |}
              Types_ValueType_I32 ct') as [t2 [st3 Hp2]].
  { cbn [fv_seg]. exact Hv3. }
  { cbn [fv_ctrl]. rewrite Hb3. exact Hbase. }
  { cbn [fv_ctrl]. rewrite Hu3. exact Hunr. }
  { exact (pop_with_type_fit st1 _ _ st2
             ltac:(pose proof (room_fit st Hroom); lia) Hp1). }
  { cbn [fv_ct fv_seg fv_ctrl]. exact Hcon2. }
  rewrite Hp2. cbn [bind]. rewrite branch_ok. cbn [bind].
  exists m, st3. split; [reflexivity|].
  split; [exact Hmal|]. exact Hmof.
Qed.
