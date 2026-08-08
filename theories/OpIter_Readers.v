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
Require Import Veriwasm.Aeneas_Specs.
Require Import Veriwasm.Translate.
Require Import Veriwasm.Spec_Binary.
Require Import Veriwasm.OpIter_State.
Require Import Veriwasm.OpIter_Decode.
Require Import Veriwasm.OpIter_Protocol.
Require Import Veriwasm.OpIter_Sim.
Require Import Veriwasm.OpIter_Checker.

From Wasm Require Import datatypes numerics type_checker operations typing.

(* Mathcomp is not imported here, so [++] is [List.app] and [rewrite <-] works.
   Binding the type keeps it that way despite mathcomp's own [Bind Scope]. *)
Local Open Scope list_scope.
Local Bind Scope list_scope with list.
Open Scope Z_scope.

(* ================================================================== *)
(** ** The readers with no immediates                                   *)
(* ================================================================== *)

Lemma read_nop_complete : forall st b,
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_nop ->
  exists st', opiter_read_nop st = Ok (Core_result_Result_Ok tt, st').
Proof.
  intros st b Hp Hb. unfold opiter_read_nop.
  destruct (take_pending_ok st opiter_op_nop b Hp Hb) as [st1 [Htp [Hobs _]]].
  exists st1. exact Htp.
Qed.

Lemma read_unreachable_complete : forall st b,
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_unreachable ->
  exists st', opiter_read_unreachable st = Ok (Core_result_Result_Ok tt, st').
Proof.
  intros st b Hp Hb. unfold opiter_read_unreachable.
  destruct (take_pending_ok st opiter_op_unreachable b Hp Hb) as [st1 [Htp _]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (mark_unreachable_total st1) as [st2 Hmu].
  rewrite Hmu. cbn [bind]. exists st2. reflexivity.
Qed.

(** [drop]'s only failure is an exhausted frame that is not unreachable, which is
    exactly when [type_update_drop] returns [None]. *)
Lemma drop_disj : forall f ct',
  type_update_drop (fv_ct f) = Some ct' ->
  fv_seg f <> [] \/ (fv_ctrl f).(opiter_Ctrl_polymorphic_base) = true.
Proof.
  intros f ct' H.
  assert (Hcase : fv_seg f = [] \/ fv_seg f <> []).
  { destruct (fv_seg f); [left; reflexivity | right; discriminate]. }
  destruct Hcase as [Hnil|Hne]; [|left; exact Hne]. right.
  unfold type_update_drop, fv_ct in H. rewrite Hnil in H.
  cbn [translate_vals List.map List.rev CT_type CT_unr] in H.
  destruct ((fv_ctrl f).(opiter_Ctrl_polymorphic_base));
    [reflexivity | discriminate].
Qed.

Lemma read_drop_complete : forall C0 st pre f b ct',
  Inv C0 st (pre ++ [f]) ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_drop ->
  type_update_drop (fv_ct f) = Some ct' ->
  exists t st', opiter_read_drop st = Ok (Core_result_Result_Ok t, st').
Proof.
  intros C0 st pre f b ct' Hinv Hp Hb Hdrop. unfold opiter_read_drop.
  destruct (take_pending_ok st opiter_op_drop b Hp Hb) as [st1 [Htp [Hobs _]]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase [Hsplit Hunr]].
  destruct (pop_stack_type_complete st1 (List.concat (List.map fv_seg pre)) f
              Hsplit Hbase Hunr (drop_disj f ct' Hdrop)) as [t [st2 Hps]].
  exists t, st2. exact Hps.
Qed.

(* ================================================================== *)
(** ** select                                                          *)
(* ================================================================== *)

(** The plumbing, so the four segment shapes below differ only in how they
    supply the three pops and the join. *)
Lemma read_select_of_pops : forall st st1 t1 st2 t2 st3 t3 st4 t,
  opiter_take_pending st opiter_op_select
    = Ok (Core_result_Result_Ok tt, st1) ->
  opiter_pop_with_type st1 Types_ValueType_I32
    = Ok (Core_result_Result_Ok t1, st2) ->
  opiter_pop_stack_type st2 = Ok (Core_result_Result_Ok t2, st3) ->
  opiter_pop_stack_type st3 = Ok (Core_result_Result_Ok t3, st4) ->
  opiter_join_stack_type t2 t3 = Ok (Core_result_Result_Ok t) ->
  room st ->
  exists st5, opiter_read_select st = Ok (Core_result_Result_Ok t, st5).
Proof.
  intros st st1 t1 st2 t2 st3 t3 st4 t Htp Hq1 Hq2 Hq3 Hj Hroom.
  destruct (push_val_total st4 t) as [st5 Hpv].
  { apply room_vals.
    pose proof (take_pending_size st opiter_op_select _ st1 Htp) as Hs1.
    pose proof (pop_with_type_size st1 _ _ st2 Hq1) as Hs2.
    pose proof (pop_stack_type_size st2 _ st3 Hq2) as Hs3.
    pose proof (pop_stack_type_size st3 _ st4 Hq3) as Hs4.
    unfold room in Hroom |- *. lia. }
  exists st5. unfold opiter_read_select.
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
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
Lemma select_no_operands : forall st st1 pre f t1 st2,
  opiter_take_pending st opiter_op_select
    = Ok (Core_result_Result_Ok tt, st1) ->
  opiter_pop_with_type st1 Types_ValueType_I32
    = Ok (Core_result_Result_Ok t1, st2) ->
  cur_base_nat st1 = List.length (List.concat (List.map fv_seg pre)) ->
  cur_unr st1 = (fv_ctrl f).(opiter_Ctrl_polymorphic_base) ->
  vec_list st2.(opiter_OpIterState_vals)
    = List.concat (List.map fv_seg pre) ++ [] ->
  cur_base_nat st2 = cur_base_nat st1 ->
  cur_unr st2 = cur_unr st1 ->
  (fv_ctrl f).(opiter_Ctrl_polymorphic_base) = true ->
  room st ->
  exists t st', opiter_read_select st = Ok (Core_result_Result_Ok t, st').
Proof.
  intros st st1 pre f t1 st2 Htp Hq1 Hbase1 Hunr1 Hv2 Hb2 Hu2 Hu Hroom.
  assert (Hq2 : opiter_pop_stack_type st2
                = Ok (Core_result_Result_Ok Opiter_StackType_Bot, st2)).
  { apply (pop_stack_type_empty st2 (List.concat (List.map fv_seg pre))
             {| fv_ctrl := fv_ctrl f; fv_seg := [];
                  fv_done := []; fv_then := [] |}).
    - cbn [fv_seg]. exact Hv2.
    - cbn [fv_ctrl]. rewrite Hb2. exact Hbase1.
    - cbn [fv_ctrl]. rewrite Hu2. exact Hunr1.
    - reflexivity.
    - cbn [fv_ctrl]. exact Hu. }
  destruct (join_stack_type_bot_l_ok Opiter_StackType_Bot) as [t Hj].
  exists t.
  destruct (read_select_of_pops st st1 t1 st2 Opiter_StackType_Bot st2
              Opiter_StackType_Bot st2 t Htp Hq1 Hq2 Hq2 Hj Hroom)
    as [st5 Hrd].
  exists st5. exact Hrd.
Qed.

Lemma read_select_complete : forall C0 st pre f b ct',
  Inv C0 st (pre ++ [f]) ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_select ->
  type_update_select (fv_ct f) None = Some ct' ->
  room st ->
  exists t st', opiter_read_select st = Ok (Core_result_Result_Ok t, st').
Proof.
  intros C0 st pre f b ct' Hinv Hp Hb Hsel Hroom.
  destruct (take_pending_ok st opiter_op_select b Hp Hb)
    as [st1 [Htp [Hobs _]]].
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  destruct (select_disj f ct' Hsel) as [[ct1 Hcons] Hshape].
  (* the condition, the one pop the checker types *)
  destruct (pop_with_type_complete st1 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 ct1 Hsplit1 Hbase1 Hunr1 Hcons)
    as [t1 [st2 Hq1]].
  destruct (pop_with_type_ok st1 _ t1 st2 Hq1) as [Hraw1 _].
  destruct (pop_stack_type_sim st1 (List.concat (List.map fv_seg pre)) f
              t1 st2 Hsplit1 Hbase1 Hunr1 Hraw1) as [seg1 [Hc2 [Hv2 D1]]].
  destruct (cur_views_ctrls st1 st2 Hc2) as [Hb2 Hu2].
  destruct Hshape as [[s [z [y [x [Hs Hjoin]]]]]
                     |[[[y [x Hs]] Hu]
                     | [[Hs | [x Hs]] Hu]]].
  - (* three or more visible, so both values are real and have to agree *)
    assert (Hseg1 : seg1 = s ++ [z; y]).
    { destruct D1 as [HL | [HR1 _]].
      - rewrite Hs in HL. rewrite snoc3_split in HL.
        apply List.app_inj_tail in HL as [HL _]. symmetry. exact HL.
      - exfalso. rewrite Hs in HR1. destruct s; discriminate HR1. }
    destruct (pop_stack_type_real st2 (List.concat (List.map fv_seg pre))
                {| fv_ctrl := fv_ctrl f; fv_seg := seg1;
                  fv_done := []; fv_then := [] |}
                (s ++ [z]) y) as [st3 [Hq2 [Hc3 Hv3]]].
    { cbn [fv_seg]. exact Hv2. }
    { cbn [fv_ctrl]. rewrite Hb2. exact Hbase1. }
    { cbn [fv_ctrl]. rewrite Hu2. exact Hunr1. }
    { cbn [fv_seg]. rewrite Hseg1. apply snoc2_split. }
    destruct (cur_views_ctrls st2 st3 Hc3) as [Hb3 Hu3].
    destruct (pop_stack_type_real st3 (List.concat (List.map fv_seg pre))
                {| fv_ctrl := fv_ctrl f; fv_seg := s ++ [z];
                  fv_done := []; fv_then := [] |}
                s z) as [st4 [Hq3 [Hc4 Hv4]]].
    { cbn [fv_seg]. exact Hv3. }
    { cbn [fv_ctrl]. rewrite Hb3. rewrite Hb2. exact Hbase1. }
    { cbn [fv_ctrl]. rewrite Hu3. rewrite Hu2. exact Hunr1. }
    { cbn [fv_seg]. reflexivity. }
    destruct Hjoin as [t Hj].
    exists t.
    destruct (read_select_of_pops st st1 t1 st2 y st3 z st4 t Htp Hq1 Hq2 Hq3 Hj
                Hroom) as [st5 Hrd].
    exists st5. exact Hrd.
  - (* exactly two, so the first value comes off Bot and the join keeps the
       second *)
    assert (Hseg1 : seg1 = [y]).
    { destruct D1 as [HL | [HR1 _]].
      - rewrite Hs in HL. change [y; x] with ([y] ++ [x]) in HL.
        apply List.app_inj_tail in HL as [HL _]. symmetry. exact HL.
      - exfalso. rewrite Hs in HR1. discriminate HR1. }
    destruct (pop_stack_type_real st2 (List.concat (List.map fv_seg pre))
                {| fv_ctrl := fv_ctrl f; fv_seg := seg1;
                  fv_done := []; fv_then := [] |}
                [] y) as [st3 [Hq2 [Hc3 Hv3]]].
    { cbn [fv_seg]. exact Hv2. }
    { cbn [fv_ctrl]. rewrite Hb2. exact Hbase1. }
    { cbn [fv_ctrl]. rewrite Hu2. exact Hunr1. }
    { cbn [fv_seg]. rewrite Hseg1. reflexivity. }
    destruct (cur_views_ctrls st2 st3 Hc3) as [Hb3 Hu3].
    assert (Hq3 : opiter_pop_stack_type st3
                  = Ok (Core_result_Result_Ok Opiter_StackType_Bot, st3)).
    { apply (pop_stack_type_empty st3 (List.concat (List.map fv_seg pre))
               {| fv_ctrl := fv_ctrl f; fv_seg := [];
                  fv_done := []; fv_then := [] |}).
      - cbn [fv_seg]. exact Hv3.
      - cbn [fv_ctrl]. rewrite Hb3. rewrite Hb2. exact Hbase1.
      - cbn [fv_ctrl]. rewrite Hu3. rewrite Hu2. exact Hunr1.
      - reflexivity.
      - cbn [fv_ctrl]. exact Hu. }
    destruct (join_stack_type_bot_r_ok y) as [t Hj].
    exists t.
    destruct (read_select_of_pops st st1 t1 st2 y st3 Opiter_StackType_Bot st3 t
                Htp Hq1 Hq2 Hq3 Hj Hroom) as [st5 Hrd].
    exists st5. exact Hrd.
  - (* nothing visible at all *)
    assert (Hseg1 : seg1 = []).
    { destruct D1 as [HL | [_ [HR2 _]]].
      - rewrite Hs in HL. destruct seg1; [reflexivity | discriminate HL].
      - exact HR2. }
    rewrite Hseg1 in Hv2.
    apply (select_no_operands st st1 pre f t1 st2
             Htp Hq1 Hbase1 Hunr1 Hv2 Hb2 Hu2 Hu Hroom).
  - (* only the condition was visible *)
    assert (Hseg1 : seg1 = []).
    { destruct D1 as [HL | [_ [HR2 _]]].
      - rewrite Hs in HL. change [x] with (@nil opiter_StackType_t ++ [x]) in HL.
        apply List.app_inj_tail in HL as [HL _]. symmetry. exact HL.
      - exact HR2. }
    rewrite Hseg1 in Hv2.
    apply (select_no_operands st st1 pre f t1 st2
             Htp Hq1 Hbase1 Hunr1 Hv2 Hb2 Hu2 Hu Hroom).
Qed.

Lemma read_binary_complete : forall C0 st pre f b opcode ty res ct',
  Inv C0 st (pre ++ [f]) ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opcode ->
  consume (fv_ct f) [translate_vt_v ty; translate_vt_v ty] = Some ct' ->
  room st ->
  exists st', opiter_read_binary st opcode ty res
                = Ok (Core_result_Result_Ok tt, st').
Proof.
  intros C0 st pre f b opcode ty res ct' Hinv Hp Hb Hcon Hroom.
  unfold opiter_read_binary.
  destruct (take_pending_ok st opcode b Hp Hb) as [st1 [Htp [Hobs _]]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 _]].
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  destruct (consume_cons_inv (fv_ct f) (translate_vt_v ty)
              [translate_vt_v ty] ct' Hcon) as [ct1 [Hcon1 Hcon2]].
  (* first pop *)
  destruct (pop_with_type_complete st1 (List.concat (List.map fv_seg pre)) f
              ty ct1 Hsplit1 Hbase1 Hunr1
              Hcon1)
    as [t1 [st2 Hp1]].
  rewrite Hp1. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (pop_with_type_sim st1 (List.concat (List.map fv_seg pre)) f
              ty t1 st2 Hsplit1 Hbase1 Hunr1 Hp1) as [seg1 [Hc2 [Hv2 Hsim1]]].
  (* the frame with the shortened segment, which is what the second pop sees *)
  destruct (cur_views_ctrls st1 st2 Hc2) as [Hb2 Hu2].
  assert (Hct1 : ct1 = <<translate_vals seg1,
                         (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>>).
  { pose proof Hsim1 as Hs. rewrite Hcon1 in Hs. injection Hs as Hs. exact Hs. }
  rewrite Hct1 in Hcon2.
  (* second pop *)
  destruct (pop_with_type_complete st2 (List.concat (List.map fv_seg pre))
              {| fv_ctrl := fv_ctrl f; fv_seg := seg1;
                  fv_done := fv_done f; fv_then := fv_then f |}
              ty ct') as [t2 [st3 Hp2]].
  { cbn [fv_seg]. exact Hv2. }
  { cbn [fv_ctrl]. rewrite Hb2. exact Hbase1. }
  { cbn [fv_ctrl]. rewrite Hu2. exact Hunr1. }
  { cbn [fv_ct fv_seg fv_ctrl]. exact Hcon2. }
  rewrite Hp2. cbn [bind]. rewrite branch_ok. cbn [bind].
  (* the push *)
  destruct (push_val_total st3 (Opiter_StackType_Val res)) as [st4 Hpv].
  { apply room_vals.
    pose proof (pop_with_type_size st1 ty _ st2 Hp1) as Hs2.
    pose proof (pop_with_type_size st2 ty _ st3 Hp2) as Hs3.
    pose proof (take_pending_size st opcode _ st1 Htp) as Hs1.
    unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. exists st4. reflexivity.
Qed.

Lemma read_conversion_complete : forall C0 st pre f b opcode from to ct',
  Inv C0 st (pre ++ [f]) ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opcode ->
  consume (fv_ct f) [translate_vt_v from] = Some ct' ->
  room st ->
  exists st', opiter_read_conversion st opcode from to
                = Ok (Core_result_Result_Ok tt, st').
Proof.
  intros C0 st pre f b opcode from to ct' Hinv Hp Hb Hcon Hroom.
  unfold opiter_read_conversion.
  destruct (take_pending_ok st opcode b Hp Hb) as [st1 [Htp [Hobs _]]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  destruct (pop_with_type_complete st1 (List.concat (List.map fv_seg pre)) f
              from ct' Hsplit1 Hbase1 Hunr1
              Hcon)
    as [t1 [st2 Hp1]].
  rewrite Hp1. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (push_val_total st2 (Opiter_StackType_Val to)) as [st3 Hpv].
  { apply room_vals.
    pose proof (pop_with_type_size st1 from _ st2 Hp1) as Hs2.
    pose proof (take_pending_size st opcode _ st1 Htp) as Hs1.
    unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. exists st3. reflexivity.
Qed.

(* ================================================================== *)
(** ** The readers with immediates                                      *)
(* ================================================================== *)

Lemma read_i32_const_complete : forall st data b z rest,
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_i32_const ->
  repr_s32 (bytes_from data st.(opiter_OpIterState_pos)) z rest ->
  room st ->
  exists v st', opiter_read_i32_const st data
                  = Ok (Core_result_Result_Ok v, st')
                /\ to_Z v = z.
Proof.
  intros st data b z rest Hp Hb Hrep Hroom.
  unfold opiter_read_i32_const.
  destruct (take_pending_ok st opiter_op_i32_const b Hp Hb)
    as [st1 [Htp [Hobs _]]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 Hpos1]].
  rewrite <- Hpos1 in Hrep.
  destruct (read_s32_leb_complete data st1.(opiter_OpIterState_pos) z rest Hrep)
    as [v [p1 [Hleb [Hval Hrest]]]].
  rewrite Hleb. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (push_val_total
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending :=
                   st1.(opiter_OpIterState_pending) |}
              (Opiter_StackType_Val Types_ValueType_I32)) as [st2 Hpv].
  { cbn [opiter_OpIterState_vals]. rewrite Hv1. apply room_vals. exact Hroom. }
  rewrite Hpv. cbn [bind]. exists v, st2. split; [reflexivity|].
  exact Hval.
Qed.

Lemma read_f32_const_complete : forall st data b z rest,
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_f32_const ->
  repr_bytes_le 4 (bytes_from data st.(opiter_OpIterState_pos)) z rest ->
  room st ->
  exists v st', opiter_read_f32_const st data
                  = Ok (Core_result_Result_Ok v, st')
                /\ to_Z v = z.
Proof.
  intros st data b z rest Hp Hb Hrep Hroom.
  unfold opiter_read_f32_const.
  destruct (take_pending_ok st opiter_op_f32_const b Hp Hb)
    as [st1 [Htp [Hobs _]]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 Hpos1]].
  rewrite <- Hpos1 in Hrep.
  destruct (read_f32_bits_complete data st1.(opiter_OpIterState_pos) z rest Hrep)
    as [v [p1 [Hleb [Hval Hrest]]]].
  rewrite Hleb. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (push_val_total
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending :=
                   st1.(opiter_OpIterState_pending) |}
              (Opiter_StackType_Val Types_ValueType_F32)) as [st2 Hpv].
  { cbn [opiter_OpIterState_vals]. rewrite Hv1. apply room_vals. exact Hroom. }
  rewrite Hpv. cbn [bind]. exists v, st2. split; [reflexivity|].
  exact Hval.
Qed.

Lemma read_f64_const_complete : forall st data b z rest,
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_f64_const ->
  repr_bytes_le 8 (bytes_from data st.(opiter_OpIterState_pos)) z rest ->
  room st ->
  exists v st', opiter_read_f64_const st data
                  = Ok (Core_result_Result_Ok v, st')
                /\ to_Z v = z.
Proof.
  intros st data b z rest Hp Hb Hrep Hroom.
  unfold opiter_read_f64_const.
  destruct (take_pending_ok st opiter_op_f64_const b Hp Hb)
    as [st1 [Htp [Hobs _]]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 Hpos1]].
  rewrite <- Hpos1 in Hrep.
  destruct (read_f64_bits_complete data st1.(opiter_OpIterState_pos) z rest Hrep)
    as [v [p1 [Hleb [Hval Hrest]]]].
  rewrite Hleb. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (push_val_total
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending :=
                   st1.(opiter_OpIterState_pending) |}
              (Opiter_StackType_Val Types_ValueType_F64)) as [st2 Hpv].
  { cbn [opiter_OpIterState_vals]. rewrite Hv1. apply room_vals. exact Hroom. }
  rewrite Hpv. cbn [bind]. exists v, st2. split; [reflexivity|].
  exact Hval.
Qed.

Lemma read_i64_const_complete : forall st data b z rest,
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_i64_const ->
  repr_sN 64 (bytes_from data st.(opiter_OpIterState_pos)) z rest ->
  room st ->
  exists v st', opiter_read_i64_const st data
                  = Ok (Core_result_Result_Ok v, st')
                /\ to_Z v = z.
Proof.
  intros st data b z rest Hp Hb Hrep Hroom.
  unfold opiter_read_i64_const.
  destruct (take_pending_ok st opiter_op_i64_const b Hp Hb)
    as [st1 [Htp [Hobs _]]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 Hpos1]].
  rewrite <- Hpos1 in Hrep.
  destruct (read_s64_leb_complete data st1.(opiter_OpIterState_pos) z rest Hrep)
    as [v [p1 [Hleb [Hval Hrest]]]].
  rewrite Hleb. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (push_val_total
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending :=
                   st1.(opiter_OpIterState_pending) |}
              (Opiter_StackType_Val Types_ValueType_I64)) as [st2 Hpv].
  { cbn [opiter_OpIterState_vals]. rewrite Hv1. apply room_vals. exact Hroom. }
  rewrite Hpv. cbn [bind]. exists v, st2. split; [reflexivity|].
  exact Hval.
Qed.

(** [block] and [loop] differ only in the kind they push, so the two proofs are
    the same modulo that argument. *)
Lemma read_block_complete : forall st data b bb bt rest,
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_block ->
  bytes_from data st.(opiter_OpIterState_pos) = bb :: rest ->
  blocktype_spec bb = Some bt ->
  room st ->
  exists bt' st', opiter_read_block st data
                    = Ok (Core_result_Result_Ok bt', st')
                  /\ translate_bt bt' = bt.
Proof.
  intros st data b bb bt rest Hp Hb Hbs Hspec Hroom.
  unfold opiter_read_block.
  destruct (take_pending_ok st opiter_op_block b Hp Hb) as [st1 [Htp [Hobs _]]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 Hpos1]].
  rewrite <- Hpos1 in Hbs.
  destruct (read_block_type_complete data st1.(opiter_OpIterState_pos) bb bt rest
              Hbs Hspec) as [bt' [p1 [Hrbt [Htr Hrest]]]].
  rewrite Hrbt. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (push_ctrl_total
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending :=
                   st1.(opiter_OpIterState_pending) |}
              Opiter_LabelKind_Block bt') as [st2 Hpc].
  { cbn [opiter_OpIterState_ctrls]. rewrite Hc1. apply room_ctrls. exact Hroom. }
  rewrite Hpc. cbn [bind]. exists bt', st2.
  split; [reflexivity | exact Htr].
Qed.

Lemma read_loop_complete : forall st data b bb bt rest,
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_loop ->
  bytes_from data st.(opiter_OpIterState_pos) = bb :: rest ->
  blocktype_spec bb = Some bt ->
  room st ->
  exists bt' st', opiter_read_loop st data
                    = Ok (Core_result_Result_Ok bt', st')
                  /\ translate_bt bt' = bt.
Proof.
  intros st data b bb bt rest Hp Hb Hbs Hspec Hroom.
  unfold opiter_read_loop.
  destruct (take_pending_ok st opiter_op_loop b Hp Hb) as [st1 [Htp [Hobs _]]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 Hpos1]].
  rewrite <- Hpos1 in Hbs.
  destruct (read_block_type_complete data st1.(opiter_OpIterState_pos) bb bt rest
              Hbs Hspec) as [bt' [p1 [Hrbt [Htr Hrest]]]].
  rewrite Hrbt. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (push_ctrl_total
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending :=
                   st1.(opiter_OpIterState_pending) |}
              Opiter_LabelKind_Loop bt') as [st2 Hpc].
  { cbn [opiter_OpIterState_ctrls]. rewrite Hc1. apply room_ctrls. exact Hroom. }
  rewrite Hpc. cbn [bind]. exists bt', st2.
  split; [reflexivity | exact Htr].
Qed.

(** [if] is [block] plus the condition pop, so it needs the frame the condition
    comes off and the [consume] the checker performed for it. *)
Lemma read_if_complete : forall C0 st pre f data b bb bt rest ct',
  Inv C0 st (pre ++ [f]) ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_if ->
  bytes_from data st.(opiter_OpIterState_pos) = bb :: rest ->
  blocktype_spec bb = Some bt ->
  consume (fv_ct f) [T_num T_i32] = Some ct' ->
  room st ->
  exists bt' st', opiter_read_if st data = Ok (Core_result_Result_Ok bt', st')
                  /\ translate_bt bt' = bt.
Proof.
  intros C0 st pre f data b bb bt rest ct' Hinv Hp Hb Hbs Hspec Hcon Hroom.
  unfold opiter_read_if.
  destruct (take_pending_ok st opiter_op_if b Hp Hb) as [st1 [Htp [Hobs _]]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 Hpos1]].
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  rewrite <- Hpos1 in Hbs.
  destruct (read_block_type_complete data st1.(opiter_OpIterState_pos) bb bt rest
              Hbs Hspec) as [bt' [p1 [Hrbt [Htr Hrest]]]].
  rewrite Hrbt. cbn [bind]. rewrite branch_ok. cbn [bind].
  (* the cursor moved past the block type byte; nothing else did *)
  set (st2 := {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending :=
                   st1.(opiter_OpIterState_pending) |}).
  assert (Hinv2 : Inv C0 st2 (pre ++ [f]))
    by (apply (Inv_fields C0 st1 st2 _ (eq_refl _) (eq_refl _) Hinv1)).
  destruct (Inv_split C0 st2 pre f Hinv2) as [Hbase2 [Hsplit2 Hunr2]].
  destruct (pop_with_type_complete st2 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 ct' Hsplit2 Hbase2 Hunr2
              Hcon)
    as [t1 [st3 Hp1]].
  rewrite Hp1. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (push_ctrl_total st3 Opiter_LabelKind_Then bt') as [st4 Hpc].
  { apply room_ctrls. apply (room_le st st3); [|exact Hroom].
    pose proof (pop_with_type_size st2 _ _ st3 Hp1) as Hs3.
    pose proof (take_pending_size st opiter_op_if _ st1 Htp) as Hs1.
    assert (Hs2 : stack_size st2 = stack_size st1) by reflexivity. lia. }
  rewrite Hpc. cbn [bind]. exists bt', st4.
  split; [reflexivity | exact Htr].
Qed.

(** [else] closes the then-branch, which is [end]'s obligation over the same
    frame, and rewrites it in place rather than popping. The frame must be an
    open then-branch, which the caller learns from the operator stream: only an
    [if] puts an [FO_else] there. *)
Lemma read_else_complete : forall C0 st pre g b,
  Inv C0 st (pre ++ [g]) ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_else ->
  (fv_ctrl g).(opiter_Ctrl_kind) = Opiter_LabelKind_Then ->
  c_types_agree (fv_ct g)
    (translate_typelist (block_results_of (fv_ctrl g).(opiter_Ctrl_block_type)))
    = true ->
  exists bt st', opiter_read_else st = Ok (Core_result_Result_Ok bt, st').
Proof.
  intros C0 st pre g b Hinv Hp Hb Hkind Hagree.
  unfold opiter_read_else.
  destruct (take_pending_ok st opiter_op_else b Hp Hb) as [st1 [Htp [Hobs _]]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  assert (Hinv1 : Inv C0 st1 (pre ++ [g]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  assert (Hsnoc : vec_list st1.(opiter_OpIterState_ctrls)
                  = List.map fv_ctrl pre ++ [fv_ctrl g]).
  { destruct Hinv1 as [K1 _]. rewrite K1. rewrite List.map_app. reflexivity. }
  destruct (Inv_split C0 st1 pre g Hinv1) as [Hbase [Hsplit Hunr]].
  assert (Hgbase : Z.to_nat (to_Z (fv_ctrl g).(opiter_Ctrl_value_stack_base))
                   = List.length (List.concat (List.map fv_seg pre))).
  { unfold cur_base_nat in Hbase.
    rewrite (cur_ctrl_snoc st1 (List.map fv_ctrl pre) (fv_ctrl g) Hsnoc)
      in Hbase. exact Hbase. }
  assert (Hnz : (alloc_vec_Vec_len st1.(opiter_OpIterState_ctrls) s= 0%usize)
                = false).
  { unfold scalar_eqb. apply Z.eqb_neq. rewrite vec_len_spec. rewrite Hsnoc.
    rewrite List.app_length. cbn [List.length].
    assert (H0 : to_Z 0%usize = 0) by reflexivity. lia. }
  rewrite Hnz. cbn beta iota.
  destruct (ctrls_sub_ok st1 (List.map fv_ctrl pre) (fv_ctrl g) Hsnoc)
    as [i Hsub].
  rewrite Hsub. cbn [bind]. rewrite vec_index_spec.
  rewrite (ctrls_last_index st1 (List.map fv_ctrl pre) (fv_ctrl g) i Hsnoc Hsub).
  cbn [bind].
  (* the frame is an open then-branch, so the guard passes *)
  destruct (is_then_total (fv_ctrl g).(opiter_Ctrl_kind)) as [bth Hit].
  rewrite Hit. cbn [bind].
  destruct (is_then_spec _ _ Hit) as [[Hbth _] | [_ Hne]];
    [|exfalso; apply Hne; exact Hkind].
  rewrite Hbth. cbn beta iota.
  destruct (block_results_total (fv_ctrl g).(opiter_Ctrl_block_type))
    as [results Hbr].
  rewrite Hbr. cbn [bind]. rewrite vec_deref_spec.
  pose proof (block_results_spec _ _ Hbr) as Hres.
  destruct (consume_of_c_types_agree _ (fv_ct g) Hagree) as [unr Hcon0].
  assert (Hcon0' : consume (fv_ct g) (translate_typelist (vec_list results))
                   = Some <<[], unr>>) by (rewrite Hres; exact Hcon0).
  destruct (pop_types_complete st1 (List.concat (List.map fv_seg pre)) g
              results <<[], unr>> Hsplit Hbase Hunr
              Hcon0')
    as [st2 Hpt].
  rewrite Hpt. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (pop_types_sim st1 (List.concat (List.map fv_seg pre)) g results st2
              Hsplit Hbase Hunr Hpt) as [seg' [Hc2 [Hv2 Hcon]]].
  assert (Hempty : seg' = []).
  { apply translate_vals_nil_inv.
    pose proof Hcon as Hc'. rewrite Hcon0' in Hc'.
    apply (f_equal (fun o => match o with
                             | Some ct => CT_type ct
                             | None => [] end)) in Hc'.
    cbn in Hc'. symmetry. exact Hc'. }
  rewrite Hempty in Hv2.
  assert (Hne2 : (alloc_vec_Vec_len st2.(opiter_OpIterState_vals)
                  s<> (fv_ctrl g).(opiter_Ctrl_value_stack_base)) = false).
  { unfold scalar_neqb, scalar_eqb. apply Bool.negb_false_iff. apply Z.eqb_eq.
    rewrite vec_len_spec. rewrite Hv2. rewrite List.app_nil_r.
    pose proof (usize_nonneg (fv_ctrl g).(opiter_Ctrl_value_stack_base)). lia. }
  rewrite Hne2. cbn beta iota.
  (* the two in-place rewrites of the frame, as in [step_switch_else] *)
  assert (Hsnoc2 : vec_list st2.(opiter_OpIterState_ctrls)
                   = List.map fv_ctrl pre ++ [fv_ctrl g])
    by (rewrite Hc2; exact Hsnoc).
  assert (Hidxlen : Z.to_nat (to_Z i) = List.length (List.map fv_ctrl pre))
    by (apply (ctrls_last_index_len st1 (List.map fv_ctrl pre) (fv_ctrl g) i
                 Hsnoc Hsub)).
  assert (Hidxlen2 : (Z.to_nat (to_Z i)
                      < List.length (vec_list st2.(opiter_OpIterState_ctrls)))%nat).
  { rewrite Hsnoc2. rewrite List.app_length. cbn [List.length].
    rewrite Hidxlen. lia. }
  destruct (vec_index_mut_ok st2.(opiter_OpIterState_ctrls) i Hidxlen2)
    as [c [back Hidx2]].
  rewrite Hidx2. cbn [bind].
  destruct (vec_index_mut_of_snoc st2.(opiter_OpIterState_ctrls)
              (List.map fv_ctrl pre) (fv_ctrl g) i c back Hsnoc2 Hidxlen Hidx2)
    as [Hceq Hback].
  subst c.
  assert (Hidxlen3 : forall x, (Z.to_nat (to_Z i)
                      < List.length (vec_list (back x)))%nat).
  { intros x. rewrite (vec_index_mut_len _ _ _ _ Hidx2 x). exact Hidxlen2. }
  set (mid := {| opiter_Ctrl_kind := Opiter_LabelKind_Else;
                 opiter_Ctrl_block_type := (fv_ctrl g).(opiter_Ctrl_block_type);
                 opiter_Ctrl_value_stack_base :=
                   (fv_ctrl g).(opiter_Ctrl_value_stack_base);
                 opiter_Ctrl_polymorphic_base :=
                   (fv_ctrl g).(opiter_Ctrl_polymorphic_base) |} : opiter_Ctrl_t).
  destruct (vec_index_mut_ok (back mid) i (Hidxlen3 mid))
    as [c1 [back1 Hidx3]].
  rewrite Hidx3. cbn [bind].
  eexists. eexists. reflexivity.
Qed.

(** [end] is where the checker's [c_types_agree] obligation and the Rust's
    "results popped, nothing else left" check meet. [consume_of_c_types_agree]
    supplies the pops, and the emptiness check follows because the [consume] it
    supplies leaves an empty stack, hence an empty segment.

    Closing a [Then] frame is the [if] whose else-branch is empty, and the
    reader rejects one with a result type. That is not a gap in this direction
    either: the empty else-branch type-checks against [tm] only for [tm = []],
    so the caller has the hypothesis to hand. *)
Lemma read_end_complete : forall C0 st pre g b,
  Inv C0 st (pre ++ [g]) ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_end ->
  c_types_agree (fv_ct g)
    (translate_typelist (block_results_of (fv_ctrl g).(opiter_Ctrl_block_type)))
    = true ->
  ((fv_ctrl g).(opiter_Ctrl_kind) = Opiter_LabelKind_Then ->
   block_results_of (fv_ctrl g).(opiter_Ctrl_block_type) = []) ->
  room st ->
  exists r st', opiter_read_end st = Ok (Core_result_Result_Ok r, st').
Proof.
  intros C0 st pre g b Hinv Hp Hb Hagree Hthen Hroom.
  unfold opiter_read_end.
  destruct (take_pending_ok st opiter_op_end b Hp Hb) as [st1 [Htp [Hobs _]]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  assert (Hinv1 : Inv C0 st1 (pre ++ [g]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  pose proof (take_pending_size st opiter_op_end _ st1 Htp) as Hs1.
  assert (Hsnoc : vec_list st1.(opiter_OpIterState_ctrls)
                  = List.map fv_ctrl pre ++ [fv_ctrl g]).
  { destruct Hinv1 as [K1 _]. rewrite K1. rewrite List.map_app. reflexivity. }
  destruct (Inv_split C0 st1 pre g Hinv1) as [Hbase [Hsplit Hunr]].
  assert (Hgbase : Z.to_nat (to_Z (fv_ctrl g).(opiter_Ctrl_value_stack_base))
                   = List.length (List.concat (List.map fv_seg pre))).
  { unfold cur_base_nat in Hbase.
    rewrite (cur_ctrl_snoc st1 (List.map fv_ctrl pre) (fv_ctrl g) Hsnoc)
      in Hbase. exact Hbase. }
  (* the frame list is non-empty, so the [n = 0] branch cannot fire *)
  assert (Hnz : (alloc_vec_Vec_len st1.(opiter_OpIterState_ctrls) s= 0%usize)
                = false).
  { unfold scalar_eqb. apply Z.eqb_neq. rewrite vec_len_spec. rewrite Hsnoc.
    rewrite List.app_length. cbn [List.length].
    assert (H0 : to_Z 0%usize = 0) by reflexivity. lia. }
  rewrite Hnz. cbn beta iota.
  destruct (ctrls_sub_ok st1 (List.map fv_ctrl pre) (fv_ctrl g) Hsnoc)
    as [i Hsub].
  rewrite Hsub. cbn [bind]. rewrite vec_index_spec.
  rewrite (ctrls_last_index st1 (List.map fv_ctrl pre) (fv_ctrl g) i Hsnoc Hsub).
  cbn [bind].
  destruct (block_results_total (fv_ctrl g).(opiter_Ctrl_block_type))
    as [results Hbr].
  rewrite Hbr. cbn [bind].
  pose proof (block_results_spec _ _ Hbr) as Hres.
  (* the bare-[if] guard, discharged once rather than under each of the two
     copies of the tail the extraction made *)
  destruct (is_then_total (fv_ctrl g).(opiter_Ctrl_kind)) as [bth Hit].
  rewrite Hit. cbn [bind].
  rewrite (then_results_guard bth _ results _ _
             (ltac:(intros Hb1;
                    destruct (is_then_spec _ _ Hit) as [[_ Hk] | [Hbad _]];
                    [rewrite Hres; exact (Hthen Hk)
                    | rewrite Hbad in Hb1; discriminate Hb1]))).
  rewrite vec_deref_spec.
  pose proof (block_results_len _ results Hbr) as Hrlen.
  destruct (consume_of_c_types_agree _ (fv_ct g) Hagree) as [unr Hcon0].
  assert (Hcon0' : consume (fv_ct g) (translate_typelist (vec_list results))
                   = Some <<[], unr>>) by (rewrite Hres; exact Hcon0).
  destruct (pop_types_complete st1 (List.concat (List.map fv_seg pre)) g
              results <<[], unr>> Hsplit Hbase Hunr
              Hcon0')
    as [st2 Hpt].
  rewrite Hpt. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (pop_types_sim st1 (List.concat (List.map fv_seg pre)) g results st2
              Hsplit Hbase Hunr Hpt) as [seg' [Hc2 [Hv2 Hcon]]].
  (* the pops emptied the frame's segment, so nothing is left above its base *)
  assert (Hempty : seg' = []).
  { apply translate_vals_nil_inv.
    pose proof Hcon as Hc'. rewrite Hcon0' in Hc'.
    apply (f_equal (fun o => match o with
                             | Some ct => CT_type ct
                             | None => [] end)) in Hc'.
    cbn in Hc'. symmetry. exact Hc'. }
  rewrite Hempty in Hv2.
  assert (Hne : (alloc_vec_Vec_len st2.(opiter_OpIterState_vals)
                 s<> (fv_ctrl g).(opiter_Ctrl_value_stack_base)) = false).
  { unfold scalar_neqb, scalar_eqb. apply Bool.negb_false_iff. apply Z.eqb_eq.
    rewrite vec_len_spec. rewrite Hv2. rewrite List.app_nil_r.
    pose proof (usize_nonneg (fv_ctrl g).(opiter_Ctrl_value_stack_base)). lia. }
  rewrite Hne. cbn beta iota.
  destruct (vec_pop_ok alloc_alloc_Global st2.(opiter_OpIterState_ctrls))
    as [o [v Hpop]].
  rewrite Hpop. cbn [bind].
  destruct (vec_pop_of_snoc st2.(opiter_OpIterState_ctrls)
              (List.map fv_ctrl pre) (fv_ctrl g) o v
              (ltac:(rewrite Hc2; exact Hsnoc)) Hpop) as [_ Hvctrls].
  destruct (push_types_total
              {| opiter_OpIterState_vals := st2.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := v;
                 opiter_OpIterState_pos := st2.(opiter_OpIterState_pos);
                 opiter_OpIterState_pending :=
                   st2.(opiter_OpIterState_pending) |}
              results) as [st3 Hpush].
  { cbn [opiter_OpIterState_vals].
    pose proof (pop_types_size st1 results _ st2 Hpt) as Hs2.
    unfold room, stack_size in Hroom. unfold stack_size in Hs1, Hs2. lia. }
  rewrite Hpush. cbn [bind]. eexists. exists st3. reflexivity.
Qed.

(** [br]: the depth the checker looked up is in range and names the frame whose
    types the pops ask for, which is [ctx_at_label_lookup] read backwards. *)
(** The local operators' prologue: the index the specification put there decodes,
    and the lookup that the checker performed succeeds here too. *)
Lemma take_local_complete : forall ctx C0 st data b opcode l rest xx,
  locals_agree ctx C0 ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opcode ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) l rest ->
  lookup_N (tc_locals C0) (Z.to_N l) = Some xx ->
  exists idx t st',
    opiter_take_local st data ctx opcode
      = Ok (Core_result_Result_Ok (idx, t), st')
    /\ to_Z idx = l
    /\ translate_vt_v t = xx.
Proof.
  intros ctx C0 st data b opcode l rest xx Hag Hp Hb Hrep Hlk.
  unfold opiter_take_local.
  destruct (take_pending_ok st opcode b Hp Hb) as [st1 [Htp [Hobs _]]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 Hpos1]].
  rewrite <- Hpos1 in Hrep.
  destruct (read_u32_leb_complete data st1.(opiter_OpIterState_pos) l rest Hrep)
    as [iv [p1 [Hleb [Hiv Hrest]]]].
  rewrite Hleb. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (local_type_complete ctx C0 iv xx Hag
              (ltac:(rewrite Hiv; exact Hlk))) as [t [Hlt Ht]].
  rewrite Hlt. cbn [bind]. rewrite branch_ok. cbn [bind].
  exists iv, t. eexists. split; [reflexivity|].
  split; [exact Hiv | exact Ht].
Qed.

Lemma read_local_get_complete : forall C0 ctx st pre f data b l rest xx,
  Inv C0 st (pre ++ [f]) ->
  locals_agree ctx C0 ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_local_get ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) l rest ->
  lookup_N (tc_locals C0) (Z.to_N l) = Some xx ->
  room st ->
  exists idx st',
    opiter_read_local_get st data ctx = Ok (Core_result_Result_Ok idx, st')
    /\ to_Z idx = l.
Proof.
  intros C0 ctx st pre f data b l rest xx Hinv Hag Hp Hb Hrep Hlk Hroom.
  unfold opiter_read_local_get.
  destruct (take_local_complete ctx C0 st data b opiter_op_local_get l rest xx
              Hag Hp Hb Hrep Hlk) as [idx [t [st1 [Htl [Hidx Ht]]]]].
  rewrite Htl. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (take_local_fields st data ctx _ _ st1 Htl) as [Hv1 Hc1].
  pose proof (take_local_size st data ctx _ _ st1 Htl) as Hs1.
  destruct (push_val_total st1 (Opiter_StackType_Val t)) as [st2 Hpv].
  { apply room_vals. unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. exists idx, st2.
  split; [reflexivity | exact Hidx].
Qed.

Lemma read_local_set_complete : forall C0 ctx st pre f data b l rest xx ct',
  Inv C0 st (pre ++ [f]) ->
  locals_agree ctx C0 ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_local_set ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) l rest ->
  lookup_N (tc_locals C0) (Z.to_N l) = Some xx ->
  consume (fv_ct f) [xx] = Some ct' ->
  exists idx st',
    opiter_read_local_set st data ctx = Ok (Core_result_Result_Ok idx, st')
    /\ to_Z idx = l.
Proof.
  intros C0 ctx st pre f data b l rest xx ct' Hinv Hag Hp Hb Hrep Hlk Hcon.
  unfold opiter_read_local_set.
  destruct (take_local_complete ctx C0 st data b opiter_op_local_set l rest xx
              Hag Hp Hb Hrep Hlk) as [idx [t [st1 [Htl [Hidx Ht]]]]].
  rewrite Htl. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (take_local_fields st data ctx _ _ st1 Htl) as [Hv1 Hc1].
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_fields C0 st st1 _ Hv1 Hc1 Hinv)).
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  destruct (pop_with_type_complete st1 (List.concat (List.map fv_seg pre)) f
              t ct' Hsplit1 Hbase1 Hunr1
              (ltac:(rewrite Ht; exact Hcon))) as [t1 [st2 Hp1]].
  rewrite Hp1. cbn [bind]. rewrite branch_ok. cbn [bind].
  exists idx, st2. split; [reflexivity|]. exact Hidx.
Qed.

Lemma read_local_tee_complete : forall C0 ctx st pre f data b l rest xx ct',
  Inv C0 st (pre ++ [f]) ->
  locals_agree ctx C0 ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_local_tee ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) l rest ->
  lookup_N (tc_locals C0) (Z.to_N l) = Some xx ->
  consume (fv_ct f) [xx] = Some ct' ->
  room st ->
  exists idx st',
    opiter_read_local_tee st data ctx = Ok (Core_result_Result_Ok idx, st')
    /\ to_Z idx = l.
Proof.
  intros C0 ctx st pre f data b l rest xx ct' Hinv Hag Hp Hb Hrep Hlk Hcon
         Hroom.
  unfold opiter_read_local_tee.
  destruct (take_local_complete ctx C0 st data b opiter_op_local_tee l rest xx
              Hag Hp Hb Hrep Hlk) as [idx [t [st1 [Htl [Hidx Ht]]]]].
  rewrite Htl. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (take_local_fields st data ctx _ _ st1 Htl) as [Hv1 Hc1].
  pose proof (take_local_size st data ctx _ _ st1 Htl) as Hs1.
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_fields C0 st st1 _ Hv1 Hc1 Hinv)).
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  destruct (pop_with_type_complete st1 (List.concat (List.map fv_seg pre)) f
              t ct' Hsplit1 Hbase1 Hunr1
              (ltac:(rewrite Ht; exact Hcon))) as [t1 [st2 Hp1]].
  rewrite Hp1. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (push_val_total st2 (Opiter_StackType_Val t)) as [st3 Hpv].
  { apply room_vals.
    pose proof (pop_with_type_size st1 t _ st2 Hp1) as Hs2.
    unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. exists idx, st3.
  split; [reflexivity | exact Hidx].
Qed.

(** The global operators' prologue, and the two readers. [global.set]'s extra
    hypothesis is the mutability the checker's [is_mut] tested. *)
Lemma take_global_complete : forall module C0 st data b opcode l rest xx,
  globals_agree module C0 ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opcode ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) l rest ->
  lookup_N (tc_globals C0) (Z.to_N l) = Some xx ->
  exists idx g st',
    opiter_take_global st data module opcode
      = Ok (Core_result_Result_Ok (idx, g), st')
    /\ to_Z idx = l
    /\ translate_globaltype g = xx.
Proof.
  intros module C0 st data b opcode l rest xx Hag Hp Hb Hrep Hlk.
  unfold opiter_take_global.
  destruct (take_pending_ok st opcode b Hp Hb) as [st1 [Htp [Hobs _]]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 Hpos1]].
  rewrite <- Hpos1 in Hrep.
  destruct (read_u32_leb_complete data st1.(opiter_OpIterState_pos) l rest Hrep)
    as [iv [p1 [Hleb [Hiv Hrest]]]].
  rewrite Hleb. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (global_type_complete module C0 iv xx Hag
              (ltac:(rewrite Hiv; exact Hlk))) as [g [Hgt Hg]].
  rewrite Hgt. cbn [bind]. rewrite branch_ok. cbn [bind].
  exists iv, g. eexists. split; [reflexivity|].
  split; [exact Hiv | exact Hg].
Qed.

Lemma read_global_get_complete : forall C0 module st pre f data b l rest xx,
  Inv C0 st (pre ++ [f]) ->
  globals_agree module C0 ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_global_get ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) l rest ->
  lookup_N (tc_globals C0) (Z.to_N l) = Some xx ->
  room st ->
  exists idx st',
    opiter_read_global_get st data module = Ok (Core_result_Result_Ok idx, st')
    /\ to_Z idx = l.
Proof.
  intros C0 module st pre f data b l rest xx Hinv Hag Hp Hb Hrep Hlk
         Hroom.
  unfold opiter_read_global_get.
  destruct (take_global_complete module C0 st data b opiter_op_global_get l rest xx
              Hag Hp Hb Hrep Hlk) as [idx [g [st1 [Htg [Hidx Hg]]]]].
  rewrite Htg. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (take_global_fields st data module _ _ st1 Htg) as [Hv1 Hc1].
  pose proof (take_global_size st data module _ _ st1 Htg) as Hs1.
  destruct (push_val_total st1
              (Opiter_StackType_Val g.(types_GlobalType_valtype))) as [st2 Hpv].
  { apply room_vals. unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. exists idx, st2.
  split; [reflexivity | exact Hidx].
Qed.

Lemma read_global_set_complete : forall C0 module st pre f data b l rest xx ct',
  Inv C0 st (pre ++ [f]) ->
  globals_agree module C0 ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_global_set ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) l rest ->
  lookup_N (tc_globals C0) (Z.to_N l) = Some xx ->
  is_mut xx = true ->
  consume (fv_ct f) [tg_t xx] = Some ct' ->
  exists idx st',
    opiter_read_global_set st data module = Ok (Core_result_Result_Ok idx, st')
    /\ to_Z idx = l.
Proof.
  intros C0 module st pre f data b l rest xx ct' Hinv Hag Hp Hb Hrep Hlk Hmut Hcon
.
  unfold opiter_read_global_set.
  destruct (take_global_complete module C0 st data b opiter_op_global_set l rest xx
              Hag Hp Hb Hrep Hlk) as [idx [g [st1 [Htg [Hidx Hg]]]]].
  rewrite Htg. cbn [bind]. rewrite branch_ok. cbn [bind].
  assert (Hvar : g.(types_GlobalType_mutability) = Types_Mut_Var)
    by (apply var_of_is_mut; rewrite Hg; exact Hmut).
  (* [destruct] rewrites [Hvar] too, so the immutable case is a contradiction *)
  destruct (g.(types_GlobalType_mutability)) eqn:Hm; [discriminate|].
  destruct (take_global_fields st data module _ _ st1 Htg) as [Hv1 Hc1].
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_fields C0 st st1 _ Hv1 Hc1 Hinv)).
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  destruct (pop_with_type_complete st1 (List.concat (List.map fv_seg pre)) f
              g.(types_GlobalType_valtype) ct' Hsplit1 Hbase1 Hunr1
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
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) l rest ->
  (Z.to_nat l < List.length (vec_list st.(opiter_OpIterState_ctrls)))%nat ->
  List.nth_error (vec_list st.(opiter_OpIterState_ctrls))
    (List.length (vec_list st.(opiter_OpIterState_ctrls)) - 1 - Z.to_nat l)
    = Some target ->
  exists depth st',
    opiter_read_label st data = Ok (Core_result_Result_Ok (depth, target), st')
    /\ to_Z depth = l
    /\ bytes_from data st'.(opiter_OpIterState_pos) = rest
    /\ Inv C0 st' fs
    /\ vec_list st'.(opiter_OpIterState_vals)
       = vec_list st.(opiter_OpIterState_vals)
    /\ vec_list st'.(opiter_OpIterState_ctrls)
       = vec_list st.(opiter_OpIterState_ctrls).
Proof.
  intros C0 st fs data l rest target Hinv Hrep Hlt Hnth.
  unfold opiter_read_label.
  destruct (read_u32_leb_complete data st.(opiter_OpIterState_pos) l rest Hrep)
    as [dv [p1 [Hleb [Hdv Hrest]]]].
  rewrite Hleb. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (cast_u32_usize_ok dv) as [d [Hcast Hdval]].
  rewrite Hcast. cbn [bind].
  pose proof (u32_nonneg dv) as Hdvnn.
  assert (Hdz : to_Z d = l) by (rewrite Hdval; exact Hdv).
  assert (Hlen1 : to_Z (alloc_vec_Vec_len st.(opiter_OpIterState_ctrls))
                  = Z.of_nat
                      (List.length (vec_list st.(opiter_OpIterState_ctrls))))
    by apply vec_len_spec.
  assert (Hge : (d s>= alloc_vec_Vec_len st.(opiter_OpIterState_ctrls)) = false).
  { apply scalar_lt_geb_false. rewrite Hlen1. rewrite Hdz. lia. }
  rewrite Hge. cbn beta iota.
  destruct (usize_sub_1_ok (alloc_vec_Vec_len st.(opiter_OpIterState_ctrls)))
    as [i [Hsub1 Hival]]; [rewrite Hlen1; lia|].
  rewrite Hsub1. cbn [bind].
  destruct (usize_sub_ok i d) as [i1 [Hsub2 Hi1val]];
    [rewrite Hival; rewrite Hlen1; rewrite Hdz; lia|].
  rewrite Hsub2. cbn [bind]. rewrite vec_index_spec.
  assert (Hidx : Z.to_nat (to_Z i1)
                 = (List.length (vec_list st.(opiter_OpIterState_ctrls)) - 1
                    - Z.to_nat l)%nat).
  { rewrite Hi1val. rewrite Hival. rewrite Hlen1. rewrite Hdz. lia. }
  rewrite Hidx. rewrite Hnth. cbn [bind].
  exists dv. eexists. split; [reflexivity|]. split; [exact Hdv|].
  cbn [opiter_OpIterState_vals opiter_OpIterState_ctrls opiter_OpIterState_pos].
  split; [exact Hrest|].
  split; [exact Hinv|].
  split; reflexivity.
Qed.

(** The branch operators' prologue is the opcode and then a label. *)
Lemma take_branch_target_complete :
  forall C0 st fs data b opcode l rest target,
  Inv C0 st fs ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opcode ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) l rest ->
  (Z.to_nat l < List.length (vec_list st.(opiter_OpIterState_ctrls)))%nat ->
  List.nth_error (vec_list st.(opiter_OpIterState_ctrls))
    (List.length (vec_list st.(opiter_OpIterState_ctrls)) - 1 - Z.to_nat l)
    = Some target ->
  exists depth st',
    opiter_take_branch_target st data opcode
      = Ok (Core_result_Result_Ok (depth, target), st')
    /\ to_Z depth = l
    /\ Inv C0 st' fs
    /\ vec_list st'.(opiter_OpIterState_vals)
       = vec_list st.(opiter_OpIterState_vals)
    /\ vec_list st'.(opiter_OpIterState_ctrls)
       = vec_list st.(opiter_OpIterState_ctrls).
Proof.
  intros C0 st fs data b opcode l rest target Hinv Hp Hb Hrep Hlt Hnth.
  unfold opiter_take_branch_target.
  destruct (take_pending_ok st opcode b Hp Hb) as [st1 [Htp [Hobs _]]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 Hpos1]].
  assert (Hvl : vec_list st1.(opiter_OpIterState_vals)
                = vec_list st.(opiter_OpIterState_vals))
    by (rewrite Hv1; reflexivity).
  assert (Hcl : vec_list st1.(opiter_OpIterState_ctrls)
                = vec_list st.(opiter_OpIterState_ctrls))
    by (rewrite Hc1; reflexivity).
  rewrite <- Hpos1 in Hrep. rewrite <- Hcl in Hlt. rewrite <- Hcl in Hnth.
  destruct (read_label_complete C0 st1 fs data l rest target
              (Inv_fields C0 st st1 fs Hvl Hcl Hinv) Hrep Hlt Hnth)
    as [depth [st' [Hrl [Hdv [_ [Hinv' [Hvl' Hcl']]]]]]].
  exists depth, st'. split; [exact Hrl|]. split; [exact Hdv|].
  split; [exact Hinv'|].
  split; [rewrite Hvl'; exact Hvl | rewrite Hcl'; exact Hcl].
Qed.

Lemma read_br_complete :
  forall C0 st pre f data b l rest target ct',
  Inv C0 st (pre ++ [f]) ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_br ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) l rest ->
  (Z.to_nat l < List.length (vec_list st.(opiter_OpIterState_ctrls)))%nat ->
  List.nth_error (vec_list st.(opiter_OpIterState_ctrls))
    (List.length (vec_list st.(opiter_OpIterState_ctrls)) - 1 - Z.to_nat l)
    = Some target ->
  consume (fv_ct f) (translate_typelist (ctrl_target target)) = Some ct' ->
  exists depth bt' st',
    opiter_read_br st data = Ok (Core_result_Result_Ok (depth, bt'), st')
    /\ to_Z depth = l.
Proof.
  intros C0 st pre f data b l rest target ct'
         Hinv Hp Hb Hrep Hlt Hnth Hcon.
  unfold opiter_read_br.
  destruct (take_branch_target_complete C0 st (pre ++ [f]) data b opiter_op_br
              l rest target Hinv Hp Hb Hrep Hlt Hnth)
    as [depth [st1 [Htb [Hdepth [Hinv1 [Hv1 Hc1]]]]]].
  rewrite Htb. cbn [bind]. rewrite branch_ok. cbn [bind].
  assert (Hsnoc : vec_list st1.(opiter_OpIterState_ctrls)
                  = List.map fv_ctrl pre ++ [fv_ctrl f]).
  { destruct Hinv1 as [K1 _]. rewrite K1. rewrite List.map_app. reflexivity. }
  destruct (branch_target_types_total target) as [types Hbtt].
  rewrite Hbtt. cbn [bind]. rewrite vec_deref_spec.
  pose proof (branch_target_types_spec target types Hbtt) as Htypes.
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase [Hsplit Hunr]].
  destruct (pop_types_complete st1 (List.concat (List.map fv_seg pre)) f
              types ct' Hsplit Hbase Hunr
              (ltac:(rewrite Htypes; exact Hcon))) as [st2 Hpt].
  rewrite Hpt. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (pop_types_sim st1 (List.concat (List.map fv_seg pre)) f types st2
              Hsplit Hbase Hunr Hpt) as [seg' [Hc2 [Hv2 _]]].
  destruct (mark_unreachable_total st2) as [st3 Hmu].
  rewrite Hmu. cbn [bind]. exists depth, target.(opiter_Ctrl_block_type), st3.
  split; [reflexivity | exact Hdepth].
Qed.

(** [br_if]: the condition pop and the target pops come from the checker's one
    [consume], split at the head, and the types then go back on. *)
Lemma read_br_if_complete :
  forall C0 st pre f data b l rest target ct',
  Inv C0 st (pre ++ [f]) ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_br_if ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) l rest ->
  (Z.to_nat l < List.length (vec_list st.(opiter_OpIterState_ctrls)))%nat ->
  List.nth_error (vec_list st.(opiter_OpIterState_ctrls))
    (List.length (vec_list st.(opiter_OpIterState_ctrls)) - 1 - Z.to_nat l)
    = Some target ->
  consume (fv_ct f)
    (T_num T_i32 :: translate_typelist (ctrl_target target)) = Some ct' ->
  room st ->
  exists depth bt' st',
    opiter_read_br_if st data = Ok (Core_result_Result_Ok (depth, bt'), st')
    /\ to_Z depth = l.
Proof.
  intros C0 st pre f data b l rest target ct'
         Hinv Hp Hb Hrep Hlt Hnth Hcon Hroom.
  unfold opiter_read_br_if.
  destruct (take_branch_target_complete C0 st (pre ++ [f]) data b
              opiter_op_br_if l rest target Hinv Hp Hb Hrep Hlt Hnth)
    as [depth [st1 [Htb [Hdepth [Hinv1 [Hvl Hcl]]]]]].
  rewrite Htb. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (branch_target_types_total target) as [types Hbtt].
  rewrite Hbtt. cbn [bind]. rewrite vec_deref_spec.
  pose proof (branch_target_types_spec target types Hbtt) as Htypes.
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  destruct (consume_cons_inv (fv_ct f) (T_num T_i32)
              (translate_typelist (ctrl_target target)) ct' Hcon)
    as [ct1 [Hcon1 Hcon2]].
  (* the condition *)
  destruct (pop_with_type_complete st1 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 ct1 Hsplit1 Hbase1 Hunr1
              Hcon1)
    as [t1 [st2 Hp1]].
  rewrite Hp1. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (pop_with_type_sim st1 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 t1 st2 Hsplit1 Hbase1 Hunr1 Hp1)
    as [seg1 [Hc2 [Hv2 Hsim1]]].
  destruct (cur_views_ctrls st1 st2 Hc2) as [Hb2 Hu2].
  assert (Hct1 : ct1 = <<translate_vals seg1,
                         (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>>).
  { pose proof Hsim1 as Hs. cbn [translate_vt_v] in Hs.
    rewrite Hcon1 in Hs. injection Hs as Hs. exact Hs. }
  rewrite Hct1 in Hcon2.
  (* the target's types, on the frame with the shortened segment *)
  destruct (pop_types_complete st2 (List.concat (List.map fv_seg pre))
              {| fv_ctrl := fv_ctrl f; fv_seg := seg1;
                  fv_done := fv_done f; fv_then := fv_then f |}
              types ct'
              (ltac:(cbn [fv_seg]; exact Hv2))
              (ltac:(cbn [fv_ctrl]; rewrite Hb2; exact Hbase1))
              (ltac:(cbn [fv_ctrl]; rewrite Hu2; exact Hunr1))
              (ltac:(cbn [fv_ct fv_seg fv_ctrl]; rewrite Htypes; exact Hcon2)))
    as [st3 Hpt].
  rewrite Hpt. cbn [bind]. rewrite branch_ok. cbn [bind].
  (* and back on: the condition pop paid for the push *)
  pose proof (branch_target_types_len _ types Hbtt) as Hlen.
  destruct (push_types_total st3 types) as [st4 Hpush].
  { pose proof (pop_with_type_size st1 _ _ st2 Hp1) as Hs2.
    pose proof (pop_types_size st2 types _ st3 Hpt) as Hs3.
    assert (Hb4 : (List.length (vec_list st3.(opiter_OpIterState_vals))
                   + List.length (vec_list types) <= stack_size st + 1)%nat).
    { unfold stack_size in Hs2, Hs3 |- *.
      unfold stack_size. rewrite <- Hvl. rewrite <- Hcl. lia. }
    apply (proj1 (Nat2Z.inj_le _ _)) in Hb4.
    rewrite Nat2Z.inj_add in Hb4. rewrite Nat2Z.inj_add in Hb4.
    unfold room in Hroom. lia. }
  rewrite Hpush. cbn [bind].
  exists depth, target.(opiter_Ctrl_block_type), st4.
  split; [reflexivity | exact Hdepth].
Qed.

(** [br_table]'s label vector, in the completeness direction: the specification's
    label list decodes, every entry resolves because the checker found a label at
    that depth, and the running block type is the one they share.

    The loop's running value starts unset and is only ever set to [common], which
    is what the disjunction in the hypothesis and the conclusion says. *)
Lemma read_table_labels_loop_complete :
  forall n C0 st fs data ls rest count i expect common,
  Inv C0 st fs ->
  to_Z i + Z.of_nat n = to_Z count ->
  repr_u32_rep n (bytes_from data st.(opiter_OpIterState_pos)) ls rest ->
  List.Forall (fun d => depth_target st d common) ls ->
  (expect = None \/ expect = Some common) ->
  exists res st',
    opiter_read_table_labels_loop st data count expect i
      = Ok (Core_result_Result_Ok res, st')
    /\ (res = None \/ res = Some common)
    /\ bytes_from data st'.(opiter_OpIterState_pos) = rest
    /\ Inv C0 st' fs
    /\ vec_list st'.(opiter_OpIterState_vals)
       = vec_list st.(opiter_OpIterState_vals)
    /\ vec_list st'.(opiter_OpIterState_ctrls)
       = vec_list st.(opiter_OpIterState_ctrls).
Proof.
  induction n as [|n IH];
    intros C0 st fs data ls rest count i expect common Hinv Hn Hrep Hall Hexp;
    unfold opiter_read_table_labels_loop; rewrite loop_unfold; cbn beta iota.
  - (* the count is exhausted, so the guard fires and nothing was read *)
    inversion Hrep; subst.
    assert (Heq : (i s= count) = true)
      by (unfold scalar_eqb; apply Z.eqb_eq; cbn in Hn; lia).
    rewrite Heq. cbn beta iota.
    exists expect, st. split; [reflexivity|]. split; [exact Hexp|].
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
    destruct (read_label_complete C0 st fs data d mid0 c Hinv Hd Hlt Hnth)
      as [depth [st1 [Hrl [Hdv [Hbytes1 [Hinv1 [Hv1 Hc1]]]]]]].
    rewrite Hrl. cbn [bind]. rewrite branch_ok. cbn [bind].
    rewrite branch_target_bt_spec. cbn [bind]. rewrite Hbtc.
    rewrite (merge_target_same expect common Hexp). cbn [bind].
    rewrite branch_ok. cbn [bind].
    (* [i] is below the count, so the increment cannot overflow *)
    pose proof (u32_bounds i) as Hib. pose proof (u32_bounds count) as Hcb.
    destruct (u32_add_ok i 1%u32) as [i1 [Hadd Hi1]].
    { assert (H1 : to_Z 1%u32 = 1) by reflexivity. rewrite H1. cbn in Hn. lia. }
    rewrite Hadd. cbn [bind].
    rewrite <- Hbytes1 in Hrest.
    destruct (IH C0 st1 fs data ls0 rest count i1 (Some common) common Hinv1
                (ltac:(assert (H1 : to_Z 1%u32 = 1) by reflexivity;
                       rewrite Hi1; rewrite H1; cbn in Hn; lia))
                Hrest
                (List.Forall_impl _
                   (fun d' Hd' => depth_target_ctrls st st1 d' common Hc1 Hd')
                   Htail)
                (or_intror eq_refl))
      as [res [st' [Hloop [Hres [Hb' [Hinv' [Hv' Hc']]]]]]].
    exists res, st'. split; [exact Hloop|]. split; [exact Hres|].
    split; [exact Hb'|]. split; [exact Hinv'|].
    split; [rewrite Hv'; exact Hv1 | rewrite Hc'; exact Hc1].
Qed.

Lemma read_table_labels_complete :
  forall C0 st fs data ls rest count common,
  Inv C0 st fs ->
  repr_u32_rep (Z.to_nat (to_Z count))
               (bytes_from data st.(opiter_OpIterState_pos)) ls rest ->
  List.Forall (fun d => depth_target st d common) ls ->
  exists res st',
    opiter_read_table_labels st data count = Ok (Core_result_Result_Ok res, st')
    /\ (res = None \/ res = Some common)
    /\ bytes_from data st'.(opiter_OpIterState_pos) = rest
    /\ Inv C0 st' fs
    /\ vec_list st'.(opiter_OpIterState_vals)
       = vec_list st.(opiter_OpIterState_vals)
    /\ vec_list st'.(opiter_OpIterState_ctrls)
       = vec_list st.(opiter_OpIterState_ctrls).
Proof.
  intros C0 st fs data ls rest count common Hinv Hrep Hall.
  unfold opiter_read_table_labels.
  apply (read_table_labels_loop_complete (Z.to_nat (to_Z count)) C0 st fs data
           ls rest count 0%u32 None common Hinv
           (ltac:(assert (H0 : to_Z 0%u32 = 0) by reflexivity; rewrite H0;
                  rewrite Z2Nat.id by apply u32_nonneg; reflexivity))
           Hrep Hall (or_introl eq_refl)).
Qed.

(** [br_table]: [br]'s effect after an [i32], with the vector and the default
    label read first. Every label names a frame with the same branch target, so
    the running comparison never fails and the reader returns that target. *)
Lemma read_br_table_complete :
  forall C0 st pre f data b ls x mid rest common ct',
  Inv C0 st (pre ++ [f]) ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_br_table ->
  repr_vec_u32 (bytes_from data st.(opiter_OpIterState_pos)) ls mid ->
  repr_u32 mid x rest ->
  List.Forall (fun d => depth_target st d common) (ls ++ [x]) ->
  consume (fv_ct f)
    (T_num T_i32 :: translate_typelist (block_results_of common)) = Some ct' ->
  exists st',
    opiter_read_br_table st data = Ok (Core_result_Result_Ok common, st').
Proof.
  intros C0 st pre f data b ls x mid rest common ct'
         Hinv Hp Hb Hvec Hdef Hall Hcon.
  apply List.Forall_app in Hall. destruct Hall as [Hallls Hallx].
  inversion Hallx as [|x0 nil0 Hxt _]; subst.
  unfold opiter_read_br_table.
  destruct (take_pending_ok st opiter_op_br_table b Hp Hb)
    as [st1 [Htp [Hobs _]]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 Hpos1]].
  assert (Hvl1 : vec_list st1.(opiter_OpIterState_vals)
                 = vec_list st.(opiter_OpIterState_vals))
    by (rewrite Hv1; reflexivity).
  assert (Hcl1 : vec_list st1.(opiter_OpIterState_ctrls)
                 = vec_list st.(opiter_OpIterState_ctrls))
    by (rewrite Hc1; reflexivity).
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_fields C0 st st1 _ Hvl1 Hcl1 Hinv)).
  (* the count, then the vector *)
  inversion Hvec as [bs0 n mid0 ls0 rest0 Hn Hrep]; subst.
  rewrite <- Hpos1 in Hn.
  destruct (read_u32_leb_complete data st1.(opiter_OpIterState_pos) n mid0 Hn)
    as [count [p1 [Hleb [Hcv Hmid0]]]].
  rewrite Hleb. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (read_table_labels_complete C0
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending := st1.(opiter_OpIterState_pending)
              |} (pre ++ [f]) data ls mid count common
              (Inv_fields C0 st1 _ _ eq_refl eq_refl Hinv1)
              (ltac:(cbn [opiter_OpIterState_pos]; rewrite Hcv;
                     rewrite Hmid0; exact Hrep))
              (List.Forall_impl _
                 (fun d Hd => depth_target_ctrls st _ d common Hcl1 Hd)
                 Hallls))
    as [res [st2 [Htl [Hres [Hb2 [Hinv2 [Hv2 Hc2]]]]]]].
  rewrite Htl. cbn [bind]. rewrite branch_ok. cbn [bind].
  assert (Hcl2 : vec_list st2.(opiter_OpIterState_ctrls)
                 = vec_list st.(opiter_OpIterState_ctrls))
    by (rewrite Hc2; exact Hcl1).
  (* the default label *)
  destruct Hxt as [c [Hlt [Hnth Hbtc]]].
  rewrite <- Hcl2 in Hlt, Hnth.
  destruct (read_label_complete C0 st2 (pre ++ [f]) data x rest c Hinv2
              (ltac:(rewrite Hb2; exact Hdef)) Hlt Hnth)
    as [depth [st3 [Hrl [_ [_ [Hinv3 [Hv3 Hc3]]]]]]].
  rewrite Hrl. cbn [bind]. rewrite branch_ok. cbn [bind].
  rewrite branch_target_bt_spec. cbn [bind]. rewrite Hbtc.
  rewrite (merge_target_same res common Hres). cbn [bind].
  rewrite branch_ok. cbn [bind].
  assert (Hsnoc : vec_list st3.(opiter_OpIterState_ctrls)
                  = List.map fv_ctrl pre ++ [fv_ctrl f])
    by (destruct Hinv3 as [K1 _]; rewrite K1; rewrite List.map_app;
        reflexivity).
  destruct (Inv_split C0 st3 pre f Hinv3) as [Hbase [Hsplit Hunr]].
  destruct (consume_cons_inv (fv_ct f) (T_num T_i32)
              (translate_typelist (block_results_of common)) ct' Hcon)
    as [ct1 [Hcon1 Hcon2]].
  (* the index *)
  destruct (pop_with_type_complete st3 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 ct1 Hsplit Hbase Hunr
              Hcon1)
    as [t1 [st4 Hp1]].
  rewrite Hp1. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (pop_with_type_sim st3 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 t1 st4 Hsplit Hbase Hunr Hp1)
    as [seg1 [Hc4 [Hv4 Hsim1]]].
  destruct (cur_views_ctrls st3 st4 Hc4) as [Hb4 Hu4].
  assert (Hct1 : ct1 = <<translate_vals seg1,
                         (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>>).
  { pose proof Hsim1 as Hs. cbn [translate_vt_v] in Hs.
    rewrite Hcon1 in Hs. injection Hs as Hs. exact Hs. }
  rewrite Hct1 in Hcon2.
  (* the target's types, then the truncation *)
  destruct (block_results_total common) as [types Hbr].
  rewrite Hbr. cbn [bind]. rewrite vec_deref_spec.
  pose proof (block_results_spec _ types Hbr) as Htypes.
  destruct (pop_types_complete st4 (List.concat (List.map fv_seg pre))
              {| fv_ctrl := fv_ctrl f; fv_seg := seg1;
                  fv_done := fv_done f; fv_then := fv_then f |}
              types ct'
              (ltac:(cbn [fv_seg]; exact Hv4))
              (ltac:(cbn [fv_ctrl]; rewrite Hb4; exact Hbase))
              (ltac:(cbn [fv_ctrl]; rewrite Hu4; exact Hunr))
              (ltac:(cbn [fv_ct fv_seg fv_ctrl]; rewrite Htypes; exact Hcon2)))
    as [st5 Hpt].
  rewrite Hpt. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (pop_types_sim st4 (List.concat (List.map fv_seg pre))
              {| fv_ctrl := fv_ctrl f; fv_seg := seg1;
                  fv_done := fv_done f; fv_then := fv_then f |}
              types st5
              (ltac:(cbn [fv_seg]; exact Hv4))
              (ltac:(cbn [fv_ctrl]; rewrite Hb4; exact Hbase))
              (ltac:(cbn [fv_ctrl]; rewrite Hu4; exact Hunr)) Hpt)
    as [seg2 [Hc5 [Hv5 _]]].
  cbn [fv_ctrl] in Hc5, Hv5.
  destruct (mark_unreachable_total st5) as [st6 Hmu].
  rewrite Hmu. cbn [bind]. exists st6. reflexivity.
Qed.

Lemma read_reserved_zero_complete : forall st data rest,
  bytes_from data st.(opiter_OpIterState_pos) = 0 :: rest ->
  exists st',
    opiter_read_reserved_zero st data = Ok (Core_result_Result_Ok tt, st')
    /\ bytes_from data st'.(opiter_OpIterState_pos) = rest
    /\ vec_list st'.(opiter_OpIterState_vals)
       = vec_list st.(opiter_OpIterState_vals)
    /\ vec_list st'.(opiter_OpIterState_ctrls)
       = vec_list st.(opiter_OpIterState_ctrls).
Proof.
  intros st data rest Hbytes. unfold opiter_read_reserved_zero.
  destruct (read_byte_complete data st.(opiter_OpIterState_pos) 0 rest Hbytes)
    as [b [p [Hrb [Hb Hrest]]]].
  rewrite Hrb. cbn [bind]. rewrite branch_ok. cbn [bind].
  assert (Hz : (b s<> 0%u8) = false).
  { unfold scalar_neqb, scalar_eqb. apply Bool.negb_false_iff.
    apply Z.eqb_eq. rewrite Hb. reflexivity. }
  rewrite Hz. cbn beta iota. eexists.
  split; [reflexivity|]. cbn [opiter_OpIterState_pos].
  split; [exact Hrest|]. split; reflexivity.
Qed.


(** The two call operators. [take_index] reads the index, the arity guard passes
    because the context is a Wasm 1.0 one, and the pops and pushes are the
    callee's signature. *)
Lemma take_index_complete : forall st data b opcode l rest,
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opcode ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) l rest ->
  exists idx st',
    opiter_take_index st data opcode = Ok (Core_result_Result_Ok idx, st')
    /\ to_Z idx = l
    /\ bytes_from data st'.(opiter_OpIterState_pos) = rest
    /\ vec_list st'.(opiter_OpIterState_vals)
       = vec_list st.(opiter_OpIterState_vals)
    /\ vec_list st'.(opiter_OpIterState_ctrls)
       = vec_list st.(opiter_OpIterState_ctrls).
Proof.
  intros st data b opcode l rest Hp Hb Hrep. unfold opiter_take_index.
  destruct (take_pending_ok st opcode b Hp Hb) as [st1 [Htp [Hobs _]]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 Hpos1]].
  rewrite <- Hpos1 in Hrep.
  destruct (read_u32_leb_complete data st1.(opiter_OpIterState_pos) l rest Hrep)
    as [iv [p1 [Hleb [Hiv Hrest]]]].
  rewrite Hleb. cbn [bind]. rewrite branch_ok. cbn [bind].
  exists iv. eexists. split; [reflexivity|]. split; [exact Hiv|].
  cbn [opiter_OpIterState_vals opiter_OpIterState_ctrls opiter_OpIterState_pos].
  split; [exact Hrest|]. split; [rewrite Hv1; reflexivity | rewrite Hc1;
  reflexivity].
Qed.

Lemma read_call_complete : forall C0 module st pre f data b l rest tn tm ct',
  Inv C0 st (pre ++ [f]) ->
  funcs_agree module C0 -> funcs_wasm10 module ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_call ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) l rest ->
  lookup_N (tc_funcs C0) (Z.to_N l) = Some (Tf tn tm) ->
  consume (fv_ct f) tn = Some ct' ->
  room st ->
  exists idx st',
    opiter_read_call st data module = Ok (Core_result_Result_Ok idx, st')
    /\ to_Z idx = l.
Proof.
  intros C0 module st pre f data b l rest tn tm ct'
         Hinv Hag Hw10 Hp Hb Hrep Hlk Hcon Hroom.
  unfold opiter_read_call.
  destruct (take_index_complete st data b opiter_op_call l rest Hp Hb Hrep)
    as [idx [st1 [Hti [Hidx [_ [Hv1 Hc1]]]]]].
  rewrite Hti. cbn [bind]. rewrite branch_ok. cbn [bind].
  pose proof (take_index_size st data _ _ st1 Hti) as Hs1.
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_fields C0 st st1 _ Hv1 Hc1 Hinv)).
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  destruct (ft_lookup_complete module.(env_Env_func_types) (tc_funcs C0) idx
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
              (ltac:(rewrite Htn; exact Hcon))) as [st2 Hpt].
  rewrite Hpt. cbn [bind]. rewrite branch_ok. cbn [bind].
  pose proof (pop_types_size st1 _ _ st2 Hpt) as Hs2.
  destruct (push_types_total st2 ft.(types_FuncType_results)) as [st3 Hpu].
  { assert (Hb3 : (List.length (vec_list st2.(opiter_OpIterState_vals))
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
  forall C0 module st pre f data b l rest tabt tn tm ct',
  Inv C0 st (pre ++ [f]) ->
  types_agree module C0 -> tables_agree module C0 -> types_wasm10 module ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_call_indirect ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) l
           (0 :: rest) ->
  lookup_N (tc_tables C0) 0%N = Some tabt ->
  lookup_N (tc_types C0) (Z.to_N l) = Some (Tf tn tm) ->
  consume (fv_ct f) (T_num T_i32 :: tn) = Some ct' ->
  room st ->
  exists idx st',
    opiter_read_call_indirect st data module
      = Ok (Core_result_Result_Ok idx, st')
    /\ to_Z idx = l.
Proof.
  intros C0 module st pre f data b l rest tabt tn tm ct'
         Hinv Hty Htab Hw10 Hp Hb Hrep Htlk Hlk Hcon Hroom.
  unfold opiter_read_call_indirect.
  destruct (take_index_complete st data b opiter_op_call_indirect l (0 :: rest)
              Hp Hb Hrep) as [idx [st1 [Hti [Hidx [Hrest [Hv1 Hc1]]]]]].
  rewrite Hti. cbn [bind]. rewrite branch_ok. cbn [bind].
  pose proof (take_index_size st data _ _ st1 Hti) as Hs1.
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
  assert (Hne : vec_list module.(env_Env_table_types) <> []).
  { intros Hnil. unfold tables_agree in Htab. rewrite Hnil in Htab.
    rewrite Htab in Htlk. discriminate. }
  destruct (vec_list module.(env_Env_table_types)) as [|t0 ts] eqn:Hts;
    [exfalso; apply Hne; reflexivity|].
  destruct (ft_lookup_complete module.(env_Env_types) (tc_types C0) idx
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
              Hcon1)
    as [t3 [st3 Hpw]].
  rewrite Hpw. cbn [bind]. rewrite branch_ok. cbn [bind].
  pose proof (pop_with_type_size st2 _ _ st3 Hpw) as Hs3.
  destruct (pop_with_type_sim st2 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 t3 st3 Hsplit2 Hbase2 Hunr2 Hpw)
    as [seg1 [Hc3 [Hv3 Hsim1]]].
  destruct (cur_views_ctrls st2 st3 Hc3) as [Hb3 Hu3].
  assert (Hct1 : ct1 = <<translate_vals seg1,
                         (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>>).
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
              (ltac:(cbn [fv_ct fv_seg fv_ctrl]; rewrite Htn; exact Hcon2)))
    as [st4 Hpt].
  rewrite Hpt. cbn [bind]. rewrite branch_ok. cbn [bind].
  pose proof (pop_types_size st3 _ _ st4 Hpt) as Hs4.
  destruct (push_types_total st4 ft.(types_FuncType_results)) as [st5 Hpu].
  { assert (Hb5 : (List.length (vec_list st4.(opiter_OpIterState_vals))
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
Lemma read_return_complete : forall C0 ctx st pre f b ct',
  Inv C0 st (pre ++ [f]) ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_return ->
  consume (fv_ct f)
    (translate_typelist (vec_list ctx.(opiter_Context_results))) = Some ct' ->
  exists st',
    opiter_read_return st ctx = Ok (Core_result_Result_Ok tt, st').
Proof.
  intros C0 ctx st pre f b ct' Hinv Hp Hb Hcon.
  unfold opiter_read_return.
  destruct (take_pending_ok st opiter_op_return b Hp Hb) as [st1 [Htp [Hobs _]]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 _]].
  assert (Hsnoc : vec_list st1.(opiter_OpIterState_ctrls)
                  = List.map fv_ctrl pre ++ [fv_ctrl f]).
  { destruct Hinv1 as [K1 _]. rewrite K1. rewrite List.map_app. reflexivity. }
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase [Hsplit Hunr]].
  rewrite vec_deref_spec.
  destruct (pop_types_complete st1 (List.concat (List.map fv_seg pre)) f
              ctx.(opiter_Context_results) ct' Hsplit Hbase Hunr
              Hcon)
    as [st2 Hpt].
  rewrite Hpt. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (pop_types_sim st1 (List.concat (List.map fv_seg pre)) f ctx.(opiter_Context_results) st2
              Hsplit Hbase Hunr Hpt) as [seg' [Hc2 [Hv2 _]]].
  destruct (mark_unreachable_total st2) as [st3 Hmu].
  rewrite Hmu. cbn [bind]. exists st3. reflexivity.
Qed.

(** [load] and [store]: the memarg decodes because the specification says so, the
    memory lookup and the alignment check are the ones the checker already made,
    and the pops come from its [consume]. *)
(** [memory.size] and [memory.grow]: the reserved byte is where the
    specification says, and the memory the checker looked up is the one the
    context has. *)
Lemma read_memory_size_complete : forall C0 module st pre f data b m rest,
  Inv C0 st (pre ++ [f]) ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_memory_size ->
  bytes_from data st.(opiter_OpIterState_pos) = 0 :: rest ->
  mems_agree module C0 ->
  lookup_N (tc_mems C0) 0%N = Some m ->
  room st ->
  exists st',
    opiter_read_memory_size st data module = Ok (Core_result_Result_Ok tt, st').
Proof.
  intros C0 module st pre f data b m rest Hinv Hp Hb Hbytes Hag Hlk Hroom.
  unfold opiter_read_memory_size.
  destruct (take_pending_ok st opiter_op_memory_size b Hp Hb)
    as [st1 [Htp [Hobs _]]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 Hpos1]].
  pose proof (take_pending_size st _ _ st1 Htp) as Hs1.
  rewrite <- Hpos1 in Hbytes.
  destruct (read_reserved_zero_complete st1 data rest Hbytes)
    as [st2 [Hrz [_ [Hv2 Hc2]]]].
  rewrite Hrz. cbn [bind]. rewrite branch_ok. cbn [bind].
  pose proof (read_reserved_zero_size st1 data _ st2 Hrz) as Hs2.
  rewrite (require_memory_complete module C0 m Hag Hlk). cbn [bind].
  rewrite branch_ok. cbn [bind].
  destruct (push_val_total st2 (Opiter_StackType_Val Types_ValueType_I32))
    as [st3 Hpv].
  { apply room_vals. unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. exists st3. reflexivity.
Qed.

Lemma read_memory_grow_complete : forall C0 module st pre f data b m rest ct',
  Inv C0 st (pre ++ [f]) ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opiter_op_memory_grow ->
  bytes_from data st.(opiter_OpIterState_pos) = 0 :: rest ->
  mems_agree module C0 ->
  lookup_N (tc_mems C0) 0%N = Some m ->
  consume (fv_ct f) [T_num T_i32] = Some ct' ->
  room st ->
  exists st',
    opiter_read_memory_grow st data module = Ok (Core_result_Result_Ok tt, st').
Proof.
  intros C0 module st pre f data b m rest ct'
         Hinv Hp Hb Hbytes Hag Hlk Hcon Hroom.
  unfold opiter_read_memory_grow.
  destruct (take_pending_ok st opiter_op_memory_grow b Hp Hb)
    as [st1 [Htp [Hobs _]]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 Hpos1]].
  pose proof (take_pending_size st _ _ st1 Htp) as Hs1.
  rewrite <- Hpos1 in Hbytes.
  destruct (read_reserved_zero_complete st1 data rest Hbytes)
    as [st2 [Hrz [_ [Hv2 Hc2]]]].
  rewrite Hrz. cbn [bind]. rewrite branch_ok. cbn [bind].
  assert (Hinv2 : Inv C0 st2 (pre ++ [f]))
    by (apply (Inv_fields C0 st1 st2 _ Hv2 Hc2 Hinv1)).
  pose proof (read_reserved_zero_size st1 data _ st2 Hrz) as Hs2.
  rewrite (require_memory_complete module C0 m Hag Hlk). cbn [bind].
  rewrite branch_ok. cbn [bind].
  destruct (Inv_split C0 st2 pre f Hinv2) as [Hbase2 [Hsplit2 Hunr2]].
  destruct (pop_with_type_complete st2 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 ct' Hsplit2 Hbase2 Hunr2
              Hcon)
    as [t3 [st3 Hp3]].
  rewrite Hp3. cbn [bind]. rewrite branch_ok. cbn [bind].
  pose proof (pop_with_type_size st2 _ _ st3 Hp3) as Hs3.
  destruct (push_val_total st3 (Opiter_StackType_Val Types_ValueType_I32))
    as [st4 Hpv].
  { apply room_vals. unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. exists st4. reflexivity.
Qed.

Lemma read_load_complete :
  forall C0 st pre f data module b opcode ty natural a o rest m0 ct',
  Inv C0 st (pre ++ [f]) ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opcode ->
  repr_memarg (bytes_from data st.(opiter_OpIterState_pos)) (a, o) rest ->
  mems_agree module C0 ->
  lookup_N (tc_mems C0) 0%N = Some m0 ->
  a <= to_Z natural ->
  consume (fv_ct f) [translate_vt_v Types_ValueType_I32] = Some ct' ->
  room st ->
  exists m st', opiter_read_load st data module opcode ty natural
                  = Ok (Core_result_Result_Ok m, st')
                /\ to_Z m.(opiter_MemArg_align) = a
                /\ to_Z m.(opiter_MemArg_offset) = o.
Proof.
  intros C0 st pre f data module b opcode ty natural a o rest m0 ct'
         Hinv Hp Hb Hrep Hmems Hlk Hal Hcon Hroom.
  unfold opiter_read_load.
  destruct (take_pending_ok st opcode b Hp Hb) as [st1 [Htp [Hobs _]]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 Hpos1]].
  rewrite <- Hpos1 in Hrep.
  pose proof (take_pending_size st opcode _ st1 Htp) as Hs1.
  (* the immediates *)
  destruct (read_memarg_complete st1 data a o rest Hrep) as [m [st2 [Hma [Hmal
              [Hmof Hmrest]]]]].
  rewrite Hma. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (read_memarg_state st1 data m st2 Hma) as [Hmv Hmc].
  pose proof (read_memarg_size st1 data _ st2 Hma) as Hs2.
  assert (Hinv2 : Inv C0 st2 (pre ++ [f])).
  { apply (Inv_fields C0 st1 st2 _); [rewrite Hmv | rewrite Hmc |];
      try reflexivity. exact Hinv1. }
  (* memory and alignment *)
  rewrite (check_memory_and_alignment_complete module C0 m natural m0 Hmems Hlk
             (ltac:(rewrite Hmal; exact Hal))).
  cbn [bind]. rewrite branch_ok. cbn [bind].
  (* the address pop *)
  destruct (Inv_split C0 st2 pre f Hinv2) as [Hbase [Hsplit Hunr]].
  destruct (pop_with_type_complete st2 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 ct' Hsplit Hbase Hunr
              Hcon)
    as [t [st3 Hpop]].
  rewrite Hpop. cbn [bind]. rewrite branch_ok. cbn [bind].
  pose proof (pop_with_type_size st2 Types_ValueType_I32 _ st3 Hpop) as Hs3.
  (* the push *)
  destruct (push_val_total st3 (Opiter_StackType_Val ty)) as [st4 Hpv].
  { apply room_vals. unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. exists m, st4. split; [reflexivity|].
  split; [exact Hmal|]. exact Hmof.
Qed.

Lemma read_store_complete :
  forall C0 st pre f data module b opcode ty natural a o rest m0 ct',
  Inv C0 st (pre ++ [f]) ->
  st.(opiter_OpIterState_pending) = Some b ->
  to_Z b = to_Z opcode ->
  repr_memarg (bytes_from data st.(opiter_OpIterState_pos)) (a, o) rest ->
  mems_agree module C0 ->
  lookup_N (tc_mems C0) 0%N = Some m0 ->
  a <= to_Z natural ->
  consume (fv_ct f) [translate_vt_v ty; translate_vt_v Types_ValueType_I32]
    = Some ct' ->
  exists m st', opiter_read_store st data module opcode ty natural
                  = Ok (Core_result_Result_Ok m, st')
                /\ to_Z m.(opiter_MemArg_align) = a
                /\ to_Z m.(opiter_MemArg_offset) = o.
Proof.
  intros C0 st pre f data module b opcode ty natural a o rest m0 ct'
         Hinv Hp Hb Hrep Hmems Hlk Hal Hcon.
  unfold opiter_read_store.
  destruct (take_pending_ok st opcode b Hp Hb) as [st1 [Htp [Hobs _]]].
  rewrite Htp. cbn [bind]. rewrite branch_ok. cbn [bind].
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 Hpos1]].
  rewrite <- Hpos1 in Hrep.
  destruct (read_memarg_complete st1 data a o rest Hrep) as [m [st2 [Hma [Hmal
              [Hmof Hmrest]]]]].
  rewrite Hma. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (read_memarg_state st1 data m st2 Hma) as [Hmv Hmc].
  assert (Hinv2 : Inv C0 st2 (pre ++ [f])).
  { apply (Inv_fields C0 st1 st2 _); [rewrite Hmv | rewrite Hmc |];
      try reflexivity. exact Hinv1. }
  rewrite (check_memory_and_alignment_complete module C0 m natural m0 Hmems Hlk
             (ltac:(rewrite Hmal; exact Hal))).
  cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (Inv_split C0 st2 pre f Hinv2) as [Hbase [Hsplit Hunr]].
  destruct (consume_cons_inv (fv_ct f) (translate_vt_v ty)
              [translate_vt_v Types_ValueType_I32] ct' Hcon)
    as [ct1 [Hcon1 Hcon2]].
  (* the stored value *)
  destruct (pop_with_type_complete st2 (List.concat (List.map fv_seg pre)) f
              ty ct1 Hsplit Hbase Hunr
              Hcon1)
    as [t1 [st3 Hp1]].
  rewrite Hp1. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (pop_with_type_sim st2 (List.concat (List.map fv_seg pre)) f
              ty t1 st3 Hsplit Hbase Hunr Hp1) as [seg1 [Hc3 [Hv3 Hsim1]]].
  destruct (cur_views_ctrls st2 st3 Hc3) as [Hb3 Hu3].
  assert (Hct1 : ct1 = <<translate_vals seg1,
                         (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>>).
  { pose proof Hsim1 as Hs. rewrite Hcon1 in Hs. injection Hs as Hs. exact Hs. }
  rewrite Hct1 in Hcon2.
  (* the address *)
  destruct (pop_with_type_complete st3 (List.concat (List.map fv_seg pre))
              {| fv_ctrl := fv_ctrl f; fv_seg := seg1;
                  fv_done := fv_done f; fv_then := fv_then f |}
              Types_ValueType_I32 ct') as [t2 [st4 Hp2]].
  { cbn [fv_seg]. exact Hv3. }
  { cbn [fv_ctrl]. rewrite Hb3. exact Hbase. }
  { cbn [fv_ctrl]. rewrite Hu3. exact Hunr. }
  { cbn [fv_ct fv_seg fv_ctrl]. exact Hcon2. }
  rewrite Hp2. cbn [bind]. rewrite branch_ok. cbn [bind].
  exists m, st4. split; [reflexivity|].
  split; [exact Hmal|]. exact Hmof.
Qed.
