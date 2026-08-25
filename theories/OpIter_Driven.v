(** * One consumer's run is another's

    Every result about the body validator is stated at whatever consumer the
    run used, and that is right: [validate_body_with_typed] holds for a hostile
    consumer, and [validate_body_with_trace] is about the hooks that consumer
    was shown. But the module walk asks a driving consumer for something else.
    [Module_Sound.code_hooks_validate] is a claim about [validate_code_entry],
    the do-nothing run, and a compiler that validates an entry runs
    [validate_code_entry_with] at its own visitor. Nothing above relates the
    two, so this file does.

    The observation is one line long: a hook is handed the state and hands back
    a verdict, so the reader half of a dispatch branch does not mention the
    visitor at all. An accepting run therefore fixes the whole state trajectory
    on its own, and any other consumer whose hooks accept walks the same one.
    Everything here is that, by induction over the two loops.

    [hooks_accept] is the hypothesis and it is the right one: a consumer that
    declines an operator stops the loop, so a run at a declining consumer is
    genuinely not the run at an accepting one. Nothing here says anything about
    verdicts, positions or types that is not already said elsewhere; the
    conclusion is only that the two runs agree. *)

Require Import Primitives.
Import Primitives.
Require Import Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Import Itasca.Aeneas_Specs.
Require Import Itasca.OpIter_Visit.
Require Import Itasca.OpIter_State.
Require Import Itasca.OpIter_Decode.
Require Import Itasca.OpIter_Validate.

Local Open Scope list_scope.
Local Bind Scope list_scope with list.
Open Scope Z_scope.

(* ================================================================== *)
(** ** The dispatch shapes                                             *)
(* ================================================================== *)

(** [OpIter_Visit.v] names the shape of a dispatch branch and proves four
    facts about each: it is total, the state it reports is the reader's, an
    accepting branch means the hook accepted, and an accepting hook keeps the
    branch accepting. The last two compose into the fifth, which is the one
    this file needs. *)

Lemma visit_hook_transfer : forall V W
  (h : result ((core_result_Result_t unit error_VisitError_t) * V))
  (h' : result ((core_result_Result_t unit error_VisitError_t) * W))
  st st' v',
  visit_hook h st = Ok (Core_result_Result_Ok tt, st', v') ->
  (exists w', h' = Ok (Core_result_Result_Ok tt, w')) ->
  exists w', visit_hook h' st = Ok (Core_result_Result_Ok tt, st', w').
Proof.
  intros V W h h' st st' v' H Hh'.
  rewrite (visit_hook_state V h st _ st' v' H).
  apply visit_hook_accept. exact Hh'.
Qed.

Lemma visit_wrap_transfer : forall T V W
  (m : result (core_result_Result_t T error_OpError_t * opiter_OpIterState_t))
  (k : opiter_OpIterState_t -> T ->
       result ((core_result_Result_t unit error_VisitError_t) * V))
  (k' : opiter_OpIterState_t -> T ->
        result ((core_result_Result_t unit error_VisitError_t) * W))
  (v : V) (w : W) st' v',
  visit_wrap m k v = Ok (Core_result_Result_Ok tt, st', v') ->
  (forall st0 x, exists w', k' st0 x = Ok (Core_result_Result_Ok tt, w')) ->
  exists w', visit_wrap m k' w = Ok (Core_result_Result_Ok tt, st', w').
Proof.
  intros T V W m k k' v w st' v' H Hk.
  destruct (visit_wrap_hook T V m k v st' v' H) as [x [Hm _]].
  apply (visit_wrap_accept T W m k' w x st' Hm (Hk st' x)).
Qed.

Lemma visit_wrap2_transfer : forall T1 T2 V W
  (m : result (core_result_Result_t (T1 * T2) error_OpError_t
               * opiter_OpIterState_t))
  (k : opiter_OpIterState_t -> T1 -> T2 ->
       result ((core_result_Result_t unit error_VisitError_t) * V))
  (k' : opiter_OpIterState_t -> T1 -> T2 ->
        result ((core_result_Result_t unit error_VisitError_t) * W))
  (v : V) (w : W) st' v',
  visit_wrap2 m k v = Ok (Core_result_Result_Ok tt, st', v') ->
  (forall st0 x y, exists w', k' st0 x y = Ok (Core_result_Result_Ok tt, w')) ->
  exists w', visit_wrap2 m k' w = Ok (Core_result_Result_Ok tt, st', w').
Proof.
  intros T1 T2 V W m k k' v w st' v' H Hk.
  destruct (visit_wrap2_hook T1 T2 V m k v st' v' H) as [x [y [Hm _]]].
  apply (visit_wrap2_accept T1 T2 W m k' w x y st' Hm (Hk st' x y)).
Qed.

(* ================================================================== *)
(** ** [br_table], whose reader has hooks of its own                   *)
(* ================================================================== *)

(** The label vector goes over one depth at a time, calling a hook per depth,
    so the reader is the one place a hook sits below [step] rather than above
    it. The loop's own decisions are the label reader's, which is hook-free, so
    the same induction works one level down. *)
Lemma read_table_labels_loop_transfer :
  forall n V W (inst : visit_OpVisitor_t V) (inst' : visit_OpVisitor_t W)
         st data count v w expect i res st' v',
  hooks_accept inst' ->
  to_Z i + Z.of_nat n = to_Z count ->
  opiter_read_table_labels_loop inst st data count v expect i
    = Ok (Core_result_Result_Ok res, st', v') ->
  exists w', opiter_read_table_labels_loop inst' st data count w expect i
             = Ok (Core_result_Result_Ok res, st', w').
Proof.
  induction n as [|n IH];
    intros V W inst inst' st data count v w expect i res st' v' Hacc Hn H;
    unfold opiter_read_table_labels_loop in H |- *;
    rewrite loop_unfold in H; rewrite loop_unfold;
    cbn beta iota in H |- *; destruct (i s= count) eqn:Heq.
  - inversion H; subst. eauto.
  - exfalso. apply scalar_eqb_false in Heq. cbn in Hn. lia.
  - inversion H; subst. eauto.
  - destruct (opiter_read_label st data) as [[r0 st1]|] eqn:Hrl;
      cbn [bind] in H |- *; [|discriminate].
    destruct r0 as [[d0 target]|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H |- *. cbn [bind] in H |- *.
    destruct (inst.(visit_OpVisitor_t_on_br_table_label) v st1 d0)
      as [[rh vh]|] eqn:Hhk; cbn [bind] in H; [|discriminate].
    destruct rh as [uh|eh]; cbn [opiter_visit bind] in H;
      [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (label_hook_accept W inst' w st1 d0 Hacc) as [wh Hwh].
    rewrite Hwh. cbn [bind opiter_visit]. rewrite branch_ok. cbn [bind].
    destruct (opiter_branch_target_bt target) as [bt|] eqn:Hbt;
      cbn [bind] in H |- *; [|discriminate].
    destruct (opiter_merge_target expect bt) as [r1|] eqn:Hmt;
      cbn [bind] in H |- *; [|discriminate].
    destruct r1 as [bt1|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H |- *. cbn [bind] in H |- *.
    destruct (u32_add i 1%u32) as [i1|] eqn:Hadd; cbn [bind] in H |- *;
      [|discriminate].
    assert (Hi1 : to_Z i1 = to_Z i + 1).
    { unfold u32_add, scalar_add in Hadd. apply mk_scalar_ok_to_Z in Hadd.
      assert (H1 : to_Z 1%u32 = 1) by reflexivity. rewrite Hadd. lia. }
    exact (IH V W inst inst' st1 data count vh wh (Some bt1) i1 res st' v'
             Hacc (ltac:(cbn in Hn; lia)) H).
Qed.

Lemma read_table_labels_transfer :
  forall V W (inst : visit_OpVisitor_t V) (inst' : visit_OpVisitor_t W)
         st data count v w res st' v',
  hooks_accept inst' ->
  opiter_read_table_labels inst st data count v
    = Ok (Core_result_Result_Ok res, st', v') ->
  exists w', opiter_read_table_labels inst' st data count w
             = Ok (Core_result_Result_Ok res, st', w').
Proof.
  intros V W inst inst' st data count v w res st' v' Hacc H.
  unfold opiter_read_table_labels in H |- *.
  apply (read_table_labels_loop_transfer (Z.to_nat (to_Z count)) V W inst inst'
           st data count v w None 0%u32 res st' v' Hacc); [|exact H].
  assert (H0 : to_Z 0%u32 = 0) by reflexivity. rewrite H0.
  rewrite Z2Nat.id by apply u32_nonneg. reflexivity.
Qed.

Lemma read_br_table_transfer :
  forall V W (inst : visit_OpVisitor_t V) (inst' : visit_OpVisitor_t W)
         st data v w res st' v',
  hooks_accept inst' ->
  opiter_read_br_table inst st data v
    = Ok (Core_result_Result_Ok res, st', v') ->
  exists w', opiter_read_br_table inst' st data w
             = Ok (Core_result_Result_Ok res, st', w').
Proof.
  intros V W inst inst' st data v w res st' v' Hacc H.
  unfold opiter_read_br_table in H |- *.
  destruct (reader_read_u32_leb data st.(opiter_OpIterState_pos)) as [r0|]
    eqn:Hleb; cbn [bind] in H |- *; [|discriminate].
  destruct r0 as [[count p1]|e0]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H |- *. cbn [bind] in H |- *.
  destruct (opiter_read_table_labels inst _ data count v) as [[[r1 st1] v1]|]
    eqn:Htl; cbn [bind] in H; [|discriminate].
  destruct r1 as [common|e1]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (read_table_labels_transfer V W inst inst' _ data count v w common
              st1 v1 Hacc Htl) as [w1 Hw1].
  rewrite Hw1. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (opiter_read_label st1 data) as [[r2 st2]|] eqn:Hrl;
    cbn [bind] in H |- *; [|discriminate].
  destruct r2 as [[dflt target]|e2]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H |- *. cbn [bind] in H |- *.
  destruct (opiter_branch_target_bt target) as [bt|] eqn:Hbt;
    cbn [bind] in H |- *; [|discriminate].
  destruct (opiter_merge_target common bt) as [r3|] eqn:Hmt;
    cbn [bind] in H |- *; [|discriminate].
  destruct r3 as [bt1|e3]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H |- *. cbn [bind] in H |- *.
  destruct (opiter_pop_with_type st2 Types_ValueType_I32) as [[r4 st3]|]
    eqn:Hpop; cbn [bind] in H |- *; [|discriminate].
  destruct r4 as [u4|e4]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H |- *. cbn [bind] in H |- *.
  destruct (opiter_block_results bt1) as [types|] eqn:Hbr;
    cbn [bind] in H |- *; [|discriminate].
  destruct (opiter_pop_types st3 (alloc_vec_Vec_deref types)) as [[r5 st4]|]
    eqn:Hpt; cbn [bind] in H |- *; [|discriminate].
  destruct r5 as [u5|e5]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H |- *. cbn [bind] in H |- *.
  destruct (opiter_mark_unreachable st4) as [st5|] eqn:Hmu;
    cbn [bind] in H |- *; [|discriminate].
  inversion H; subst. eauto.
Qed.

(* ================================================================== *)
(** ** The dispatch                                                    *)
(* ================================================================== *)

(** The two fan-outs first: [visit_numeric_accept] and [visit_memory_accept]
    already say a fan-out inherits acceptance from the table it dispatches
    through, so both are one branch shape each. *)
Lemma step_numeric_transfer :
  forall V W (inst : visit_OpVisitor_t V) (inst' : visit_OpVisitor_t W)
         st opcode v w st' v',
  hooks_accept inst' ->
  opiter_step_numeric inst st opcode v
    = Ok (Core_result_Result_Ok tt, st', v') ->
  exists w', opiter_step_numeric inst' st opcode w
             = Ok (Core_result_Result_Ok tt, st', w').
Proof.
  intros V W inst inst' st opcode v w st' v' Hacc H.
  unfold opiter_step_numeric in H |- *.
  destruct (opiter_convert_types opcode) as [o|] eqn:Hc;
    cbn [bind] in H |- *; [|discriminate].
  destruct o as [[from to]|].
  { eapply (visit_wrap_transfer _ _ _ _ _ _ _ _ _ _ H).
    intros. apply visit_numeric_accept. exact Hacc. }
  destruct (opiter_binary_types opcode) as [o1|] eqn:Hb;
    cbn [bind] in H |- *; [|discriminate].
  destruct o1 as [[ty rty]|]; [|discriminate].
  eapply (visit_wrap_transfer _ _ _ _ _ _ _ _ _ _ H).
  intros. apply visit_numeric_accept. exact Hacc.
Qed.

(** Closing a branch: the hook it ends in accepts, either because it is one of
    the two fan-outs or because it is one of [hooks_accept]'s conjuncts. *)
Local Ltac hook_ok Hacc :=
  intros;
  first [ apply visit_memory_accept; exact Hacc
        | apply visit_numeric_accept; exact Hacc
        | let H0 := fresh "Hacc0" in
          pose proof Hacc as H0; unfold hooks_accept in H0;
          repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end;
          eauto ].

Lemma step_memory_transfer :
  forall V W (inst : visit_OpVisitor_t V) (inst' : visit_OpVisitor_t W)
         st data env opcode v w st' v',
  hooks_accept inst' ->
  opiter_step_memory inst st data env opcode v
    = Ok (Core_result_Result_Ok tt, st', v') ->
  exists w', opiter_step_memory inst' st data env opcode w
             = Ok (Core_result_Result_Ok tt, st', w').
Proof.
  intros V W inst inst' st data env opcode v w st' v' Hacc H.
  unfold opiter_step_memory in H |- *.
  repeat (match goal with
          | |- context [ if ?c then _ else _ ] => destruct c
          end;
          [ eapply (visit_wrap_transfer _ _ _ _ _ _ _ _ _ _ H);
            hook_ok Hacc | ]).
  exact (step_numeric_transfer V W inst inst' st opcode v w st' v' Hacc H).
Qed.

(** A branch is one of three shapes, and which one is not worth naming. *)
Local Ltac xfer H Hacc :=
  first [ eapply (visit_hook_transfer _ _ _ _ _ _ _ H); hook_ok Hacc
        | eapply (visit_wrap_transfer _ _ _ _ _ _ _ _ _ _ H); hook_ok Hacc
        | eapply (visit_wrap2_transfer _ _ _ _ _ _ _ _ _ _ _ H); hook_ok Hacc ].

Lemma step_transfer :
  forall V W (inst : visit_OpVisitor_t V) (inst' : visit_OpVisitor_t W)
         st data env ctx opcode v w st' v',
  hooks_accept inst' ->
  opiter_step inst st data env ctx opcode v
    = Ok (Core_result_Result_Ok tt, st', v') ->
  exists w', opiter_step inst' st data env ctx opcode w
             = Ok (Core_result_Result_Ok tt, st', w').
Proof.
  intros V W inst inst' st data env ctx opcode v w st' v' Hacc H.
  unfold opiter_step in H |- *.
  do 15 (match goal with
         | |- context [ if ?c then _ else _ ] => destruct c
         end; [ xfer H Hacc | ]).
  (* [br_table]: the reader itself calls a hook per label, so the transfer
     goes through [read_br_table] before the operator's own hook. *)
  match goal with
  | |- context [ if ?c then _ else _ ] => destruct c
  end.
  { destruct (visit_wrapv_ok _ _ _ _ _ _ _ H) as [x [y [v0 Hm]]].
    destruct (read_br_table_transfer V W inst inst' st data v w (x, y) st' v0
                Hacc Hm) as [w0 Hw0].
    eapply (visit_wrapv_accept _ _ _ _ _ _ _ _ _ Hw0). hook_ok Hacc. }
  repeat (match goal with
          | |- context [ if ?c then _ else _ ] => destruct c
          end; [ xfer H Hacc | ]).
  exact (step_memory_transfer V W inst inst' st data env opcode v w st' v'
           Hacc H).
Qed.

(* ================================================================== *)
(** ** The loop, and the two directions a consumer wants               *)
(* ================================================================== *)

(** The measure is the bytes left, as it is for no-panic: [read_op] shortens it
    by one and no reader lengthens it. *)
Lemma validate_body_loop_transfer :
  forall m V W (inst : visit_OpVisitor_t V) (inst' : visit_OpVisitor_t W)
         v w data env locals results st v',
  hooks_accept inst' ->
  to_Z (slice_len data) - to_Z st.(opiter_OpIterState_pos) <= Z.of_nat m ->
  opiter_validate_body_with_loop inst data env locals results v st
    = Ok (Core_result_Result_Ok tt, v') ->
  exists w', opiter_validate_body_with_loop inst' data env locals results w st
             = Ok (Core_result_Result_Ok tt, w').
Proof.
  induction m as [|m IH];
    intros V W inst inst' v w data env locals results st v' Hacc Hmeas H;
    unfold opiter_validate_body_with_loop in H |- *;
    rewrite loop_unfold in H; rewrite loop_unfold;
    cbn beta iota in H |- *;
    unfold opiter_control_stack_empty in H |- *;
    rewrite vec_is_empty_spec in H |- *; cbn [bind] in H |- *;
    destruct (vec_list st.(opiter_OpIterState_ctrls)) eqn:Hctrls.
  1,3: destruct (st.(opiter_OpIterState_pos) s= slice_len data);
       [inversion H; subst; eauto | discriminate].
  - (* the budget is spent, so [read_op] is past the end and the run rejected *)
    assert (Hend : Z.of_nat (List.length (vec_list data))
                   <= to_Z st.(opiter_OpIterState_pos)).
    { rewrite slice_len_spec in Hmeas. cbn in Hmeas. lia. }
    rewrite (read_op_err_at_end st data Hend) in H. cbn [bind] in H.
    try_err_rw_in H. discriminate.
  - destruct (opiter_read_op st data) as [[r0 st2]|] eqn:Hro;
      cbn [bind] in H |- *; [|discriminate].
    destruct r0 as [b|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H |- *. cbn [bind] in H |- *.
    destruct (opiter_step inst st2 data env
                (mkopiter_Context_t locals results) b v) as [[[r1 st3] v4]|]
      eqn:Hstep; cbn [bind] in H; [|discriminate].
    destruct r1 as [u1|e1]; [|try_err_rw_in H; discriminate].
    destruct u1. rewrite branch_ok in H. cbn [bind] in H.
    destruct (step_transfer V W inst inst' st2 data env
                (mkopiter_Context_t locals results) b v w st3 v4 Hacc Hstep)
      as [w4 Hw4].
    rewrite Hw4. cbn [bind]. rewrite branch_ok. cbn [bind].
    pose proof (read_op_advance st data b st2 Hro) as Hadv.
    pose proof (step_mono V inst v st2 data env
                  (mkopiter_Context_t locals results) b _ st3 v4 Hstep) as Hmono.
    exact (IH V W inst inst' v4 w4 data env locals results st3 v' Hacc
             (ltac:(cbn in Hmeas; lia)) H).
Qed.

(** An accepting run at one consumer is an accepting run at any consumer whose
    hooks accept. The two corollaries below are this at the do-nothing consumer,
    one on each side. *)
Theorem validate_body_with_transfer :
  forall V W (inst : visit_OpVisitor_t V) (inst' : visit_OpVisitor_t W)
         data env ctx v w v',
  hooks_accept inst' ->
  opiter_validate_body_with inst data env ctx v
    = Ok (Core_result_Result_Ok tt, v') ->
  exists w', opiter_validate_body_with inst' data env ctx w
             = Ok (Core_result_Result_Ok tt, w').
Proof.
  intros V W inst inst' data env ctx v w v' Hacc H.
  unfold opiter_validate_body_with in H |- *.
  destruct (slice_len data s> limits_max_function_bytes); [discriminate|].
  rewrite vec_deref_spec in H |- *.
  destruct (opiter_start_function ctx.(opiter_Context_results)) as [st|]
    eqn:Hsf; cbn [bind] in H |- *; [|discriminate].
  pose proof (start_function_pos _ st Hsf) as Hpos.
  apply (validate_body_loop_transfer (Z.to_nat (to_Z (slice_len data)))
           V W inst inst' v w data env ctx.(opiter_Context_locals)
           ctx.(opiter_Context_results) st v' Hacc); [|exact H].
  rewrite Hpos. rewrite Z2Nat.id by apply usize_nonneg. lia.
Qed.

(** What a consumer that validates a body with its own visitor may conclude:
    [validate_body] would have accepted the same bytes. This is what turns a
    compiler's own run into the verdict the module walk asks it for. *)
Corollary validate_body_driven :
  forall V (inst : visit_OpVisitor_t V) data env ctx v v',
  opiter_validate_body_with inst data env ctx v
    = Ok (Core_result_Result_Ok tt, v') ->
  opiter_validate_body data env ctx = Ok (Core_result_Result_Ok tt).
Proof.
  intros V inst data env ctx v v' H.
  destruct (validate_body_with_transfer V visit_NopVisitor_t inst
              visit_NopVisitor_Insts_ItascaVisitOpVisitor data env ctx v tt v'
              nop_hooks_accept H) as [w' Hw].
  unfold opiter_validate_body. rewrite Hw. cbn [bind]. reflexivity.
Qed.

(** And the converse, which completeness needs: a body [validate_body] accepts
    is one the consumer's own run accepts too, provided its hooks do not decline. *)
Corollary validate_body_accepts :
  forall V (inst : visit_OpVisitor_t V) data env ctx v,
  hooks_accept inst ->
  opiter_validate_body data env ctx = Ok (Core_result_Result_Ok tt) ->
  exists v', opiter_validate_body_with inst data env ctx v
             = Ok (Core_result_Result_Ok tt, v').
Proof.
  intros V inst data env ctx v Hacc H.
  apply (validate_body_with_transfer visit_NopVisitor_t V
           visit_NopVisitor_Insts_ItascaVisitOpVisitor inst data env ctx tt v
           tt Hacc).
  exact (validate_body_nop data env ctx _ H).
Qed.
