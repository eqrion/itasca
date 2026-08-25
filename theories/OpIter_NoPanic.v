(** * The streaming validator cannot panic

    [validate_body] always returns a verdict. Never [Fail_], which is what the
    Aeneas extraction turns a Rust panic into, and never a non-terminating loop.
    For a browser this is arguably the more valuable half of the story: a
    validator that accepts the right programs but can be made to abort on a
    crafted module is not usable.

    The whole argument rests on one implementation limit. [validate_body] rejects
    a body longer than [MAX_FUNCTION_BYTES], so the cursor is bounded; [read_op]
    advances it by one byte per iteration, which both terminates the loop and pays
    for the at most one stack entry a reader adds; and with the stacks bounded,
    [Vec::push] cannot reach [usize_max]. Take the limit away and there is no
    bound on either stack, and the push becomes a live panic site.

    Everything below it is already proved: the readers are total
    ([OpIter_State.v], [OpIter_Decode.v]), no reader grows the stacks by more than
    one, and no reader moves the cursor backwards. This file is the assembly. *)

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

Open Scope Z_scope.

(* ================================================================== *)
(** ** The two ends of a run                                          *)
(* ================================================================== *)

Lemma max_function_bytes_val : to_Z limits_max_function_bytes = 7654321.
Proof. reflexivity. Qed.

(** Room to spare: the limit is under [u32_max], which [usize_max_bound] says a
    [usize] can hold. *)
Lemma max_function_bytes_fits : 7654321 + 2 <= usize_max.
Proof.
  pose proof usize_max_bound as H. rewrite u32_max_val in H. lia.
Qed.

(** [start_function] pushes the body frame onto empty stacks, so the run starts
    with the cursor at zero and one entry in play. *)
Lemma start_function_total : forall results,
  exists st, opiter_start_function results = Ok st
             /\ to_Z st.(opiter_OpIterState_pos) = 0
             /\ stack_size st = 1%nat.
Proof.
  intros results. unfold opiter_start_function.
  assert (Hbt : exists bt,
            (if slice_len results s= 1%usize
             then (vt <- slice_index_usize results 0%usize;
                   Ok (Opiter_BlockType_Value vt))
             else Ok Opiter_BlockType_Empty) = Ok bt).
  { destruct (slice_len results s= 1%usize) eqn:H1; [|eexists; reflexivity].
    apply scalar_eqb_true in H1. rewrite slice_len_spec in H1.
    assert (H1' : to_Z 1%usize = 1) by reflexivity.
    destruct (slice_index_usize_ok results 0%usize) as [vt Hidx].
    { assert (H0 : to_Z 0%usize = 0) by reflexivity. lia. }
    rewrite Hidx. cbn [bind]. eexists. reflexivity. }
  destruct Hbt as [bt Hbt]. rewrite Hbt. cbn [bind].
  destruct (push_ctrl_total
              {| opiter_OpIterState_vals := alloc_vec_Vec_new opiter_StackType_t;
                 opiter_OpIterState_ctrls := alloc_vec_Vec_new opiter_Ctrl_t;
                 opiter_OpIterState_pos := 0%usize |}
              Opiter_LabelKind_Body bt) as [st Hpc].
  { cbn [opiter_OpIterState_ctrls]. pose proof max_function_bytes_fits. cbn. lia. }
  exists st. split; [exact Hpc|].
  destruct (push_ctrl_spec _ _ _ st Hpc) as [Hv Hc].
  cbn [opiter_OpIterState_vals opiter_OpIterState_ctrls] in Hv, Hc.
  split.
  - pose proof (push_ctrl_pos _ _ _ st Hpc) as Hp. unfold pos_of in Hp.
    cbn [opiter_OpIterState_pos] in Hp. rewrite Hp. reflexivity.
  - unfold stack_size. rewrite Hv. rewrite Hc. reflexivity.
Qed.

(* ================================================================== *)
(** ** The loop                                                        *)
(* ================================================================== *)

(** [m] is both the iteration budget and the stack budget. The measure is the
    bytes left, which [read_op] shortens by one and no reader lengthens; the stack
    invariant is that the current size plus the remaining iterations stays within
    the body length, which holds because each iteration trades one byte for at
    most one entry. *)
Lemma validate_body_loop_total : forall m V (inst : visit_OpVisitor_t V) v
                                        data module locals results st,
  hooks_total inst ->
  to_Z (slice_len data) - to_Z st.(opiter_OpIterState_pos) <= Z.of_nat m ->
  Z.of_nat (stack_size st) + Z.of_nat m <= to_Z (slice_len data) + 1 ->
  to_Z (slice_len data) <= 7654321 ->
  exists r, opiter_validate_body_with_loop inst data module locals results v st
            = Ok r.
Proof.
  induction m as [|m IH];
    intros V inst v data module locals results st Hvt Hmeas Hbudget Hlim;
    unfold opiter_validate_body_with_loop; rewrite loop_unfold; cbn beta iota;
    unfold opiter_control_stack_empty; rewrite vec_is_empty_spec; cbn [bind];
    destruct (vec_list st.(opiter_OpIterState_ctrls)) eqn:Hctrls;
    [ destruct (st.(opiter_OpIterState_pos) s= slice_len data);
      eexists; reflexivity
    | | destruct (st.(opiter_OpIterState_pos) s= slice_len data);
        eexists; reflexivity
    | ].
  - (* the budget is spent, so the cursor is at or past the end *)
    assert (Hend : Z.of_nat (List.length (vec_list data))
                   <= to_Z st.(opiter_OpIterState_pos)).
    { rewrite slice_len_spec in Hmeas. cbn in Hmeas. lia. }
    rewrite (read_op_err_at_end st data Hend). cbn [bind].
    rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
    eexists. reflexivity.
  - (* one operator, then round again *)
    destruct (read_op_total st data) as [r0 [st2 Hro]].
    rewrite Hro. cbn [bind].
    pose proof (read_op_size st data r0 st2 Hro) as Hsz2.
    destruct r0 as [b|e].
    2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
         eexists. reflexivity. }
    rewrite branch_ok. cbn [bind].
    pose proof (read_op_advance st data b st2 Hro) as Hadv.
    assert (Hroom2 : room st2).
    { unfold room. rewrite Hsz2. pose proof max_function_bytes_fits. lia. }
    destruct (step_total V inst v st2 data module
                (mkopiter_Context_t locals results) b Hvt Hroom2)
      as [r1 [st3 [v4 Hstep]]].
    rewrite Hstep. cbn [bind].
    pose proof (step_mono V inst v st2 data module
                  (mkopiter_Context_t locals results) b r1 st3 v4 Hstep) as Hmono.
    pose proof (step_size V inst v st2 data module
                  (mkopiter_Context_t locals results) b r1 st3 v4 Hstep) as Hsz3.
    destruct r1 as [u1|e1].
    2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
         eexists. reflexivity. }
    destruct u1. rewrite branch_ok. cbn [bind].
    apply (IH V inst v4 data module locals results st3 Hvt).
    + cbn in Hmeas. lia.
    + cbn in Hbudget. lia.
    + exact Hlim.
Qed.

(* ================================================================== *)
(** ** The theorem                                                     *)
(* ================================================================== *)

(** No input makes the push validator panic or diverge, whatever the consumer
    is, provided its hooks return. The size check is inside the function, so
    there is no precondition for a caller to get wrong. *)
Theorem validate_body_with_no_panic : forall V (inst : visit_OpVisitor_t V) v
                                             data module ctx,
  hooks_total inst ->
  exists r, opiter_validate_body_with inst data module ctx v = Ok r.
Proof.
  intros V inst v data module ctx Hvt. unfold opiter_validate_body_with.
  destruct (slice_len data s> limits_max_function_bytes) eqn:Hbig;
    [eexists; reflexivity|].
  apply scalar_gtb_false in Hbig. rewrite max_function_bytes_val in Hbig.
  rewrite vec_deref_spec.
  destruct (start_function_total ctx.(opiter_Context_results))
    as [st [Hsf [Hpos Hsz]]].
  rewrite Hsf. cbn [bind].
  apply (validate_body_loop_total
           (Z.to_nat (to_Z (slice_len data))) V inst v data module
           ctx.(opiter_Context_locals) ctx.(opiter_Context_results) st Hvt).
  - rewrite Hpos. rewrite Z2Nat.id by apply usize_nonneg. lia.
  - rewrite Hsz. rewrite Z2Nat.id by apply usize_nonneg. lia.
  - exact Hbig.
Qed.

(** The validating-only consumer accepts every hook, so [validate_body] itself
    never panics and never diverges: no hypothesis at all. *)
Theorem validate_body_no_panic : forall data module ctx,
  exists r, opiter_validate_body data module ctx = Ok r.
Proof.
  intros data module ctx. unfold opiter_validate_body.
  destruct (validate_body_with_no_panic _
              visit_NopVisitor_Insts_ItascaVisitOpVisitor tt data module ctx
              nop_hooks_total) as [r Hr].
  rewrite Hr. cbn [bind]. destruct r as [r0 v0]. eexists. reflexivity.
Qed.
