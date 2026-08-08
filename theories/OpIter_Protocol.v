(** * The pending-opcode protocol

    The API is two-phase: [read_op] returns an opcode and the consumer dispatches
    to a matching reader itself. Nothing in a consumer's type system forces the
    dispatch to be correct, and SpiderMonkey's [OpIter] keeps the last-read
    opcode under [#ifdef DEBUG] (WasmOpIter.h), so a release-build mis-dispatch
    silently misparses.

    The Rust records the pending opcode unconditionally and every reader checks
    it. What is proved here is that a mismatched reader is *inert*: it reports
    ProtocolViolation and leaves the operand stack, the control stack and the
    cursor exactly as they were. That converts "the consumer must dispatch
    correctly" from an unverifiable assumption about the caller into a property
    of the Rust. *)

Require Import Primitives.
Import Primitives.
Require Import Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Import Veriwasm.Aeneas_Specs.

Open Scope Z_scope.

(** Everything a consumer can observe apart from the pending opcode itself. *)
Definition obs (st : opiter_OpIterState_t) :=
  (st.(opiter_OpIterState_vals),
   st.(opiter_OpIterState_ctrls),
   st.(opiter_OpIterState_pos)).

(** No pending opcode, or one that is not [e]. Both must be rejected: a reader
    called without a preceding [read_op] is as much a protocol error as one
    called for the wrong opcode. *)
Definition mismatches (st : opiter_OpIterState_t) (e : u8) : Prop :=
  forall b, st.(opiter_OpIterState_pending) = Some b -> to_Z b <> to_Z e.

Lemma take_pending_mismatch : forall st e,
  mismatches st e ->
  exists st',
    opiter_take_pending st e
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof.
  intros st e Hmis. unfold opiter_take_pending, obs.
  destruct (st.(opiter_OpIterState_pending)) as [b|] eqn:Hp.
  - rewrite (scalar_neqb_of_neq b e (Hmis b Hp)).
    eexists. split; reflexivity.
  - eexists. split; reflexivity.
Qed.

Lemma take_pending_ok : forall st e b,
  st.(opiter_OpIterState_pending) = Some b -> to_Z b = to_Z e ->
  exists st',
    opiter_take_pending st e = Ok (Core_result_Result_Ok tt, st')
    /\ obs st' = obs st
    /\ st'.(opiter_OpIterState_pending) = None.
Proof.
  intros st e b Hp Heq. unfold opiter_take_pending, obs.
  rewrite Hp.
  assert (Hneq : (b s<> e) = false).
  { unfold scalar_neqb, scalar_eqb. apply Bool.negb_false_iff.
    apply Z.eqb_eq. exact Heq. }
  rewrite Hneq. eexists. split; [reflexivity|]. split; reflexivity.
Qed.

(** [read_op] always records what it read, which is the precondition every
    reader's success case needs. *)
Lemma read_op_sets_pending : forall st data b st',
  opiter_read_op st data = Ok (Core_result_Result_Ok b, st') ->
  st'.(opiter_OpIterState_pending) = Some b.
Proof.
  intros st data b st' H. unfold opiter_read_op in H.
  destruct (reader_read_byte data st.(opiter_OpIterState_pos)) as [r|] eqn:Hrb;
    cbn [bind] in H; [|discriminate].
  destruct r as [[b0 p0]|e].
  - rewrite branch_ok in H. cbn [bind] in H. injection H as <- <-. reflexivity.
  - rewrite branch_err in H. cbn [bind] in H.
    rewrite from_residual_err in H. cbn [bind] in H. discriminate.
Qed.

(** Each reader begins with [take_pending] and threads its result through the
    [?] plumbing, so a mismatch short-circuits with the state untouched. *)
Ltac reader_inert :=
  match goal with
  | [ Hmis : mismatches ?st ?e |- _ ] =>
      destruct (take_pending_mismatch st e Hmis) as [st' [Htp Hobs]];
      rewrite Htp; cbn [bind];
      rewrite branch_err; cbn [bind];
      rewrite from_residual_err; cbn [bind];
      exists st'; split; [reflexivity | exact Hobs]
  end.

Lemma read_nop_inert : forall st,
  mismatches st opiter_op_nop ->
  exists st',
    opiter_read_nop st
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof.
  intros st Hmis. unfold opiter_read_nop.
  destruct (take_pending_mismatch st opiter_op_nop Hmis) as [st' [Htp Hobs]].
  rewrite Htp. exists st'. split; [reflexivity | exact Hobs].
Qed.

Lemma read_unreachable_inert : forall st,
  mismatches st opiter_op_unreachable ->
  exists st',
    opiter_read_unreachable st
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof. intros st Hmis. unfold opiter_read_unreachable. reader_inert. Qed.

Lemma read_drop_inert : forall st,
  mismatches st opiter_op_drop ->
  exists st',
    opiter_read_drop st
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof. intros st Hmis. unfold opiter_read_drop. reader_inert. Qed.

Lemma read_select_inert : forall st,
  mismatches st opiter_op_select ->
  exists st',
    opiter_read_select st
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof. intros st Hmis. unfold opiter_read_select. reader_inert. Qed.

Lemma read_i32_const_inert : forall st data,
  mismatches st opiter_op_i32_const ->
  exists st',
    opiter_read_i32_const st data
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof. intros st data Hmis. unfold opiter_read_i32_const. reader_inert. Qed.

Lemma read_f32_const_inert : forall st data,
  mismatches st opiter_op_f32_const ->
  exists st',
    opiter_read_f32_const st data
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof. intros st data Hmis. unfold opiter_read_f32_const. reader_inert. Qed.

Lemma read_f64_const_inert : forall st data,
  mismatches st opiter_op_f64_const ->
  exists st',
    opiter_read_f64_const st data
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof. intros st data Hmis. unfold opiter_read_f64_const. reader_inert. Qed.

Lemma read_i64_const_inert : forall st data,
  mismatches st opiter_op_i64_const ->
  exists st',
    opiter_read_i64_const st data
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof. intros st data Hmis. unfold opiter_read_i64_const. reader_inert. Qed.

Lemma read_binary_inert : forall st op ty res,
  mismatches st op ->
  exists st',
    opiter_read_binary st op ty res
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof. intros st op ty res Hmis. unfold opiter_read_binary. reader_inert. Qed.

Lemma read_conversion_inert : forall st op from to,
  mismatches st op ->
  exists st',
    opiter_read_conversion st op from to
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof.
  intros st op from to Hmis. unfold opiter_read_conversion. reader_inert.
Qed.

(** The prologue is where [take_pending] sits, so a mis-dispatch to any of the
    three local readers stops there. *)
Lemma take_local_inert : forall st data ctx op,
  mismatches st op ->
  exists st',
    opiter_take_local st data ctx op
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof.
  intros st data ctx op Hmis. unfold opiter_take_local. reader_inert.
Qed.

Lemma read_local_get_inert : forall st data ctx,
  mismatches st opiter_op_local_get ->
  exists st',
    opiter_read_local_get st data ctx
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof.
  intros st data ctx Hmis. unfold opiter_read_local_get.
  destruct (take_local_inert st data ctx opiter_op_local_get Hmis)
    as [st' [Htl Hobs]].
  rewrite Htl. cbn [bind]. rewrite branch_err. cbn [bind].
  rewrite from_residual_err. cbn [bind]. exists st'.
  split; [reflexivity | exact Hobs].
Qed.

Lemma read_local_set_inert : forall st data ctx,
  mismatches st opiter_op_local_set ->
  exists st',
    opiter_read_local_set st data ctx
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof.
  intros st data ctx Hmis. unfold opiter_read_local_set.
  destruct (take_local_inert st data ctx opiter_op_local_set Hmis)
    as [st' [Htl Hobs]].
  rewrite Htl. cbn [bind]. rewrite branch_err. cbn [bind].
  rewrite from_residual_err. cbn [bind]. exists st'.
  split; [reflexivity | exact Hobs].
Qed.

Lemma read_local_tee_inert : forall st data ctx,
  mismatches st opiter_op_local_tee ->
  exists st',
    opiter_read_local_tee st data ctx
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof.
  intros st data ctx Hmis. unfold opiter_read_local_tee.
  destruct (take_local_inert st data ctx opiter_op_local_tee Hmis)
    as [st' [Htl Hobs]].
  rewrite Htl. cbn [bind]. rewrite branch_err. cbn [bind].
  rewrite from_residual_err. cbn [bind]. exists st'.
  split; [reflexivity | exact Hobs].
Qed.

(** The globals' prologue is the locals' one, so the mis-dispatch stops in the
    same place: before the index, the lookup and the mutability guard. *)
Lemma take_global_inert : forall st data module op,
  mismatches st op ->
  exists st',
    opiter_take_global st data module op
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof.
  intros st data module op Hmis. unfold opiter_take_global. reader_inert.
Qed.

Lemma read_global_get_inert : forall st data module,
  mismatches st opiter_op_global_get ->
  exists st',
    opiter_read_global_get st data module
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof.
  intros st data module Hmis. unfold opiter_read_global_get.
  destruct (take_global_inert st data module opiter_op_global_get Hmis)
    as [st' [Htg Hobs]].
  rewrite Htg. cbn [bind]. rewrite branch_err. cbn [bind].
  rewrite from_residual_err. cbn [bind]. exists st'.
  split; [reflexivity | exact Hobs].
Qed.

Lemma read_global_set_inert : forall st data module,
  mismatches st opiter_op_global_set ->
  exists st',
    opiter_read_global_set st data module
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof.
  intros st data module Hmis. unfold opiter_read_global_set.
  destruct (take_global_inert st data module opiter_op_global_set Hmis)
    as [st' [Htg Hobs]].
  rewrite Htg. cbn [bind]. rewrite branch_err. cbn [bind].
  rewrite from_residual_err. cbn [bind]. exists st'.
  split; [reflexivity | exact Hobs].
Qed.

Lemma read_block_inert : forall st data,
  mismatches st opiter_op_block ->
  exists st',
    opiter_read_block st data
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof. intros st data Hmis. unfold opiter_read_block. reader_inert. Qed.

Lemma read_loop_inert : forall st data,
  mismatches st opiter_op_loop ->
  exists st',
    opiter_read_loop st data
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof. intros st data Hmis. unfold opiter_read_loop. reader_inert. Qed.

Lemma read_end_inert : forall st,
  mismatches st opiter_op_end ->
  exists st',
    opiter_read_end st
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof. intros st Hmis. unfold opiter_read_end. reader_inert. Qed.

Lemma take_branch_target_inert : forall st data op,
  mismatches st op ->
  exists st',
    opiter_take_branch_target st data op
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof.
  intros st data op Hmis. unfold opiter_take_branch_target. reader_inert.
Qed.

(** The two call operators, whose prologue is [take_index]. *)
Lemma take_index_inert : forall st data op,
  mismatches st op ->
  exists st',
    opiter_take_index st data op
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof.
  intros st data op Hmis. unfold opiter_take_index. reader_inert.
Qed.

Lemma read_call_inert : forall st data module,
  mismatches st opiter_op_call ->
  exists st',
    opiter_read_call st data module
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof.
  intros st data module Hmis. unfold opiter_read_call.
  destruct (take_index_inert st data opiter_op_call Hmis) as [st' [Hti Hobs]].
  rewrite Hti. cbn [bind]. rewrite branch_err. cbn [bind].
  rewrite from_residual_err. cbn [bind]. exists st'.
  split; [reflexivity | exact Hobs].
Qed.

Lemma read_call_indirect_inert : forall st data module,
  mismatches st opiter_op_call_indirect ->
  exists st',
    opiter_read_call_indirect st data module
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof.
  intros st data module Hmis. unfold opiter_read_call_indirect.
  destruct (take_index_inert st data opiter_op_call_indirect Hmis)
    as [st' [Hti Hobs]].
  rewrite Hti. cbn [bind]. rewrite branch_err. cbn [bind].
  rewrite from_residual_err. cbn [bind]. exists st'.
  split; [reflexivity | exact Hobs].
Qed.

Lemma read_br_inert : forall st data,
  mismatches st opiter_op_br ->
  exists st',
    opiter_read_br st data
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof.
  intros st data Hmis. unfold opiter_read_br.
  destruct (take_branch_target_inert st data opiter_op_br Hmis)
    as [st' [Htb Hobs]].
  rewrite Htb. cbn [bind]. rewrite branch_err. cbn [bind].
  rewrite from_residual_err. cbn [bind]. exists st'.
  split; [reflexivity | exact Hobs].
Qed.

Lemma read_br_if_inert : forall st data,
  mismatches st opiter_op_br_if ->
  exists st',
    opiter_read_br_if st data
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof.
  intros st data Hmis. unfold opiter_read_br_if.
  destruct (take_branch_target_inert st data opiter_op_br_if Hmis)
    as [st' [Htb Hobs]].
  rewrite Htb. cbn [bind]. rewrite branch_err. cbn [bind].
  rewrite from_residual_err. cbn [bind]. exists st'.
  split; [reflexivity | exact Hobs].
Qed.

Lemma read_return_inert : forall st ctx,
  mismatches st opiter_op_return ->
  exists st',
    opiter_read_return st ctx
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof. intros st ctx Hmis. unfold opiter_read_return. reader_inert. Qed.

Lemma read_load_inert : forall st data module op ty align,
  mismatches st op ->
  exists st',
    opiter_read_load st data module op ty align
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof.
  intros st data module op ty align Hmis. unfold opiter_read_load. reader_inert.
Qed.

(** The reserved byte comes after [take_pending], so a mis-dispatch stops
    before it and the cursor does not move. *)
Lemma read_memory_size_inert : forall st data module,
  mismatches st opiter_op_memory_size ->
  exists st',
    opiter_read_memory_size st data module
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof. intros st data module Hmis. unfold opiter_read_memory_size. reader_inert. Qed.

Lemma read_memory_grow_inert : forall st data module,
  mismatches st opiter_op_memory_grow ->
  exists st',
    opiter_read_memory_grow st data module
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof. intros st data module Hmis. unfold opiter_read_memory_grow. reader_inert. Qed.

Lemma read_store_inert : forall st data module op ty align,
  mismatches st op ->
  exists st',
    opiter_read_store st data module op ty align
      = Ok (Core_result_Result_Err Error_OpError_ProtocolViolation, st')
    /\ obs st' = obs st.
Proof.
  intros st data module op ty align Hmis. unfold opiter_read_store. reader_inert.
Qed.

(** The success direction, read backwards: a reader that got past
    [take_pending] left the observable state alone. Every step lemma for a
    reader that does not touch the stacks goes through this. *)
Lemma take_pending_ok_inv : forall st e st',
  opiter_take_pending st e = Ok (Core_result_Result_Ok tt, st') ->
  obs st' = obs st.
Proof.
  intros st e st' H. unfold opiter_take_pending in H.
  destruct (st.(opiter_OpIterState_pending)) as [b|]; [|discriminate].
  destruct (b s<> e); [discriminate|].
  (* the unit payload collapses, so injection yields one equation *)
  injection H as H2. rewrite <- H2. reflexivity.
Qed.

Lemma obs_fields : forall st st', obs st' = obs st ->
  st'.(opiter_OpIterState_vals) = st.(opiter_OpIterState_vals)
  /\ st'.(opiter_OpIterState_ctrls) = st.(opiter_OpIterState_ctrls)
  /\ st'.(opiter_OpIterState_pos) = st.(opiter_OpIterState_pos).
Proof.
  intros st st' H. unfold obs in H. injection H as H1 H2 H3.
  repeat split; assumption.
Qed.
