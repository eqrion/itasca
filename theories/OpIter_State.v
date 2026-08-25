(** * Properties of the operand and control stack helpers

    The cursor and the two stacks are independent: reading bytes never touches
    the stacks, and the stack operations never touch the cursor. This file proves
    the second half, which is what lets the decode correspondence be stated
    without mentioning stacks and the simulation invariant be stated without
    re-deriving cursor positions. *)

Require Import Primitives.
Import Primitives.
Require Import Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Import Itasca.Aeneas_Specs.

Open Scope Z_scope.

Definition pos_of (st : code_OpIterState_t) : usize :=
  st.(code_OpIterState_pos).

(** Aeneas hoists the context's fields out of [validate_body]'s loop and
    rebuilds the record from them on each iteration, so proofs about the loop
    have to see through the copy. *)
Lemma ctx_eta : forall ctx,
  {| code_Context_locals := ctx.(code_Context_locals);
     code_Context_results := ctx.(code_Context_results) |} = ctx.
Proof. intros [locals results]. reflexivity. Qed.

(** A list, split from the right at up to three elements. [select] pops three
    operands and WasmCert's [type_update_select] splits on exactly these four
    cases, so this is where the two case analyses are made to line up. *)
Lemma seg_cases : forall {A} (l : list A),
  l = []
  \/ (exists x, l = [x])
  \/ (exists y x, l = [y; x])
  \/ (exists s z y x, l = s ++ [z; y; x]).
Proof.
  intros A l. induction l as [|x l IH] using List.rev_ind.
  - left. reflexivity.
  - destruct IH as
      [-> | [[x1 ->] | [[y1 [x1 ->]] | [s [z1 [y1 [x1 ->]]]]]]].
    + right. left. exists x. reflexivity.
    + right. right. left. exists x1, x. reflexivity.
    + right. right. right. exists [], y1, x1, x. reflexivity.
    + right. right. right. exists (s ++ [z1]), y1, x1, x.
      rewrite <- List.app_assoc. rewrite <- List.app_assoc. reflexivity.
Qed.

(** An in-bounds index into a vector always yields an element, which is what
    turns each reader's own bounds check into totality. *)
Lemma vec_index_ok : forall {T} (v : alloc_vec_Vec T) (i : usize),
  (i s>= alloc_vec_Vec_len v) = false ->
  exists x,
    alloc_vec_Vec_index (core_slice_index_SliceIndexUsizeSliceInst T) v i
      = Ok x.
Proof.
  intros T v i Hge. rewrite vec_index_spec.
  destruct (List.nth_error (vec_list v) (Z.to_nat (to_Z i))) as [x|] eqn:Hnth;
    [exists x; reflexivity|].
  exfalso. apply List.nth_error_None in Hnth.
  apply scalar_geb_false_lt in Hge. rewrite vec_len_spec in Hge.
  pose proof (usize_nonneg i). lia.
Qed.

(** [index_mut]'s update closure is [alloc_vec_Vec_update v i], which never
    changes the vector's length. [read_else] rewrites its frame in place twice
    in a row, so this is what keeps both totality and the size bound from
    having to know anything about the content of either rewrite. *)
Lemma vec_index_mut_len : forall {T} (v : alloc_vec_Vec T) (i : usize)
    (c : T) (back : T -> alloc_vec_Vec T),
  alloc_vec_Vec_index_mut (core_slice_index_SliceIndexUsizeSliceInst T) v i
    = Ok (c, back) ->
  forall x, List.length (vec_list (back x)) = List.length (vec_list v).
Proof.
  intros T v i c back H x. rewrite vec_index_mut_spec in H.
  destruct (List.nth_error (vec_list v) (Z.to_nat (to_Z i))) as [y|] eqn:Hnth;
    [|discriminate].
  injection H as <- <-. rewrite vec_update_spec. apply list_update_length.
Qed.

Lemma vec_index_mut_ok : forall {T} (v : alloc_vec_Vec T) (i : usize),
  (Z.to_nat (to_Z i) < List.length (vec_list v))%nat ->
  exists c back,
    alloc_vec_Vec_index_mut (core_slice_index_SliceIndexUsizeSliceInst T) v i
      = Ok (c, back).
Proof.
  intros T v i Hlt. rewrite vec_index_mut_spec.
  destruct (List.nth_error (vec_list v) (Z.to_nat (to_Z i))) as [x|] eqn:Hnth.
  - eexists. eexists. reflexivity.
  - exfalso. apply List.nth_error_None in Hnth. lia.
Qed.

(** Indexing at the last position of a snoc: [index_mut] hands back exactly the
    snoc's last element, and its back-closure always rewrites that same slot,
    whatever it is called with. *)
Lemma vec_index_mut_of_snoc : forall {T} (v : alloc_vec_Vec T) cs c i c' back,
  vec_list v = cs ++ [c] ->
  Z.to_nat (to_Z i) = List.length cs ->
  alloc_vec_Vec_index_mut (core_slice_index_SliceIndexUsizeSliceInst T) v i
    = Ok (c', back) ->
  c' = c /\ forall x, vec_list (back x) = cs ++ [x].
Proof.
  intros T v cs c i c' back Hsnoc Hi H. rewrite vec_index_mut_spec in H.
  rewrite Hsnoc in H. rewrite Hi in H.
  rewrite List.nth_error_app2 in H; [|lia].
  rewrite Nat.sub_diag in H. cbn [List.nth_error] in H.
  injection H as <- <-. split; [reflexivity|].
  intros x. rewrite vec_update_spec. rewrite Hsnoc. rewrite Hi.
  apply list_update_snoc.
Qed.

Lemma vec_pop_len : forall {T} (v : alloc_vec_Vec T) o v',
  alloc_vec_Vec_pop alloc_alloc_Global v = Ok (o, v') ->
  vec_list v <> [] ->
  (List.length (vec_list v') < List.length (vec_list v))%nat.
Proof.
  intros T v o v' Hpop Hne.
  pose proof (vec_pop_last alloc_alloc_Global v o v' Hpop) as Hspec.
  destruct (List.rev (vec_list v)) as [|x rest] eqn:Hrev.
  - exfalso. apply Hne.
    apply (f_equal (@List.rev T)) in Hrev.
    rewrite List.rev_involutive in Hrev. simpl in Hrev. exact Hrev.
  - destruct Hspec as [_ Hv']. rewrite Hv'.
    rewrite List.rev_length.
    apply (f_equal (@List.length T)) in Hrev.
    rewrite List.rev_length in Hrev. rewrite Hrev. simpl. lia.
Qed.

(* ================================================================== *)
(** ** Helpers that do not loop                                        *)
(* ================================================================== *)

Lemma pop_stack_type_pos : forall st r st',
  code_pop_stack_type st = Ok (r, st') -> pos_of st' = pos_of st.
Proof.
  intros st r st' H. unfold code_pop_stack_type in H.
  destruct (code_ValsStack_len st.(code_OpIterState_vals)) as [n|e] eqn:Hlen
    in H; cbn [bind] in H; [|inversion H].
  destruct (code_cur_base st) as [base|e] eqn:Hcb in H;
    cbn [bind] in H; [|inversion H].
  destruct (n s= base) eqn:Hb.
  - destruct (code_cur_polymorphic st) as [pb|e] eqn:Hcp in H;
      cbn [bind] in H; [|inversion H].
    destruct pb; injection H as _ <-; reflexivity.
  - destruct (code_ValsStack_pop
                st.(code_OpIterState_vals)) as [[o v]|e] eqn:Hpop in H;
      cbn [bind] in H; [|inversion H].
    destruct o; injection H as _ <-; reflexivity.
Qed.

Lemma pop_with_type_pos : forall st vt r st',
  code_pop_with_type st vt = Ok (r, st') -> pos_of st' = pos_of st.
Proof.
  intros st vt r st' H. unfold code_pop_with_type in H.
  destruct (code_pop_stack_type st) as [[r0 st0]|] eqn:Hps; cbn [bind] in H;
    [|discriminate].
  pose proof (pop_stack_type_pos st r0 st0 Hps) as Hp0.
  destruct r0 as [t|e].
  - rewrite branch_ok in H. cbn [bind] in H.
    destruct t as [v|].
    + (* the ValueType comparison goes through the PartialEq instance *)
      destruct (types_ValueType_Insts_CoreCmpPartialEqValueType_eq v vt) as [b|]
        eqn:Heq; cbn [bind] in H; [|discriminate].
      destruct b; injection H as _ <-; exact Hp0.
    + injection H as _ <-. exact Hp0.
  - rewrite branch_err in H. cbn [bind] in H.
    rewrite from_residual_err in H. cbn [bind] in H.
    injection H as _ <-. exact Hp0.
Qed.

Lemma pop_block_results_pos : forall st bt r st',
  code_pop_block_results st bt = Ok (r, st') -> pos_of st' = pos_of st.
Proof.
  intros st bt r st' H. destruct bt as [|vt].
  - cbn [code_pop_block_results] in H. injection H as _ <-. reflexivity.
  - unfold code_pop_block_results in H.
    unfold bind in H.
    destruct (code_pop_with_type st vt) as [[r0 st0]|e] eqn:Hpop.
    2: { change (Fail_ e = Ok (r, st')) in H. congruence. }
    cbn in H.
    pose proof (pop_with_type_pos st vt r0 st0 Hpop) as Hp.
    destruct r0 as [u|e0].
    + rewrite branch_ok in H. cbn [bind] in H. destruct u.
      all: unfold pos_of in *; congruence.
    + rewrite branch_err in H. cbn [bind] in H.
      rewrite from_residual_err in H. cbn [bind] in H.
      unfold pos_of in *. congruence.
Qed.

Lemma push_val_pos : forall st t st',
  code_push_val st t = Ok st' -> pos_of st' = pos_of st.
Proof.
  intros st t st' H. unfold code_push_val in H.
  destruct (code_ValsStack_push st.(code_OpIterState_vals) t) as [v|] eqn:Hpush;
    cbn [bind] in H; [|discriminate].
  injection H as <-. reflexivity.
Qed.

Lemma push_block_results_pos : forall st bt st',
  code_push_block_results st bt = Ok st' -> pos_of st' = pos_of st.
Proof.
  intros st bt st' H. destruct bt as [|vt].
  - injection H as <-. reflexivity.
  - apply (push_val_pos st (Code_StackType_Val vt) st' H).
Qed.

Lemma push_ctrl_pos : forall st kind bt st',
  code_push_ctrl st kind bt = Ok st' -> pos_of st' = pos_of st.
Proof.
  intros st kind bt st' H. unfold code_push_ctrl in H.
  destruct (code_ValsStack_len st.(code_OpIterState_vals)) as [base|] eqn:Hlen;
    cbn [bind] in H; [|discriminate].
  destruct (code_CtrlsStack_push st.(code_OpIterState_ctrls) _) as [v|] eqn:Hpush;
    cbn [bind] in H; [|discriminate].
  injection H as <-. reflexivity.
Qed.

(* ================================================================== *)
(** ** Helpers that loop                                               *)
(* ================================================================== *)

(** [mark_unreachable] pops down to the frame base. The measure is the operand
    stack's length; [pos] is copied verbatim in the [Cont] branch and read from
    the state in the [Done] branch. *)
Lemma mark_unreachable_loop_pos : forall n st base vals ctrls pos,
  (List.length (vals_list st.(code_OpIterState_vals)) <= n)%nat ->
  code_mark_unreachable_loop st base = Ok (vals, ctrls, pos) ->
  pos = pos_of st.
Proof.
  induction n as [|n IH]; intros st base vals ctrls pos Hlen H;
    unfold code_mark_unreachable_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H.
  all: destruct (code_ValsStack_len st.(code_OpIterState_vals)) as [size|e]
      eqn:Hslen in H; cbn [bind] in H.
  2,4: inversion H.
  all: destruct (size s<= base) eqn:Hle in H.
  - injection H as _ _ <-. reflexivity.
  - (* n = 0 forces an empty operand stack, so the pop branch is unreachable *)
    apply scalar_leb_false in Hle.
    destruct (code_ValsStack_pop st.(code_OpIterState_vals)) as [[o v]|e]
      eqn:Hpop in H; cbn [bind] in H; [|inversion H].
    exfalso.
    assert (Hnil : vals_list st.(code_OpIterState_vals) = []).
    { destruct (vals_list st.(code_OpIterState_vals)); [reflexivity|].
      simpl in Hlen. lia. }
    pose proof (vals_stack_len_spec _ size Hslen) as Hsize.
    rewrite Hnil in Hsize. cbn in Hsize. rewrite Hsize in Hle.
    pose proof (usize_nonneg base). lia.
  - injection H as _ _ <-. reflexivity.
  - destruct (code_ValsStack_pop st.(code_OpIterState_vals)) as [[o v]|e]
      eqn:Hpop in H; cbn [bind] in H; [|inversion H].
    (* The recursive call is on a state whose operand stack is one shorter. *)
    apply scalar_leb_false in Hle.
    assert (Hne : vals_list st.(code_OpIterState_vals) <> []).
    { intros Hnil.
      pose proof (vals_stack_len_spec _ size Hslen) as Hsize.
      rewrite Hnil in Hsize. cbn in Hsize. rewrite Hsize in Hle.
      pose proof (usize_nonneg base). lia. }
    pose proof (vals_stack_pop_len _ o v Hpop Hne) as Hlt.
    (* Name the shortened state: its [pos] is [st]'s by construction, so the IH
       transports through. Unification cannot guess it from the goal. *)
    set (st' := {| code_OpIterState_vals := v;
                   code_OpIterState_ctrls := st.(code_OpIterState_ctrls);
                   code_OpIterState_pos := st.(code_OpIterState_pos)
                |}) in H.
    transitivity (pos_of st'); [|reflexivity].
    apply (IH st' base vals ctrls pos); [|exact H].
    subst st'. cbn [code_OpIterState_vals]. lia.
Qed.

Lemma mark_unreachable_pos : forall st st',
  code_mark_unreachable st = Ok st' -> pos_of st' = pos_of st.
Proof.
  intros st st' H. unfold code_mark_unreachable in H.
  destruct (code_cur_base st) as [base|e] eqn:Hcb in H; cbn [bind] in H;
    [|inversion H].
  destruct (code_mark_unreachable_loop st base) as [[[v v1] i]|e]
    eqn:Hloop in H; cbn [bind] in H; [|inversion H].
  pose proof (mark_unreachable_loop_pos
                (List.length (vals_list st.(code_OpIterState_vals)))
                st base v v1 i (Nat.le_refl _) Hloop) as Hi.
  destruct (code_CtrlsStack_len v1) as [n|e] eqn:Hlen in H;
    cbn [bind] in H; [|inversion H].
  destruct (n s= 0%usize) eqn:Hempty in H;
    [injection H as <-; exact Hi | ].
  (* The else branch flips the top frame's polymorphic flag in place, via
     index_mut, and rebuilds the record with pos := i. *)
  destruct (usize_sub n 1%usize) as [i1|e] eqn:Hsub in H;
    cbn [bind] in H; [|inversion H].
  destruct (code_CtrlsStack_get v1 i1) as [c|e] eqn:Hget in H;
    cbn [bind] in H; [|inversion H].
  destruct (code_CtrlsStack_set v1 i1 _) as [cs|e] eqn:Hset in H;
    cbn [bind] in H; [|inversion H].
  injection H as <-. exact Hi.
Qed.

(** [pop_types] walks the expected types backwards, so the measure is the index
    itself. *)
Lemma pop_types_loop_pos : forall n st types i r st',
  to_Z i <= Z.of_nat n ->
  code_pop_types_loop st types i = Ok (r, st') -> pos_of st' = pos_of st.
Proof.
  induction n as [|n IH]; intros st types i r st' Hn H;
    unfold code_pop_types_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H;
    destruct (i s= 0%usize) eqn:Hz; [injection H as _ <-; reflexivity | | |].
  - (* n = 0 forces i = 0, so the decrementing branch is unreachable *)
    exfalso. apply scalar_eqb_false in Hz.
    assert (to_Z 0%usize = 0) by reflexivity.
    pose proof (usize_nonneg i). cbn in Hn. lia.
  - injection H as _ <-. reflexivity.
  - apply scalar_eqb_false in Hz.
    assert (H0 : to_Z 0%usize = 0) by reflexivity.
    rewrite H0 in Hz.
    destruct (usize_sub_1_ok i) as [i2 [Hsub Hi2]];
      [pose proof (usize_nonneg i); lia|].
    rewrite Hsub in H. cbn [bind] in H.
    destruct (slice_index_usize types i2) as [vt|] eqn:Hidx; cbn [bind] in H;
      [|discriminate].
    destruct (code_pop_with_type st vt) as [[r0 st0]|] eqn:Hpwt;
      cbn [bind] in H; [|discriminate].
    pose proof (pop_with_type_pos st vt r0 st0 Hpwt) as Hp0.
    destruct r0 as [t|e].
    + rewrite branch_ok in H. cbn [bind] in H.
      rewrite (IH st0 types i2 r st'); [exact Hp0 | lia | exact H].
    + rewrite branch_err in H. cbn [bind] in H.
      rewrite from_residual_err in H. cbn [bind] in H.
      injection H as _ <-. exact Hp0.
Qed.

Lemma pop_types_pos : forall st types r st',
  code_pop_types st types = Ok (r, st') -> pos_of st' = pos_of st.
Proof.
  intros st types r st' H. unfold code_pop_types in H.
  eapply pop_types_loop_pos with (n := Z.to_nat (to_Z (slice_len types)));
    [|exact H].
  rewrite Z2Nat.id by apply usize_nonneg. lia.
Qed.

(** None of the popping helpers ever touch the control stack: [read_else] needs
    this to know the frame it looked up in [st1] is still there, at the same
    index, in the state [pop_types] hands back. *)
Lemma pop_stack_type_ctrls : forall st r st',
  code_pop_stack_type st = Ok (r, st') ->
  ctrls_list st'.(code_OpIterState_ctrls)
    = ctrls_list st.(code_OpIterState_ctrls).
Proof.
  intros st r st' H. unfold code_pop_stack_type in H.
  destruct (code_ValsStack_len st.(code_OpIterState_vals)) as [n|e] eqn:Hlen
    in H; cbn [bind] in H; [|inversion H].
  destruct (code_cur_base st) as [base|e] eqn:Hcb in H;
    cbn [bind] in H; [|inversion H].
  destruct (n s= base) eqn:Hb.
  - destruct (code_cur_polymorphic st) as [pb|e] eqn:Hcp in H;
      cbn [bind] in H; [|inversion H].
    destruct pb; injection H as _ <-; reflexivity.
  - destruct (code_ValsStack_pop st.(code_OpIterState_vals)) as [[o v]|e]
      eqn:Hpop in H; cbn [bind] in H; [|inversion H].
    destruct o; injection H as _ <-; reflexivity.
Qed.

Lemma pop_with_type_ctrls : forall st vt r st',
  code_pop_with_type st vt = Ok (r, st') ->
  ctrls_list st'.(code_OpIterState_ctrls)
    = ctrls_list st.(code_OpIterState_ctrls).
Proof.
  intros st vt r st' H. unfold code_pop_with_type in H.
  destruct (code_pop_stack_type st) as [[r0 st0]|] eqn:Hps; cbn [bind] in H;
    [|discriminate].
  pose proof (pop_stack_type_ctrls st r0 st0 Hps) as Hc0.
  destruct r0 as [t|e].
  - rewrite branch_ok in H. cbn [bind] in H.
    destruct t as [v|].
    + destruct (types_ValueType_Insts_CoreCmpPartialEqValueType_eq v vt) as [b|]
        eqn:Heq; cbn [bind] in H; [|discriminate].
      destruct b; injection H as _ <-; exact Hc0.
    + injection H as _ <-. exact Hc0.
  - rewrite branch_err in H. cbn [bind] in H.
    rewrite from_residual_err in H. cbn [bind] in H.
    injection H as _ <-. exact Hc0.
Qed.

Lemma pop_types_loop_ctrls : forall n st types i r st',
  to_Z i <= Z.of_nat n ->
  code_pop_types_loop st types i = Ok (r, st') ->
  ctrls_list st'.(code_OpIterState_ctrls)
    = ctrls_list st.(code_OpIterState_ctrls).
Proof.
  induction n as [|n IH]; intros st types i r st' Hn H;
    unfold code_pop_types_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H;
    destruct (i s= 0%usize) eqn:Hz; [injection H as _ <-; reflexivity | | |].
  - exfalso. apply scalar_eqb_false in Hz.
    assert (to_Z 0%usize = 0) by reflexivity.
    pose proof (usize_nonneg i). cbn in Hn. lia.
  - injection H as _ <-. reflexivity.
  - apply scalar_eqb_false in Hz.
    assert (H0 : to_Z 0%usize = 0) by reflexivity.
    rewrite H0 in Hz.
    destruct (usize_sub_1_ok i) as [i2 [Hsub Hi2]];
      [pose proof (usize_nonneg i); lia|].
    rewrite Hsub in H. cbn [bind] in H.
    destruct (slice_index_usize types i2) as [vt|] eqn:Hidx; cbn [bind] in H;
      [|discriminate].
    destruct (code_pop_with_type st vt) as [[r0 st0]|] eqn:Hpwt;
      cbn [bind] in H; [|discriminate].
    pose proof (pop_with_type_ctrls st vt r0 st0 Hpwt) as Hc0.
    destruct r0 as [t|e].
    + rewrite branch_ok in H. cbn [bind] in H.
      rewrite (IH st0 types i2 r st'); [exact Hc0 | lia | exact H].
    + rewrite branch_err in H. cbn [bind] in H.
      rewrite from_residual_err in H. cbn [bind] in H.
      injection H as _ <-. exact Hc0.
Qed.

Lemma pop_types_ctrls : forall st types r st',
  code_pop_types st types = Ok (r, st') ->
  ctrls_list st'.(code_OpIterState_ctrls)
    = ctrls_list st.(code_OpIterState_ctrls).
Proof.
  intros st types r st' H. unfold code_pop_types in H.
  eapply pop_types_loop_ctrls with (n := Z.to_nat (to_Z (slice_len types)));
    [|exact H].
  rewrite Z2Nat.id by apply usize_nonneg. lia.
Qed.

(** [push_types] counts up, so the measure is what is left of the slice. *)
Lemma push_types_loop_pos : forall n st types i st',
  to_Z (slice_len types) - to_Z i <= Z.of_nat n ->
  code_push_types_loop st types i = Ok st' -> pos_of st' = pos_of st.
Proof.
  induction n as [|n IH]; intros st types i st' Hn H;
    unfold code_push_types_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H;
    destruct (i s>= slice_len types) eqn:Hge;
    [injection H as <-; reflexivity | | |].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hn. lia.
  - injection H as <-. reflexivity.
  - apply scalar_geb_false_lt in Hge.
    destruct (slice_index_usize types i) as [vt|] eqn:Hidx; cbn [bind] in H;
      [|discriminate].
    destruct (code_push_val st (Code_StackType_Val vt)) as [st0|] eqn:Hpv;
      cbn [bind] in H; [|discriminate].
    pose proof (push_val_pos st _ st0 Hpv) as Hp0.
    destruct (usize_add_1_ok i) as [i3 [Hadd Hi3]].
    { pose proof (usize_le_max (slice_len types)). lia. }
    rewrite Hadd in H. cbn [bind] in H.
    rewrite (IH st0 types i3 st'); [exact Hp0 | lia | exact H].
Qed.

Lemma push_types_pos : forall st types st',
  code_push_types st types = Ok st' -> pos_of st' = pos_of st.
Proof.
  intros st types st' H. unfold code_push_types in H.
  eapply push_types_loop_pos with (n := Z.to_nat (to_Z (slice_len types)));
    [|exact H].
  rewrite Z2Nat.id by apply usize_nonneg.
  pose proof (usize_nonneg 0%usize). assert (to_Z 0%usize = 0) by reflexivity.
  lia.
Qed.

(* ================================================================== *)
(** ** Readers that consume no immediates                              *)
(* ================================================================== *)

(** These readers touch only the stacks, so the cursor is exactly where
    [read_op] left it. Stated for an arbitrary result rather than for [Ok],
    because the error branches copy the cursor too, which makes the proofs a
    single walk with no case split on success. *)

Lemma read_unreachable_pos : forall st r st',
  code_read_unreachable st = Ok (r, st') -> pos_of st' = pos_of st.
Proof.
  intros st r st' H. unfold code_read_unreachable in H.
  destruct (code_mark_unreachable st) as [st1|] eqn:Hmu; cbn [bind] in H;
    [|discriminate].
  injection H as _ <-.
  rewrite (mark_unreachable_pos st st1 Hmu). reflexivity.
Qed.

(** [return] has no immediate either, so it too leaves the cursor alone. *)
Lemma read_return_pos : forall st ctx r st',
  code_read_return st ctx = Ok (r, st') -> pos_of st' = pos_of st.
Proof.
  intros st ctx r st' H. unfold code_read_return in H.
  destruct ctx.(code_Context_results) as [vt|] eqn:Hresults;
    cbn [bind] in H.
  all: match type of H with
       | context [code_pop_block_results ?s ?bt] =>
           destruct (code_pop_block_results s bt) as [[r1 st1]|e]
             eqn:Hpt in H; cbn [bind] in H; [|inversion H];
           pose proof (pop_block_results_pos s bt r1 st1 Hpt) as Hp1
       end.
  all: destruct r1 as [u1|e1].
  all: try (rewrite branch_err in H; cbn [bind] in H;
    rewrite from_residual_err in H; cbn [bind] in H;
    injection H as _ <-; rewrite Hp1; reflexivity).
  all: destruct u1; rewrite branch_ok in H; cbn [bind] in H.
  all: destruct (code_mark_unreachable st1) as [st2|e] eqn:Hmu in H;
    cbn [bind] in H; [|inversion H].
  all: injection H as _ <-;
    rewrite (mark_unreachable_pos st1 st2 Hmu); rewrite Hp1; reflexivity.
Qed.

Lemma read_drop_pos : forall st r st',
  code_read_drop st = Ok (r, st') -> pos_of st' = pos_of st.
Proof.
  intros st r st' H. unfold code_read_drop in H.
  rewrite (pop_stack_type_pos st r st' H). reflexivity.
Qed.

(** [join_stack_type] is pure, so its only relevance to the state lemmas is that
    it cannot fail. *)
Lemma join_stack_type_total : forall a b,
  exists r, code_join_stack_type a b = Ok r.
Proof.
  intros a b. unfold code_join_stack_type.
  destruct a as [va|]; [|eexists; reflexivity].
  destruct b as [vb|]; [|eexists; reflexivity].
  rewrite vt_eq_spec. cbn [bind].
  destruct (types_ValueType_t_beq va vb); eexists; reflexivity.
Qed.

Lemma read_select_pos : forall st r st',
  code_read_select st = Ok (r, st') -> pos_of st' = pos_of st.
Proof.
  intros st r st' H. unfold code_read_select in H.
  destruct (code_pop_with_type st Types_ValueType_I32) as [[r1 st1]|] eqn:Hp;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos st _ r1 st1 Hp) as Hp1.
  destruct r1 as [t1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. rewrite Hp1. reflexivity. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_pop_stack_type st1) as [[r2 st2]|] eqn:Hq2;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_stack_type_pos st1 r2 st2 Hq2) as Hp2.
  destruct r2 as [t2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. rewrite Hp2. rewrite Hp1. reflexivity. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_pop_stack_type st2) as [[r3 st3]|] eqn:Hq3;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_stack_type_pos st2 r3 st3 Hq3) as Hp3.
  destruct r3 as [t3|e3].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. rewrite Hp3. rewrite Hp2. rewrite Hp1. reflexivity. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_join_stack_type t2 t3) as [rj|] eqn:Hj;
    cbn [bind] in H; [|discriminate].
  destruct rj as [t|ej].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. rewrite Hp3. rewrite Hp2. rewrite Hp1. reflexivity. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_push_val st3 t) as [st4|] eqn:Hpv; cbn [bind] in H;
    [|discriminate].
  injection H as _ <-.
  rewrite (push_val_pos st3 t st4 Hpv). rewrite Hp3. rewrite Hp2. rewrite Hp1.
  reflexivity.
Qed.

Lemma read_binary_pos : forall st ty res r st',
  code_read_binary st ty res = Ok (r, st') -> pos_of st' = pos_of st.
Proof.
  intros st ty res r st' H. unfold code_read_binary in H.
  destruct (code_pop_with_type st ty) as [[r1 st1]|] eqn:Hp1e;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos st ty r1 st1 Hp1e) as Hp1.
  destruct r1 as [t1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. rewrite Hp1. reflexivity. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_pop_with_type st1 ty) as [[r2 st2]|] eqn:Hp2e;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos st1 ty r2 st2 Hp2e) as Hp2.
  destruct r2 as [t2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. rewrite Hp2. rewrite Hp1. reflexivity. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_push_val st2 (Code_StackType_Val res)) as [st3|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  rewrite (push_val_pos st2 _ st3 Hpv). rewrite Hp2. rewrite Hp1. reflexivity.
Qed.

Lemma read_conversion_pos : forall st from to r st',
  code_read_conversion st from to = Ok (r, st') ->
  pos_of st' = pos_of st.
Proof.
  intros st from to r st' H. unfold code_read_conversion in H.
  destruct (code_pop_with_type st from) as [[r1 st1]|] eqn:Hp1e;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos st from r1 st1 Hp1e) as Hp1.
  destruct r1 as [t1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. rewrite Hp1. reflexivity. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_push_val st1 (Code_StackType_Val to)) as [st2|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  rewrite (push_val_pos st1 _ st2 Hpv). rewrite Hp1. reflexivity.
Qed.

(** [is_then] is a plain function of the [LabelKind], never touching the
    state: it exists only so [read_end] and [read_else] can guard on "is this
    an open then-branch" with one boolean rather than a five-way [match], which
    would otherwise duplicate whatever follows once per [LabelKind]
    constructor. *)
Lemma is_then_total : forall kind, exists b, code_is_then kind = Ok b.
Proof. intros kind. destruct kind; eexists; reflexivity. Qed.

Lemma vec_is_empty_total : forall {T} (A : Type) (v : alloc_vec_Vec T),
  exists b, alloc_vec_Vec_is_empty A v = Ok b.
Proof. intros T A v. eexists. apply vec_is_empty_spec. Qed.

Lemma is_then_spec : forall kind b,
  code_is_then kind = Ok b ->
  (b = true /\ kind = Code_LabelKind_Then)
  \/ (b = false /\ kind <> Code_LabelKind_Then).
Proof.
  intros kind b H. unfold code_is_then in H.
  destruct kind; injection H as <-.
  - right. split; [reflexivity | discriminate].
  - right. split; [reflexivity | discriminate].
  - right. split; [reflexivity | discriminate].
  - left. split; reflexivity.
  - right. split; [reflexivity | discriminate].
Qed.

(** [read_end]'s rejection of a bare [if] with a result type, collapsed. The
    guard duplicates the whole of [read_end]'s tail in the extraction, once
    under each branch; this says that when the results are empty the two
    branches are the same term, so a proof that walks the tail walks it once.
    [K] and [E] are whatever the extraction put there. *)
Lemma then_results_guard : forall {T U : Type} (b : bool) (A : Type)
                                  (v : alloc_vec_Vec U) (K E : result T),
  (b = true -> vec_list v = []) ->
  (if b
   then (b1 <- alloc_vec_Vec_is_empty A v; if b1 then K else E)
   else K) = K.
Proof.
  intros T U b A v K E H. destruct b; [|reflexivity].
  rewrite vec_is_empty_spec. rewrite (H (eq_refl _)). reflexivity.
Qed.

(** [else] closes the then-branch's results and rewrites the frame in place to
    [Else], touching only the control stack; the cursor is copied through
    every branch, including the two rewrites. *)
Lemma read_else_pos : forall st r st',
  code_read_else st = Ok (r, st') -> pos_of st' = pos_of st.
Proof.
  intros st r st' H. unfold code_read_else in H.
  destruct (code_CtrlsStack_len st.(code_OpIterState_ctrls)) as [n|e]
    eqn:Hlen in H; cbn [bind] in H; [|inversion H].
  destruct (n s= 0%usize) eqn:Hn in H.
  { injection H as _ <-. reflexivity. }
  destruct (usize_sub n 1%usize) as [i|e] eqn:Hsub in H;
    cbn [bind] in H; [|inversion H].
  destruct (code_CtrlsStack_get st.(code_OpIterState_ctrls) i) as [frame|e]
    eqn:Hidx in H; cbn [bind] in H; [|inversion H].
  destruct (code_is_then frame.(code_Ctrl_kind)) as [b|e] eqn:Hit in H;
    cbn [bind] in H; [|inversion H].
  destruct b; [|injection H as _ <-; reflexivity].
  destruct (code_pop_block_results st frame.(code_Ctrl_block_type))
    as [[r1 st1]|e] eqn:Hpt in H; cbn [bind] in H; [|inversion H].
  pose proof (pop_block_results_pos st _ r1 st1 Hpt) as Hp1.
  destruct r1 as [u1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. rewrite Hp1. reflexivity. }
  destruct u1. rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_ValsStack_len st1.(code_OpIterState_vals)) as [nv|e]
    eqn:Hvlen in H; cbn [bind] in H; [|inversion H].
  destruct (nv s<> frame.(code_Ctrl_value_stack_base)) eqn:Hg in H.
  { injection H as _ <-. rewrite Hp1. reflexivity. }
  destruct (code_CtrlsStack_set st1.(code_OpIterState_ctrls) i _)
    as [cs|e] eqn:Hset in H; cbn [bind] in H; [|inversion H].
  injection H as _ <-.
  exact Hp1.
Qed.

(** [end] pops and pushes types and drops a control frame, all of which copy the
    cursor; the final [push_types] runs on a record whose [pos] is [st1]'s. A
    [Then] frame with a nonempty result type is rejected before any of that, so
    the state does not change at all in that case. *)
Lemma read_end_pos : forall st r st',
  code_read_end st = Ok (r, st') -> pos_of st' = pos_of st.
Proof.
  intros st r st' H. unfold code_read_end in H.
  destruct (code_CtrlsStack_len st.(code_OpIterState_ctrls)) as [n|e]
    eqn:Hlen in H; cbn [bind] in H; [|inversion H].
  destruct (n s= 0%usize) eqn:Hn in H.
  { injection H as _ <-. reflexivity. }
  destruct (usize_sub n 1%usize) as [i|e] eqn:Hsub in H;
    cbn [bind] in H; [|inversion H].
  destruct (code_CtrlsStack_get st.(code_OpIterState_ctrls) i) as [frame|e]
    eqn:Hidx in H; cbn [bind] in H; [|inversion H].
  destruct frame.(code_Ctrl_block_type) as [|vt] eqn:Hbt;
    cbn [bind] in H.
  all: destruct (code_is_then frame.(code_Ctrl_kind)) as [b|e]
    eqn:Hit in H; cbn [bind] in H; [|inversion H].
  all: destruct b; cbn [bind] in H.
  3: { injection H as _ <-. reflexivity. }
  all: match type of H with
       | context [code_pop_block_results ?s ?bt] =>
           destruct (code_pop_block_results s bt) as [[r1 st1]|e]
             eqn:Hpt in H; cbn [bind] in H; [|inversion H];
           pose proof (pop_block_results_pos s bt r1 st1 Hpt) as Hp1
       end.
  all: destruct r1 as [u1|e1].
  all: try (rewrite branch_err in H; cbn [bind] in H;
    rewrite from_residual_err in H; cbn [bind] in H;
    unfold pos_of in *; congruence).
  all: destruct u1; rewrite branch_ok in H; cbn [bind] in H.
  all: destruct (code_ValsStack_len st1.(code_OpIterState_vals)) as [nv|e]
    eqn:Hvlen in H; cbn [bind] in H; [|inversion H].
  all: destruct (nv s<> frame.(code_Ctrl_value_stack_base)) eqn:Hg in H.
  all: try (unfold pos_of in *; congruence).
  all: destruct (code_CtrlsStack_pop st1.(code_OpIterState_ctrls))
    as [[o cs]|e] eqn:Hpop in H; cbn [bind] in H; [|inversion H].
  all: match type of H with
       | context [code_push_block_results ?s ?bt] =>
           destruct (code_push_block_results s bt) as [st2|e]
             eqn:Hpush in H; cbn [bind] in H; [|inversion H];
           pose proof (push_block_results_pos s bt st2 Hpush) as Hp2
       end.
  all: unfold pos_of in *;
    cbn [code_OpIterState_pos] in Hp2;
    assert (Hst : st2 = st') by congruence;
    rewrite <- Hst;
    transitivity st1.(code_OpIterState_pos); assumption.
Qed.

(** Full characterisation of a push, so callers need not unfold it. *)
Lemma push_val_spec : forall st t st',
  code_push_val st t = Ok st' ->
  vals_list st'.(code_OpIterState_vals)
    = vals_list st.(code_OpIterState_vals) ++ [t]
  /\ st'.(code_OpIterState_ctrls) = st.(code_OpIterState_ctrls)
  /\ pos_of st' = pos_of st.
Proof.
  intros st t st' H. unfold code_push_val in H.
  destruct (code_ValsStack_push st.(code_OpIterState_vals) t) as [v|e]
    eqn:Hpush in H; cbn [bind] in H; [|inversion H].
  injection H as <-. apply vals_stack_push_spec in Hpush.
  cbn [code_OpIterState_vals code_OpIterState_ctrls].
  repeat split.
  all: try reflexivity.
  all: exact Hpush.
Qed.
(* ================================================================== *)
(** ** Pure views of the streaming state                              *)
(* ================================================================== *)

(** The extracted accessors are monadic because indexing a [Vec] can in
    principle fail. These are their pure counterparts, with agreement lemmas, so
    the invariant can be stated without threading [result] through it. *)

Definition cur_ctrl (st : code_OpIterState_t) : option code_Ctrl_t :=
  List.last (List.map Some (ctrls_list st.(code_OpIterState_ctrls))) None.

Definition cur_base_nat (st : code_OpIterState_t) : nat :=
  match cur_ctrl st with
  | None => 0%nat
  | Some c => Z.to_nat (to_Z c.(code_Ctrl_value_stack_base))
  end.

Definition cur_unr (st : code_OpIterState_t) : bool :=
  match cur_ctrl st with
  | None => false
  | Some c => c.(code_Ctrl_polymorphic_base)
  end.

Lemma cur_ctrl_nil : forall st,
  ctrls_list st.(code_OpIterState_ctrls) = [] -> cur_ctrl st = None.
Proof. intros st H. unfold cur_ctrl. rewrite H. reflexivity. Qed.

Lemma cur_ctrl_snoc : forall st cs c,
  ctrls_list st.(code_OpIterState_ctrls) = cs ++ [c] -> cur_ctrl st = Some c.
Proof.
  intros st cs c H. unfold cur_ctrl. rewrite H.
  rewrite List.map_app. cbn [List.map]. rewrite List.last_last. reflexivity.
Qed.

(** A non-empty control stack is a snoc, which is the shape both accessors and
    the [end] case need. *)
Lemma ctrls_snoc : forall st,
  ctrls_list st.(code_OpIterState_ctrls) <> [] ->
  exists cs c, ctrls_list st.(code_OpIterState_ctrls) = cs ++ [c].
Proof.
  intros st H.
  destruct (List.rev (ctrls_list st.(code_OpIterState_ctrls))) as [|c rcs] eqn:Hrev.
  - exfalso. apply H.
    apply (f_equal (@List.rev _)) in Hrev.
    rewrite List.rev_involutive in Hrev. simpl in Hrev. exact Hrev.
  - exists (List.rev rcs), c.
    apply (f_equal (@List.rev _)) in Hrev.
    rewrite List.rev_involutive in Hrev. rewrite Hrev. reflexivity.
Qed.

(** Shared by both accessors: the extracted code indexes the control stack at
    [len - 1], which is the last frame. *)
(** The index [read_end]/[read_else] compute for the last frame, in plain
    [nat] terms: what [index_mut]-based rewrites need, since they update by
    position rather than by popping. *)
Lemma ctrls_last_index_len : forall st cs c n i,
  ctrls_list st.(code_OpIterState_ctrls) = cs ++ [c] ->
  code_CtrlsStack_len st.(code_OpIterState_ctrls) = Ok n ->
  usize_sub n 1%usize = Ok i ->
  Z.to_nat (to_Z i) = List.length cs.
Proof.
  intros st cs c n i Hsnoc Hlen Hsub.
  assert (Hival : to_Z i = to_Z n - 1).
  { unfold usize_sub, scalar_sub in Hsub.
    apply mk_scalar_ok_to_Z in Hsub. rewrite Hsub.
    assert (to_Z 1%usize = 1). { reflexivity. } lia. }
  rewrite Hival. rewrite (ctrls_stack_len_spec _ _ Hlen). rewrite Hsnoc.
  rewrite List.app_length. simpl. lia.
Qed.

Lemma ctrls_last_index : forall st cs c n i,
  ctrls_list st.(code_OpIterState_ctrls) = cs ++ [c] ->
  code_CtrlsStack_len st.(code_OpIterState_ctrls) = Ok n ->
  usize_sub n 1%usize = Ok i ->
  List.nth_error (ctrls_list st.(code_OpIterState_ctrls)) (Z.to_nat (to_Z i))
    = Some c.
Proof.
  intros st cs c n i Hsnoc Hlen Hsub.
  rewrite Hsnoc. rewrite (ctrls_last_index_len st cs c n i Hsnoc Hlen Hsub).
  apply nth_error_snoc.
Qed.

(** The control stack is non-empty exactly when the extracted accessors take
    their indexing branch. *)
Lemma ctrls_len_nonzero : forall st n,
  code_CtrlsStack_len st.(code_OpIterState_ctrls) = Ok n ->
  (n s= 0%usize) = false ->
  ctrls_list st.(code_OpIterState_ctrls) <> [].
Proof.
  intros st n Hlen Hz Hnil. apply scalar_eqb_false in Hz.
  rewrite (ctrls_stack_len_spec _ _ Hlen) in Hz. rewrite Hnil in Hz. simpl in Hz.
  assert (to_Z 0%usize = 0). { reflexivity. } lia.
Qed.

Lemma ctrls_len_zero : forall st n,
  code_CtrlsStack_len st.(code_OpIterState_ctrls) = Ok n ->
  (n s= 0%usize) = true ->
  ctrls_list st.(code_OpIterState_ctrls) = [].
Proof.
  intros st n Hlen Hz. apply scalar_eqb_true in Hz.
  rewrite (ctrls_stack_len_spec _ _ Hlen) in Hz.
  destruct (ctrls_list st.(code_OpIterState_ctrls)); [reflexivity|].
  simpl in Hz. assert (to_Z 0%usize = 0). { reflexivity. } lia.
Qed.

Lemma cur_base_agrees : forall st b,
  code_cur_base st = Ok b -> Z.to_nat (to_Z b) = cur_base_nat st.
Proof.
  intros st b H. unfold code_cur_base in H.
  destruct (code_CtrlsStack_len st.(code_OpIterState_ctrls)) as [n|e]
    eqn:Hlen in H; cbn [bind] in H; [|inversion H].
  destruct (n s= 0%usize) eqn:Hz.
  - injection H as <-. unfold cur_base_nat.
    rewrite (cur_ctrl_nil st (ctrls_len_zero st n Hlen Hz)). reflexivity.
  - destruct (ctrls_snoc st (ctrls_len_nonzero st n Hlen Hz)) as [cs [c Hsnoc]].
    destruct (usize_sub n 1%usize) as [i|e] eqn:Hsub in H;
      cbn [bind] in H; [|inversion H].
    destruct (code_CtrlsStack_get st.(code_OpIterState_ctrls) i)
      as [c'|e] eqn:Hget in H; cbn [bind] in H; [|inversion H].
    pose proof (ctrls_stack_get_spec _ _ _
      ltac:(rewrite (ctrls_last_index_len st cs c n i Hsnoc Hlen Hsub);
             rewrite Hsnoc, List.app_length; cbn; lia) Hget) as Hnth.
    rewrite (ctrls_last_index st cs c n i Hsnoc Hlen Hsub) in Hnth.
    injection Hnth as <-. injection H as <-.
    unfold cur_base_nat. rewrite (cur_ctrl_snoc st cs c Hsnoc). reflexivity.
Qed.

Lemma cur_unr_agrees : forall st u,
  code_cur_polymorphic st = Ok u -> u = cur_unr st.
Proof.
  intros st u H. unfold code_cur_polymorphic in H.
  destruct (code_CtrlsStack_len st.(code_OpIterState_ctrls)) as [n|e]
    eqn:Hlen in H; cbn [bind] in H; [|inversion H].
  destruct (n s= 0%usize) eqn:Hz.
  - injection H as <-. unfold cur_unr.
    rewrite (cur_ctrl_nil st (ctrls_len_zero st n Hlen Hz)). reflexivity.
  - destruct (ctrls_snoc st (ctrls_len_nonzero st n Hlen Hz)) as [cs [c Hsnoc]].
    destruct (usize_sub n 1%usize) as [i|e] eqn:Hsub in H;
      cbn [bind] in H; [|inversion H].
    destruct (code_CtrlsStack_get st.(code_OpIterState_ctrls) i)
      as [c'|e] eqn:Hget in H; cbn [bind] in H; [|inversion H].
    pose proof (ctrls_stack_get_spec _ _ _
      ltac:(rewrite (ctrls_last_index_len st cs c n i Hsnoc Hlen Hsub);
             rewrite Hsnoc, List.app_length; cbn; lia) Hget) as Hnth.
    rewrite (ctrls_last_index st cs c n i Hsnoc Hlen Hsub) in Hnth.
    injection Hnth as <-. injection H as <-.
    unfold cur_unr. rewrite (cur_ctrl_snoc st cs c Hsnoc). reflexivity.
Qed.

(** Full characterisation of a successful pop. Either it really popped, which
    the base check guarantees only happens when the current frame owns at least
    one operand, or the frame was exhausted and unreachable, in which case it
    yields [Bot] and changes nothing. *)
Lemma pop_stack_type_ok : forall st t st',
  code_pop_stack_type st = Ok (Core_result_Result_Ok t, st') ->
  st'.(code_OpIterState_ctrls) = st.(code_OpIterState_ctrls)
  /\ ((exists pre,
         vals_list st.(code_OpIterState_vals) = pre ++ [t]
         /\ vals_list st'.(code_OpIterState_vals) = pre
         /\ cur_base_nat st
            <> List.length (vals_list st.(code_OpIterState_vals)))
      \/ (t = Code_StackType_Bot
          /\ vals_list st'.(code_OpIterState_vals)
             = vals_list st.(code_OpIterState_vals)
          /\ cur_unr st = true
          /\ List.length (vals_list st.(code_OpIterState_vals))
             = cur_base_nat st)).
Proof.
  intros st t st' H. unfold code_pop_stack_type in H.
  destruct (code_ValsStack_len st.(code_OpIterState_vals)) as [n|e]
    eqn:Hlen in H; cbn [bind] in H.
  2: inversion H.
  destruct (code_cur_base st) as [base|e] eqn:Hcb in H; cbn [bind] in H.
  2: inversion H.
  pose proof (cur_base_agrees st base Hcb) as Hbase.
  destruct (n s= base) eqn:Hz.
  - (* frame exhausted *)
    destruct (code_cur_polymorphic st) as [pb|e] eqn:Hcp in H; cbn [bind] in H.
    2: inversion H.
    pose proof (cur_unr_agrees st pb Hcp) as Hunr.
    destruct pb; [|discriminate].
    injection H as <- <-. cbn [code_OpIterState_ctrls code_OpIterState_vals].
    split; [reflexivity|]. right.
    apply scalar_eqb_true in Hz. rewrite (vals_stack_len_spec _ _ Hlen) in Hz.
    repeat split.
    all: try reflexivity.
    all: try (symmetry; exact Hunr).
    all: try (rewrite <- Hbase; lia).
  - (* a real pop *)
    destruct (code_ValsStack_pop st.(code_OpIterState_vals))
      as [[o v]|e] eqn:Hpop in H; cbn [bind] in H.
    2: inversion H.
    pose proof (vals_stack_pop_spec _ o v Hpop) as Hspec.
    destruct o as [t0|]; [|discriminate].
    injection H as <- <-. cbn [code_OpIterState_ctrls code_OpIterState_vals].
    split; [reflexivity|]. left.
    apply scalar_eqb_false in Hz. rewrite (vals_stack_len_spec _ _ Hlen) in Hz.
    destruct (List.rev (vals_list st.(code_OpIterState_vals))) as [|x rest]
      eqn:Hrev.
    { (* the pop yielded Some, so the vector was not empty *)
      destruct Hspec as [Ho _]. discriminate Ho. }
    destruct Hspec as [Ho Hview]. injection Ho as <-.
    exists (List.rev rest). repeat split.
    + apply (f_equal (@List.rev _)) in Hrev.
      rewrite List.rev_involutive in Hrev. rewrite Hrev. reflexivity.
    + exact Hview.
    + (* the raw base check; turning it into "the current frame owns an operand"
         needs base <= length, which is an invariant fact, not a local one *)
      rewrite <- Hbase. pose proof (usize_nonneg base). lia.
Qed.

Lemma vt_beq_eq : forall a b, types_ValueType_t_beq a b = true -> a = b.
Proof. intros a b H. destruct a, b; try reflexivity; discriminate. Qed.

Lemma vt_beq_refl : forall a, types_ValueType_t_beq a a = true.
Proof. intros a. destruct a; reflexivity. Qed.

Lemma bt_beq_eq : forall a b, code_BlockType_t_beq a b = true -> a = b.
Proof.
  intros a b H. destruct a as [|x]; destruct b as [|y]; try discriminate;
    [reflexivity|]. cbn in H. rewrite (vt_beq_eq x y H). reflexivity.
Qed.

Lemma bt_beq_refl : forall a, code_BlockType_t_beq a a = true.
Proof. intros a. destruct a as [|x]; [reflexivity | apply vt_beq_refl]. Qed.

(** A successful typed pop is a successful raw pop whose result is either [Bot]
    or exactly the expected type. *)
Lemma pop_with_type_ok : forall st vt t st',
  code_pop_with_type st vt = Ok (Core_result_Result_Ok t, st') ->
  code_pop_stack_type st = Ok (Core_result_Result_Ok t, st')
  /\ (t = Code_StackType_Bot \/ t = Code_StackType_Val vt).
Proof.
  intros st vt t st' H. unfold code_pop_with_type in H.
  destruct (code_pop_stack_type st) as [[r0 st0]|] eqn:Hps; cbn [bind] in H;
    [|discriminate].
  destruct r0 as [t0|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct t0 as [v|].
  - rewrite vt_eq_spec in H. cbn [bind] in H.
    destruct (types_ValueType_t_beq v vt) eqn:Hbeq; [|discriminate].
    (* [destruct ... eqn:] already rewrote the goal's occurrence *)
    injection H as <- <-. split.
    + reflexivity.
    + right. rewrite (vt_beq_eq v vt Hbeq). reflexivity.
  - injection H as <- <-. split; [reflexivity | left; reflexivity].
Qed.

(** [mark_unreachable]'s loop pops down to the frame base, so its result is the
    operand array truncated there. The measure is the array's length. *)
Lemma mark_unreachable_loop_spec : forall n st base vals ctrls pos,
  (List.length (vals_list st.(code_OpIterState_vals)) <= n)%nat ->
  (Z.to_nat (to_Z base)
     <= List.length (vals_list st.(code_OpIterState_vals)))%nat ->
  code_mark_unreachable_loop st base = Ok (vals, ctrls, pos) ->
  vals_list vals
    = List.firstn (Z.to_nat (to_Z base)) (vals_list st.(code_OpIterState_vals))
  /\ ctrls = st.(code_OpIterState_ctrls).
Proof.
  induction n as [|n IH];
    intros st base vals ctrls pos Hn Hle H;
    unfold code_mark_unreachable_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H.
  all: destruct (code_ValsStack_len st.(code_OpIterState_vals))
    as [len|e] eqn:Hlen in H; cbn [bind] in H; [|inversion H].
  all: destruct (len s<= base) eqn:Hb.
  - (* already at or below the base, so the truncation is the whole array *)
    injection H as <- <- _. apply scalar_leb_true in Hb.
    rewrite (vals_stack_len_spec _ _ Hlen) in Hb.
    split; [|reflexivity].
    rewrite List.firstn_all2; [reflexivity | lia].
  - (* n = 0 forces an empty array, so this branch cannot pop *)
    exfalso. apply scalar_leb_false in Hb.
    rewrite (vals_stack_len_spec _ _ Hlen) in Hb.
    pose proof (usize_nonneg base). lia.
  - injection H as <- <- _. apply scalar_leb_true in Hb.
    rewrite (vals_stack_len_spec _ _ Hlen) in Hb.
    split; [|reflexivity].
    rewrite List.firstn_all2; [reflexivity | lia].
  - apply scalar_leb_false in Hb.
    rewrite (vals_stack_len_spec _ _ Hlen) in Hb.
    destruct (code_ValsStack_pop st.(code_OpIterState_vals))
      as [[o v]|e] eqn:Hpop in H; cbn [bind] in H; [|inversion H].
    pose proof (vals_stack_pop_spec _ o v Hpop) as Hspec.
    destruct o as [x|].
    2: { (* pop yielded nothing, so the array was empty, contradicting the base *)
         exfalso.
         destruct (List.rev (vals_list st.(code_OpIterState_vals)))
           as [|y r] eqn:Hrev; [|destruct Hspec as [Ho _]; discriminate Ho].
         apply (f_equal (@List.rev _)) in Hrev.
         rewrite List.rev_involutive in Hrev. cbn [List.rev] in Hrev.
         rewrite Hrev in Hb. cbn [List.length] in Hb.
         pose proof (usize_nonneg base). lia. }
    destruct (List.rev (vals_list st.(code_OpIterState_vals)))
      as [|y r] eqn:Hrev; [destruct Hspec as [Ho _]; discriminate Ho|].
    destruct Hspec as [Ho Hview]. injection Ho as <-.
    assert (Hsnoc : vals_list st.(code_OpIterState_vals)
                     = vals_list v ++ [x]).
    { apply (f_equal (@List.rev _)) in Hrev.
      rewrite List.rev_involutive in Hrev. rewrite Hrev, Hview. reflexivity. }
    assert (Hlen1 : (List.length (vals_list v) + 1
                     = List.length (vals_list st.(code_OpIterState_vals)))%nat).
    { rewrite Hsnoc. rewrite List.app_length. reflexivity. }
    assert (Hp1 : (List.length (vals_list v) <= n)%nat). { lia. }
    assert (Hp2 : (Z.to_nat (to_Z base) <= List.length (vals_list v))%nat).
    { pose proof (usize_nonneg base). lia. }
    destruct (IH {| code_OpIterState_vals := v;
                    code_OpIterState_ctrls := st.(code_OpIterState_ctrls);
                    code_OpIterState_pos := st.(code_OpIterState_pos)
                 |} base vals ctrls pos Hp1 Hp2 H) as [Hv Hc].
    split; [|exact Hc].
    cbn [code_OpIterState_vals] in Hv. rewrite Hv.
    (* truncating below the last element is the same before and after the pop *)
    rewrite Hsnoc. rewrite List.firstn_app.
    replace (Z.to_nat (to_Z base) - List.length (vals_list v))%nat with 0%nat
      by lia.
    cbn [List.firstn]. rewrite List.app_nil_r. reflexivity.
Qed.

(** [mark_unreachable] truncates the operand array to the current frame's base
    and sets that frame's polymorphic flag. The base itself is untouched, which
    is what lets the invariant's [bases_ok_from] survive. *)
Lemma mark_unreachable_spec : forall st st' cs c,
  ctrls_list st.(code_OpIterState_ctrls) = cs ++ [c] ->
  (Z.to_nat (to_Z c.(code_Ctrl_value_stack_base))
     <= List.length (vals_list st.(code_OpIterState_vals)))%nat ->
  code_mark_unreachable st = Ok st' ->
  vals_list st'.(code_OpIterState_vals)
    = List.firstn (Z.to_nat (to_Z c.(code_Ctrl_value_stack_base)))
                  (vals_list st.(code_OpIterState_vals))
  /\ ctrls_list st'.(code_OpIterState_ctrls)
     = cs ++ [{| code_Ctrl_kind := c.(code_Ctrl_kind);
                 code_Ctrl_block_type := c.(code_Ctrl_block_type);
                 code_Ctrl_value_stack_base :=
                   c.(code_Ctrl_value_stack_base);
                 code_Ctrl_polymorphic_base := true |}].
Proof.
  intros st st' cs c Hsnoc Hle H. unfold code_mark_unreachable in H.
  destruct (code_cur_base st) as [base|] eqn:Hcb; cbn [bind] in H;
    [|discriminate].
  (* the base the loop is given is this frame's *)
  pose proof (cur_base_agrees st base Hcb) as Hbase.
  unfold cur_base_nat in Hbase. rewrite (cur_ctrl_snoc st cs c Hsnoc) in Hbase.
  destruct (code_mark_unreachable_loop st base)
    as [[[v v1] i]|] eqn:Hloop; cbn [bind] in H; [|discriminate].
  destruct (mark_unreachable_loop_spec
              (List.length (vals_list st.(code_OpIterState_vals)))
              st base v v1 i (Nat.le_refl _)
              (ltac:(rewrite Hbase; exact Hle)) Hloop) as [Hv Hc].
  (* the control stack is non-empty, so the flag-setting branch is taken *)
  assert (Hsnoc1 : ctrls_list v1 = cs ++ [c]) by (rewrite Hc; exact Hsnoc).
  destruct (code_CtrlsStack_len v1) as [n|e] eqn:Hlen in H;
    cbn [bind] in H; [|inversion H].
  destruct (n s= 0%usize) eqn:Hnz in H.
  { exfalso. apply scalar_eqb_true in Hnz.
    rewrite (ctrls_stack_len_spec _ _ Hlen), Hsnoc1,
      List.app_length in Hnz. cbn [List.length] in Hnz.
    assert (to_Z 0%usize = 0) by reflexivity. lia. }
  cbn [bind] in H.
  destruct (usize_sub n 1%usize) as [i1|e] eqn:Hsub in H;
    cbn [bind] in H; [|inversion H].
  assert (Hidx : Z.to_nat (to_Z i1) = List.length cs).
  { assert (Hlen' : code_CtrlsStack_len st.(code_OpIterState_ctrls) = Ok n)
      by (rewrite <- Hc; exact Hlen).
    exact (ctrls_last_index_len st cs c n i1 Hsnoc Hlen' Hsub). }
  destruct (code_CtrlsStack_get v1 i1) as [top|e] eqn:Hget in H;
    cbn [bind] in H; [|inversion H].
  assert (Htop : top = c).
  { pose proof (ctrls_stack_get_spec v1 i1 top
      ltac:(rewrite Hidx, Hsnoc1, List.app_length; cbn; lia) Hget) as Hnth.
    rewrite Hsnoc1, Hidx, nth_error_snoc in Hnth. injection Hnth as <-.
    reflexivity. }
  subst top.
  destruct (code_CtrlsStack_set v1 i1 _) as [v2|e] eqn:Hset in H;
    cbn [bind] in H; [|inversion H].
  injection H as <-.
  cbn [code_OpIterState_vals code_OpIterState_ctrls].
  split; [rewrite Hv; rewrite Hbase; reflexivity|].
  rewrite (ctrls_stack_set_spec _ _ _ _
    ltac:(rewrite Hidx, Hsnoc1, List.app_length; cbn; lia) Hset).
  rewrite Hidx, Hsnoc1.
  apply list_update_snoc.
Qed.

(** [read_memarg] moves only the cursor. *)
Lemma read_memarg_state : forall st data m st',
  code_read_memarg st data = Ok (Core_result_Result_Ok m, st') ->
  st'.(code_OpIterState_vals) = st.(code_OpIterState_vals)
  /\ st'.(code_OpIterState_ctrls) = st.(code_OpIterState_ctrls).
Proof.
  intros st data m st' H. unfold code_read_memarg in H.
  destruct (reader_read_u32_leb data st.(code_OpIterState_pos)) as [r1|]
    eqn:H1; cbn [bind] in H; [|discriminate].
  destruct r1 as [[a p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_u32_leb data p1) as [r2|] eqn:H2; cbn [bind] in H;
    [|discriminate].
  destruct r2 as [[o p2]|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H. injection H as _ <-.
  cbn [code_OpIterState_vals code_OpIterState_ctrls].
  split; reflexivity.
Qed.

(** Full effect of pushing a control frame: the operand array is untouched and
    the new frame records the array's current length as its base. *)
Lemma push_ctrl_spec : forall st kind bt st',
  code_push_ctrl st kind bt = Ok st' ->
  exists base,
    to_Z base = Z.of_nat (List.length (vals_list st.(code_OpIterState_vals)))
    /\ vals_list st'.(code_OpIterState_vals)
       = vals_list st.(code_OpIterState_vals)
    /\ ctrls_list st'.(code_OpIterState_ctrls)
       = ctrls_list st.(code_OpIterState_ctrls)
         ++ [{| code_Ctrl_kind := kind;
                code_Ctrl_block_type := bt;
                code_Ctrl_value_stack_base := base;
                code_Ctrl_polymorphic_base := false |}].
Proof.
  intros st kind bt st' H. unfold code_push_ctrl in H.
  destruct (code_ValsStack_len st.(code_OpIterState_vals)) as [base|e]
    eqn:Hlen in H; cbn [bind] in H; [|inversion H].
  destruct (code_CtrlsStack_push st.(code_OpIterState_ctrls) _) as [v|e]
    eqn:Hpush in H; cbn [bind] in H; [|inversion H].
  injection H as <-. apply ctrls_stack_push_spec in Hpush.
  cbn [code_OpIterState_vals code_OpIterState_ctrls].
  exists base. repeat split; try reflexivity.
  - exact (vals_stack_len_spec _ _ Hlen).
  - exact Hpush.
Qed.

(* ================================================================== *)
(** ** How much a reader can grow the stacks                           *)
(* ================================================================== *)

(** The two stacks' combined size. This is what [MAX_FUNCTION_BYTES] bounds:
    [read_op] advances the cursor by one byte per iteration and no reader grows
    this by more than one, so with the body length capped both stacks stay far
    below [usize_max] and [Vec::push] cannot fail. Without that bound the push is
    a live panic site, not a dead one.

    The bound of one is tight, and not only for the pushing readers: on an
    exhausted unreachable frame [i32.add]'s two pops yield [Bot] without changing
    anything, so its push is a net gain of one. *)
Definition stack_size (st : code_OpIterState_t) : nat :=
  (List.length (vals_list st.(code_OpIterState_vals))
   + List.length (ctrls_list st.(code_OpIterState_ctrls)))%nat.

Lemma read_op_size : forall st data r st',
  code_read_op st data = Ok (r, st') -> stack_size st' = stack_size st.
Proof.
  intros st data r st' H. unfold code_read_op in H.
  destruct (reader_read_byte data st.(code_OpIterState_pos)) as [r0|] eqn:Hrb;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [[b p]|e].
  - rewrite branch_ok in H. cbn [bind] in H. injection H as _ <-. reflexivity.
  - rewrite branch_err in H. cbn [bind] in H.
    rewrite from_residual_err in H. cbn [bind] in H.
    injection H as _ <-. reflexivity.
Qed.

(** [start_function] leaves the cursor at zero. *)
Lemma start_function_pos : forall results st,
  code_start_function results = Ok st ->
  to_Z st.(code_OpIterState_pos) = 0.
Proof.
  intros results st H. unfold code_start_function in H.
  destruct code_ValsStack_new as [vs|e] eqn:Hvs in H;
    cbn [bind] in H; [|inversion H].
  destruct code_CtrlsStack_new as [cs|e] eqn:Hcs in H;
    cbn [bind] in H; [|inversion H].
  destruct results; cbn [bind] in H.
  all: pose proof (push_ctrl_pos _ _ _ st H) as Hp;
       unfold pos_of in Hp; cbn [code_OpIterState_pos] in Hp;
       rewrite Hp; reflexivity.
Qed.

(** [read_op] touches only the cursor, so the invariant
    transports through it. *)
Lemma read_op_state : forall st data r st',
  code_read_op st data = Ok (r, st') ->
  vals_list st'.(code_OpIterState_vals) = vals_list st.(code_OpIterState_vals)
  /\ ctrls_list st'.(code_OpIterState_ctrls)
     = ctrls_list st.(code_OpIterState_ctrls).
Proof.
  intros st data r st' H. unfold code_read_op in H.
  destruct (reader_read_byte data st.(code_OpIterState_pos)) as [r0|] eqn:Hrb;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [[b p]|e].
  - rewrite branch_ok in H. cbn [bind] in H. injection H as _ <-.
    split; reflexivity.
  - rewrite branch_err in H. cbn [bind] in H.
    rewrite from_residual_err in H. cbn [bind] in H.
    injection H as _ <-. split; reflexivity.
Qed.

Lemma push_val_size : forall st t st',
  code_push_val st t = Ok st' -> stack_size st' = (stack_size st + 1)%nat.
Proof.
  intros st t st' H. destruct (push_val_spec st t st' H) as [Hv [Hc _]].
  unfold stack_size. rewrite Hv. rewrite Hc.
  rewrite List.app_length. cbn [List.length]. lia.
Qed.

Lemma push_ctrl_size : forall st kind bt st',
  code_push_ctrl st kind bt = Ok st'
  -> stack_size st' = (stack_size st + 1)%nat.
Proof.
  intros st kind bt st' H.
  destruct (push_ctrl_spec st kind bt st' H) as [base [_ [Hv Hc]]].
  unfold stack_size. rewrite Hv. rewrite Hc.
  rewrite List.app_length. cbn [List.length]. lia.
Qed.

Lemma pop_stack_type_size : forall st r st',
  code_pop_stack_type st = Ok (r, st') ->
  (stack_size st' <= stack_size st)%nat.
Proof.
  intros st r st' H. unfold code_pop_stack_type in H.
  destruct (code_ValsStack_len st.(code_OpIterState_vals)) as [n|e]
    eqn:Hlen in H; cbn [bind] in H; [|inversion H].
  destruct (code_cur_base st) as [base|e] eqn:Hcb in H;
    cbn [bind] in H; [|inversion H].
  destruct (n s= base) eqn:Hb.
  - destruct (code_cur_polymorphic st) as [pb|e] eqn:Hcp in H;
      cbn [bind] in H; [|inversion H].
    destruct pb; injection H as _ <-; apply Nat.le_refl.
  - destruct (code_ValsStack_pop st.(code_OpIterState_vals))
      as [[o v]|e] eqn:Hpop in H; cbn [bind] in H; [|inversion H].
    pose proof (vals_stack_pop_size _ o v Hpop) as Hsize.
    destruct o; injection H as _ <-; unfold stack_size;
      cbn [code_OpIterState_vals code_OpIterState_ctrls]; lia.
Qed.

Lemma pop_with_type_size : forall st vt r st',
  code_pop_with_type st vt = Ok (r, st') ->
  (stack_size st' <= stack_size st)%nat.
Proof.
  intros st vt r st' H. unfold code_pop_with_type in H.
  destruct (code_pop_stack_type st) as [[r0 st0]|] eqn:Hps; cbn [bind] in H;
    [|discriminate].
  pose proof (pop_stack_type_size st r0 st0 Hps) as Hs0.
  destruct r0 as [t|e].
  - rewrite branch_ok in H. cbn [bind] in H.
    destruct t as [v|].
    + destruct (types_ValueType_Insts_CoreCmpPartialEqValueType_eq v vt) as [b|]
        eqn:Heq; cbn [bind] in H; [|discriminate].
      destruct b; injection H as _ <-; exact Hs0.
    + injection H as _ <-. exact Hs0.
  - rewrite branch_err in H. cbn [bind] in H.
    rewrite from_residual_err in H. cbn [bind] in H.
    injection H as _ <-. exact Hs0.
Qed.

(** The two loops. [pop_types] never grows the stacks; [push_types] grows them by
    at most one per expected type, and a Wasm 1.0 result list has at most one. *)
Lemma pop_types_loop_size : forall n st types i r st',
  to_Z i <= Z.of_nat n ->
  code_pop_types_loop st types i = Ok (r, st') ->
  (stack_size st' <= stack_size st)%nat.
Proof.
  induction n as [|n IH]; intros st types i r st' Hn H;
    unfold code_pop_types_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H;
    destruct (i s= 0%usize) eqn:Hz;
    [injection H as _ <-; apply Nat.le_refl | | |].
  - exfalso. apply scalar_eqb_false in Hz.
    assert (to_Z 0%usize = 0) by reflexivity.
    pose proof (usize_nonneg i). cbn in Hn. lia.
  - injection H as _ <-. apply Nat.le_refl.
  - apply scalar_eqb_false in Hz.
    assert (H0 : to_Z 0%usize = 0) by reflexivity.
    destruct (usize_sub_1_ok i) as [i2 [Hsub Hi2]];
      [pose proof (usize_nonneg i); lia|].
    rewrite Hsub in H. cbn [bind] in H.
    destruct (slice_index_usize types i2) as [vt|] eqn:Hidx; cbn [bind] in H;
      [|discriminate].
    destruct (code_pop_with_type st vt) as [[r0 st0]|] eqn:Hpwt;
      cbn [bind] in H; [|discriminate].
    pose proof (pop_with_type_size st vt r0 st0 Hpwt) as Hs0.
    destruct r0 as [t|e].
    + rewrite branch_ok in H. cbn [bind] in H.
      pose proof (IH st0 types i2 r st' (ltac:(lia)) H) as Hs1. lia.
    + rewrite branch_err in H. cbn [bind] in H.
      rewrite from_residual_err in H. cbn [bind] in H.
      injection H as _ <-. exact Hs0.
Qed.

Lemma pop_types_size : forall st types r st',
  code_pop_types st types = Ok (r, st') ->
  (stack_size st' <= stack_size st)%nat.
Proof.
  intros st types r st' H. unfold code_pop_types in H.
  eapply pop_types_loop_size with (n := Z.to_nat (to_Z (slice_len types)));
    [|exact H].
  rewrite Z2Nat.id by apply usize_nonneg. lia.
Qed.

Lemma push_types_loop_size : forall n st types i st',
  to_Z (slice_len types) - to_Z i <= Z.of_nat n ->
  code_push_types_loop st types i = Ok st' ->
  (stack_size st' <= stack_size st + n)%nat.
Proof.
  induction n as [|n IH]; intros st types i st' Hn H;
    unfold code_push_types_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H;
    destruct (i s>= slice_len types) eqn:Hge;
    [injection H as <-; lia | | |].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hn. lia.
  - injection H as <-. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (slice_index_usize types i) as [vt|] eqn:Hidx; cbn [bind] in H;
      [|discriminate].
    destruct (code_push_val st (Code_StackType_Val vt)) as [st0|] eqn:Hpv;
      cbn [bind] in H; [|discriminate].
    pose proof (push_val_size st _ st0 Hpv) as Hs0.
    destruct (usize_add_1_ok i) as [i3 [Hadd Hi3]].
    { pose proof (usize_le_max (slice_len types)). lia. }
    rewrite Hadd in H. cbn [bind] in H.
    pose proof (IH st0 types i3 st' (ltac:(lia)) H) as Hs1. lia.
Qed.

Lemma push_types_size : forall st types st',
  code_push_types st types = Ok st' ->
  (stack_size st'
     <= stack_size st + List.length (vec_list types))%nat.
Proof.
  intros st types st' H. unfold code_push_types in H.
  eapply push_types_loop_size
    with (n := List.length (vec_list types)); [|exact H].
  rewrite slice_len_spec.
  assert (to_Z 0%usize = 0) by reflexivity. lia.
Qed.

(** [mark_unreachable] truncates the operand stack and rewrites one control frame
    in place, so it can only shrink. *)
Lemma mark_unreachable_loop_size : forall n st base vals ctrls pos,
  (List.length (vals_list st.(code_OpIterState_vals)) <= n)%nat ->
  code_mark_unreachable_loop st base = Ok (vals, ctrls, pos) ->
  (List.length (vals_list vals)
     <= List.length (vals_list st.(code_OpIterState_vals)))%nat
  /\ ctrls_list ctrls = ctrls_list st.(code_OpIterState_ctrls).
Proof.
  induction n as [|n IH]; intros st base vals ctrls pos Hlen H;
    unfold code_mark_unreachable_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H.
  all: destruct (code_ValsStack_len st.(code_OpIterState_vals))
    as [len|e] eqn:Hstacklen in H; cbn [bind] in H; [|inversion H].
  all: destruct (len s<= base) eqn:Hle.
  - injection H as <- <- _. split; [apply Nat.le_refl | reflexivity].
  - exfalso. apply scalar_leb_false in Hle.
    assert (Hnil : vals_list st.(code_OpIterState_vals) = []).
    { destruct (vals_list st.(code_OpIterState_vals)); [reflexivity|].
      cbn [List.length] in Hlen. lia. }
    rewrite (vals_stack_len_spec _ _ Hstacklen) in Hle.
    rewrite Hnil in Hle. cbn [List.length] in Hle.
    pose proof (usize_nonneg base). lia.
  - injection H as <- <- _. split; [apply Nat.le_refl | reflexivity].
  - destruct (code_ValsStack_pop st.(code_OpIterState_vals))
      as [[o v]|e] eqn:Hpop in H; cbn [bind] in H; [|inversion H].
    pose proof (vals_stack_pop_size _ o v Hpop) as Hsh.
    apply scalar_leb_false in Hle.
    assert (Hne : vals_list st.(code_OpIterState_vals) <> []).
    { intros Hnil. rewrite (vals_stack_len_spec _ _ Hstacklen) in Hle.
      rewrite Hnil in Hle.
      cbn [List.length] in Hle. pose proof (usize_nonneg base). lia. }
    pose proof (vals_stack_pop_len _ o v Hpop Hne) as Hlt.
    destruct (IH {| code_OpIterState_vals := v;
                    code_OpIterState_ctrls := st.(code_OpIterState_ctrls);
                    code_OpIterState_pos := st.(code_OpIterState_pos)
                 |} base vals ctrls pos
                 (ltac:(cbn [code_OpIterState_vals]; lia)) H) as [Hv Hc].
    cbn [code_OpIterState_vals code_OpIterState_ctrls] in Hv, Hc.
    split; [lia | exact Hc].
Qed.

Lemma mark_unreachable_size : forall st st',
  code_mark_unreachable st = Ok st' ->
  (stack_size st' <= stack_size st)%nat.
Proof.
  intros st st' H. unfold code_mark_unreachable in H.
  destruct (code_cur_base st) as [base|e] eqn:Hcb in H; cbn [bind] in H;
    [|inversion H].
  destruct (code_mark_unreachable_loop st base)
    as [[[v v1] i]|e] eqn:Hloop in H; cbn [bind] in H; [|inversion H].
  destruct (mark_unreachable_loop_size
              (List.length (vals_list st.(code_OpIterState_vals)))
              st base v v1 i (Nat.le_refl _) Hloop) as [Hv Hc].
  destruct (code_CtrlsStack_len v1) as [n|e] eqn:Hlen in H;
    cbn [bind] in H; [|inversion H].
  destruct (n s= 0%usize) eqn:Hz in H.
  { injection H as <-. unfold stack_size.
    cbn [code_OpIterState_vals code_OpIterState_ctrls]. rewrite Hc. lia. }
  destruct (usize_sub n 1%usize) as [i1|e] eqn:Hsub in H;
    cbn [bind] in H; [|inversion H].
  pose proof Hz as Hnz. apply scalar_eqb_false in Hnz.
  assert (Hnpos : 1 <= to_Z n).
  { pose proof (usize_nonneg n).
    assert (to_Z 0%usize = 0) by reflexivity. lia. }
  assert (Hidx : Z.to_nat (to_Z i1) =
    (List.length (ctrls_list v1) - 1)%nat).
  { unfold usize_sub, scalar_sub in Hsub. apply mk_scalar_ok_to_Z in Hsub.
    assert (Hone : to_Z 1%usize = 1) by reflexivity.
    rewrite Hsub, Hone. rewrite Z2Nat.inj_sub by lia.
    rewrite (ctrls_stack_len_spec _ _ Hlen), Nat2Z.id. cbn. reflexivity. }
  assert (Hbound : (Z.to_nat (to_Z i1) < List.length (ctrls_list v1))%nat).
  { rewrite (ctrls_stack_len_spec _ _ Hlen) in Hnz.
    assert (Hlenpos : (0 < List.length (ctrls_list v1))%nat).
    { destruct (List.length (ctrls_list v1)); [cbn in Hnz; contradiction|lia]. }
    rewrite Hidx. lia. }
  destruct (code_CtrlsStack_get v1 i1) as [c|e] eqn:Hget in H;
    cbn [bind] in H; [|inversion H].
  destruct (code_CtrlsStack_set v1 i1 _) as [v2|e] eqn:Hset in H;
    cbn [bind] in H; [|inversion H].
  injection H as <-. unfold stack_size.
  cbn [code_OpIterState_vals code_OpIterState_ctrls].
  rewrite (ctrls_stack_set_spec _ _ _ _ Hbound Hset).
  rewrite list_update_length, Hc. lia.
Qed.

(** Each reader, with the bound the loop invariant needs. Stated uniformly at
    [+1] even where the reader can only shrink, since one shape is what the loop
    consumes and the extra slack costs nothing. *)

Lemma read_unreachable_size : forall st r st',
  code_read_unreachable st = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st r st' H. unfold code_read_unreachable in H.
  destruct (code_mark_unreachable st) as [st1|] eqn:Hmu; cbn [bind] in H;
    [|discriminate].
  injection H as _ <-.
  pose proof (mark_unreachable_size st st1 Hmu) as Hs1. lia.
Qed.

Lemma pop_block_results_size : forall st bt r st',
  code_pop_block_results st bt = Ok (r, st') ->
  (stack_size st' <= stack_size st)%nat.
Proof.
  intros st bt r st' H. destruct bt as [|vt].
  - cbn [code_pop_block_results] in H. injection H as _ <-. apply Nat.le_refl.
  - unfold code_pop_block_results in H.
    destruct (code_pop_with_type st vt) as [[r0 st0]|e] eqn:Hpop in H;
      cbn [bind] in H; [|inversion H].
    pose proof (pop_with_type_size st vt r0 st0 Hpop) as Hsize.
    destruct r0 as [t|e].
    + rewrite branch_ok in H. cbn [bind] in H. injection H as _ <-. exact Hsize.
    + rewrite branch_err in H. cbn [bind] in H.
      rewrite from_residual_err in H. cbn [bind] in H.
      injection H as _ <-. exact Hsize.
Qed.

Lemma pop_block_results_ctrls : forall st bt r st',
  code_pop_block_results st bt = Ok (r, st') ->
  ctrls_list st'.(code_OpIterState_ctrls) =
    ctrls_list st.(code_OpIterState_ctrls).
Proof.
  intros st bt r st' H. destruct bt as [|vt].
  - cbn [code_pop_block_results] in H. injection H as _ <-. reflexivity.
  - unfold code_pop_block_results in H.
    destruct (code_pop_with_type st vt) as [[r0 st0]|e] eqn:Hpop in H;
      cbn [bind] in H; [|inversion H].
    pose proof (pop_with_type_ctrls st vt r0 st0 Hpop) as Hc.
    destruct r0 as [t|e].
    + rewrite branch_ok in H. cbn [bind] in H. injection H as _ <-. exact Hc.
    + rewrite branch_err in H. cbn [bind] in H.
      rewrite from_residual_err in H. cbn [bind] in H.
      injection H as _ <-. exact Hc.
Qed.

Lemma push_block_results_size : forall st bt st',
  code_push_block_results st bt = Ok st' ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st bt st' H. destruct bt as [|vt].
  - cbn [code_push_block_results] in H. injection H as <-. lia.
  - cbn [code_push_block_results] in H.
    rewrite (push_val_size st (Code_StackType_Val vt) st' H). lia.
Qed.

Lemma read_return_size : forall st ctx r st',
  code_read_return st ctx = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st ctx r st' H. unfold code_read_return in H.
  destruct ctx.(code_Context_results) as [vt|]; cbn [bind] in H.
  all: destruct (code_pop_block_results st _) as [[r1 st1]|e]
    eqn:Hpt in H; cbn [bind] in H; [|inversion H].
  all: pose proof (pop_block_results_size st _ r1 st1 Hpt) as Hs1.
  all:
  destruct r1 as [u1|e1].
  all: try (rewrite branch_err in H; cbn [bind] in H;
       rewrite from_residual_err in H; cbn [bind] in H;
       injection H as _ <-; lia).
  all: destruct u1; rewrite branch_ok in H; cbn [bind] in H.
  all:
  destruct (code_mark_unreachable st1) as [st2|] eqn:Hmu; cbn [bind] in H;
    [|discriminate].
  all: injection H as _ <-;
       pose proof (mark_unreachable_size st1 st2 Hmu) as Hs2; lia.
Qed.

Lemma read_drop_size : forall st r st',
  code_read_drop st = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st r st' H. unfold code_read_drop in H.
  pose proof (pop_stack_type_size st r st' H) as Hs1. lia.
Qed.

(** Three pops and one push, so the bound of one is not even tight here. *)
Lemma read_select_size : forall st r st',
  code_read_select st = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st r st' H. unfold code_read_select in H.
  destruct (code_pop_with_type st Types_ValueType_I32) as [[r1 st1]|] eqn:Hp;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_size st _ r1 st1 Hp) as Hs1.
  destruct r1 as [t1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_pop_stack_type st1) as [[r2 st2]|] eqn:Hq2;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_stack_type_size st1 r2 st2 Hq2) as Hs2.
  destruct r2 as [t2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_pop_stack_type st2) as [[r3 st3]|] eqn:Hq3;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_stack_type_size st2 r3 st3 Hq3) as Hs3.
  destruct r3 as [t3|e3].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_join_stack_type t2 t3) as [rj|] eqn:Hj;
    cbn [bind] in H; [|discriminate].
  destruct rj as [t|ej].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_push_val st3 t) as [st4|] eqn:Hpv; cbn [bind] in H;
    [|discriminate].
  injection H as _ <-.
  rewrite (push_val_size st3 t st4 Hpv). lia.
Qed.

Lemma read_binary_size : forall st ty res r st',
  code_read_binary st ty res = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st ty res r st' H. unfold code_read_binary in H.
  destruct (code_pop_with_type st ty) as [[r1 st1]|] eqn:Hpop1;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_size st ty r1 st1 Hpop1) as Hs1.
  destruct r1 as [t1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_pop_with_type st1 ty) as [[r2 st2]|] eqn:Hpop2;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_size st1 ty r2 st2 Hpop2) as Hs2.
  destruct r2 as [t2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_push_val st2 (Code_StackType_Val res)) as [st3|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  rewrite (push_val_size st2 _ st3 Hpv). lia.
Qed.

Lemma read_conversion_size : forall st from to r st',
  code_read_conversion st from to = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st from to r st' H. unfold code_read_conversion in H.
  destruct (code_pop_with_type st from) as [[r1 st1]|] eqn:Hpop1;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_size st from r1 st1 Hpop1) as Hs1.
  destruct r1 as [t1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_push_val st1 (Code_StackType_Val to)) as [st2|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  rewrite (push_val_size st1 _ st2 Hpv). lia.
Qed.

Lemma read_i32_const_size : forall st data r st',
  code_read_i32_const st data = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st data r st' H. unfold code_read_i32_const in H.
  destruct (reader_read_s32_leb data st.(code_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[v0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_push_val
              {| code_OpIterState_vals := st.(code_OpIterState_vals);
                 code_OpIterState_ctrls := st.(code_OpIterState_ctrls);
                 code_OpIterState_pos := p1
              |} (Code_StackType_Val Types_ValueType_I32)) as [st1|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  rewrite (push_val_size _ _ st1 Hpv). unfold stack_size.
  cbn [code_OpIterState_vals code_OpIterState_ctrls]. lia.
Qed.

Lemma read_f32_const_size : forall st data r st',
  code_read_f32_const st data = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st data r st' H. unfold code_read_f32_const in H.
  destruct (reader_read_f32_bits data st.(code_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[v0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_push_val
              {| code_OpIterState_vals := st.(code_OpIterState_vals);
                 code_OpIterState_ctrls := st.(code_OpIterState_ctrls);
                 code_OpIterState_pos := p1
              |} (Code_StackType_Val Types_ValueType_F32)) as [st1|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  rewrite (push_val_size _ _ st1 Hpv). unfold stack_size.
  cbn [code_OpIterState_vals code_OpIterState_ctrls]. lia.
Qed.

Lemma read_f64_const_size : forall st data r st',
  code_read_f64_const st data = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st data r st' H. unfold code_read_f64_const in H.
  destruct (reader_read_f64_bits data st.(code_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[v0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_push_val
              {| code_OpIterState_vals := st.(code_OpIterState_vals);
                 code_OpIterState_ctrls := st.(code_OpIterState_ctrls);
                 code_OpIterState_pos := p1
              |} (Code_StackType_Val Types_ValueType_F64)) as [st1|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  rewrite (push_val_size _ _ st1 Hpv). unfold stack_size.
  cbn [code_OpIterState_vals code_OpIterState_ctrls]. lia.
Qed.

Lemma read_i64_const_size : forall st data r st',
  code_read_i64_const st data = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st data r st' H. unfold code_read_i64_const in H.
  destruct (reader_read_s64_leb data st.(code_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[v0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_push_val
              {| code_OpIterState_vals := st.(code_OpIterState_vals);
                 code_OpIterState_ctrls := st.(code_OpIterState_ctrls);
                 code_OpIterState_pos := p1
              |} (Code_StackType_Val Types_ValueType_I64)) as [st1|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  rewrite (push_val_size _ _ st1 Hpv). unfold stack_size.
  cbn [code_OpIterState_vals code_OpIterState_ctrls]. lia.
Qed.

Lemma read_block_size : forall st data r st',
  code_read_block st data = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st data r st' H. unfold code_read_block in H.
  destruct (code_read_block_type data st.(code_OpIterState_pos)) as [r1|]
    eqn:Hbt; cbn [bind] in H; [|discriminate].
  destruct r1 as [[bt0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_push_ctrl
              {| code_OpIterState_vals := st.(code_OpIterState_vals);
                 code_OpIterState_ctrls := st.(code_OpIterState_ctrls);
                 code_OpIterState_pos := p1
              |} Code_LabelKind_Block bt0) as [st1|] eqn:Hpc;
    cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  rewrite (push_ctrl_size _ _ _ st1 Hpc). unfold stack_size.
  cbn [code_OpIterState_vals code_OpIterState_ctrls]. lia.
Qed.

Lemma read_loop_size : forall st data r st',
  code_read_loop st data = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st data r st' H. unfold code_read_loop in H.
  destruct (code_read_block_type data st.(code_OpIterState_pos)) as [r1|]
    eqn:Hbt; cbn [bind] in H; [|discriminate].
  destruct r1 as [[bt0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_push_ctrl
              {| code_OpIterState_vals := st.(code_OpIterState_vals);
                 code_OpIterState_ctrls := st.(code_OpIterState_ctrls);
                 code_OpIterState_pos := p1
              |} Code_LabelKind_Loop bt0) as [st1|] eqn:Hpc;
    cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  rewrite (push_ctrl_size _ _ _ st1 Hpc). unfold stack_size.
  cbn [code_OpIterState_vals code_OpIterState_ctrls]. lia.
Qed.

(** [if] pops the condition and pushes a [Then] frame, so it is [read_block]
    plus one pop; the pop can only shrink, so the bound is still one. *)
Lemma read_if_size : forall st data r st',
  code_read_if st data = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st data r st' H. unfold code_read_if in H.
  destruct (code_read_block_type data st.(code_OpIterState_pos)) as [r1|]
    eqn:Hbt; cbn [bind] in H; [|discriminate].
  destruct r1 as [[bt0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_pop_with_type
              {| code_OpIterState_vals := st.(code_OpIterState_vals);
                 code_OpIterState_ctrls := st.(code_OpIterState_ctrls);
                 code_OpIterState_pos := p1
              |} Types_ValueType_I32) as [[r2 st1]|] eqn:Hpw;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_size _ _ r2 st1 Hpw) as Hs1.
  unfold stack_size in Hs1. cbn [code_OpIterState_vals
    code_OpIterState_ctrls] in Hs1.
  fold (stack_size st1) in Hs1. fold (stack_size st) in Hs1.
  destruct r2 as [t2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_push_ctrl st1 Code_LabelKind_Then bt0) as [st2|] eqn:Hpc;
    cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  rewrite (push_ctrl_size _ _ _ st2 Hpc). lia.
Qed.

(** Resolving a label moves only the cursor: the depth and the frame lookup
    leave both stacks alone, in every branch. *)
Lemma read_label_fields : forall st data r st',
  code_read_label st data = Ok (r, st') ->
  vals_list st'.(code_OpIterState_vals)
    = vals_list st.(code_OpIterState_vals)
  /\ ctrls_list st'.(code_OpIterState_ctrls)
     = ctrls_list st.(code_OpIterState_ctrls).
Proof.
  intros st data r st' H. unfold code_read_label in H.
  destruct (reader_read_u32_leb data st.(code_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[d0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. split; reflexivity. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_CtrlsStack_len st.(code_OpIterState_ctrls)) as [n|e]
    eqn:Hlen in H; cbn [bind] in H; [|inversion H].
  destruct (scalar_cast U32 Usize d0) as [d|e] eqn:Hcast in H;
    cbn [bind] in H; [|inversion H].
  destruct (d s>= n) eqn:Hge.
  { injection H as _ <-.
    cbn [code_OpIterState_vals code_OpIterState_ctrls].
    split; reflexivity. }
  destruct (usize_sub n 1%usize) as [i|e] eqn:Hsub1 in H;
    cbn [bind] in H; [|inversion H].
  destruct (usize_sub i d) as [i1|e] eqn:Hsub2 in H;
    cbn [bind] in H; [|inversion H].
  destruct (code_CtrlsStack_get st.(code_OpIterState_ctrls) i1)
    as [target|e] eqn:Hidx in H; cbn [bind] in H; [|inversion H].
  injection H as _ <-.
  cbn [code_OpIterState_vals code_OpIterState_ctrls].
  split; reflexivity.
Qed.

Lemma read_label_size : forall st data r st',
  code_read_label st data = Ok (r, st') -> stack_size st' = stack_size st.
Proof.
  intros st data r st' H.
  destruct (read_label_fields st data r st' H) as [Hv Hc].
  unfold stack_size. rewrite Hv. rewrite Hc. reflexivity.
Qed.

(** Pure counterpart of [code_branch_target_bt], which is monadic only because
    Aeneas makes every function one. What a branch to a frame supplies, as a
    block type: [br_table] folds one of these per label. *)
Definition branch_target_bt_of (c : code_Ctrl_t) : code_BlockType_t :=
  match c.(code_Ctrl_kind) with
  | Code_LabelKind_Loop => Code_BlockType_Empty
  | _ => c.(code_Ctrl_block_type)
  end.

Lemma branch_target_bt_spec : forall c,
  code_branch_target_bt c = Ok (branch_target_bt_of c).
Proof.
  intros c. unfold code_branch_target_bt, branch_target_bt_of.
  destruct (c.(code_Ctrl_kind)); reflexivity.
Qed.

(** Depth [d] names a control frame, and a branch to it supplies [bt].

    Stated over the control stack alone, with no mention of WasmCert, so that
    [br_table]'s decode lemma can establish one of these per label without
    reaching into the simulation invariant; [ctx_at_label_lookup] turns it into
    the checker's [tc_labels] lookup on the other side. That split is what lets
    the two halves of [br_table]'s correspondence agree on a label list the
    reader does not return. *)
Definition depth_target (st : code_OpIterState_t) (d : Z)
                        (bt : code_BlockType_t) : Prop :=
  exists c,
    (Z.to_nat d < List.length (ctrls_list st.(code_OpIterState_ctrls)))%nat
    /\ List.nth_error (ctrls_list st.(code_OpIterState_ctrls))
         (List.length (ctrls_list st.(code_OpIterState_ctrls)) - 1 - Z.to_nat d)
       = Some c
    /\ branch_target_bt_of c = bt.

(** Both stacks are untouched by everything [br_table]'s loop does, so a depth
    resolved at one point of the run is resolved at every other. *)
Lemma depth_target_ctrls : forall st st' d bt,
  ctrls_list st'.(code_OpIterState_ctrls)
    = ctrls_list st.(code_OpIterState_ctrls) ->
  depth_target st d bt -> depth_target st' d bt.
Proof. intros st st' d bt Hc H. unfold depth_target in *. rewrite Hc. exact H. Qed.

Lemma read_br_size : forall st data r st',
  code_read_br st data = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st data r st' H. unfold code_read_br in H.
  destruct (code_read_label st data) as [[r0 st1]|]
    eqn:Htb; cbn [bind] in H; [|discriminate].
  pose proof (read_label_size st data r0 st1 Htb) as Hs1.
  destruct r0 as [[depth target]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_branch_target_bt target) as [bt|] eqn:Hbtt;
    cbn [bind] in H; [|discriminate].
  destruct (code_pop_block_results st1 bt) as [[r2 st2]|]
    eqn:Hpt; cbn [bind] in H; [|discriminate].
  pose proof (pop_block_results_size _ _ r2 st2 Hpt) as Hs2.
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_mark_unreachable st2) as [st3|] eqn:Hmu; cbn [bind] in H;
    [|discriminate].
  injection H as _ <-.
  pose proof (mark_unreachable_size st2 st3 Hmu) as Hs3. lia.
Qed.

(** The table's loop only reads labels, so neither stack moves. Bounded by the
    count it read: each round increments [i] and stops at [count]. *)
Lemma read_table_labels_loop_fields : forall n V (inst : code_OpVisitor_t V)
                                             v st data count expect i r st' v',
  to_Z i + Z.of_nat n = to_Z count ->
  code_read_table_labels_loop inst st data count v expect i
    = Ok (r, st', v') ->
  vals_list st'.(code_OpIterState_vals)
    = vals_list st.(code_OpIterState_vals)
  /\ ctrls_list st'.(code_OpIterState_ctrls)
     = ctrls_list st.(code_OpIterState_ctrls).
Proof.
  induction n as [|n IH];
    intros V inst v st data count expect i r st' v' Hn H;
    unfold code_read_table_labels_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (i s= count) eqn:Heq;
    [inversion H; subst; split; reflexivity | |
     inversion H; subst; split; reflexivity | ].
  - exfalso. apply scalar_eqb_false in Heq. cbn in Hn. lia.
  - destruct (code_read_label st data) as [[r0 st1]|] eqn:Hrl;
      cbn [bind] in H; [|discriminate].
    destruct (read_label_fields st data r0 st1 Hrl) as [Hv1 Hc1].
    destruct r0 as [[d0 target]|e].
    2: { rewrite branch_err in H. cbn [bind] in H.
         rewrite from_residual_err in H. cbn [bind] in H.
         inversion H; subst. split; [exact Hv1 | exact Hc1]. }
    rewrite branch_ok in H. cbn [bind] in H.
    (* the per-label hook: it cannot touch either stack *)
    destruct (inst.(code_OpVisitor_t_on_br_table_label) v st1 d0)
      as [[rh vh]|] eqn:Hhk; cbn [bind] in H; [|discriminate].
    destruct rh as [uh|eh]; cbn [code_visit bind] in H.
    2: { rewrite branch_err in H. cbn [bind] in H.
         rewrite from_residual_err in H. cbn [bind] in H.
         inversion H; subst. split; [exact Hv1 | exact Hc1]. }
    rewrite branch_ok in H. cbn [bind] in H.
    rewrite branch_target_bt_spec in H. cbn [bind] in H.
    destruct (code_merge_target expect (branch_target_bt_of target)) as [r1|]
      eqn:Hmt; cbn [bind] in H; [|discriminate].
    destruct r1 as [bt|e1].
    2: { rewrite branch_err in H. cbn [bind] in H.
         rewrite from_residual_err in H. cbn [bind] in H.
         inversion H; subst. split; [exact Hv1 | exact Hc1]. }
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (u32_add i 1%u32) as [i1|] eqn:Hadd; cbn [bind] in H;
      [|discriminate].
    assert (Hi1 : to_Z i1 = to_Z i + 1).
    { unfold u32_add, scalar_add in Hadd. apply mk_scalar_ok_to_Z in Hadd.
      assert (H1 : to_Z 1%u32 = 1) by reflexivity. rewrite Hadd. lia. }
    destruct (IH V inst vh st1 data count (Some bt) i1 r st' v'
                (ltac:(cbn in Hn; lia)) H) as [Hv Hc].
    split; [rewrite Hv; exact Hv1 | rewrite Hc; exact Hc1].
Qed.

Lemma read_table_labels_fields : forall V (inst : code_OpVisitor_t V) v
                                        st data count r st' v',
  code_read_table_labels inst st data count v = Ok (r, st', v') ->
  vals_list st'.(code_OpIterState_vals)
    = vals_list st.(code_OpIterState_vals)
  /\ ctrls_list st'.(code_OpIterState_ctrls)
     = ctrls_list st.(code_OpIterState_ctrls).
Proof.
  intros V inst v st data count r st' v' H.
  unfold code_read_table_labels in H.
  apply (read_table_labels_loop_fields (Z.to_nat (to_Z count)) V inst v st data
           count None 0%u32 r st' v'); [|exact H].
  assert (H0 : to_Z 0%u32 = 0) by reflexivity. rewrite H0.
  rewrite Z2Nat.id by apply u32_nonneg. reflexivity.
Qed.

Lemma read_table_labels_size : forall V (inst : code_OpVisitor_t V) v
                                      st data count r st' v',
  code_read_table_labels inst st data count v = Ok (r, st', v') ->
  stack_size st' = stack_size st.
Proof.
  intros V inst v st data count r st' v' H.
  destruct (read_table_labels_fields V inst v st data count r st' v' H)
    as [Hv Hc].
  unfold stack_size. rewrite Hv. rewrite Hc. reflexivity.
Qed.

(** [br_table] pops and then truncates, so like [br] it never grows a stack. *)
Lemma read_br_table_size : forall V (inst : code_OpVisitor_t V) v st data r st'
                                  v',
  code_read_br_table inst st data v = Ok (r, st', v') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros V inst v st data r st' v' H. unfold code_read_br_table in H.
  destruct (reader_read_u32_leb data st.(code_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[count p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       inversion H; subst. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_read_table_labels inst
              {| code_OpIterState_vals := st.(code_OpIterState_vals);
                 code_OpIterState_ctrls := st.(code_OpIterState_ctrls);
                 code_OpIterState_pos := p1
              |} data count v) as [[[r2 st1] v1]|] eqn:Htl;
    cbn [bind] in H; [|discriminate].
  assert (Hs1 : stack_size st1 = stack_size st)
    by (rewrite (read_table_labels_size V inst v _ data count r2 st1 v1 Htl);
        reflexivity).
  destruct r2 as [expect|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       inversion H; subst. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_read_label st1 data) as [[r3 st2]|] eqn:Hrl;
    cbn [bind] in H; [|discriminate].
  pose proof (read_label_size st1 data r3 st2 Hrl) as Hs2.
  destruct r3 as [[d0 target]|e3].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       inversion H; subst. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  rewrite branch_target_bt_spec in H. cbn [bind] in H.
  destruct (code_merge_target expect (branch_target_bt_of target)) as [r4|]
    eqn:Hmt; cbn [bind] in H; [|discriminate].
  destruct r4 as [common|e4].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       inversion H; subst. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_pop_with_type st2 Types_ValueType_I32) as [[r5 st3]|] eqn:Hp5;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_size st2 _ r5 st3 Hp5) as Hs3.
  destruct r5 as [t5|e5].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       inversion H; subst. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_pop_block_results st3 common) as [[r6 st4]|]
    eqn:Hpt; cbn [bind] in H; [|discriminate].
  pose proof (pop_block_results_size _ _ r6 st4 Hpt) as Hs4.
  destruct r6 as [u6|e6].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       inversion H; subst. lia. }
  destruct u6. rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_mark_unreachable st4) as [st5|] eqn:Hmu; cbn [bind] in H;
    [|discriminate].
  inversion H; subst.
  pose proof (mark_unreachable_size st4 _ Hmu) as Hs5. lia.
Qed.

(** [read_memarg] rebuilds the record with a new cursor and copies both stacks,
    in every branch. *)
Lemma read_memarg_size : forall st data r st',
  code_read_memarg st data = Ok (r, st') -> stack_size st' = stack_size st.
Proof.
  intros st data r st' H. unfold code_read_memarg in H.
  destruct (reader_read_u32_leb data st.(code_OpIterState_pos)) as [r1|]
    eqn:H1; cbn [bind] in H; [|discriminate].
  destruct r1 as [[a p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. reflexivity. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_u32_leb data p1) as [r2|] eqn:H2; cbn [bind] in H;
    [|discriminate].
  destruct r2 as [[o p2]|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. reflexivity. }
  rewrite branch_ok in H. cbn [bind] in H. injection H as _ <-. reflexivity.
Qed.

Lemma read_load_size : forall st data module ty natural r st',
  code_read_load st data module ty natural = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st data module ty natural r st' H. unfold code_read_load in H.
  destruct (code_read_memarg st data) as [[r1 st1]|] eqn:Hma;
    cbn [bind] in H; [|discriminate].
  pose proof (read_memarg_size st data r1 st1 Hma) as Hs1.
  destruct r1 as [m0|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_check_memory_and_alignment module m0 natural) as [r2|] eqn:Hck;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_pop_with_type st1 Types_ValueType_I32) as [[r3 st2]|] eqn:Hpop;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_size st1 _ r3 st2 Hpop) as Hs2.
  destruct r3 as [t3|e3].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_push_val st2 (Code_StackType_Val ty)) as [st3|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  rewrite (push_val_size st2 _ st3 Hpv). lia.
Qed.

Lemma read_store_size : forall st data module ty natural r st',
  code_read_store st data module ty natural = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st data module ty natural r st' H. unfold code_read_store in H.
  destruct (code_read_memarg st data) as [[r1 st1]|] eqn:Hma;
    cbn [bind] in H; [|discriminate].
  pose proof (read_memarg_size st data r1 st1 Hma) as Hs1.
  destruct r1 as [m0|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_check_memory_and_alignment module m0 natural) as [r2|] eqn:Hck;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_pop_with_type st1 ty) as [[r3 st2]|] eqn:Hpop1;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_size st1 ty r3 st2 Hpop1) as Hs2.
  destruct r3 as [t3|e3].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_pop_with_type st2 Types_ValueType_I32) as [[r4 st3]|] eqn:Hpop2;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_size st2 _ r4 st3 Hpop2) as Hs3.
  destruct r4 as [t4|e4].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  injection H as _ <-. lia.
Qed.

(** [else]'s two rewrites-in-place touch only the control stack's content, not
    its length, so the operand stack's shrink from [pop_types] is the only
    change to [stack_size]: it can only go down. *)
Lemma read_else_size : forall st r st',
  code_read_else st = Ok (r, st') ->
  (stack_size st' <= stack_size st)%nat.
Proof.
  intros st r st' H. unfold code_read_else in H.
  destruct (code_CtrlsStack_len st.(code_OpIterState_ctrls)) as [n|e]
    eqn:Hlen in H; cbn [bind] in H; [|inversion H].
  destruct (n s= 0%usize) eqn:Hn.
  { injection H as _ <-. lia. }
  destruct (usize_sub n 1%usize) as [i|e] eqn:Hsub in H;
    cbn [bind] in H; [|inversion H].
  destruct (code_CtrlsStack_get st.(code_OpIterState_ctrls) i)
    as [frame|e] eqn:Hidx in H; cbn [bind] in H; [|inversion H].
  destruct (code_is_then frame.(code_Ctrl_kind)) as [b|] eqn:Hit;
    cbn [bind] in H; [|discriminate].
  destruct b; [|injection H as _ <-; lia].
  destruct (code_pop_block_results st frame.(code_Ctrl_block_type))
    as [[r1 st1]|] eqn:Hpt; cbn [bind] in H; [|discriminate].
  pose proof (pop_block_results_size st _ r1 st1 Hpt) as Hs1.
  destruct r1 as [u1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u1. rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_ValsStack_len st1.(code_OpIterState_vals)) as [nv|e]
    eqn:Hvlen in H; cbn [bind] in H; [|inversion H].
  destruct (nv s<> frame.(code_Ctrl_value_stack_base)) eqn:Hg.
  { injection H as _ <-. lia. }
  destruct (code_CtrlsStack_set st1.(code_OpIterState_ctrls) i _)
    as [cs1|e] eqn:Hset in H; cbn [bind] in H; [|inversion H].
  injection H as _ <-.
  pose proof (ctrls_stack_set_length _ _ _ _ Hset) as Hlen2.
  unfold stack_size in Hs1 |- *.
  cbn [code_OpIterState_vals code_OpIterState_ctrls] in Hlen2 |- *.
  lia.
Qed.

(** [end] pops results, drops a control frame and pushes the results back. Wasm
    1.0 caps the results at one, so the frame it drops pays for them. *)
Lemma read_end_size : forall st r st',
  code_read_end st = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st r st' H. unfold code_read_end in H.
  destruct (code_CtrlsStack_len st.(code_OpIterState_ctrls)) as [n|e]
    eqn:Hlen in H; cbn [bind] in H; [|inversion H].
  destruct (n s= 0%usize) eqn:Hn.
  { injection H as _ <-. lia. }
  destruct (usize_sub n 1%usize) as [i|e] eqn:Hsub in H;
    cbn [bind] in H; [|inversion H].
  destruct (code_CtrlsStack_get st.(code_OpIterState_ctrls) i)
    as [frame|e] eqn:Hidx in H; cbn [bind] in H; [|inversion H].
  destruct frame.(code_Ctrl_block_type) as [|vt] eqn:Hbt in H;
    cbn [bind] in H.
  all:
  destruct (code_is_then frame.(code_Ctrl_kind)) as [b|] eqn:Hit;
    cbn [bind] in H; [|discriminate].
  all: destruct b; cbn [bind] in H.
  all: try (injection H as _ <-; lia).
  all: destruct (code_pop_block_results st _) as [[r1 st1]|e]
    eqn:Hpt in H; cbn [bind] in H; [|inversion H].
  all: pose proof (pop_block_results_size st _ r1 st1 Hpt) as Hs1.
  all: destruct r1 as [u1|e1].
  all: try (rewrite branch_err in H; cbn [bind] in H;
    rewrite from_residual_err in H; cbn [bind] in H;
    injection H as _ <-; lia).
  all: destruct u1; rewrite branch_ok in H; cbn [bind] in H.
  all: destruct (code_ValsStack_len st1.(code_OpIterState_vals))
    as [nv|e] eqn:Hvlen in H; cbn [bind] in H; [|inversion H].
  all: destruct (nv s<> frame.(code_Ctrl_value_stack_base)) eqn:Hg in H.
  all: try (injection H as _ <-; lia).
  all: destruct (code_CtrlsStack_pop st1.(code_OpIterState_ctrls))
    as [[o cs]|e] eqn:Hpop in H; cbn [bind] in H; [|inversion H].
  all: pose proof (ctrls_stack_pop_size _ o cs Hpop) as Hcp.
  all: destruct (code_push_block_results
    {| code_OpIterState_vals := st1.(code_OpIterState_vals);
       code_OpIterState_ctrls := cs;
       code_OpIterState_pos := st1.(code_OpIterState_pos) |} _)
    as [st2|e] eqn:Hpush in H; cbn [bind] in H; [|inversion H].
  all: injection H as _ <-.
  all: pose proof (push_block_results_size _ _ st2 Hpush) as Hs2.
  all: unfold stack_size in Hs1, Hs2 |- *;
       cbn [code_OpIterState_vals code_OpIterState_ctrls] in Hs2; lia.
Qed.

(* ================================================================== *)
(** ** The state helpers cannot fail                                   *)
(* ================================================================== *)

(** Panic-freedom, one layer at a time. A [Fail_] in the extraction is a Rust
    panic, so these say the branch does not exist. Only the two pushes have a
    precondition, and it is the one the body size limit supplies.

    The accessors are total because the code checks the control stack for
    emptiness before indexing it, and [len - 1] is in range once it is not. *)
Lemma cur_base_total : forall st,
  Z.of_nat (List.length (ctrls_list st.(code_OpIterState_ctrls))) <= usize_max ->
  exists b, code_cur_base st = Ok b.
Proof.
  intros st Hmax. unfold code_cur_base.
  destruct (ctrls_stack_len_total st.(code_OpIterState_ctrls) Hmax)
    as [n Hlen]. rewrite Hlen. cbn [bind].
  destruct (n s= 0%usize) eqn:Hz.
  - eexists. reflexivity.
  - apply scalar_eqb_false in Hz.
    assert (H0 : to_Z 0%usize = 0) by reflexivity.
    rewrite H0 in Hz.
    assert (Hnpos : (1 <= to_Z n)%Z) by (pose proof (usize_nonneg n); lia).
    destruct (usize_sub_1_ok n ltac:(lia)) as [i [Hsub Hival]].
    rewrite Hsub. cbn [bind].
    assert (Hlenpos : (0 < List.length
      (ctrls_list st.(code_OpIterState_ctrls)))%nat).
    { rewrite (ctrls_stack_len_spec _ _ Hlen) in Hnpos.
      destruct (List.length (ctrls_list st.(code_OpIterState_ctrls)));
        cbn in Hnpos; lia. }
    assert (Hlt : (Z.to_nat (to_Z i)
                   < List.length (ctrls_list st.(code_OpIterState_ctrls)))%nat).
    { rewrite Hival, (ctrls_stack_len_spec _ _ Hlen).
      rewrite Z2Nat.inj_sub by lia. cbn. rewrite Nat2Z.id.
      lia. }
    destruct (ctrls_stack_get_total _ i Hlt) as [c Hget].
    rewrite Hget. cbn [bind]. eexists. reflexivity.
Qed.

Lemma cur_polymorphic_total : forall st,
  Z.of_nat (List.length (ctrls_list st.(code_OpIterState_ctrls))) <= usize_max ->
  exists u, code_cur_polymorphic st = Ok u.
Proof.
  intros st Hmax. unfold code_cur_polymorphic.
  destruct (ctrls_stack_len_total st.(code_OpIterState_ctrls) Hmax)
    as [n Hlen]. rewrite Hlen. cbn [bind].
  destruct (n s= 0%usize) eqn:Hz.
  - eexists. reflexivity.
  - apply scalar_eqb_false in Hz.
    assert (H0 : to_Z 0%usize = 0) by reflexivity.
    rewrite H0 in Hz.
    assert (Hnpos : (1 <= to_Z n)%Z) by (pose proof (usize_nonneg n); lia).
    destruct (usize_sub_1_ok n ltac:(lia)) as [i [Hsub Hival]].
    rewrite Hsub. cbn [bind].
    assert (Hlenpos : (0 < List.length
      (ctrls_list st.(code_OpIterState_ctrls)))%nat).
    { rewrite (ctrls_stack_len_spec _ _ Hlen) in Hnpos.
      destruct (List.length (ctrls_list st.(code_OpIterState_ctrls)));
        cbn in Hnpos; lia. }
    assert (Hlt : (Z.to_nat (to_Z i)
                   < List.length (ctrls_list st.(code_OpIterState_ctrls)))%nat).
    { rewrite Hival, (ctrls_stack_len_spec _ _ Hlen).
      rewrite Z2Nat.inj_sub by lia. cbn. rewrite Nat2Z.id.
      lia. }
    destruct (ctrls_stack_get_total _ i Hlt) as [c Hget].
    rewrite Hget. cbn [bind]. eexists. reflexivity.
Qed.

Lemma pop_stack_type_total : forall st,
  Z.of_nat (List.length (vals_list st.(code_OpIterState_vals))) <= usize_max ->
  Z.of_nat (List.length (ctrls_list st.(code_OpIterState_ctrls))) <= usize_max ->
  exists r st', code_pop_stack_type st = Ok (r, st').
Proof.
  intros st Hvmax Hcmax. unfold code_pop_stack_type.
  destruct (vals_stack_len_total st.(code_OpIterState_vals) Hvmax)
    as [n Hlen]. rewrite Hlen. cbn [bind].
  destruct (cur_base_total st Hcmax) as [base Hcb]. rewrite Hcb. cbn [bind].
  destruct (n s= base).
  - destruct (cur_polymorphic_total st Hcmax) as [pb Hcp]. rewrite Hcp. cbn [bind].
    destruct pb; eexists; eexists; reflexivity.
  - destruct (vals_stack_pop_total st.(code_OpIterState_vals)) as [o [v Hpop]].
    rewrite Hpop. cbn [bind].
    destruct o; eexists; eexists; reflexivity.
Qed.

Lemma pop_with_type_total : forall st vt,
  Z.of_nat (List.length (vals_list st.(code_OpIterState_vals))) <= usize_max ->
  Z.of_nat (List.length (ctrls_list st.(code_OpIterState_ctrls))) <= usize_max ->
  exists r st', code_pop_with_type st vt = Ok (r, st').
Proof.
  intros st vt Hvmax Hcmax. unfold code_pop_with_type.
  destruct (pop_stack_type_total st Hvmax Hcmax) as [r0 [st0 Hps]].
  rewrite Hps. cbn [bind].
  destruct r0 as [t|e].
  - rewrite branch_ok. cbn [bind].
    destruct t as [v|].
    + rewrite vt_eq_spec. cbn [bind].
      destruct (types_ValueType_t_beq v vt); eexists; eexists; reflexivity.
    + eexists. eexists. reflexivity.
  - rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
    eexists. eexists. reflexivity.
Qed.

Lemma pop_block_results_total : forall st bt,
  Z.of_nat (stack_size st) <= usize_max ->
  exists r st', code_pop_block_results st bt = Ok (r, st').
Proof.
  intros st bt Hfit. destruct bt as [|vt].
  - eexists; eexists; reflexivity.
  - unfold code_pop_block_results.
    destruct (pop_with_type_total st vt
      ltac:(unfold stack_size in Hfit; lia)
      ltac:(unfold stack_size in Hfit; lia)) as [r0 [st0 Hpop]].
    rewrite Hpop. cbn [bind]. destruct r0 as [t|e].
    + rewrite branch_ok. cbn [bind]. eexists; eexists; reflexivity.
    + rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
      eexists; eexists; reflexivity.
Qed.

Lemma push_val_total : forall st t,
  Z.of_nat (List.length (vals_list st.(code_OpIterState_vals))) + 1
    <= usize_max ->
  exists st', code_push_val st t = Ok st'.
Proof.
  intros st t Hle. unfold code_push_val.
  destruct (vals_stack_push_total st.(code_OpIterState_vals) t Hle) as [v Hpush].
  rewrite Hpush. cbn [bind]. eexists. reflexivity.
Qed.

Lemma push_block_results_total : forall st bt,
  Z.of_nat (List.length (vals_list st.(code_OpIterState_vals))) + 1
    <= usize_max ->
  exists st', code_push_block_results st bt = Ok st'.
Proof.
  intros st bt Hroom. destruct bt as [|vt].
  - eexists. reflexivity.
  - cbn [code_push_block_results].
    exact (push_val_total st (Code_StackType_Val vt) Hroom).
Qed.

Lemma push_ctrl_total : forall st kind bt,
  Z.of_nat (List.length (vals_list st.(code_OpIterState_vals))) <= usize_max ->
  Z.of_nat (List.length (ctrls_list st.(code_OpIterState_ctrls))) + 1
    <= usize_max ->
  exists st', code_push_ctrl st kind bt = Ok st'.
Proof.
  intros st kind bt Hvmax Hle. unfold code_push_ctrl.
  destruct (vals_stack_len_total st.(code_OpIterState_vals) Hvmax)
    as [base Hlen]. rewrite Hlen. cbn [bind].
  destruct (ctrls_stack_push_total st.(code_OpIterState_ctrls)
              {| code_Ctrl_kind := kind;
                 code_Ctrl_block_type := bt;
                 code_Ctrl_value_stack_base := base;
                 code_Ctrl_polymorphic_base := false |} Hle) as [v Hpush].
  rewrite Hpush. cbn [bind]. eexists. reflexivity.
Qed.

(** The loops. [pop_types] walks the expected types backwards, so the index is
    both the measure and the bound that keeps the slice access in range. *)
Lemma pop_types_loop_total : forall n st types i,
  Z.of_nat (stack_size st) <= usize_max ->
  to_Z i <= Z.of_nat n ->
  to_Z i <= to_Z (slice_len types) ->
  exists r st', code_pop_types_loop st types i = Ok (r, st').
Proof.
  induction n as [|n IH]; intros st types i Hfit Hn Hbd;
    unfold code_pop_types_loop; rewrite loop_unfold; cbn beta iota;
    destruct (i s= 0%usize) eqn:Hz;
    [eexists; eexists; reflexivity | | eexists; eexists; reflexivity | ].
  - exfalso. apply scalar_eqb_false in Hz.
    assert (H0 : to_Z 0%usize = 0) by reflexivity.
    pose proof (usize_nonneg i). cbn in Hn. lia.
  - apply scalar_eqb_false in Hz.
    assert (H0 : to_Z 0%usize = 0) by reflexivity.
    pose proof (usize_nonneg i) as Hipos.
    destruct (usize_sub_1_ok i) as [i2 [Hsub Hi2]]; [lia|].
    rewrite Hsub. cbn [bind].
    destruct (slice_index_usize_ok types i2) as [vt Hidx].
    { rewrite slice_len_spec in Hbd. lia. }
    rewrite Hidx. cbn [bind].
    destruct (pop_with_type_total st vt
      ltac:(unfold stack_size in Hfit; lia)
      ltac:(unfold stack_size in Hfit; lia)) as [r0 [st0 Hpwt]].
    pose proof (pop_with_type_size st vt r0 st0 Hpwt) as Hsize.
    rewrite Hpwt. cbn [bind].
    destruct r0 as [t|e].
    + rewrite branch_ok. cbn [bind].
      assert (Hfit0 : Z.of_nat (stack_size st0) <= usize_max).
      { apply Nat2Z.inj_le in Hsize. lia. }
      apply (IH st0 types i2); [exact Hfit0 |cbn in Hn; lia | lia].
    + rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
      eexists. eexists. reflexivity.
Qed.

Lemma pop_types_total : forall st types,
  Z.of_nat (stack_size st) <= usize_max ->
  exists r st', code_pop_types st types = Ok (r, st').
Proof.
  intros st types Hfit. unfold code_pop_types.
  apply (pop_types_loop_total (Z.to_nat (to_Z (slice_len types))) st types);
    [exact Hfit | rewrite Z2Nat.id by apply usize_nonneg | ]; lia.
Qed.

(** [push_types] counts up, and each iteration pushes, so the budget it needs is
    one slot per remaining type. *)
Lemma push_types_loop_total : forall n st types i,
  to_Z (slice_len types) - to_Z i <= Z.of_nat n ->
  Z.of_nat (List.length (vals_list st.(code_OpIterState_vals)))
    + (to_Z (slice_len types) - to_Z i) <= usize_max ->
  exists st', code_push_types_loop st types i = Ok st'.
Proof.
  induction n as [|n IH]; intros st types i Hn Hbudget;
    unfold code_push_types_loop; rewrite loop_unfold; cbn beta iota;
    destruct (i s>= slice_len types) eqn:Hge;
    [eexists; reflexivity | | eexists; reflexivity | ].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hn. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (slice_index_usize_ok types i) as [vt Hidx].
    { rewrite slice_len_spec in Hge. exact Hge. }
    rewrite Hidx. cbn [bind].
    destruct (push_val_total st (Code_StackType_Val vt)) as [st0 Hpv]; [lia|].
    rewrite Hpv. cbn [bind].
    destruct (usize_add_1_ok i) as [i3 [Hadd Hi3]].
    { pose proof (usize_le_max (slice_len types)). lia. }
    rewrite Hadd. cbn [bind].
    apply (IH st0 types i3); [lia|].
    destruct (push_val_spec st _ st0 Hpv) as [Hv _].
    rewrite Hv. rewrite List.app_length. cbn [List.length]. lia.
Qed.

Lemma push_types_total : forall st types,
  Z.of_nat (List.length (vals_list st.(code_OpIterState_vals)))
    + Z.of_nat (List.length (vec_list types)) <= usize_max ->
  exists st', code_push_types st types = Ok st'.
Proof.
  intros st types Hbudget. unfold code_push_types.
  apply (push_types_loop_total (Z.to_nat (to_Z (slice_len types))) st types).
  - rewrite Z2Nat.id by apply usize_nonneg.
    assert (H0 : to_Z 0%usize = 0) by reflexivity. lia.
  - assert (H0 : to_Z 0%usize = 0) by reflexivity.
    rewrite slice_len_spec. lia.
Qed.

(** [mark_unreachable] pops down to the frame base, so the operand stack's length
    is the measure, and then rewrites one frame in place. *)
Lemma mark_unreachable_loop_total : forall n st base,
  Z.of_nat (List.length (vals_list st.(code_OpIterState_vals))) <= usize_max ->
  (List.length (vals_list st.(code_OpIterState_vals)) <= n)%nat ->
  exists r, code_mark_unreachable_loop st base = Ok r.
Proof.
  induction n as [|n IH]; intros st base Hmax Hlen;
    unfold code_mark_unreachable_loop; rewrite loop_unfold; cbn beta iota;
    destruct (vals_stack_len_total st.(code_OpIterState_vals) Hmax)
      as [len Hstacklen]; rewrite Hstacklen; cbn [bind];
    destruct (len s<= base) eqn:Hle;
    [eexists; reflexivity | | eexists; reflexivity | ].
  - exfalso. apply scalar_leb_false in Hle.
    rewrite (vals_stack_len_spec _ _ Hstacklen) in Hle.
    assert (Hnil : vals_list st.(code_OpIterState_vals) = []).
    { destruct (vals_list st.(code_OpIterState_vals)); [reflexivity|].
      cbn [List.length] in Hlen. lia. }
    rewrite Hnil in Hle. cbn [List.length] in Hle.
    pose proof (usize_nonneg base). lia.
  - destruct (vals_stack_pop_total st.(code_OpIterState_vals))
      as [o [v Hpop]].
    rewrite Hpop. cbn [bind].
    apply scalar_leb_false in Hle.
    assert (Hne : vals_list st.(code_OpIterState_vals) <> []).
    { intros Hnil. rewrite (vals_stack_len_spec _ _ Hstacklen) in Hle.
      rewrite Hnil in Hle.
      cbn [List.length] in Hle. pose proof (usize_nonneg base). lia. }
    pose proof (vals_stack_pop_len _ o v Hpop Hne) as Hlt.
    apply (IH {| code_OpIterState_vals := v;
                 code_OpIterState_ctrls := st.(code_OpIterState_ctrls);
                 code_OpIterState_pos := st.(code_OpIterState_pos)
              |} base).
    + cbn [code_OpIterState_vals].
      pose proof (vals_stack_pop_size _ o v Hpop) as Hsize.
      apply Nat2Z.inj_le in Hsize. lia.
    + cbn [code_OpIterState_vals]. lia.
Qed.

Lemma mark_unreachable_total : forall st,
  Z.of_nat (stack_size st) <= usize_max ->
  exists st', code_mark_unreachable st = Ok st'.
Proof.
  intros st Hfit. unfold code_mark_unreachable.
  destruct (cur_base_total st ltac:(unfold stack_size in Hfit; lia))
    as [base Hcb]. rewrite Hcb. cbn [bind].
  destruct (mark_unreachable_loop_total
              (List.length (vals_list st.(code_OpIterState_vals)))
              st base ltac:(unfold stack_size in Hfit; lia) (Nat.le_refl _))
    as [r Hloop].
  destruct r as [[v v1] i]. rewrite Hloop. cbn [bind].
  destruct (mark_unreachable_loop_size
    (List.length (vals_list st.(code_OpIterState_vals))) st base v v1 i
    (Nat.le_refl _) Hloop) as [_ Hc].
  assert (Hcmax : Z.of_nat (List.length (ctrls_list v1)) <= usize_max).
  { rewrite Hc. unfold stack_size in Hfit. lia. }
  destruct (ctrls_stack_len_total v1 Hcmax) as [n Hlen].
  rewrite Hlen. cbn [bind].
  destruct (n s= 0%usize) eqn:Hz; [eexists; reflexivity|].
  apply scalar_eqb_false in Hz.
  assert (H0 : to_Z 0%usize = 0) by reflexivity.
  rewrite H0 in Hz.
  assert (Hnpos : (1 <= to_Z n)%Z) by (pose proof (usize_nonneg n); lia).
  destruct (usize_sub_1_ok n ltac:(lia)) as [i1 [Hsub Hi1]].
  rewrite Hsub. cbn [bind].
  assert (Hlenpos : (0 < List.length (ctrls_list v1))%nat).
  { rewrite (ctrls_stack_len_spec _ _ Hlen) in Hnpos.
    destruct (List.length (ctrls_list v1)); cbn in Hnpos; lia. }
  assert (Hlt : (Z.to_nat (to_Z i1) < List.length (ctrls_list v1))%nat).
  { rewrite Hi1, (ctrls_stack_len_spec _ _ Hlen).
    rewrite Z2Nat.inj_sub by lia. cbn. rewrite Nat2Z.id. lia. }
  destruct (ctrls_stack_get_total v1 i1 Hlt) as [c Hget].
  rewrite Hget. cbn [bind].
  destruct (ctrls_stack_set_total v1 i1
    {| code_Ctrl_kind := c.(code_Ctrl_kind);
       code_Ctrl_block_type := c.(code_Ctrl_block_type);
       code_Ctrl_value_stack_base := c.(code_Ctrl_value_stack_base);
       code_Ctrl_polymorphic_base := true |} Hlt) as [cs Hset].
  rewrite Hset. cbn [bind]. eexists. reflexivity.
Qed.

(** [br_if] pops the condition and the target's types and pushes the types
    back, so the target list's length bounds the net growth: one. *)
Lemma read_br_if_size : forall st data r st',
  code_read_br_if st data = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st data r st' H. unfold code_read_br_if in H.
  destruct (code_read_label st data) as [[r0 st1]|]
    eqn:Htb; cbn [bind] in H; [|discriminate].
  pose proof (read_label_size st data r0 st1 Htb) as Hs1.
  destruct r0 as [[depth target]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_branch_target_bt target) as [bt|] eqn:Hbtt;
    cbn [bind] in H; [|discriminate].
  destruct (code_pop_with_type st1 Types_ValueType_I32) as [[r1 st2]|] eqn:Hp1;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_size st1 _ r1 st2 Hp1) as Hs2.
  destruct r1 as [t1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_pop_block_results st2 bt) as [[r2 st3]|]
    eqn:Hpt; cbn [bind] in H; [|discriminate].
  pose proof (pop_block_results_size st2 _ r2 st3 Hpt) as Hs3.
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_push_block_results st3 bt) as [st4|]
    eqn:Hpush; cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  pose proof (push_block_results_size st3 _ st4 Hpush) as Hs4. lia.
Qed.

(* ================================================================== *)
(** ** memory.size and memory.grow                                     *)
(* ================================================================== *)

(** The reserved byte moves the cursor and nothing else. *)
Lemma read_reserved_zero_fields : forall st data r st',
  code_read_reserved_zero st data = Ok (r, st') ->
  vals_list st'.(code_OpIterState_vals)
    = vals_list st.(code_OpIterState_vals)
  /\ ctrls_list st'.(code_OpIterState_ctrls)
     = ctrls_list st.(code_OpIterState_ctrls).
Proof.
  intros st data r st' H. unfold code_read_reserved_zero in H.
  destruct (reader_read_byte data st.(code_OpIterState_pos)) as [r0|] eqn:Hrb;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [[b p]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. split; reflexivity. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (b s<> 0%u8); injection H as _ <-;
    cbn [code_OpIterState_vals code_OpIterState_ctrls];
    split; reflexivity.
Qed.

Lemma read_reserved_zero_size : forall st data r st',
  code_read_reserved_zero st data = Ok (r, st') ->
  stack_size st' = stack_size st.
Proof.
  intros st data r st' H.
  destruct (read_reserved_zero_fields st data r st' H) as [Hv Hc].
  unfold stack_size. rewrite Hv. rewrite Hc. reflexivity.
Qed.

Lemma read_memory_size_size : forall st data module r st',
  code_read_memory_size st data module = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st data module r st' H. unfold code_read_memory_size in H.
  destruct (code_read_reserved_zero st data) as [[r1 st1]|] eqn:Hrz;
    cbn [bind] in H; [|discriminate].
  pose proof (read_reserved_zero_size st data r1 st1 Hrz) as Hs1.
  destruct r1 as [u1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u1. rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_require_memory module) as [r2|] eqn:Hrm;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_push_val st1 (Code_StackType_Val Types_ValueType_I32))
    as [st2|] eqn:Hpv; cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  rewrite (push_val_size st1 _ st2 Hpv). lia.
Qed.

Lemma read_memory_grow_size : forall st data module r st',
  code_read_memory_grow st data module = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st data module r st' H. unfold code_read_memory_grow in H.
  destruct (code_read_reserved_zero st data) as [[r1 st1]|] eqn:Hrz;
    cbn [bind] in H; [|discriminate].
  pose proof (read_reserved_zero_size st data r1 st1 Hrz) as Hs1.
  destruct r1 as [u1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u1. rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_require_memory module) as [r2|] eqn:Hrm;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_pop_with_type st1 Types_ValueType_I32) as [[r3 st2]|] eqn:Hp3;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_size st1 _ r3 st2 Hp3) as Hs2.
  destruct r3 as [t3|e3].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_push_val st2 (Code_StackType_Val Types_ValueType_I32))
    as [st3|] eqn:Hpv; cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  rewrite (push_val_size st2 _ st3 Hpv). lia.
Qed.

(** The one precondition the readers need: room for one more entry. The body size
    limit gives it, since [stack_size] never exceeds the byte count. *)
Definition room (st : code_OpIterState_t) : Prop :=
  Z.of_nat (stack_size st) + 1 <= usize_max.

Lemma room_vals : forall st, room st ->
  Z.of_nat (List.length (vals_list st.(code_OpIterState_vals))) + 1
    <= usize_max.
Proof. intros st H. unfold room, stack_size in H. lia. Qed.

Lemma room_ctrls : forall st, room st ->
  Z.of_nat (List.length (ctrls_list st.(code_OpIterState_ctrls))) + 1
    <= usize_max.
Proof. intros st H. unfold room, stack_size in H. lia. Qed.

Lemma room_le : forall st st',
  (stack_size st' <= stack_size st)%nat -> room st -> room st'.
Proof. intros st st' Hle H. unfold room in *. lia. Qed.

Lemma read_unreachable_total : forall st,
  room st ->
  exists r st', code_read_unreachable st = Ok (r, st').
Proof.
  intros st Hroom. unfold code_read_unreachable.
  destruct (mark_unreachable_total st ltac:(unfold room in Hroom; lia))
    as [st1 Hmu].
  rewrite Hmu. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma read_return_total : forall st ctx,
  room st ->
  exists r st', code_read_return st ctx = Ok (r, st').
Proof.
  intros st ctx Hroom. unfold code_read_return.
  destruct ctx.(code_Context_results) as [vt|]; cbn [bind].
  - destruct (pop_block_results_total st (Code_BlockType_Value vt)
      ltac:(unfold room in Hroom; lia)) as [r1 [st1 Hpt]].
    rewrite Hpt. cbn [bind].
    pose proof (pop_block_results_size st _ r1 st1 Hpt) as Hsize.
    destruct r1 as [u1|e1].
    + destruct u1. rewrite branch_ok. cbn [bind].
      destruct (mark_unreachable_total st1
        ltac:(apply Nat2Z.inj_le in Hsize; unfold room in Hroom; lia))
        as [st2 Hmu].
      rewrite Hmu. cbn [bind]. eexists; eexists; reflexivity.
    + rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
      eexists; eexists; reflexivity.
  - destruct (pop_block_results_total st Code_BlockType_Empty
      ltac:(unfold room in Hroom; lia)) as [r1 [st1 Hpt]].
    rewrite Hpt. cbn [bind].
    pose proof (pop_block_results_size st _ r1 st1 Hpt) as Hsize.
    destruct r1 as [u1|e1].
    + destruct u1. rewrite branch_ok. cbn [bind].
      destruct (mark_unreachable_total st1
        ltac:(apply Nat2Z.inj_le in Hsize; unfold room in Hroom; lia))
        as [st2 Hmu].
      rewrite Hmu. cbn [bind]. eexists; eexists; reflexivity.
    + rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
      eexists; eexists; reflexivity.
Qed.

Lemma read_drop_total : forall st,
  room st ->
  exists r st', code_read_drop st = Ok (r, st').
Proof.
  intros st Hroom. unfold code_read_drop.
  apply pop_stack_type_total; unfold room, stack_size in *; lia.
Qed.

Lemma read_select_total : forall st,
  room st -> exists r st', code_read_select st = Ok (r, st').
Proof.
  intros st Hroom. unfold code_read_select.
  destruct (pop_with_type_total st Types_ValueType_I32
    ltac:(unfold room, stack_size in *; lia)
    ltac:(unfold room, stack_size in *; lia)) as [r1 [st1 Hp]].
  rewrite Hp. cbn [bind].
  pose proof (pop_with_type_size st _ r1 st1 Hp) as Hs1.
  destruct r1 as [t1|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (pop_stack_type_total st1
    ltac:(pose proof (room_le st st1 Hs1 Hroom); unfold room, stack_size in *; lia)
    ltac:(pose proof (room_le st st1 Hs1 Hroom); unfold room, stack_size in *; lia))
    as [r2 [st2 Hq2]].
  rewrite Hq2. cbn [bind].
  pose proof (pop_stack_type_size st1 r2 st2 Hq2) as Hs2.
  destruct r2 as [t2|e2].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (pop_stack_type_total st2
    ltac:(pose proof (room_le st st1 Hs1 Hroom) as Hr1;
      pose proof (room_le st1 st2 Hs2 Hr1); unfold room, stack_size in *; lia)
    ltac:(pose proof (room_le st st1 Hs1 Hroom) as Hr1;
      pose proof (room_le st1 st2 Hs2 Hr1); unfold room, stack_size in *; lia))
    as [r3 [st3 Hq3]].
  rewrite Hq3. cbn [bind].
  pose proof (pop_stack_type_size st2 r3 st3 Hq3) as Hs3.
  destruct r3 as [t3|e3].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (join_stack_type_total t2 t3) as [rj Hj]. rewrite Hj. cbn [bind].
  destruct rj as [t|ej].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (push_val_total st3 t) as [st4 Hpv].
  { apply room_vals. unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma read_binary_total : forall st ty res,
  room st -> exists r st', code_read_binary st ty res = Ok (r, st').
Proof.
  intros st ty res Hroom. unfold code_read_binary.
  destruct (pop_with_type_total st ty
    ltac:(unfold room, stack_size in *; lia)
    ltac:(unfold room, stack_size in *; lia)) as [r1 [st1 Hp1]].
  rewrite Hp1. cbn [bind].
  pose proof (pop_with_type_size st ty r1 st1 Hp1) as Hs1.
  destruct r1 as [t1|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (pop_with_type_total st1 ty
    ltac:(pose proof (room_le st st1 Hs1 Hroom);
      unfold room, stack_size in *; lia)
    ltac:(pose proof (room_le st st1 Hs1 Hroom);
      unfold room, stack_size in *; lia)) as [r2 [st2 Hp2]].
  rewrite Hp2. cbn [bind].
  pose proof (pop_with_type_size st1 ty r2 st2 Hp2) as Hs2.
  destruct r2 as [t2|e2].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (push_val_total st2 (Code_StackType_Val res)) as [st3 Hpv].
  { apply room_vals. unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. eexists. eexists. reflexivity.
Qed.

(* ================================================================== *)
(** ** The local operators' shared prologue                            *)
(* ================================================================== *)

(** The segmented bounds check makes the lookup total without needing to add
    the inline capacity to an arbitrary overflow-vector length. *)
Lemma local_type_ok : forall ctx idx,
  exists r, code_local_type ctx idx = Ok r.
Proof.
  intros ctx idx. unfold code_local_type.
  destruct (scalar_cast_u32_usize idx) as [i [Hcast Hi]].
  rewrite Hcast. cbn [bind].
  destruct (locals_stack_get_checked_total ctx.(code_Context_locals) i)
    as [o Hget].
  rewrite Hget. cbn [bind]. destruct o; eexists; reflexivity.
Qed.

(** [take_local] moves only the cursor: the index and the lookup are pure, so
    the state it returns is the incoming one with the cursor advanced. *)
Lemma take_local_fields : forall st data ctx r st',
  code_take_local st data ctx = Ok (r, st') ->
  vals_list st'.(code_OpIterState_vals)
    = vals_list st.(code_OpIterState_vals)
  /\ ctrls_list st'.(code_OpIterState_ctrls)
     = ctrls_list st.(code_OpIterState_ctrls).
Proof.
  intros st data ctx r st' H. unfold code_take_local in H.
  destruct (reader_read_u32_leb data st.(code_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[idx0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. split; reflexivity. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_local_type ctx idx0) as [r2|] eqn:Hlt;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [t|e2].
  - rewrite branch_ok in H. cbn [bind] in H. injection H as _ <-.
    cbn [code_OpIterState_vals code_OpIterState_ctrls].
    split; reflexivity.
  - rewrite branch_err in H. cbn [bind] in H.
    rewrite from_residual_err in H. cbn [bind] in H. injection H as _ <-.
    cbn [code_OpIterState_vals code_OpIterState_ctrls].
    split; reflexivity.
Qed.

Lemma take_local_size : forall st data ctx r st',
  code_take_local st data ctx = Ok (r, st') ->
  stack_size st' = stack_size st.
Proof.
  intros st data ctx r st' H.
  destruct (take_local_fields st data ctx r st' H) as [Hv Hc].
  unfold stack_size. rewrite Hv. rewrite Hc. reflexivity.
Qed.

(** The lookup the prologue performed, for the step lemmas: the type it returned
    is the one the context has at that index. *)
Lemma take_local_type : forall st data ctx idx t st',
  code_take_local st data ctx
    = Ok (Core_result_Result_Ok (idx, t), st') ->
  code_local_type ctx idx = Ok (Core_result_Result_Ok t).
Proof.
  intros st data ctx idx t st' H. unfold code_take_local in H.
  destruct (reader_read_u32_leb data st.(code_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[idx0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_local_type ctx idx0) as [r2|] eqn:Hlt;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [t0|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  injection H as Hidx Ht _. rewrite <- Hidx. rewrite <- Ht. exact Hlt.
Qed.

Lemma read_local_get_size : forall st data ctx r st',
  code_read_local_get st data ctx = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st data ctx r st' H. unfold code_read_local_get in H.
  destruct (code_take_local st data ctx) as [[r0 st1]|]
    eqn:Htl; cbn [bind] in H; [|discriminate].
  pose proof (take_local_size st data ctx r0 st1 Htl) as Hs1.
  destruct r0 as [[idx t]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_push_val st1 (Code_StackType_Val t)) as [st2|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as _ <-. rewrite (push_val_size st1 _ st2 Hpv). lia.
Qed.

Lemma read_local_set_size : forall st data ctx r st',
  code_read_local_set st data ctx = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st data ctx r st' H. unfold code_read_local_set in H.
  destruct (code_take_local st data ctx) as [[r0 st1]|]
    eqn:Htl; cbn [bind] in H; [|discriminate].
  pose proof (take_local_size st data ctx r0 st1 Htl) as Hs1.
  destruct r0 as [[idx t]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_pop_with_type st1 t) as [[r1 st2]|] eqn:Hp1;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_size st1 t r1 st2 Hp1) as Hs2.
  destruct r1 as [t1|e1].
  - rewrite branch_ok in H. cbn [bind] in H. injection H as _ <-. lia.
  - rewrite branch_err in H. cbn [bind] in H.
    rewrite from_residual_err in H. cbn [bind] in H. injection H as _ <-. lia.
Qed.

Lemma read_local_tee_size : forall st data ctx r st',
  code_read_local_tee st data ctx = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st data ctx r st' H. unfold code_read_local_tee in H.
  destruct (code_take_local st data ctx) as [[r0 st1]|]
    eqn:Htl; cbn [bind] in H; [|discriminate].
  pose proof (take_local_size st data ctx r0 st1 Htl) as Hs1.
  destruct r0 as [[idx t]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_pop_with_type st1 t) as [[r1 st2]|] eqn:Hp1;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_size st1 t r1 st2 Hp1) as Hs2.
  destruct r1 as [t1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_push_val st2 (Code_StackType_Val t)) as [st3|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as _ <-. rewrite (push_val_size st2 _ st3 Hpv). lia.
Qed.

(* ================================================================== *)
(** ** The global operators' shared prologue                           *)
(* ================================================================== *)

(** [local_type_ok]'s counterpart: the bounds check is what makes the lookup
    total. *)
Lemma global_type_ok : forall module idx,
  exists r, code_global_type module idx = Ok r.
Proof.
  intros module idx. unfold code_global_type.
  destruct (scalar_cast_u32_usize idx) as [i [Hcast Hi]].
  rewrite Hcast. cbn [bind].
  destruct (i s>= alloc_vec_Vec_len module.(module_Env_global_types)) eqn:Hge;
    [eexists; reflexivity|].
  rewrite vec_index_spec.
  destruct (List.nth_error (vec_list module.(module_Env_global_types))
              (Z.to_nat (to_Z i))) as [g|] eqn:Hnth;
    [cbn [bind]; eexists; reflexivity|].
  exfalso. apply List.nth_error_None in Hnth.
  apply scalar_geb_false_lt in Hge.
  assert (Hlen : to_Z (alloc_vec_Vec_len module.(module_Env_global_types))
                 = Z.of_nat (List.length
                     (vec_list module.(module_Env_global_types)))) by reflexivity.
  rewrite Hlen in Hge.
  pose proof (usize_nonneg i) as Hnn. lia.
Qed.

Lemma take_global_fields : forall st data module r st',
  code_take_global st data module = Ok (r, st') ->
  vals_list st'.(code_OpIterState_vals)
    = vals_list st.(code_OpIterState_vals)
  /\ ctrls_list st'.(code_OpIterState_ctrls)
     = ctrls_list st.(code_OpIterState_ctrls).
Proof.
  intros st data module r st' H. unfold code_take_global in H.
  destruct (reader_read_u32_leb data st.(code_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[idx0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. split; reflexivity. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_global_type module idx0) as [r2|] eqn:Hgt;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [g|e2].
  - rewrite branch_ok in H. cbn [bind] in H. injection H as _ <-.
    cbn [code_OpIterState_vals code_OpIterState_ctrls].
    split; reflexivity.
  - rewrite branch_err in H. cbn [bind] in H.
    rewrite from_residual_err in H. cbn [bind] in H. injection H as _ <-.
    cbn [code_OpIterState_vals code_OpIterState_ctrls].
    split; reflexivity.
Qed.

Lemma take_global_size : forall st data module r st',
  code_take_global st data module = Ok (r, st') ->
  stack_size st' = stack_size st.
Proof.
  intros st data module r st' H.
  destruct (take_global_fields st data module r st' H) as [Hv Hc].
  unfold stack_size. rewrite Hv. rewrite Hc. reflexivity.
Qed.

(** The lookup the prologue performed, for the step lemmas. *)
Lemma take_global_type : forall st data module idx g st',
  code_take_global st data module
    = Ok (Core_result_Result_Ok (idx, g), st') ->
  code_global_type module idx = Ok (Core_result_Result_Ok g).
Proof.
  intros st data module idx g st' H. unfold code_take_global in H.
  destruct (reader_read_u32_leb data st.(code_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[idx0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_global_type module idx0) as [r2|] eqn:Hgt;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [g0|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  injection H as Hidx Hg _. rewrite <- Hidx. rewrite <- Hg. exact Hgt.
Qed.

Lemma read_global_get_size : forall st data module r st',
  code_read_global_get st data module = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st data module r st' H. unfold code_read_global_get in H.
  destruct (code_take_global st data module) as [[r0 st1]|]
    eqn:Htg; cbn [bind] in H; [|discriminate].
  pose proof (take_global_size st data module r0 st1 Htg) as Hs1.
  destruct r0 as [[idx g]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_push_val st1
              (Code_StackType_Val g.(types_GlobalType_valtype))) as [st2|]
    eqn:Hpv; cbn [bind] in H; [|discriminate].
  injection H as _ <-. rewrite (push_val_size st1 _ st2 Hpv). lia.
Qed.

(** The mutability guard is an early return, so it needs a case of its own. *)
Lemma read_global_set_size : forall st data module r st',
  code_read_global_set st data module = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st data module r st' H. unfold code_read_global_set in H.
  destruct (code_take_global st data module) as [[r0 st1]|]
    eqn:Htg; cbn [bind] in H; [|discriminate].
  pose proof (take_global_size st data module r0 st1 Htg) as Hs1.
  destruct r0 as [[idx g]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (g.(types_GlobalType_mutability)).
  { injection H as _ <-. lia. }
  destruct (code_pop_with_type st1 g.(types_GlobalType_valtype))
    as [[r1 st2]|] eqn:Hp1; cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_size st1 _ r1 st2 Hp1) as Hs2.
  destruct r1 as [t1|e1].
  - rewrite branch_ok in H. cbn [bind] in H. injection H as _ <-. lia.
  - rewrite branch_err in H. cbn [bind] in H.
    rewrite from_residual_err in H. cbn [bind] in H. injection H as _ <-. lia.
Qed.

(** The opcode table is a chain of comparisons returning [Ok] in every branch,
    so it cannot fail. Totality of the numeric dispatch needs this to see past
    the bind. *)
(* ================================================================== *)
(** ** The two call operators                                          *)
(* ================================================================== *)

(** [take_index] is the prologue [call] and [call_indirect] share: the opcode
    and the index immediate, so it moves the cursor and nothing else. *)
Lemma take_index_fields : forall st data r st',
  code_take_index st data = Ok (r, st') ->
  vals_list st'.(code_OpIterState_vals)
    = vals_list st.(code_OpIterState_vals)
  /\ ctrls_list st'.(code_OpIterState_ctrls)
     = ctrls_list st.(code_OpIterState_ctrls).
Proof.
  intros st data r st' H. unfold code_take_index in H.
  destruct (reader_read_u32_leb data st.(code_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[idx0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. split; reflexivity. }
  rewrite branch_ok in H. cbn [bind] in H. injection H as _ <-.
  cbn [code_OpIterState_vals code_OpIterState_ctrls].
  split; reflexivity.
Qed.

Lemma take_index_size : forall st data r st',
  code_take_index st data = Ok (r, st') ->
  stack_size st' = stack_size st.
Proof.
  intros st data r st' H.
  destruct (take_index_fields st data r st' H) as [Hv Hc].
  unfold stack_size. rewrite Hv. rewrite Hc. reflexivity.
Qed.

(** The Wasm 1.0 arity guard, read as the bound the panic-freedom argument
    needs: at most one result means at most one push. *)
Lemma require_single_result_le : forall (s : slice types_ValueType_t),
  code_require_single_result s = Ok (Core_result_Result_Ok tt) ->
  (List.length (vec_list s) <= 1)%nat.
Proof.
  intros s H. unfold code_require_single_result in H.
  destruct (slice_len s s> limits_max_results) eqn:Hgt; [discriminate|].
  apply scalar_gtb_false in Hgt. rewrite slice_len_spec in Hgt.
  assert (H1 : to_Z limits_max_results = 1) by reflexivity. lia.
Qed.

Lemma require_single_result_intro : forall (s : slice types_ValueType_t),
  (List.length (vec_list s) <= 1)%nat ->
  code_require_single_result s = Ok (Core_result_Result_Ok tt).
Proof.
  intros s Hlen. unfold code_require_single_result.
  assert (Hgt : (slice_len s s> limits_max_results) = false).
  { apply scalar_gtb_of_le. rewrite slice_len_spec.
    assert (H1 : to_Z limits_max_results = 1) by reflexivity. lia. }
  rewrite Hgt. reflexivity.
Qed.

Lemma require_single_result_ok : forall (s : slice types_ValueType_t),
  exists r, code_require_single_result s = Ok r.
Proof.
  intros s. unfold code_require_single_result.
  destruct (slice_len s s> limits_max_results); eexists; reflexivity.
Qed.

(** The stack effect is a list of pops and at most one push, so the bound of one
    still holds. This is what the arity guard is for. *)
Lemma read_call_size : forall st data module r st',
  code_read_call st data module = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st data module r st' H. unfold code_read_call in H.
  destruct (code_take_index st data) as [[r0 st1]|] eqn:Hti;
    cbn [bind] in H; [|discriminate].
  pose proof (take_index_size st data r0 st1 Hti) as Hs1.
  destruct r0 as [idx|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (scalar_cast U32 Usize idx) as [i|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  destruct (i s>= alloc_vec_Vec_len module.(module_Env_func_types));
    [injection H as _ <-; lia|].
  destruct (alloc_vec_Vec_index
              (core_slice_index_SliceIndexUsizeSliceInst types_FuncType_t)
              module.(module_Env_func_types) i) as [ft|] eqn:Hidx;
    cbn [bind] in H; [|discriminate].
  destruct (code_require_single_result
              (alloc_vec_Vec_deref ft.(types_FuncType_results))) as [r1|] eqn:Hrs;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [u1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u1. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (require_single_result_le _ Hrs) as Hlen.
  rewrite vec_deref_spec in Hlen.
  destruct (code_pop_types st1 (alloc_vec_Vec_deref ft.(types_FuncType_params)))
    as [[r2 st2]|] eqn:Hpt; cbn [bind] in H; [|discriminate].
  pose proof (pop_types_size st1 _ r2 st2 Hpt) as Hs2.
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_push_types st2 (alloc_vec_Vec_deref ft.(types_FuncType_results)))
    as [st3|] eqn:Hpu; cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  pose proof (push_types_size st2 _ st3 Hpu) as Hs3.
  rewrite vec_deref_spec in Hs3. lia.
Qed.

Lemma read_call_indirect_size : forall st data module r st',
  code_read_call_indirect st data module = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st data module r st' H. unfold code_read_call_indirect in H.
  destruct (code_take_index st data) as [[r0 st1]|]
    eqn:Hti; cbn [bind] in H; [|discriminate].
  pose proof (take_index_size st data r0 st1 Hti) as Hs1.
  destruct r0 as [idx|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_read_reserved_zero st1 data) as [[r1 st2]|] eqn:Hrz;
    cbn [bind] in H; [|discriminate].
  pose proof (read_reserved_zero_size st1 data r1 st2 Hrz) as Hs2.
  destruct r1 as [u1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u1. rewrite branch_ok in H. cbn [bind] in H.
  destruct (alloc_vec_Vec_is_empty alloc_alloc_Global
              module.(module_Env_table_types)) as [emp|] eqn:Hemp;
    cbn [bind] in H; [|discriminate].
  destruct emp; [injection H as _ <-; lia|].
  destruct (scalar_cast U32 Usize idx) as [i|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  destruct (i s>= alloc_vec_Vec_len module.(module_Env_types));
    [injection H as _ <-; lia|].
  destruct (alloc_vec_Vec_index
              (core_slice_index_SliceIndexUsizeSliceInst types_FuncType_t)
              module.(module_Env_types) i) as [ft|] eqn:Hidx;
    cbn [bind] in H; [|discriminate].
  destruct (code_require_single_result
              (alloc_vec_Vec_deref ft.(types_FuncType_results))) as [r2|] eqn:Hrs;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (require_single_result_le _ Hrs) as Hlen.
  rewrite vec_deref_spec in Hlen.
  destruct (code_pop_with_type st2 Types_ValueType_I32) as [[r3 st3]|] eqn:Hpw;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_size st2 _ r3 st3 Hpw) as Hs3.
  destruct r3 as [t3|e3].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_pop_types st3 (alloc_vec_Vec_deref ft.(types_FuncType_params)))
    as [[r4 st4]|] eqn:Hpt; cbn [bind] in H; [|discriminate].
  pose proof (pop_types_size st3 _ r4 st4 Hpt) as Hs4.
  destruct r4 as [u4|e4].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u4. rewrite branch_ok in H. cbn [bind] in H.
  destruct (code_push_types st4 (alloc_vec_Vec_deref ft.(types_FuncType_results)))
    as [st5|] eqn:Hpu; cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  pose proof (push_types_size st4 _ st5 Hpu) as Hs5.
  rewrite vec_deref_spec in Hs5. lia.
Qed.

Lemma convert_types_ok : forall b, exists o, code_convert_types b = Ok o.
Proof.
  intros b. unfold code_convert_types.
  repeat (match goal with
          | [ |- context [ if ?g then _ else _ ] ] => destruct g
          end); eexists; reflexivity.
Qed.

Lemma binary_types_ok : forall b, exists o, code_binary_types b = Ok o.
Proof.
  intros b. unfold code_binary_types.
  repeat (match goal with
          | [ |- context [ if ?g then _ else _ ] ] => destruct g
          end); eexists; reflexivity.
Qed.

Lemma read_conversion_total : forall st from to,
  room st ->
  exists r st', code_read_conversion st from to = Ok (r, st').
Proof.
  intros st from to Hroom. unfold code_read_conversion.
  destruct (pop_with_type_total st from
    ltac:(unfold room, stack_size in *; lia)
    ltac:(unfold room, stack_size in *; lia)) as [r1 [st1 Hp1]].
  rewrite Hp1. cbn [bind].
  pose proof (pop_with_type_size st from r1 st1 Hp1) as Hs1.
  destruct r1 as [t1|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (push_val_total st1 (Code_StackType_Val to)) as [st2 Hpv].
  { apply room_vals. unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma read_else_total : forall st,
  room st ->
  exists r st', code_read_else st = Ok (r, st').
Proof.
  intros st Hroom. unfold code_read_else.
  destruct (ctrls_stack_len_total st.(code_OpIterState_ctrls)
    ltac:(pose proof (room_ctrls st Hroom); lia)) as [n Hlen].
  rewrite Hlen. cbn [bind]. destruct (n s= 0%usize) eqn:Hz;
    [eexists; eexists; reflexivity|].
  apply scalar_eqb_false in Hz.
  assert (H0 : to_Z 0%usize = 0) by reflexivity.
  rewrite H0 in Hz.
  assert (Hnpos : (1 <= to_Z n)%Z) by (pose proof (usize_nonneg n); lia).
  destruct (usize_sub_1_ok n ltac:(lia)) as [i [Hsub Hival]].
  rewrite Hsub. cbn [bind].
  assert (Hlenpos : (0 < List.length
    (ctrls_list st.(code_OpIterState_ctrls)))%nat).
  { rewrite (ctrls_stack_len_spec _ _ Hlen) in Hnpos.
    destruct (List.length (ctrls_list st.(code_OpIterState_ctrls)));
      cbn in Hnpos; lia. }
  assert (Hlt1 : (Z.to_nat (to_Z i)
                 < List.length (ctrls_list st.(code_OpIterState_ctrls)))%nat).
  { rewrite Hival, (ctrls_stack_len_spec _ _ Hlen).
    rewrite Z2Nat.inj_sub by lia. cbn. rewrite Nat2Z.id. lia. }
  destruct (ctrls_stack_get_total _ i Hlt1) as [frame Hget].
  rewrite Hget. cbn [bind].
  destruct (is_then_total frame.(code_Ctrl_kind)) as [b Hit].
  rewrite Hit. cbn [bind].
  destruct b; [|eexists; eexists; reflexivity].
  destruct (pop_block_results_total st frame.(code_Ctrl_block_type)
    ltac:(unfold room in Hroom; lia)) as [r1 [st1 Hpt]].
  rewrite Hpt. cbn [bind].
  pose proof (pop_block_results_ctrls st _ r1 st1 Hpt) as Hcc.
  pose proof (pop_block_results_size st _ r1 st1 Hpt) as Hsize.
  destruct r1 as [u1|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u1. rewrite branch_ok. cbn [bind].
  destruct (vals_stack_len_total st1.(code_OpIterState_vals)
    ltac:(apply Nat2Z.inj_le in Hsize; unfold room, stack_size in *; lia))
    as [nv Hvlen].
  rewrite Hvlen. cbn [bind].
  destruct (nv s<> frame.(code_Ctrl_value_stack_base));
    [eexists; eexists; reflexivity|].
  assert (Hlt2 : (Z.to_nat (to_Z i)
                 < List.length (ctrls_list st1.(code_OpIterState_ctrls)))%nat).
  { rewrite Hcc. exact Hlt1. }
  destruct (ctrls_stack_set_total st1.(code_OpIterState_ctrls) i
    {| code_Ctrl_kind := Code_LabelKind_Else;
       code_Ctrl_block_type := frame.(code_Ctrl_block_type);
       code_Ctrl_value_stack_base := frame.(code_Ctrl_value_stack_base);
       code_Ctrl_polymorphic_base := false |} Hlt2) as [cs Hset].
  rewrite Hset. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma read_end_total : forall st,
  room st -> exists r st', code_read_end st = Ok (r, st').
Proof.
  intros st Hroom. unfold code_read_end.
  destruct (ctrls_stack_len_total st.(code_OpIterState_ctrls)
    ltac:(pose proof (room_ctrls st Hroom); lia)) as [n Hlen].
  rewrite Hlen. cbn [bind]. destruct (n s= 0%usize) eqn:Hz;
    [eexists; eexists; reflexivity|].
  apply scalar_eqb_false in Hz.
  assert (H0 : to_Z 0%usize = 0) by reflexivity.
  rewrite H0 in Hz.
  assert (Hnpos : (1 <= to_Z n)%Z) by (pose proof (usize_nonneg n); lia).
  destruct (usize_sub_1_ok n ltac:(lia)) as [i [Hsub Hival]].
  rewrite Hsub. cbn [bind].
  assert (Hlenpos : (0 < List.length
    (ctrls_list st.(code_OpIterState_ctrls)))%nat).
  { rewrite (ctrls_stack_len_spec _ _ Hlen) in Hnpos.
    destruct (List.length (ctrls_list st.(code_OpIterState_ctrls)));
      cbn in Hnpos; lia. }
  assert (Hlt : (Z.to_nat (to_Z i)
                 < List.length (ctrls_list st.(code_OpIterState_ctrls)))%nat).
  { rewrite Hival, (ctrls_stack_len_spec _ _ Hlen).
    rewrite Z2Nat.inj_sub by lia. cbn. rewrite Nat2Z.id. lia. }
  destruct (ctrls_stack_get_total _ i Hlt) as [frame Hget].
  rewrite Hget. cbn [bind].
  Ltac finish_end stx framex Hroomx bt :=
    destruct (pop_block_results_total stx bt
      ltac:(unfold room in Hroomx; lia)) as [r1 [st1 Hpt]];
    rewrite Hpt; cbn [bind];
    let Hs1 := fresh "Hs1" in
    pose proof (pop_block_results_size stx bt r1 st1 Hpt) as Hs1;
    destruct r1 as [u1|e1];
    [ destruct u1; rewrite branch_ok; cbn [bind];
      destruct (vals_stack_len_total st1.(code_OpIterState_vals)
        ltac:(apply Nat2Z.inj_le in Hs1; unfold room, stack_size in *; lia))
        as [nv Hvlen];
      rewrite Hvlen; cbn [bind];
      destruct (nv s<> framex.(code_Ctrl_value_stack_base));
      [ eexists; eexists; reflexivity
      | destruct (ctrls_stack_pop_total st1.(code_OpIterState_ctrls))
          as [o [cs Hpop]];
        rewrite Hpop; cbn [bind];
        destruct (push_block_results_total
          {| code_OpIterState_vals := st1.(code_OpIterState_vals);
             code_OpIterState_ctrls := cs;
             code_OpIterState_pos := st1.(code_OpIterState_pos) |} bt
          ltac:(cbn [code_OpIterState_vals];
            apply Nat2Z.inj_le in Hs1; unfold room, stack_size in *; lia))
          as [st2 Hpush];
        rewrite Hpush; cbn [bind]; eexists; eexists; reflexivity ]
    | rewrite branch_err; cbn [bind]; rewrite from_residual_err; cbn [bind];
      eexists; eexists; reflexivity ].
  destruct frame.(code_Ctrl_block_type) as [|vt] eqn:Hbt; cbn [bind].
  - destruct (is_then_total frame.(code_Ctrl_kind)) as [b Hit].
    rewrite Hit. cbn [bind]. destruct b;
      finish_end st frame Hroom Code_BlockType_Empty.
  - destruct (is_then_total frame.(code_Ctrl_kind)) as [b Hit].
    rewrite Hit. cbn [bind]. destruct b.
    + eexists; eexists; reflexivity.
    + finish_end st frame Hroom (Code_BlockType_Value vt).
Qed.
