(** * The streaming validator accepts everything WasmCert accepts

    The other direction of [OpIter_Validate.v]. Soundness follows the code and
    asks what it proves; completeness follows the *specification* -- the operator
    stream the bytes encode, and the instruction tree WasmCert's checker
    accepts -- and shows the code keeps up at every step.

    Three pieces. [OpIter_Decode.v] already has the decoders: every encoding the
    specification admits is read. [OpIter_Readers.v] has the readers: every
    instruction the checker accepts is consumed. This file is the dispatch and the
    loop, and the loop is driven by the operator stream rather than by the bytes,
    because that is what says the run gets all the way to the body's [end] rather
    than merely not crashing.

    The loop invariant is [todo_ok]: one remaining instruction list per open
    frame, each still typechecking from where that frame has got to. Its point is
    that a frame's checker type is frozen while a nested frame is open, so an
    enclosing frame's obligation can be stated without mentioning the child's
    body at all -- only the results the child will push. That is what makes the
    [end] case transport by a rewrite instead of by an induction. *)

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
Require Import Veriwasm.OpIter_Visit.
Require Import Veriwasm.OpIter_State.
Require Import Veriwasm.OpIter_Decode.
Require Import Veriwasm.OpIter_Sim.
Require Import Veriwasm.OpIter_Expr.
Require Import Veriwasm.OpIter_Table.
Require Import Veriwasm.OpIter_NoPanic.
Require Import Veriwasm.OpIter_Validate.
Require Import Veriwasm.OpIter_Checker.
Require Import Veriwasm.OpIter_Readers.

From Wasm Require Import datatypes numerics type_checker operations typing.

Local Open Scope list_scope.
Local Bind Scope list_scope with list.
Open Scope Z_scope.

(* ================================================================== *)
(** ** Walking the opcode dispatch                                     *)
(* ================================================================== *)

Lemma scalar_eqb_of_eq : forall {ty} (x y : scalar ty),
  to_Z x = to_Z y -> (x s= y) = true.
Proof. intros ty x y H. unfold scalar_eqb. apply Z.eqb_eq. exact H. Qed.

Lemma scalar_eqb_of_ne : forall {ty} (x y : scalar ty),
  to_Z x <> to_Z y -> (x s= y) = false.
Proof. intros ty x y H. unfold scalar_eqb. apply Z.eqb_neq. exact H. Qed.

(** Step past one opcode test that cannot match, given the byte's value. The
    tactic fails on the test that does match, which is what makes [repeat] stop
    in the right place. *)
Ltac guard_false Hb :=
  let E := fresh "Eg" in
  match goal with
  | [ |- context [ if (?x s= ?y) then _ else _ ] ] =>
      destruct (x s= y) eqn:E;
      [ exfalso; apply scalar_eqb_true in E; rewrite Hb in E; cbn in E;
        discriminate E
      | clear E ]
  end.

Ltac guard_true Hb :=
  let E := fresh "Eg" in
  match goal with
  | [ |- context [ if (?x s= ?y) then _ else _ ] ] =>
      assert (E : (x s= y) = true)
        by (apply scalar_eqb_of_eq; rewrite Hb; reflexivity);
      rewrite E; clear E
  end.

(* ================================================================== *)
(** ** Taking a [repr_op] derivation apart                             *)
(* ================================================================== *)

(** One disjunct per rule. Stated once because [inversion]'s naming and equation
    order shift with the index's shape, and the dispatch takes this apart once
    per opcode family. *)
Lemma repr_op_inv : forall bs op rest,
  repr_op bs op rest ->
  exists b bs', bs = b :: bs'
  /\ ((exists be, op_spec b = Some (Sh_nullary be) /\ op = FO_plain be
                  /\ rest = bs')
      \/ (op_spec b = Some Sh_end /\ op = FO_end /\ rest = bs')
      \/ (exists btb bt r, op_spec b = Some Sh_block /\ bs' = btb :: r
                  /\ blocktype_spec btb = Some bt /\ op = FO_block bt
                  /\ rest = r)
      \/ (exists btb bt r, op_spec b = Some Sh_loop /\ bs' = btb :: r
                  /\ blocktype_spec btb = Some bt /\ op = FO_loop bt
                  /\ rest = r)
      \/ (exists btb bt r, op_spec b = Some Sh_if /\ bs' = btb :: r
                  /\ blocktype_spec btb = Some bt /\ op = FO_if bt
                  /\ rest = r)
      \/ (op_spec b = Some Sh_else /\ op = FO_else /\ rest = bs')
      \/ (exists be r, op_spec b = Some (Sh_reserved be) /\ bs' = 0 :: r
                  /\ op = FO_plain be /\ rest = r)
      \/ (exists nt z, op_spec b = Some (Sh_const nt)
                  /\ repr_sN (const_bits nt) bs' z rest
                  /\ op = FO_plain (BI_const_num (const_val nt z)))
      \/ (exists nt bits, op_spec b = Some (Sh_fconst nt)
                  /\ repr_bytes_le (fconst_bytes nt) bs' bits rest
                  /\ op = FO_plain (BI_const_num (fconst_val nt bits)))
      \/ (exists io x, op_spec b = Some (Sh_idx io)
                  /\ repr_u32 bs' x rest
                  /\ op = FO_plain (idx_instr io (Z.to_N x)))
      \/ (exists nt tp a o, op_spec b = Some (Sh_load nt tp)
                  /\ repr_memarg bs' (a, o) rest
                  /\ op = FO_plain (BI_load nt tp (Z.to_N a) (Z.to_N o)))
      \/ (exists nt tp a o, op_spec b = Some (Sh_store nt tp)
                  /\ repr_memarg bs' (a, o) rest
                  /\ op = FO_plain (BI_store nt tp (Z.to_N a) (Z.to_N o)))
      \/ (exists ls x mid, op_spec b = Some Sh_br_table
                  /\ repr_vec_u32 bs' ls mid
                  /\ repr_u32 mid x rest
                  /\ op = FO_plain (BI_br_table (List.map Z.to_N ls) (Z.to_N x)))
      \/ (exists y, op_spec b = Some Sh_call_indirect
                  /\ repr_u32 bs' y (0 :: rest)
                  /\ op = FO_plain (BI_call_indirect 0%N (Z.to_N y)))).
Proof.
  intros bs op rest H. destruct H as
    [b be r Hsp | b r Hsp | b btb bt r Hsp Hbt | b btb bt r Hsp Hbt
    | b btb bt r Hsp Hbt | b r Hsp
    | b be r Hsp | b nt z bs0 r Hsp Hz | b nt bits bs0 r Hsp Hbits
    | b io x bs0 r Hsp Hx
    | b nt tp a o bs0 r Hsp Hm | b nt tp a o bs0 r Hsp Hm
    | b ls bs0 mid x r Hsp Hvec Hx
    | b y bs0 r Hsp Hx].
  - exists b, r. split; [reflexivity|]. left. exists be.
    split; [exact Hsp|]. split; reflexivity.
  - exists b, r. split; [reflexivity|]. right. left.
    split; [exact Hsp|]. split; reflexivity.
  - exists b, (btb :: r). split; [reflexivity|]. right. right. left.
    exists btb, bt, r. split; [exact Hsp|]. split; [reflexivity|].
    split; [exact Hbt|]. split; reflexivity.
  - exists b, (btb :: r). split; [reflexivity|]. right. right. right. left.
    exists btb, bt, r. split; [exact Hsp|]. split; [reflexivity|].
    split; [exact Hbt|]. split; reflexivity.
  - exists b, (btb :: r). split; [reflexivity|].
    right. right. right. right. left.
    exists btb, bt, r. split; [exact Hsp|]. split; [reflexivity|].
    split; [exact Hbt|]. split; reflexivity.
  - exists b, r. split; [reflexivity|].
    right. right. right. right. right. left.
    split; [exact Hsp|]. split; reflexivity.
  - exists b, (0 :: r). split; [reflexivity|].
    right. right. right. right. right. right. left. exists be, r.
    split; [exact Hsp|]. split; [reflexivity|]. split; reflexivity.
  - exists b, bs0. split; [reflexivity|].
    right. right. right. right. right. right. right. left. exists nt, z.
    split; [exact Hsp|]. split; [exact Hz | reflexivity].
  - exists b, bs0. split; [reflexivity|].
    right. right. right. right. right. right. right. right. left. exists nt, bits.
    split; [exact Hsp|]. split; [exact Hbits | reflexivity].
  - exists b, bs0. split; [reflexivity|].
    right. right. right. right. right. right. right. right. right. left.
    exists io, x.
    split; [exact Hsp|]. split; [exact Hx | reflexivity].
  - exists b, bs0. split; [reflexivity|].
    do 10 right. left.
    exists nt, tp, a, o.
    split; [exact Hsp|]. split; [exact Hm | reflexivity].
  - exists b, bs0. split; [reflexivity|].
    do 11 right. left.
    exists nt, tp, a, o.
    split; [exact Hsp|]. split; [exact Hm | reflexivity].
  - exists b, bs0. split; [reflexivity|].
    do 12 right. left.
    exists ls, x, mid.
    split; [exact Hsp|]. split; [exact Hvec|].
    split; [exact Hx | reflexivity].
  - exists b, bs0. split; [reflexivity|].
    do 13 right.
    exists y.
    split; [exact Hsp|]. split; [exact Hx | reflexivity].
Qed.

(** Unsigned LEB128 decodes a non-negative number, which the alignment bound and
    the branch-depth lookup both need. *)
Lemma repr_uN_nonneg : forall bits bs v rest, repr_uN bits bs v rest -> 0 <= v.
Proof.
  intros bits bs v rest H.
  induction H as [bits b r Hlo Hhi | bits b more m r Hlo Hb7 Hsub IH]; lia.
Qed.

Lemma repr_u32_nonneg : forall bs v rest, repr_u32 bs v rest -> 0 <= v.
Proof. intros bs v rest H. apply (repr_uN_nonneg 32 bs v rest H). Qed.

Lemma repr_memarg_nonneg : forall bs a o rest,
  repr_memarg bs (a, o) rest -> 0 <= a.
Proof.
  intros bs a o rest H.
  destruct (repr_memarg_inv bs a o rest H) as [mid [Ha _]].
  apply (repr_u32_nonneg bs a mid Ha).
Qed.

(** The fourteen rules, with the thirteen that the opcode byte rules out
    discharged by computing the table at that byte. [Hd] is [repr_op_inv]'s
    disjunction and [Hb] the byte's value. Count the nesting brackets on the last
    line separately from the pattern itself: for *n* disjuncts the last line
    closes its own pattern plus *n-1* brackets. *)
Ltac op_cases Hd Hb :=
  destruct Hd as [[cbe [Hsp [Hop Hr]]]
                 |[[Hsp [Hop Hr]]
                 |[[cbtb [cbt [cr [Hsp [Hbs2 [Hbtspec [Hop Hr]]]]]]]
                 |[[cbtb [cbt [cr [Hsp [Hbs2 [Hbtspec [Hop Hr]]]]]]]
                 |[[cbtb [cbt [cr [Hsp [Hbs2 [Hbtspec [Hop Hr]]]]]]]
                 |[[Hsp [Hop Hr]]
                 |[[crbe [crr [Hsp [Hbs2 [Hop Hr]]]]]
                 |[[cnt2 [cz [Hsp [Himm Hop]]]]
                 |[[cnt3 [cbits [Hsp [Himm Hop]]]]
                 |[[cio [cx [Hsp [Himm Hop]]]]
                 |[[cnt [ctp [ca [co [Hsp [Himm Hop]]]]]]
                 |[[cnt [ctp [ca [co [Hsp [Himm Hop]]]]]]
                 |[[cls [cx2 [cmid [Hsp [Hvec [Himm Hop]]]]]]
                 | [cy [Hsp [Himm Hop]]]]]]]]]]]]]]]];
  rewrite Hb in Hsp; cbn in Hsp; try discriminate Hsp.

(* ================================================================== *)
(** ** What one operator does to the frame list                        *)
(* ================================================================== *)

(** The results a frame pushes onto its parent when it closes. Determined by the
    frame's block type alone, which is what lets an enclosing frame's obligation
    be stated without mentioning the child's body. *)
Definition ctrl_results (c : opiter_Ctrl_t) : list value_type :=
  translate_typelist (block_results_of c.(opiter_Ctrl_block_type)).

(** A step that rewrites the innermost frame: a new operand segment and one more
    instruction, with the fields [ctrl_label], [ctrl_results] and [frame_open]
    read left alone. [unreachable] and [br] are covered because they change only
    the polymorphic flag. *)
Definition adv_plain (C0 : t_context) (st2 : opiter_OpIterState_t)
                     (fs fs' : list fview) (be : basic_instruction) : Prop :=
  exists pre f f',
    fs = pre ++ [f] /\ fs' = pre ++ [f']
    /\ (fv_ctrl f').(opiter_Ctrl_kind) = (fv_ctrl f).(opiter_Ctrl_kind)
    /\ (fv_ctrl f').(opiter_Ctrl_block_type)
       = (fv_ctrl f).(opiter_Ctrl_block_type)
    /\ fv_done f' = fv_done f ++ [be]
    /\ flat_of_one be = [FO_plain be]
    /\ Inv C0 st2 fs'.

Definition adv_push (C0 : t_context) (st2 : opiter_OpIterState_t)
                    (fs fs' : list fview) (kind : opiter_LabelKind_t)
                    (bt : opiter_BlockType_t) : Prop :=
  exists g,
    fs' = fs ++ [g]
    /\ fv_seg g = [] /\ fv_done g = []
    /\ (fv_ctrl g).(opiter_Ctrl_kind) = kind
    /\ (fv_ctrl g).(opiter_Ctrl_block_type) = bt
    /\ (fv_ctrl g).(opiter_Ctrl_polymorphic_base) = false
    /\ Inv C0 st2 fs'.

(** [if] pushes a frame like [block] does, but the condition comes off the
    enclosing frame first, so unlike [adv_push] the frame below the new one is
    rewritten too. Its ghost list is untouched -- the [BI_if] only reaches it
    when the whole [if] closes -- which is what lets [todo_ok_push_if] read the
    pop off the two invariants. *)
Definition adv_if (C0 : t_context) (st2 : opiter_OpIterState_t)
                  (fs fs' : list fview) (bt : opiter_BlockType_t) : Prop :=
  exists pre f f' g,
    fs = pre ++ [f] /\ fs' = (pre ++ [f']) ++ [g]
    /\ fv_ctrl f' = fv_ctrl f /\ fv_done f' = fv_done f
    /\ fv_seg g = [] /\ fv_done g = []
    /\ (fv_ctrl g).(opiter_Ctrl_kind) = Opiter_LabelKind_Then
    /\ (fv_ctrl g).(opiter_Ctrl_block_type) = bt
    /\ (fv_ctrl g).(opiter_Ctrl_polymorphic_base) = false
    /\ Inv C0 st2 fs'.

(** [else] rewrites the innermost frame in place rather than pushing or popping
    one: same block type, kind [Else], and nothing owned yet. *)
Definition adv_else (C0 : t_context) (st2 : opiter_OpIterState_t)
                    (fs fs' : list fview) : Prop :=
  exists pre g g',
    fs = pre ++ [g] /\ fs' = pre ++ [g']
    /\ (fv_ctrl g').(opiter_Ctrl_kind) = Opiter_LabelKind_Else
    /\ (fv_ctrl g').(opiter_Ctrl_block_type)
       = (fv_ctrl g).(opiter_Ctrl_block_type)
    /\ (fv_ctrl g').(opiter_Ctrl_polymorphic_base) = false
    /\ fv_seg g' = [] /\ fv_done g' = []
    /\ Inv C0 st2 fs'.

Definition adv_end (C0 : t_context) (st2 : opiter_OpIterState_t)
                   (fs fs' : list fview) : Prop :=
  exists pre f g f',
    fs = pre ++ [f] ++ [g] /\ fs' = pre ++ [f']
    /\ fv_ctrl f' = fv_ctrl f
    /\ fv_seg f' = fv_seg f
                   ++ results_seg (fv_ctrl g).(opiter_Ctrl_block_type)
    /\ Inv C0 st2 fs'.

(** The body's own [end]: nothing is left on the control stack, and the cursor
    has not moved since [read_op], which is what pins it to the end of the
    body. *)
Definition adv_body_end (st1 st2 : opiter_OpIterState_t)
                        (fs : list fview) : Prop :=
  exists f, fs = [f]
    /\ vec_list st2.(opiter_OpIterState_ctrls) = []
    /\ to_Z st2.(opiter_OpIterState_pos) = to_Z st1.(opiter_OpIterState_pos).

Definition step_shape (C0 : t_context) (st1 st2 : opiter_OpIterState_t)
                      (fs : list fview) (op : flat_op) : Prop :=
  match op with
     | FO_plain be => exists fs', adv_plain C0 st2 fs fs' be
     | FO_block bt => exists fs' bt', translate_bt bt' = bt
                        /\ adv_push C0 st2 fs fs' Opiter_LabelKind_Block bt'
     | FO_loop bt => exists fs' bt', translate_bt bt' = bt
                        /\ adv_push C0 st2 fs fs' Opiter_LabelKind_Loop bt'
     | FO_if bt => exists fs' bt', translate_bt bt' = bt
                        /\ adv_if C0 st2 fs fs' bt'
     | FO_else => exists fs', adv_else C0 st2 fs fs'
     | FO_end => (exists fs', adv_end C0 st2 fs fs') \/ adv_body_end st1 st2 fs
     end.

(** What the checker has to say for the reader to succeed. One clause per
    operator, and for a plain instruction it is just "the checker accepts it
    here", because [check_single]'s own case analysis then hands each reader
    exactly the fact it needs. *)
Definition op_typed (C0 : t_context) (labels : list (list value_type))
                    (f : fview) (op : flat_op) : Prop :=
  match op with
  | FO_plain be => exists ct,
      check_single (with_labels C0 (ctrl_label (fv_ctrl f) :: labels))
                   (Some (fv_ct f)) be = Some ct
  | FO_block _ => True
  | FO_loop _ => True
  (* [if]'s two bodies are not in the operator stream, so the checker fact is
     stated over the instruction the todo list still has: [step_complete] takes
     the condition's [consume] out of it *)
  | FO_if bt => exists es1 es2 ct,
      check_single (with_labels C0 (ctrl_label (fv_ctrl f) :: labels))
                   (Some (fv_ct f)) (BI_if bt es1 es2) = Some ct
  (* [else] closes the then-branch, which is [end]'s obligation over the same
     frame. That the frame is an open then-branch is not a checker fact, but it
     is what the operator stream says: only an [if] puts an [FO_else] there. *)
  | FO_else => (fv_ctrl f).(opiter_Ctrl_kind) = Opiter_LabelKind_Then
               /\ c_types_agree (fv_ct f) (ctrl_results (fv_ctrl f)) = true
  (* the second clause is the bare [if]: an empty else-branch supplies no
     results, so the reader rejects a [Then] frame that declares any *)
  | FO_end => c_types_agree (fv_ct f) (ctrl_results (fv_ctrl f)) = true
              /\ ((fv_ctrl f).(opiter_Ctrl_kind) = Opiter_LabelKind_Then ->
                  block_results_of (fv_ctrl f).(opiter_Ctrl_block_type) = [])
  end.

(* ================================================================== *)
(** ** [check_single], taken apart                                     *)
(* ================================================================== *)

Lemma check_single_local_get_inv : forall C ts x ct,
  check_single C (Some ts) (BI_local_get x) = Some ct ->
  exists xx, lookup_N (tc_locals C) x = Some xx.
Proof.
  intros C ts x ct H. cbn [check_single] in H.
  destruct (lookup_N (tc_locals C) x) as [xx|] eqn:Hlk;
    [exists xx; reflexivity | discriminate].
Qed.

Lemma check_single_local_set_inv : forall C ts x ct,
  check_single C (Some ts) (BI_local_set x) = Some ct ->
  exists xx ct1, lookup_N (tc_locals C) x = Some xx
                 /\ consume ts [xx] = Some ct1.
Proof.
  intros C ts x ct H. cbn [check_single] in H.
  destruct (lookup_N (tc_locals C) x) as [xx|] eqn:Hlk; [|discriminate].
  exists xx. unfold type_update in H.
  destruct (consume ts [xx]) as [ct1|];
    [exists ct1; split; reflexivity | discriminate].
Qed.

Lemma check_single_local_tee_inv : forall C ts x ct,
  check_single C (Some ts) (BI_local_tee x) = Some ct ->
  exists xx ct1, lookup_N (tc_locals C) x = Some xx
                 /\ consume ts [xx] = Some ct1.
Proof.
  intros C ts x ct H. cbn [check_single] in H.
  destruct (lookup_N (tc_locals C) x) as [xx|] eqn:Hlk; [|discriminate].
  exists xx. unfold type_update in H.
  destruct (consume ts [xx]) as [ct1|];
    [exists ct1; split; reflexivity | discriminate].
Qed.

Lemma check_single_global_get_inv : forall C ts x ct,
  check_single C (Some ts) (BI_global_get x) = Some ct ->
  exists xx, lookup_N (tc_globals C) x = Some xx.
Proof.
  intros C ts x ct H. cbn [check_single] in H.
  destruct (lookup_N (tc_globals C) x) as [xx|] eqn:Hlk;
    [exists xx; reflexivity | discriminate].
Qed.

(** The mutability guard sits outside the [type_update], so it is part of what
    an accepting checker run reports. *)
Lemma check_single_global_set_inv : forall C ts x ct,
  check_single C (Some ts) (BI_global_set x) = Some ct ->
  exists xx ct1, lookup_N (tc_globals C) x = Some xx
                 /\ is_mut xx = true
                 /\ consume ts [tg_t xx] = Some ct1.
Proof.
  intros C ts x ct H. cbn [check_single] in H.
  destruct (lookup_N (tc_globals C) x) as [xx|] eqn:Hlk; [|discriminate].
  exists xx. destruct (is_mut xx) eqn:Hmut; [|discriminate].
  unfold type_update in H.
  destruct (consume ts [tg_t xx]) as [ct1|];
    [exists ct1; split; [reflexivity | split; reflexivity] | discriminate].
Qed.

Lemma check_single_call_inv : forall C ts x ct,
  check_single C (Some ts) (BI_call x) = Some ct ->
  exists tn tm ct1, lookup_N (tc_funcs C) x = Some (Tf tn tm)
                    /\ consume ts tn = Some ct1.
Proof.
  intros C ts x ct H. cbn [check_single] in H.
  destruct (lookup_N (tc_funcs C) x) as [tf|] eqn:Hlk; [|discriminate].
  destruct tf as [tn tm]. exists tn, tm. unfold type_update in H.
  destruct (consume ts tn) as [ct1|];
    [exists ct1; split; reflexivity | discriminate].
Qed.

Lemma check_single_memory_size_inv : forall C ts ct,
  check_single C (Some ts) BI_memory_size = Some ct ->
  exists m, lookup_N (tc_mems C) 0%N = Some m.
Proof.
  intros C ts ct H. cbn [check_single] in H.
  destruct (lookup_N (tc_mems C) 0%N) as [m|] eqn:Hm;
    [exists m; reflexivity | discriminate].
Qed.

Lemma check_single_memory_grow_inv : forall C ts ct,
  check_single C (Some ts) BI_memory_grow = Some ct ->
  (exists m, lookup_N (tc_mems C) 0%N = Some m)
  /\ exists ct1, consume ts [T_num T_i32] = Some ct1.
Proof.
  intros C ts ct H. cbn [check_single] in H.
  destruct (lookup_N (tc_mems C) 0%N) as [m|] eqn:Hm; [|discriminate].
  unfold type_update in H.
  destruct (consume ts [T_num T_i32]) as [ct1|] eqn:Hc; [|discriminate].
  split; [exists m; first [exact Hm | reflexivity]|].
  exists ct1. first [exact Hc | reflexivity].
Qed.

Lemma check_single_drop_inv : forall C ts ct,
  check_single C (Some ts) BI_drop = Some ct -> type_update_drop ts = Some ct.
Proof. intros C ts ct H. cbn [check_single] in H. exact H. Qed.

Lemma check_single_select_inv : forall C ts ot ct,
  check_single C (Some ts) (BI_select ot) = Some ct ->
  type_update_select ts ot = Some ct.
Proof. intros C ts ot ct H. cbn [check_single] in H. exact H. Qed.

Lemma check_single_br_inv : forall C ts i ct,
  check_single C (Some ts) (BI_br i) = Some ct ->
  exists xx ct1, lookup_N (tc_labels C) i = Some xx
                 /\ consume ts xx = Some ct1.
Proof.
  intros C ts i ct H. cbn [check_single] in H.
  destruct (lookup_N (tc_labels C) i) as [xx|] eqn:Hl; [|discriminate].
  unfold type_update_top in H.
  destruct (consume ts xx) as [ct1|] eqn:Hc; [|discriminate].
  exists xx, ct1. split;
    [first [exact Hl | reflexivity] | first [exact Hc | reflexivity]].
Qed.

Lemma check_single_br_if_inv : forall C ts i ct,
  check_single C (Some ts) (BI_br_if i) = Some ct ->
  exists xx ct1, lookup_N (tc_labels C) i = Some xx
                 /\ consume ts (T_num T_i32 :: xx) = Some ct1.
Proof.
  intros C ts i ct H. cbn [check_single] in H.
  destruct (lookup_N (tc_labels C) i) as [xx|] eqn:Hl; [|discriminate].
  unfold type_update in H.
  destruct (consume ts (T_num T_i32 :: xx)) as [ct1|] eqn:Hc; [|discriminate].
  exists xx, ct1. split;
    [first [exact Hl | reflexivity] | first [exact Hc | reflexivity]].
Qed.

(** [same_lab] over the table plus its default label, then [br]'s pops with the
    index on top. WasmCert writes the append with [seq.cat]; [cat_app] is the
    bridge to the [List.app] everything else here uses. *)
Lemma check_single_br_table_inv : forall C ts iss i ct,
  check_single C (Some ts) (BI_br_table iss i) = Some ct ->
  exists tls ct1, same_lab (iss ++ [i]) (tc_labels C) = Some tls
                  /\ consume ts (T_num T_i32 :: tls) = Some ct1.
Proof.
  intros C ts iss i ct H. cbn [check_single] in H. rewrite cat_app in H.
  destruct (same_lab (iss ++ [i]) (tc_labels C)) as [tls|] eqn:Hs;
    [|discriminate].
  unfold type_update_top in H.
  destruct (consume ts (T_num T_i32 :: tls)) as [ct1|] eqn:Hc; [|discriminate].
  exists tls, ct1. split;
    [first [exact Hs | reflexivity] | first [exact Hc | reflexivity]].
Qed.

Lemma check_single_return_inv : forall C ts ct,
  check_single C (Some ts) BI_return = Some ct ->
  exists tls ct1, tc_return C = Some tls /\ consume ts tls = Some ct1.
Proof.
  intros C ts ct H. cbn [check_single] in H.
  destruct (tc_return C) as [tls|] eqn:Hr; [|discriminate].
  unfold type_update_top in H.
  destruct (consume ts tls) as [ct1|] eqn:Hc; [|discriminate].
  exists tls, ct1. split;
    [first [exact Hr | reflexivity] | first [exact Hc | reflexivity]].
Qed.

Lemma check_single_load_inv : forall C ts nt tp a o ct,
  check_single C (Some ts) (BI_load nt tp a o) = Some ct ->
  (exists m, lookup_N (tc_mems C) 0%N = Some m)
  /\ load_store_t_bounds a (option_projl tp) nt = true
  /\ exists ct1, consume ts [T_num T_i32] = Some ct1.
Proof.
  intros C ts nt tp a o ct H. cbn [check_single] in H.
  destruct (lookup_N (tc_mems C) 0%N) as [m|] eqn:Hm; [|discriminate].
  destruct (load_store_t_bounds a (option_projl tp) nt) eqn:Hb; [|discriminate].
  unfold type_update in H.
  destruct (consume ts [T_num T_i32]) as [ct1|] eqn:Hc; [|discriminate].
  split; [exists m; first [exact Hm | reflexivity]|].
  split; [first [exact Hb | reflexivity]|].
  exists ct1. first [exact Hc | reflexivity].
Qed.

Lemma check_single_store_inv : forall C ts nt tp a o ct,
  check_single C (Some ts) (BI_store nt tp a o) = Some ct ->
  (exists m, lookup_N (tc_mems C) 0%N = Some m)
  /\ load_store_t_bounds a tp nt = true
  /\ exists ct1, consume ts [T_num nt; T_num T_i32] = Some ct1.
Proof.
  intros C ts nt tp a o ct H. cbn [check_single] in H.
  destruct (lookup_N (tc_mems C) 0%N) as [m|] eqn:Hm; [|discriminate].
  destruct (load_store_t_bounds a tp nt) eqn:Hb; [|discriminate].
  unfold type_update in H.
  destruct (consume ts [T_num nt; T_num T_i32]) as [ct1|] eqn:Hc;
    [|discriminate].
  split; [exists m; first [exact Hm | reflexivity]|].
  split; [first [exact Hb | reflexivity]|].
  exists ct1. first [exact Hc | reflexivity].
Qed.

(** Reading an entry off a reversed mapped list. Kept generic in the element
    types: stating it over [tc_labels] directly leaves [nth_error]'s implicit type
    at [result_type] in one place and at [list value_type] in another, and
    [rewrite] matches on the elaborated term. *)
Lemma nth_error_rev_map_inv : forall {A B} (f : A -> B) (l : list A) n (y : B),
  List.nth_error (List.rev (List.map f l)) n = Some y ->
  (n < List.length l)%nat
  /\ exists x, List.nth_error l (List.length l - 1 - n) = Some x /\ f x = y.
Proof.
  intros A B f l n y H.
  assert (Hn : (n < List.length l)%nat).
  { destruct (Nat.le_gt_cases (List.length l) n) as [Hle|Hgt]; [|exact Hgt].
    exfalso.
    assert (Hnone : List.nth_error (List.rev (List.map f l)) n = None).
    { apply List.nth_error_None. rewrite List.rev_length.
      rewrite List.map_length. exact Hle. }
    rewrite Hnone in H. discriminate H. }
  split; [exact Hn|].
  rewrite (nth_error_rev_map f l n Hn) in H.
  destruct (List.nth_error l (List.length l - 1 - n)) as [x|] eqn:Hx;
    [|discriminate H].
  exists x. split; [first [exact Hx | reflexivity]|].
  cbn [option_map] in H. injection H as <-. reflexivity.
Qed.

(** The converse of [ctx_at_label_lookup]: a label the checker found names a
    control frame, at the index [read_br] reaches for. *)
Lemma ctx_at_label_lookup_inv : forall C0 st n xx,
  List.nth_error (tc_labels (ctx_at C0 st)) n = Some xx ->
  (n < List.length (vec_list st.(opiter_OpIterState_ctrls)))%nat
  /\ exists c,
       List.nth_error (vec_list st.(opiter_OpIterState_ctrls))
         (List.length (vec_list st.(opiter_OpIterState_ctrls)) - 1 - n) = Some c
       /\ ctrl_label c = xx.
Proof.
  intros C0 st n xx H.
  apply (nth_error_rev_map_inv ctrl_label
           (vec_list st.(opiter_OpIterState_ctrls)) n xx). exact H.
Qed.

(** [check_single]'s [BI_if] case: *two* body obligations at once, which is the
    whole reason an [Else] frame carries its then-branch in [fv_then] and its
    todo entry carries the else-branch. The results the enclosing frame gains
    come after the condition is consumed, which is the third component. *)
Lemma check_single_if_inv : forall C ts bt es1 es2 ct,
  check_single C (Some ts) (BI_if (translate_bt bt) es1 es2) = Some ct ->
  (exists ct1,
     List.fold_left
       (check_single (with_labels C
          (translate_typelist (block_results_of bt) :: tc_labels C)))
       es1 (Some <<[], false>>) = Some ct1
     /\ c_types_agree ct1 (translate_typelist (block_results_of bt)) = true)
  /\ (exists ct2,
        List.fold_left
          (check_single (with_labels C
             (translate_typelist (block_results_of bt) :: tc_labels C)))
          es2 (Some <<[], false>>) = Some ct2
        /\ c_types_agree ct2 (translate_typelist (block_results_of bt)) = true)
  /\ exists ct0,
       consume ts [T_num T_i32] = Some ct0
       /\ ct = produce ct0 (translate_typelist (block_results_of bt)).
Proof.
  intros C ts bt es1 es2 ct H.
  assert (Hexp : expand_t C (translate_bt bt)
                 = Some (Tf [] (translate_typelist (block_results_of bt))))
    by (destruct bt; reflexivity).
  cbn [check_single] in H. rewrite Hexp in H. cbn beta iota in H.
  match type of H with
  | (if ?c then _ else _) = _ => destruct c eqn:Hc
  end; [|discriminate H].
  apply Bool.andb_true_iff in Hc as [Hc1 Hc2].
  match type of Hc1 with
  | (match ?e with | Some _ => _ | None => _ end) = true =>
      destruct e as [ct1|] eqn:Hf1
  end; [|discriminate Hc1].
  match type of Hc2 with
  | (match ?e with | Some _ => _ | None => _ end) = true =>
      destruct e as [ct2|] eqn:Hf2
  end; [|discriminate Hc2].
  split; [exists ct1; split; [exact Hf1 | exact Hc1]|].
  split; [exists ct2; split; [exact Hf2 | exact Hc2]|].
  unfold type_update in H.
  destruct (consume ts [T_num T_i32]) as [ct0|] eqn:Hcon; [|discriminate H].
  exists ct0. split; [reflexivity|]. injection H as Hct. rewrite <- Hct.
  reflexivity.
Qed.

(* ================================================================== *)
(** ** The memory branches, once                                       *)
(* ================================================================== *)

(** Fourteen load opcodes and nine store opcodes differ only in the literals they
    pass, so the branch is proved once and applied with those literals. The two
    alignment side conditions are the same fact in both directions: WasmCert
    bounds [2 ^ a] by the access width, the Rust bounds [a] by the natural
    alignment exponent. *)
Lemma load_branch : forall C0 module data st1 pre f ty natural nt tp a o mid ct, Inv C0 st1 (pre ++ [f]) ->
  translate_vt_v ty = T_num nt ->
  (forall x, 0 <= x <= to_Z natural ->
     load_store_t_bounds (Z.to_N x) (option_projl tp) nt = true) ->
  Nat.lt (align_limit (option_projl tp) nt)
         (Nat.pow 2 (S (Z.to_nat (to_Z natural)))) ->
  mems_agree module C0 ->
  repr_memarg (bytes_from data st1.(opiter_OpIterState_pos)) (a, o) mid ->
  check_single (with_labels C0 (ctrl_label (fv_ctrl f) :: labels_after [] pre))
              (Some (fv_ct f)) (BI_load nt tp (Z.to_N a) (Z.to_N o)) = Some ct ->
  room st1 ->
  exists m st2,
    opiter_read_load st1 data module ty natural
      = Ok (Core_result_Result_Ok m, st2)
    /\ exists fs', adv_plain C0 st2 (pre ++ [f]) fs'
                     (BI_load nt tp (Z.to_N a) (Z.to_N o)).
Proof.
  intros C0 module data st1 pre f ty natural nt tp a o mid ct
         Hinv Hnt Hbounds Halim Hmems Hrep Hct Hroom.
  destruct (check_single_load_inv _ _ _ _ _ _ _ Hct)
    as [[m0 Hlk] [Hbnd [ct1 Hcon]]].
  assert (Hlk' : lookup_N (tc_mems C0) 0%N = Some m0) by exact Hlk.
  pose proof (repr_memarg_nonneg _ _ _ _ Hrep) as Hann.
  assert (Hale : a <= to_Z natural).
  { pose proof (load_store_align_bound a (option_projl tp) nt
                  (Z.to_nat (to_Z natural)) Hann Hbnd Halim) as Hb'.
    pose proof (u32_nonneg natural) as Hnn.
    rewrite Z2Nat.id in Hb'; [exact Hb' | exact Hnn]. }
  destruct (read_load_complete C0 st1 pre f data module ty natural a o mid m0 ct1 Hinv Hrep Hmems Hlk' Hale Hcon Hroom)
    as [m [st2 [Hrd [Hmal Hmof]]]].
  exists m, st2. split; [exact Hrd|].
  destruct (step_load C0 st1 (pre ++ [f]) pre f data module ty natural nt tp m st2
              Hinv (eq_refl _) Hmems Hnt Hbounds Hrd) as [seg' Hinv2].
  rewrite Hmal in Hinv2. rewrite Hmof in Hinv2.
  eexists. unfold adv_plain.
  exists pre, f,
    {| fv_ctrl := fv_ctrl f;
       fv_seg := seg' ++ [Opiter_StackType_Val ty];
       fv_done := fv_done f ++ [BI_load nt tp (Z.to_N a) (Z.to_N o)];
       fv_then := fv_then f |}.
  split; [reflexivity|]. split; [reflexivity|].
  cbn [fv_ctrl fv_done]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [apply flat_of_one_load | exact Hinv2].
Qed.

Lemma store_branch : forall C0 module data st1 pre f ty natural nt tp a o mid ct, Inv C0 st1 (pre ++ [f]) ->
  translate_vt_v ty = T_num nt ->
  (forall x, 0 <= x <= to_Z natural ->
     load_store_t_bounds (Z.to_N x) tp nt = true) ->
  Nat.lt (align_limit tp nt) (Nat.pow 2 (S (Z.to_nat (to_Z natural)))) ->
  mems_agree module C0 ->
  repr_memarg (bytes_from data st1.(opiter_OpIterState_pos)) (a, o) mid ->
  check_single (with_labels C0 (ctrl_label (fv_ctrl f) :: labels_after [] pre))
              (Some (fv_ct f)) (BI_store nt tp (Z.to_N a) (Z.to_N o))
    = Some ct ->
  exists m st2,
    opiter_read_store st1 data module ty natural
      = Ok (Core_result_Result_Ok m, st2)
    /\ exists fs', adv_plain C0 st2 (pre ++ [f]) fs'
                     (BI_store nt tp (Z.to_N a) (Z.to_N o)).
Proof.
  intros C0 module data st1 pre f ty natural nt tp a o mid ct
         Hinv Hnt Hbounds Halim Hmems Hrep Hct.
  destruct (check_single_store_inv _ _ _ _ _ _ _ Hct)
    as [[m0 Hlk] [Hbnd [ct1 Hcon]]].
  assert (Hlk' : lookup_N (tc_mems C0) 0%N = Some m0) by exact Hlk.
  pose proof (repr_memarg_nonneg _ _ _ _ Hrep) as Hann.
  assert (Hale : a <= to_Z natural).
  { pose proof (load_store_align_bound a tp nt
                  (Z.to_nat (to_Z natural)) Hann Hbnd Halim) as Hb'.
    pose proof (u32_nonneg natural) as Hnn.
    rewrite Z2Nat.id in Hb'; [exact Hb' | exact Hnn]. }
  assert (Hcon' : consume (fv_ct f)
                    [translate_vt_v ty; translate_vt_v Types_ValueType_I32]
                  = Some ct1) by (rewrite Hnt; exact Hcon).
  destruct (read_store_complete C0 st1 pre f data module ty natural a o mid m0 ct1 Hinv Hrep Hmems Hlk' Hale Hcon')
    as [m [st2 [Hrd [Hmal Hmof]]]].
  exists m, st2. split; [exact Hrd|].
  destruct (step_store C0 st1 (pre ++ [f]) pre f data module ty natural nt tp m
              st2 Hinv (eq_refl _) Hmems Hnt Hbounds Hrd) as [seg' Hinv2].
  rewrite Hmal in Hinv2. rewrite Hmof in Hinv2.
  eexists. unfold adv_plain.
  exists pre, f,
    {| fv_ctrl := fv_ctrl f;
       fv_seg := seg';
       fv_done := fv_done f ++ [BI_store nt tp (Z.to_N a) (Z.to_N o)];
       fv_then := fv_then f |}.
  split; [reflexivity|]. split; [reflexivity|].
  cbn [fv_ctrl fv_done]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [apply flat_of_one_store | exact Hinv2].
Qed.

(* ================================================================== *)
(** ** The dispatch                                                    *)
(* ================================================================== *)

Lemma repr_op_shape : forall bs op rest,
  repr_op bs op rest -> exists b bs' sh, bs = b :: bs' /\ op_spec b = Some sh.
Proof.
  intros bs op rest H. destruct H;
    (eexists; eexists; eexists; split; [reflexivity | eassumption]).
Qed.

(** The alignment side conditions, as in [OpIter_Validate.v]: one tactic per
    natural alignment, each a computation because the exponent ranges over at
    most four values. *)
Local Ltac ls_bounds :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hz := fresh "Hz" in
  intros a Ha; cbn in Ha;
  first [ (assert (Hz : a = 0) by lia; subst a; reflexivity)
        | (assert (Hz : a = 0 \/ a = 1) by lia;
           destruct Hz as [Hz|Hz]; subst a; reflexivity)
        | (assert (Hz : a = 0 \/ a = 1 \/ a = 2) by lia;
           destruct Hz as [Hz|[Hz|Hz]]; subst a; reflexivity)
        | (assert (Hz : a = 0 \/ a = 1 \/ a = 2 \/ a = 3) by lia;
           destruct Hz as [Hz|[Hz|[Hz|Hz]]]; subst a; reflexivity) ].

Local Ltac align_lt := vm_compute; lia.

(** One operator's worth of the code, in the completeness direction: the byte the
    specification put there names an operator, the checker accepts it, so the
    matching reader runs and the frame list advances in one of four ways.

    The shape is [step_op_step]'s, walked in the other order: the code's opcode
    chain decides the branch, and the two lookups of [op_spec] on the same byte
    then collapse, which is what rules out every rule but one. *)
Theorem step_complete :
  forall V (inst : visit_OpVisitor_t V) vis
         C0 bt0 module ctx data st fs pre f b st1 op mid,
  hooks_accept inst ->
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  room st ->
  mems_agree module C0 -> locals_agree ctx C0 ->
  globals_agree module C0 -> return_agree ctx C0 ->
  funcs_agree module C0 -> types_agree module C0 -> tables_agree module C0 ->
  funcs_wasm10 module -> types_wasm10 module ->
  opiter_read_op st data = Ok (Core_result_Result_Ok b, st1) ->
  repr_op (bytes_from data st.(opiter_OpIterState_pos)) op mid ->
  op_typed C0 (labels_after [] pre) f op ->
  exists st2,
    (exists vis2, opiter_step inst st1 data module ctx b vis
                  = Ok (Core_result_Result_Ok tt, st2, vis2))
    /\ step_shape C0 st1 st2 fs op.
Proof.
  intros V inst vis C0 bt0 module ctx data st fs pre f b st1 op mid
         Hacc Hinv Hbfirst Hfs Hroom Hmems Hlocals Hglobals
         Hret Hfuncs Htypes Htables Hfw10 Htw10 Hro Hrop Hty0.
  subst fs.
  (* the hooks, one hypothesis each, so [eauto] can close a hook goal *)
  pose proof Hacc as Hall. unfold hooks_accept in Hall.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  destruct (read_op_state st data _ st1 Hro) as [Hv1 Hc1].
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_fields C0 st st1 _ Hv1 Hc1 Hinv)).
  pose proof (read_op_sound st data b st1 Hro) as Hbytes.
  pose proof (read_op_size st data _ st1 Hro) as Hsz1.
  assert (Hroom1 : room st1) by (unfold room in Hroom |- *; lia).
  destruct (repr_op_shape _ _ _ Hrop) as [b1 [bs1 [sh [Hbs1 Hsp0]]]].
  assert (Hb1 : b1 = to_Z b).
  { rewrite Hbytes in Hbs1. injection Hbs1 as Hb1 _. symmetry. exact Hb1. }
  rewrite Hb1 in Hsp0.
  destruct (repr_op_inv _ _ _ Hrop) as [b0 [bs' [Hbs Hd]]].
  rewrite Hbytes in Hbs. injection Hbs as Hb0 Hbs'.
  rewrite <- Hb0 in Hd. rewrite <- Hbs' in Hd.
  unfold opiter_step.
  (* nop *)
  destruct (b s= opiter_op_nop) eqn:E1.
  { apply scalar_eqb_true in E1.
    assert (Hb : to_Z b = 1) by (rewrite E1; reflexivity).
    op_cases Hd Hb. injection Hsp as Hbe. subst cbe. subst op.
    (* [nop] has no reader: the hook is the whole of the dispatch *)
    exists st1. split; [apply visit_hook_accept; eauto|].
    unfold step_shape.
    eexists. unfold adv_plain.
    exists pre, f, {| fv_ctrl := fv_ctrl f; fv_seg := fv_seg f;
                      fv_done := fv_done f ++ [BI_nop];
                      fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [apply flat_of_one_nop|].
    apply (step_nop C0 st1 (pre ++ [f]) pre f Hinv1 (eq_refl _)). }
  (* unreachable *)
  destruct (b s= opiter_op_unreachable) eqn:E2.
  { apply scalar_eqb_true in E2.
    assert (Hb : to_Z b = 0) by (rewrite E2; reflexivity).
    op_cases Hd Hb. injection Hsp as Hbe. subst cbe. subst op.
    destruct (read_unreachable_complete st1)
      as [st2 Hrd].
    exists st2. split; [eapply visit_wrap_accept; [exact Hrd | eauto]|].
    unfold step_shape.
    eexists. unfold adv_plain.
    exists pre, f,
      {| fv_ctrl := {| opiter_Ctrl_kind := (fv_ctrl f).(opiter_Ctrl_kind);
                       opiter_Ctrl_block_type :=
                         (fv_ctrl f).(opiter_Ctrl_block_type);
                       opiter_Ctrl_value_stack_base :=
                         (fv_ctrl f).(opiter_Ctrl_value_stack_base);
                       opiter_Ctrl_polymorphic_base := true |};
         fv_seg := [];
         fv_done := fv_done f ++ [BI_unreachable];
         fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done opiter_Ctrl_kind opiter_Ctrl_block_type].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [apply flat_of_one_unreachable|].
    apply (step_unreachable C0 st1 (pre ++ [f]) pre f st2 Hinv1 (eq_refl _) Hrd). }
  (* the two integer const operators, one row of [op_spec] each *)
  destruct (b s= opiter_op_i32_const) eqn:E3.
  { apply scalar_eqb_true in E3.
    assert (Hb : to_Z b = 65) by (rewrite E3; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt. subst cnt2.
    cbn [const_bits] in Himm. cbn [const_val] in Hop. subst op.
    destruct (read_i32_const_complete st1 data cz mid Himm Hroom1
               ) as [v [st2 [Hrd Hval]]].
    exists st2. split.
    { eapply visit_wrap_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    pose proof (step_i32_const C0 st1 (pre ++ [f]) pre f data v st2 Hinv1
                  (eq_refl _) Hrd) as Hinv2.
    rewrite Hval in Hinv2.
    eexists. unfold adv_plain.
    exists pre, f,
      {| fv_ctrl := fv_ctrl f;
         fv_seg := fv_seg f ++ [Opiter_StackType_Val Types_ValueType_I32];
         fv_done := fv_done f
                    ++ [BI_const_num (VAL_int32 (Wasm_int.Int32.repr cz))];
         fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [apply flat_of_one_const_num | exact Hinv2]. }
  destruct (b s= opiter_op_i64_const) eqn:E3b.
  { apply scalar_eqb_true in E3b.
    assert (Hb : to_Z b = 66) by (rewrite E3b; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt. subst cnt2.
    cbn [const_bits] in Himm. cbn [const_val] in Hop. subst op.
    destruct (read_i64_const_complete st1 data cz mid Himm Hroom1
               ) as [v [st2 [Hrd Hval]]].
    exists st2. split.
    { eapply visit_wrap_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    pose proof (step_i64_const C0 st1 (pre ++ [f]) pre f data v st2 Hinv1
                  (eq_refl _) Hrd) as Hinv2.
    rewrite Hval in Hinv2.
    eexists. unfold adv_plain.
    exists pre, f,
      {| fv_ctrl := fv_ctrl f;
         fv_seg := fv_seg f ++ [Opiter_StackType_Val Types_ValueType_I64];
         fv_done := fv_done f
                    ++ [BI_const_num (VAL_int64 (Wasm_int.Int64.repr cz))];
         fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [apply flat_of_one_const_num | exact Hinv2]. }
  destruct (b s= opiter_op_f32_const) eqn:E3c.
  { apply scalar_eqb_true in E3c.
    assert (Hb : to_Z b = 67) by (rewrite E3c; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt. subst cnt3.
    cbn [fconst_bytes] in Himm. subst op.
    destruct (read_f32_const_complete st1 data cbits mid Himm Hroom1
               ) as [v [st2 [Hrd Hval]]].
    exists st2. split.
    { eapply visit_wrap_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    pose proof (step_f32_const C0 st1 (pre ++ [f]) pre f data v st2 Hinv1
                  (eq_refl _) Hrd) as Hinv2.
    rewrite Hval in Hinv2.
    eexists. unfold adv_plain.
    exists pre, f,
      {| fv_ctrl := fv_ctrl f;
         fv_seg := fv_seg f ++ [Opiter_StackType_Val Types_ValueType_F32];
         fv_done := fv_done f ++ [BI_const_num (fconst_val T_f32 cbits)];
         fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [apply flat_of_one_const_num | exact Hinv2]. }
  destruct (b s= opiter_op_f64_const) eqn:E3d.
  { apply scalar_eqb_true in E3d.
    assert (Hb : to_Z b = 68) by (rewrite E3d; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt. subst cnt3.
    cbn [fconst_bytes] in Himm. subst op.
    destruct (read_f64_const_complete st1 data cbits mid Himm Hroom1
               ) as [v [st2 [Hrd Hval]]].
    exists st2. split.
    { eapply visit_wrap_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    pose proof (step_f64_const C0 st1 (pre ++ [f]) pre f data v st2 Hinv1
                  (eq_refl _) Hrd) as Hinv2.
    rewrite Hval in Hinv2.
    eexists. unfold adv_plain.
    exists pre, f,
      {| fv_ctrl := fv_ctrl f;
         fv_seg := fv_seg f ++ [Opiter_StackType_Val Types_ValueType_F64];
         fv_done := fv_done f ++ [BI_const_num (fconst_val T_f64 cbits)];
         fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [apply flat_of_one_const_num | exact Hinv2]. }
  (* drop *)
  destruct (b s= opiter_op_drop) eqn:E5.
  { apply scalar_eqb_true in E5.
    assert (Hb : to_Z b = 26) by (rewrite E5; reflexivity).
    op_cases Hd Hb. injection Hsp as Hbe. subst cbe. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    pose proof (check_single_drop_inv _ _ _ Hct) as Hdrop.
    destruct (read_drop_complete C0 st1 pre f ct Hinv1 Hdrop)
      as [t [st2 Hrd]].
    exists st2. split.
    { eapply visit_wrap_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    destruct (step_drop C0 st1 (pre ++ [f]) pre f t st2 Hinv1 (eq_refl _) Hrd)
      as [seg' Hinv2].
    eexists. unfold adv_plain.
    exists pre, f,
      {| fv_ctrl := fv_ctrl f; fv_seg := seg';
         fv_done := fv_done f ++ [BI_drop];
         fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [apply flat_of_one_drop | exact Hinv2]. }
  (* select *)
  destruct (b s= opiter_op_select) eqn:E5s.
  { apply scalar_eqb_true in E5s.
    assert (Hb : to_Z b = 27) by (rewrite E5s; reflexivity).
    op_cases Hd Hb. injection Hsp as Hbe. subst cbe. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    pose proof (check_single_select_inv _ _ _ _ Hct) as Hsel.
    destruct (read_select_complete C0 st1 pre f ct Hinv1 Hsel Hroom1) as [t [st2 Hrd]].
    exists st2. split.
    { eapply visit_wrap_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    destruct (step_select C0 st1 (pre ++ [f]) pre f t st2 Hinv1 (eq_refl _) Hrd)
      as [seg' Hinv2].
    eexists. unfold adv_plain.
    exists pre, f,
      {| fv_ctrl := fv_ctrl f; fv_seg := seg';
         fv_done := fv_done f ++ [BI_select None];
         fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [apply flat_of_one_select | exact Hinv2]. }
  (* block *)
  destruct (b s= opiter_op_block) eqn:E6.
  { apply scalar_eqb_true in E6.
    assert (Hb : to_Z b = 2) by (rewrite E6; reflexivity).
    op_cases Hd Hb. subst op.
    destruct (read_block_complete st1 data cbtb cbt cr Hbs2 Hbtspec Hroom1) as [bt' [st2 [Hrd Htr]]].
    exists st2. split.
    { eapply visit_wrap_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    destruct (step_block C0 st1 (pre ++ [f]) data bt' st2 Hinv1 Hrd)
      as [base Hinv2].
    eexists. exists bt'. split; [exact Htr|]. unfold adv_push.
    exists {| fv_ctrl := {| opiter_Ctrl_kind := Opiter_LabelKind_Block;
                          opiter_Ctrl_block_type := bt';
                          opiter_Ctrl_value_stack_base := base;
                          opiter_Ctrl_polymorphic_base := false |};
             fv_seg := []; fv_done := [];
             fv_then := [] |}.
    split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done opiter_Ctrl_kind opiter_Ctrl_block_type
         opiter_Ctrl_polymorphic_base].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity | exact Hinv2]. }
  (* loop *)
  destruct (b s= opiter_op_loop) eqn:E7.
  { apply scalar_eqb_true in E7.
    assert (Hb : to_Z b = 3) by (rewrite E7; reflexivity).
    op_cases Hd Hb. subst op.
    destruct (read_loop_complete st1 data cbtb cbt cr Hbs2 Hbtspec Hroom1) as [bt' [st2 [Hrd Htr]]].
    exists st2. split.
    { eapply visit_wrap_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    destruct (step_loop C0 st1 (pre ++ [f]) data bt' st2 Hinv1 Hrd)
      as [base Hinv2].
    eexists. exists bt'. split; [exact Htr|]. unfold adv_push.
    exists {| fv_ctrl := {| opiter_Ctrl_kind := Opiter_LabelKind_Loop;
                          opiter_Ctrl_block_type := bt';
                          opiter_Ctrl_value_stack_base := base;
                          opiter_Ctrl_polymorphic_base := false |};
             fv_seg := []; fv_done := [];
             fv_then := [] |}.
    split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done opiter_Ctrl_kind opiter_Ctrl_block_type
         opiter_Ctrl_polymorphic_base].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity | exact Hinv2]. }
  (* if *)
  destruct (b s= opiter_op_if) eqn:E7i.
  { apply scalar_eqb_true in E7i.
    assert (Hb : to_Z b = 4) by (rewrite E7i; reflexivity).
    op_cases Hd Hb. subst op. cbn [op_typed] in Hty0.
    destruct Hty0 as [es1 [es2 [ct Hct]]].
    (* the block type is one [blocktype_spec] admits, so it is a translated one,
       which is what makes WasmCert's [expand_t] compute *)
    destruct (read_block_type_complete data st1.(opiter_OpIterState_pos) cbtb cbt
                cr Hbs2 Hbtspec) as [btw [pw [_ [Htrw _]]]].
    rewrite <- Htrw in Hct.
    destruct (check_single_if_inv _ _ _ _ _ _ Hct) as [_ [_ [ct1 [Hcon _]]]].
    destruct (read_if_complete C0 st1 pre f data cbtb cbt cr ct1 Hinv1 Hbs2 Hbtspec Hcon Hroom1)
      as [bt' [st2 [Hrd Htr]]].
    exists st2. split.
    { eapply visit_wrap_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    destruct (step_if C0 st1 (pre ++ [f]) pre f data bt' st2 Hinv1 (eq_refl _)
                Hrd) as [seg' [base Hinv2]].
    rewrite List.app_assoc in Hinv2.
    eexists. exists bt'. split; [exact Htr|]. unfold adv_if.
    exists pre, f,
      {| fv_ctrl := fv_ctrl f; fv_seg := seg'; fv_done := fv_done f;
         fv_then := fv_then f |},
      {| fv_ctrl := {| opiter_Ctrl_kind := Opiter_LabelKind_Then;
                       opiter_Ctrl_block_type := bt';
                       opiter_Ctrl_value_stack_base := base;
                       opiter_Ctrl_polymorphic_base := false |};
         fv_seg := []; fv_done := []; fv_then := [] |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done opiter_Ctrl_kind opiter_Ctrl_block_type
         opiter_Ctrl_polymorphic_base].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity | exact Hinv2]. }
  (* else *)
  destruct (b s= opiter_op_else) eqn:E7e.
  { apply scalar_eqb_true in E7e.
    assert (Hb : to_Z b = 5) by (rewrite E7e; reflexivity).
    op_cases Hd Hb. subst op. cbn [op_typed] in Hty0.
    destruct Hty0 as [Hkind Hagree]. unfold ctrl_results in Hagree.
    destruct (read_else_complete C0 st1 pre f Hinv1 Hkind Hagree
               ) as [bt [st2 Hrd]].
    exists st2. split.
    { eapply visit_wrap_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    pose proof (step_switch_else C0 st1 (pre ++ [f]) pre f st2 bt Hinv1
                  (eq_refl _) Hkind Hrd) as Hinv2.
    eexists. unfold adv_else. exists pre, f,
      {| fv_ctrl :=
           {| opiter_Ctrl_kind := Opiter_LabelKind_Else;
              opiter_Ctrl_block_type := (fv_ctrl f).(opiter_Ctrl_block_type);
              opiter_Ctrl_value_stack_base :=
                (fv_ctrl f).(opiter_Ctrl_value_stack_base);
              opiter_Ctrl_polymorphic_base := false |};
         fv_seg := []; fv_done := []; fv_then := fv_done f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done opiter_Ctrl_kind opiter_Ctrl_block_type
         opiter_Ctrl_polymorphic_base].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity | exact Hinv2]. }
  (* end: either a nested frame closes or the body's does *)
  destruct (b s= opiter_op_end) eqn:E8.
  { apply scalar_eqb_true in E8.
    assert (Hb : to_Z b = 11) by (rewrite E8; reflexivity).
    op_cases Hd Hb. subst op. cbn [op_typed] in Hty0.
    destruct Hty0 as [Hagree Hthen].
    destruct (read_end_complete C0 st1 pre f Hinv1 Hagree Hthen Hroom1)
      as [r [st2 Hrd]].
    exists st2. split.
    { destruct r as [ekind ebt].
      eapply visit_wrap2_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    destruct (body_first_innermost bt0 (pre ++ [f]) pre f Hbfirst (eq_refl _))
      as [[Hprenil [Hk Hbt]] | [pre2 [f2 [Hfs2 Hkind]]]].
    - (* the body's own [end] *)
      right.
      destruct (end_state C0 st1 (pre ++ [f]) pre f r st2 Hinv1 (eq_refl _) Hrd)
        as [_ [_ [_ [Hc2 _]]]].
      pose proof (read_end_pos st1 _ st2 Hrd) as Hpos. unfold pos_of in Hpos.
      exists f. split; [rewrite Hprenil; reflexivity|].
      split; [rewrite Hc2; rewrite Hprenil; reflexivity|].
      rewrite Hpos. reflexivity.
    - (* a nested frame closed: block, loop, then or else *)
      left. destruct Hkind as [Hkb | [Hkl | [Hkt | Hke]]].
      4: { pose proof (step_end_else C0 st1 (pre ++ [f]) pre2 f2 f r st2 Hinv1
                         Hfs2 Hke Hrd) as Hinv2.
           eexists. unfold adv_end. exists pre2, f2, f.
           exists {| fv_ctrl := fv_ctrl f2;
                     fv_seg := fv_seg f2
                               ++ results_seg
                                    (fv_ctrl f).(opiter_Ctrl_block_type);
                     fv_done :=
                       fv_done f2
                       ++ [BI_if (translate_bt
                                    (fv_ctrl f).(opiter_Ctrl_block_type))
                                 (fv_then f) (fv_done f)];
                     fv_then := fv_then f2 |}.
           split; [exact Hfs2|]. split; [reflexivity|].
           cbn [fv_ctrl fv_seg]. split; [reflexivity|]. split; [reflexivity|].
           exact Hinv2. }
      3: { pose proof (step_end_then C0 st1 (pre ++ [f]) pre2 f2 f r st2 Hinv1
                         Hfs2 Hkt Hrd) as Hinv2.
           eexists. unfold adv_end. exists pre2, f2, f.
           exists {| fv_ctrl := fv_ctrl f2;
                     fv_seg := fv_seg f2
                               ++ results_seg
                                    (fv_ctrl f).(opiter_Ctrl_block_type);
                     fv_done :=
                       fv_done f2
                       ++ [BI_if (translate_bt
                                    (fv_ctrl f).(opiter_Ctrl_block_type))
                                 (fv_done f) []];
                     fv_then := fv_then f2 |}.
           split; [exact Hfs2|]. split; [reflexivity|].
           cbn [fv_ctrl fv_seg]. split; [reflexivity|]. split; [reflexivity|].
           exact Hinv2. }
      + pose proof (step_end_block C0 st1 (pre ++ [f]) pre2 f2 f r st2 Hinv1
                      Hfs2 Hkb Hrd) as Hinv2.
        eexists. unfold adv_end. exists pre2, f2, f.
        exists {| fv_ctrl := fv_ctrl f2;
                  fv_seg := fv_seg f2
                            ++ results_seg (fv_ctrl f).(opiter_Ctrl_block_type);
                  fv_done :=
                    fv_done f2
                    ++ [BI_block (translate_bt
                                    (fv_ctrl f).(opiter_Ctrl_block_type))
                                 (fv_done f)];
                  fv_then := fv_then f2 |}.
        split; [exact Hfs2|]. split; [reflexivity|].
        cbn [fv_ctrl fv_seg]. split; [reflexivity|]. split; [reflexivity|].
        exact Hinv2.
      + pose proof (step_end_loop C0 st1 (pre ++ [f]) pre2 f2 f r st2 Hinv1
                      Hfs2 Hkl Hrd) as Hinv2.
        eexists. unfold adv_end. exists pre2, f2, f.
        exists {| fv_ctrl := fv_ctrl f2;
                  fv_seg := fv_seg f2
                            ++ results_seg (fv_ctrl f).(opiter_Ctrl_block_type);
                  fv_done :=
                    fv_done f2
                    ++ [BI_loop (translate_bt
                                   (fv_ctrl f).(opiter_Ctrl_block_type))
                                (fv_done f)];
                  fv_then := fv_then f2 |}.
        split; [exact Hfs2|]. split; [reflexivity|].
        cbn [fv_ctrl fv_seg]. split; [reflexivity|]. split; [reflexivity|].
        exact Hinv2. }
  (* br *)
  destruct (b s= opiter_op_br) eqn:E9.
  { apply scalar_eqb_true in E9.
    assert (Hb : to_Z b = 12) by (rewrite E9; reflexivity).
    op_cases Hd Hb. injection Hsp as Hio. subst cio. subst op.
    cbn [op_typed idx_instr] in Hty0. destruct Hty0 as [ct Hct].
    destruct (check_single_br_inv _ _ _ _ Hct) as [xx [ct1 [Hlk Hcon]]].
    assert (Hlbls : tc_labels (ctx_at C0 st1)
                    = ctrl_label (fv_ctrl f) :: labels_after [] pre).
    { destruct Hinv1 as [K1 _].
      pose proof (labels_after_ctx_at C0 st1 (pre ++ [f]) K1) as Hla.
      rewrite (labels_after_snoc [] pre f) in Hla. symmetry. exact Hla. }
    assert (Hlk2 : List.nth_error (tc_labels (ctx_at C0 st1)) (Z.to_nat cx)
                   = Some xx).
    { rewrite Hlbls. unfold lookup_N in Hlk. rewrite N_to_nat_Z_to_N in Hlk.
      exact Hlk. }
    destruct (ctx_at_label_lookup_inv C0 st1 (Z.to_nat cx) xx Hlk2)
      as [Hlt [c [Hnth Hcl]]].
    assert (Hcon' : consume (fv_ct f) (translate_typelist (ctrl_target c))
                    = Some ct1).
    { unfold ctrl_label in Hcl. rewrite Hcl. exact Hcon. }
    destruct (read_br_complete C0 st1 pre f data cx mid c ct1 Hinv1 Himm Hlt Hnth Hcon')
      as [depth [bt' [st2 [Hrd Hdepth]]]].
    exists st2. split.
    { eapply visit_wrap2_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    pose proof (step_br C0 st1 (pre ++ [f]) pre f data depth bt' st2 Hinv1
                  (eq_refl _) Hrd) as Hinv2.
    rewrite Hdepth in Hinv2.
    eexists. unfold adv_plain.
    exists pre, f,
      {| fv_ctrl := {| opiter_Ctrl_kind := (fv_ctrl f).(opiter_Ctrl_kind);
                       opiter_Ctrl_block_type :=
                         (fv_ctrl f).(opiter_Ctrl_block_type);
                       opiter_Ctrl_value_stack_base :=
                         (fv_ctrl f).(opiter_Ctrl_value_stack_base);
                       opiter_Ctrl_polymorphic_base := true |};
         fv_seg := [];
         fv_done := fv_done f ++ [BI_br (Z.to_N cx)];
         fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done opiter_Ctrl_kind opiter_Ctrl_block_type].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [apply flat_of_one_br | exact Hinv2]. }
  (* br_if: the same lookup, and the pops come from one [consume] *)
  destruct (b s= opiter_op_br_if) eqn:E9b.
  { apply scalar_eqb_true in E9b.
    assert (Hb : to_Z b = 13) by (rewrite E9b; reflexivity).
    op_cases Hd Hb. injection Hsp as Hio. subst cio. subst op.
    cbn [op_typed idx_instr] in Hty0. destruct Hty0 as [ct Hct].
    destruct (check_single_br_if_inv _ _ _ _ Hct) as [xx [ct1 [Hlk Hcon]]].
    assert (Hlbls : tc_labels (ctx_at C0 st1)
                    = ctrl_label (fv_ctrl f) :: labels_after [] pre).
    { destruct Hinv1 as [K1 _].
      pose proof (labels_after_ctx_at C0 st1 (pre ++ [f]) K1) as Hla.
      rewrite (labels_after_snoc [] pre f) in Hla. symmetry. exact Hla. }
    assert (Hlk2 : List.nth_error (tc_labels (ctx_at C0 st1)) (Z.to_nat cx)
                   = Some xx).
    { rewrite Hlbls. unfold lookup_N in Hlk. rewrite N_to_nat_Z_to_N in Hlk.
      exact Hlk. }
    destruct (ctx_at_label_lookup_inv C0 st1 (Z.to_nat cx) xx Hlk2)
      as [Hlt [c [Hnth Hcl]]].
    assert (Hcon' : consume (fv_ct f)
                      (T_num T_i32 :: translate_typelist (ctrl_target c))
                    = Some ct1).
    { unfold ctrl_label in Hcl. rewrite Hcl. exact Hcon. }
    destruct (read_br_if_complete C0 st1 pre f data cx mid c ct1 Hinv1 Himm Hlt Hnth Hcon' Hroom1)
      as [depth [bt' [st2 [Hrd Hdepth]]]].
    exists st2. split.
    { eapply visit_wrap2_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    destruct (step_br_if C0 st1 (pre ++ [f]) pre f data depth bt' st2 Hinv1
                (eq_refl _) Hrd) as [seg' Hinv2].
    rewrite Hdepth in Hinv2.
    eexists. unfold adv_plain.
    exists pre, f,
      {| fv_ctrl := fv_ctrl f; fv_seg := seg';
         fv_done := fv_done f ++ [BI_br_if (Z.to_N cx)];
         fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [apply flat_of_one_br_if | exact Hinv2]. }
  (* br_table: every label looks up to the same list, so they all have the same
     branch target and the reader's running comparison never fails *)
  destruct (b s= opiter_op_br_table) eqn:E9t.
  { apply scalar_eqb_true in E9t.
    assert (Hb : to_Z b = 14) by (rewrite E9t; reflexivity).
    op_cases Hd Hb. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (check_single_br_table_inv _ _ _ _ _ Hct) as [tls [ct1 [Hsame Hcon]]].
    assert (Hlbls : tc_labels (ctx_at C0 st1)
                    = ctrl_label (fv_ctrl f) :: labels_after [] pre).
    { destruct Hinv1 as [K1 _].
      pose proof (labels_after_ctx_at C0 st1 (pre ++ [f]) K1) as Hla.
      rewrite (labels_after_snoc [] pre f) in Hla. symmetry. exact Hla. }
    (* the default label first: its frame fixes the common branch target *)
    assert (Hres : forall d, List.In d (cls ++ [cx2]) ->
              exists c,
                (Z.to_nat d
                 < List.length (vec_list st1.(opiter_OpIterState_ctrls)))%nat
                /\ List.nth_error (vec_list st1.(opiter_OpIterState_ctrls))
                     (List.length (vec_list st1.(opiter_OpIterState_ctrls))
                      - 1 - Z.to_nat d) = Some c
                /\ ctrl_label c = tls).
    { intros d Hd.
      assert (Hin : List.In (Z.to_N d) (List.map Z.to_N cls ++ [Z.to_N cx2])).
      { apply List.in_or_app. apply List.in_app_or in Hd.
        destruct Hd as [Hd|Hd]; [left; apply List.in_map; exact Hd|].
        right. destruct Hd as [Hd|Hd];
          [left; rewrite Hd; reflexivity | contradiction]. }
      pose proof (same_lab_inv _ _ _ Hsame _ Hin) as Hlk.
      assert (Hlk2 : List.nth_error (tc_labels (ctx_at C0 st1)) (Z.to_nat d)
                     = Some tls).
      { rewrite Hlbls. unfold lookup_N in Hlk. rewrite N_to_nat_Z_to_N in Hlk.
        exact Hlk. }
      destruct (ctx_at_label_lookup_inv C0 st1 (Z.to_nat d) tls Hlk2)
        as [Hlt [c [Hnth Hcl]]].
      exists c. split; [exact Hlt|]. split; [exact Hnth | exact Hcl]. }
    destruct (Hres cx2 (ltac:(apply List.in_or_app; right; left; reflexivity)))
      as [cdef [Hltd [Hnthd Hcld]]].
    (* every label shares that target, because they share a label list *)
    assert (Hall : List.Forall
                     (fun d => depth_target st1 d (branch_target_bt_of cdef))
                     (cls ++ [cx2])).
    { apply List.Forall_forall. intros d Hd.
      destruct (Hres d Hd) as [c [Hlt [Hnth Hcl]]].
      exists c. split; [exact Hlt|]. split; [exact Hnth|].
      apply ctrl_label_bt_inj. rewrite Hcl. rewrite Hcld. reflexivity. }
    assert (Hcon' : consume (fv_ct f)
                      (T_num T_i32
                       :: translate_typelist
                            (block_results_of (branch_target_bt_of cdef)))
                    = Some ct1)
      by (unfold ctrl_label, ctrl_target in Hcld; rewrite Hcld; exact Hcon).
    destruct (read_br_table_complete V inst vis C0 st1 pre f data cls cx2 cmid
                mid (branch_target_bt_of cdef) ct1 Hacc Hinv1 Hvec Himm Hall
                Hcon') as [dflt [st2 [vis1 Hrd]]].
    exists st2. split.
    { eapply visit_wrapv_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    pose proof (step_br_table V inst vis vis1 dflt C0 st1 (pre ++ [f]) pre f data
                  cls cx2 (branch_target_bt_of cdef) st2 Hinv1 (eq_refl _) Hall
                  Hrd)
      as Hinv2.
    eexists. unfold adv_plain.
    exists pre, f,
      {| fv_ctrl := {| opiter_Ctrl_kind := (fv_ctrl f).(opiter_Ctrl_kind);
                       opiter_Ctrl_block_type :=
                         (fv_ctrl f).(opiter_Ctrl_block_type);
                       opiter_Ctrl_value_stack_base :=
                         (fv_ctrl f).(opiter_Ctrl_value_stack_base);
                       opiter_Ctrl_polymorphic_base := true |};
         fv_seg := [];
         fv_done := fv_done f
                    ++ [BI_br_table (List.map Z.to_N cls) (Z.to_N cx2)];
         fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done opiter_Ctrl_kind opiter_Ctrl_block_type].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [apply flat_of_one_br_table | exact Hinv2]. }
  (* return: the result list is the context's, and the pops are its consume *)
  destruct (b s= opiter_op_return) eqn:E9r.
  { apply scalar_eqb_true in E9r.
    assert (Hb : to_Z b = 15) by (rewrite E9r; reflexivity).
    op_cases Hd Hb. injection Hsp as Hbe. subst cbe. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (check_single_return_inv _ _ _ Hct) as [tls [ct1 [Hrc Hcon]]].
    cbn [with_labels tc_return] in Hrc.
    (* the context's list is the one the checker looked up *)
    unfold return_agree in Hret.
    assert (Htls : tls
                   = translate_typelist
                       (vec_list ctx.(opiter_Context_results)))
      by (rewrite Hret in Hrc; injection Hrc as Hrc; symmetry; exact Hrc).
    rewrite Htls in Hcon.
    destruct (read_return_complete C0 ctx st1 pre f ct1 Hinv1 Hcon) as [st2 Hrd].
    exists st2. split.
    { eapply visit_wrap_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    pose proof (step_return C0 ctx st1 (pre ++ [f]) pre f st2 Hinv1
                  (eq_refl _) Hret Hrd) as Hinv2.
    eexists. unfold adv_plain.
    exists pre, f,
      {| fv_ctrl := {| opiter_Ctrl_kind := (fv_ctrl f).(opiter_Ctrl_kind);
                       opiter_Ctrl_block_type :=
                         (fv_ctrl f).(opiter_Ctrl_block_type);
                       opiter_Ctrl_value_stack_base :=
                         (fv_ctrl f).(opiter_Ctrl_value_stack_base);
                       opiter_Ctrl_polymorphic_base := true |};
         fv_seg := [];
         fv_done := fv_done f ++ [BI_return];
         fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done opiter_Ctrl_kind opiter_Ctrl_block_type].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [apply flat_of_one_return | exact Hinv2]. }
  (* the three local operators: the index is the immediate and the lookup is
     the one the checker performed *)
  (* the two call operators: the callee's signature comes from the context *)
  destruct (b s= opiter_op_call) eqn:EC1.
  { apply scalar_eqb_true in EC1.
    assert (Hb : to_Z b = 16) by (rewrite EC1; reflexivity).
    op_cases Hd Hb. injection Hsp as Hio. subst cio. subst op.
    cbn [op_typed idx_instr] in Hty0. destruct Hty0 as [ct Hct].
    destruct (check_single_call_inv _ _ _ _ Hct) as [tn [tm [ct1 [Hlk Hcon]]]].
    cbn [with_labels tc_funcs] in Hlk.
    destruct (read_call_complete C0 module st1 pre f data cx mid tn tm ct1 Hinv1 Hfuncs Hfw10 Himm Hlk Hcon Hroom1)
      as [idx [st2 [Hrd Hidx]]].
    exists st2. split.
    { eapply visit_wrap_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    destruct (step_call C0 module st1 (pre ++ [f]) pre f data idx st2
                Hinv1 (eq_refl _) Hfuncs Hrd) as [seg' Hinv2].
    rewrite Hidx in Hinv2.
    eexists. unfold adv_plain.
    exists pre, f,
      {| fv_ctrl := fv_ctrl f;
         fv_seg := seg';
         fv_done := fv_done f ++ [BI_call (Z.to_N cx)];
         fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity | exact Hinv2]. }
  destruct (b s= opiter_op_call_indirect) eqn:EC2.
  { apply scalar_eqb_true in EC2.
    assert (Hb : to_Z b = 17) by (rewrite EC2; reflexivity).
    op_cases Hd Hb. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (check_single_call_indirect_inv _ _ _ _ _ Hct)
      as [tabt [tn [tm [ct1 [Htlk [Helem [Hlk Hcon]]]]]]].
    cbn [with_labels tc_tables tc_types] in Htlk, Hlk.
    destruct (read_call_indirect_complete C0 module st1 pre f data cy mid tabt tn tm ct1 Hinv1 Htypes Htables Htw10 Himm Htlk Hlk Hcon Hroom1) as [idx [st2 [Hrd Hidx]]].
    exists st2. split.
    { eapply visit_wrap_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    destruct (step_call_indirect C0 module st1 (pre ++ [f]) pre f data idx st2
                Hinv1 (eq_refl _) Htypes Htables Hrd) as [seg' Hinv2].
    rewrite Hidx in Hinv2.
    eexists. unfold adv_plain.
    exists pre, f,
      {| fv_ctrl := fv_ctrl f;
         fv_seg := seg';
         fv_done := fv_done f ++ [BI_call_indirect 0%N (Z.to_N cy)];
         fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity | exact Hinv2]. }
  destruct (b s= opiter_op_local_get) eqn:EL1.
  { apply scalar_eqb_true in EL1.
    assert (Hb : to_Z b = 32) by (rewrite EL1; reflexivity).
    op_cases Hd Hb. injection Hsp as Hio. subst cio. subst op.
    cbn [op_typed idx_instr] in Hty0. destruct Hty0 as [ct Hct].
    destruct (check_single_local_get_inv _ _ _ _ Hct) as [xx Hlk].
    cbn [with_labels tc_locals] in Hlk.
    destruct (read_local_get_complete C0 ctx st1 pre f data cx mid xx Hinv1 Hlocals Himm Hlk Hroom1)
      as [idx [st2 [Hrd Hidx]]].
    exists st2. split.
    { eapply visit_wrap_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    destruct (step_local_get C0 ctx st1 (pre ++ [f]) pre f data idx st2
                Hinv1 (eq_refl _) Hlocals Hrd) as [t Hinv2].
    rewrite Hidx in Hinv2.
    eexists. unfold adv_plain.
    exists pre, f,
      {| fv_ctrl := fv_ctrl f;
         fv_seg := fv_seg f ++ [Opiter_StackType_Val t];
         fv_done := fv_done f ++ [BI_local_get (Z.to_N cx)];
         fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity | exact Hinv2]. }
  destruct (b s= opiter_op_local_set) eqn:EL2.
  { apply scalar_eqb_true in EL2.
    assert (Hb : to_Z b = 33) by (rewrite EL2; reflexivity).
    op_cases Hd Hb. injection Hsp as Hio. subst cio. subst op.
    cbn [op_typed idx_instr] in Hty0. destruct Hty0 as [ct Hct].
    destruct (check_single_local_set_inv _ _ _ _ Hct) as [xx [ct1 [Hlk Hcon]]].
    cbn [with_labels tc_locals] in Hlk.
    destruct (read_local_set_complete C0 ctx st1 pre f data cx mid xx ct1 Hinv1 Hlocals Himm Hlk Hcon)
      as [idx [st2 [Hrd Hidx]]].
    exists st2. split.
    { eapply visit_wrap_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    destruct (step_local_set C0 ctx st1 (pre ++ [f]) pre f data idx st2
                Hinv1 (eq_refl _) Hlocals Hrd) as [seg' Hinv2].
    rewrite Hidx in Hinv2.
    eexists. unfold adv_plain.
    exists pre, f,
      {| fv_ctrl := fv_ctrl f; fv_seg := seg';
         fv_done := fv_done f ++ [BI_local_set (Z.to_N cx)];
         fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity | exact Hinv2]. }
  destruct (b s= opiter_op_local_tee) eqn:EL3.
  { apply scalar_eqb_true in EL3.
    assert (Hb : to_Z b = 34) by (rewrite EL3; reflexivity).
    op_cases Hd Hb. injection Hsp as Hio. subst cio. subst op.
    cbn [op_typed idx_instr] in Hty0. destruct Hty0 as [ct Hct].
    destruct (check_single_local_tee_inv _ _ _ _ Hct) as [xx [ct1 [Hlk Hcon]]].
    cbn [with_labels tc_locals] in Hlk.
    destruct (read_local_tee_complete C0 ctx st1 pre f data cx mid xx ct1 Hinv1 Hlocals Himm Hlk Hcon Hroom1)
      as [idx [st2 [Hrd Hidx]]].
    exists st2. split.
    { eapply visit_wrap_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    destruct (step_local_tee C0 ctx st1 (pre ++ [f]) pre f data idx st2
                Hinv1 (eq_refl _) Hlocals Hrd) as [seg' [t Hinv2]].
    rewrite Hidx in Hinv2.
    eexists. unfold adv_plain.
    exists pre, f,
      {| fv_ctrl := fv_ctrl f;
         fv_seg := seg' ++ [Opiter_StackType_Val t];
         fv_done := fv_done f ++ [BI_local_tee (Z.to_N cx)];
         fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity | exact Hinv2]. }
  (* the two global operators, with the mutability guard on the set *)
  destruct (b s= opiter_op_global_get) eqn:EG1.
  { apply scalar_eqb_true in EG1.
    assert (Hb : to_Z b = 35) by (rewrite EG1; reflexivity).
    op_cases Hd Hb. injection Hsp as Hio. subst cio. subst op.
    cbn [op_typed idx_instr] in Hty0. destruct Hty0 as [ct Hct].
    destruct (check_single_global_get_inv _ _ _ _ Hct) as [xx Hlk].
    cbn [with_labels tc_globals] in Hlk.
    destruct (read_global_get_complete C0 module st1 pre f data cx mid xx Hinv1 Hglobals Himm Hlk Hroom1)
      as [idx [st2 [Hrd Hidx]]].
    exists st2. split.
    { eapply visit_wrap_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    destruct (step_global_get C0 module st1 (pre ++ [f]) pre f data idx st2
                Hinv1 (eq_refl _) Hglobals Hrd) as [t Hinv2].
    rewrite Hidx in Hinv2.
    eexists. unfold adv_plain.
    exists pre, f,
      {| fv_ctrl := fv_ctrl f;
         fv_seg := fv_seg f ++ [Opiter_StackType_Val t];
         fv_done := fv_done f ++ [BI_global_get (Z.to_N cx)];
         fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity | exact Hinv2]. }
  destruct (b s= opiter_op_global_set) eqn:EG2.
  { apply scalar_eqb_true in EG2.
    assert (Hb : to_Z b = 36) by (rewrite EG2; reflexivity).
    op_cases Hd Hb. injection Hsp as Hio. subst cio. subst op.
    cbn [op_typed idx_instr] in Hty0. destruct Hty0 as [ct Hct].
    destruct (check_single_global_set_inv _ _ _ _ Hct)
      as [xx [ct1 [Hlk [Hmut Hcon]]]].
    cbn [with_labels tc_globals] in Hlk.
    destruct (read_global_set_complete C0 module st1 pre f data cx mid xx ct1 Hinv1 Hglobals Himm Hlk Hmut Hcon)
      as [idx [st2 [Hrd Hidx]]].
    exists st2. split.
    { eapply visit_wrap_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    destruct (step_global_set C0 module st1 (pre ++ [f]) pre f data idx st2
                Hinv1 (eq_refl _) Hglobals Hrd) as [seg' Hinv2].
    rewrite Hidx in Hinv2.
    eexists. unfold adv_plain.
    exists pre, f,
      {| fv_ctrl := fv_ctrl f; fv_seg := seg';
         fv_done := fv_done f ++ [BI_global_set (Z.to_N cx)];
         fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity | exact Hinv2]. }
  unfold opiter_step_memory.
  destruct (b s= opiter_op_i32_load) eqn:E10.
  { apply scalar_eqb_true in E10.
    assert (Hb : to_Z b = 40) by (rewrite E10; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (load_branch C0 module data st1 pre f Types_ValueType_I32 2%u32 T_i32 None ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct Hroom1
               ) as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  destruct (b s= opiter_op_i64_load) eqn:E11.
  { apply scalar_eqb_true in E11.
    assert (Hb : to_Z b = 41) by (rewrite E11; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (load_branch C0 module data st1 pre f Types_ValueType_I64 3%u32 T_i64 None ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct Hroom1
               ) as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  destruct (b s= opiter_op_f32_load) eqn:E12.
  { apply scalar_eqb_true in E12.
    assert (Hb : to_Z b = 42) by (rewrite E12; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (load_branch C0 module data st1 pre f Types_ValueType_F32 2%u32 T_f32 None ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct Hroom1
               ) as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  destruct (b s= opiter_op_f64_load) eqn:E13.
  { apply scalar_eqb_true in E13.
    assert (Hb : to_Z b = 43) by (rewrite E13; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (load_branch C0 module data st1 pre f Types_ValueType_F64 3%u32 T_f64 None ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct Hroom1
               ) as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  destruct (b s= opiter_op_i32_load8_s) eqn:E14.
  { apply scalar_eqb_true in E14.
    assert (Hb : to_Z b = 44) by (rewrite E14; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (load_branch C0 module data st1 pre f Types_ValueType_I32 0%u32 T_i32 (Some (Tp_i8, SX_S))
                ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct Hroom1
               ) as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  destruct (b s= opiter_op_i32_load8_u) eqn:E15.
  { apply scalar_eqb_true in E15.
    assert (Hb : to_Z b = 45) by (rewrite E15; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (load_branch C0 module data st1 pre f Types_ValueType_I32 0%u32 T_i32 (Some (Tp_i8, SX_U))
                ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct Hroom1
               ) as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  destruct (b s= opiter_op_i32_load16_s) eqn:E16.
  { apply scalar_eqb_true in E16.
    assert (Hb : to_Z b = 46) by (rewrite E16; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (load_branch C0 module data st1 pre f Types_ValueType_I32 1%u32 T_i32 (Some (Tp_i16, SX_S))
                ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct Hroom1
               ) as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  destruct (b s= opiter_op_i32_load16_u) eqn:E17.
  { apply scalar_eqb_true in E17.
    assert (Hb : to_Z b = 47) by (rewrite E17; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (load_branch C0 module data st1 pre f Types_ValueType_I32 1%u32 T_i32 (Some (Tp_i16, SX_U))
                ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct Hroom1
               ) as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  destruct (b s= opiter_op_i64_load8_s) eqn:E18.
  { apply scalar_eqb_true in E18.
    assert (Hb : to_Z b = 48) by (rewrite E18; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (load_branch C0 module data st1 pre f Types_ValueType_I64 0%u32 T_i64 (Some (Tp_i8, SX_S))
                ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct Hroom1
               ) as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  destruct (b s= opiter_op_i64_load8_u) eqn:E19.
  { apply scalar_eqb_true in E19.
    assert (Hb : to_Z b = 49) by (rewrite E19; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (load_branch C0 module data st1 pre f Types_ValueType_I64 0%u32 T_i64 (Some (Tp_i8, SX_U))
                ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct Hroom1
               ) as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  destruct (b s= opiter_op_i64_load16_s) eqn:E20.
  { apply scalar_eqb_true in E20.
    assert (Hb : to_Z b = 50) by (rewrite E20; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (load_branch C0 module data st1 pre f Types_ValueType_I64 1%u32 T_i64 (Some (Tp_i16, SX_S))
                ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct Hroom1
               ) as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  destruct (b s= opiter_op_i64_load16_u) eqn:E21.
  { apply scalar_eqb_true in E21.
    assert (Hb : to_Z b = 51) by (rewrite E21; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (load_branch C0 module data st1 pre f Types_ValueType_I64 1%u32 T_i64 (Some (Tp_i16, SX_U))
                ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct Hroom1
               ) as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  destruct (b s= opiter_op_i64_load32_s) eqn:E22.
  { apply scalar_eqb_true in E22.
    assert (Hb : to_Z b = 52) by (rewrite E22; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (load_branch C0 module data st1 pre f Types_ValueType_I64 2%u32 T_i64 (Some (Tp_i32, SX_S))
                ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct Hroom1
               ) as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  destruct (b s= opiter_op_i64_load32_u) eqn:E23.
  { apply scalar_eqb_true in E23.
    assert (Hb : to_Z b = 53) by (rewrite E23; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (load_branch C0 module data st1 pre f Types_ValueType_I64 2%u32 T_i64 (Some (Tp_i32, SX_U))
                ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct Hroom1
               ) as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  destruct (b s= opiter_op_i32_store) eqn:E24.
  { apply scalar_eqb_true in E24.
    assert (Hb : to_Z b = 54) by (rewrite E24; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (store_branch C0 module data st1 pre f Types_ValueType_I32 2%u32 T_i32 None ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct)
      as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  destruct (b s= opiter_op_i64_store) eqn:E25.
  { apply scalar_eqb_true in E25.
    assert (Hb : to_Z b = 55) by (rewrite E25; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (store_branch C0 module data st1 pre f Types_ValueType_I64 3%u32 T_i64 None ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct)
      as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  destruct (b s= opiter_op_f32_store) eqn:E26.
  { apply scalar_eqb_true in E26.
    assert (Hb : to_Z b = 56) by (rewrite E26; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (store_branch C0 module data st1 pre f Types_ValueType_F32 2%u32 T_f32 None ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct)
      as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  destruct (b s= opiter_op_f64_store) eqn:E27.
  { apply scalar_eqb_true in E27.
    assert (Hb : to_Z b = 57) by (rewrite E27; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (store_branch C0 module data st1 pre f Types_ValueType_F64 3%u32 T_f64 None ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct)
      as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  destruct (b s= opiter_op_i32_store8) eqn:E28.
  { apply scalar_eqb_true in E28.
    assert (Hb : to_Z b = 58) by (rewrite E28; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (store_branch C0 module data st1 pre f Types_ValueType_I32 0%u32 T_i32 (Some Tp_i8)
                ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct)
      as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  destruct (b s= opiter_op_i32_store16) eqn:E29.
  { apply scalar_eqb_true in E29.
    assert (Hb : to_Z b = 59) by (rewrite E29; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (store_branch C0 module data st1 pre f Types_ValueType_I32 1%u32 T_i32 (Some Tp_i16)
                ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct)
      as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  destruct (b s= opiter_op_i64_store8) eqn:E30.
  { apply scalar_eqb_true in E30.
    assert (Hb : to_Z b = 60) by (rewrite E30; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (store_branch C0 module data st1 pre f Types_ValueType_I64 0%u32 T_i64 (Some Tp_i8)
                ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct)
      as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  destruct (b s= opiter_op_i64_store16) eqn:E31.
  { apply scalar_eqb_true in E31.
    assert (Hb : to_Z b = 61) by (rewrite E31; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (store_branch C0 module data st1 pre f Types_ValueType_I64 1%u32 T_i64 (Some Tp_i16)
                ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct)
      as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  destruct (b s= opiter_op_i64_store32) eqn:E32.
  { apply scalar_eqb_true in E32.
    assert (Hb : to_Z b = 62) by (rewrite E32; reflexivity).
    op_cases Hd Hb. injection Hsp as Hnt0 Htp0. subst cnt. subst ctp. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (store_branch C0 module data st1 pre f Types_ValueType_I64 2%u32 T_i64 (Some Tp_i32)
                ca co mid ct Hinv1 (eq_refl _) (ltac:(ls_bounds))
                (ltac:(align_lt)) Hmems Himm Hct)
      as [m [st2 [Hrd Hadv]]].
    exists st2. split.
    { eapply visit_wrap_accept;
        [exact Hrd | intros; apply visit_memory_accept; exact Hacc]. }
    unfold step_shape. exact Hadv. }
  (* memory.size and memory.grow: the immediate is the reserved zero byte, and
     the memory the checker looked up is the one the context has *)
  destruct (b s= opiter_op_memory_size) eqn:EM1.
  { apply scalar_eqb_true in EM1.
    assert (Hb : to_Z b = 63) by (rewrite EM1; reflexivity).
    op_cases Hd Hb. injection Hsp as Hbe. subst crbe. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (check_single_memory_size_inv _ _ _ Hct) as [m Hlk].
    cbn [with_labels tc_mems] in Hlk.
    destruct (read_memory_size_complete C0 module st1 pre f data m crr Hinv1 Hbs2 Hmems Hlk Hroom1) as [st2 Hrd].
    exists st2. split.
    { eapply visit_wrap_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    pose proof (step_memory_size C0 module st1 (pre ++ [f]) pre f data st2
                  Hinv1 (eq_refl _) Hmems Hrd) as Hinv2.
    eexists. unfold adv_plain.
    exists pre, f,
      {| fv_ctrl := fv_ctrl f;
         fv_seg := fv_seg f ++ [Opiter_StackType_Val Types_ValueType_I32];
         fv_done := fv_done f ++ [BI_memory_size];
         fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity | exact Hinv2]. }
  destruct (b s= opiter_op_memory_grow) eqn:EM2.
  { apply scalar_eqb_true in EM2.
    assert (Hb : to_Z b = 64) by (rewrite EM2; reflexivity).
    op_cases Hd Hb. injection Hsp as Hbe. subst crbe. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (check_single_memory_grow_inv _ _ _ Hct) as [[m Hlk] [ct1 Hcon]].
    cbn [with_labels tc_mems] in Hlk.
    destruct (read_memory_grow_complete C0 module st1 pre f data m crr ct1 Hinv1 Hbs2 Hmems Hlk Hcon Hroom1) as [st2 Hrd].
    exists st2. split.
    { eapply visit_wrap_accept; [exact Hrd | eauto]. }
    unfold step_shape.
    destruct (step_memory_grow C0 module st1 (pre ++ [f]) pre f data st2
                Hinv1 (eq_refl _) Hmems Hrd) as [seg' Hinv2].
    eexists. unfold adv_plain.
    exists pre, f,
      {| fv_ctrl := fv_ctrl f;
         fv_seg := seg' ++ [Opiter_StackType_Val Types_ValueType_I32];
         fv_done := fv_done f ++ [BI_memory_grow];
         fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity | exact Hinv2]. }
  (* the numeric opcodes, through the table: the row names the instruction and
     supplies its typing effect, so one branch covers the whole block *)
  unfold opiter_step_numeric.
  destruct (convert_types_ok b) as [o Hcv]. rewrite Hcv. cbn [bind].
  destruct o as [[from to]|].
  { destruct (convert_types_spec b from to Hcv)
      as [be [Hsp2 [Heff Hflat]]].
    (* the byte is not a literal here, so the seven other rules are ruled out by
       collapsing the two lookups of the table rather than by computing it *)
    destruct Hd as [[cbe [Hsp [Hop Hr]]]
                   |[[Hsp [Hop Hr]]
                   |[[cbtb [cbt [cr [Hsp [Hbs2 [Hbtspec [Hop Hr]]]]]]]
                   |[[cbtb [cbt [cr [Hsp [Hbs2 [Hbtspec [Hop Hr]]]]]]]
                   |[[cbtb [cbt [cr [Hsp [Hbs2 [Hbtspec [Hop Hr]]]]]]]
                   |[[Hsp [Hop Hr]]
                   |[[crbe [crr [Hsp [Hbs2 [Hop Hr]]]]]
                   |[[cnt2 [cz [Hsp [Himm Hop]]]]
                   |[[cnt3 [cbits [Hsp [Himm Hop]]]]
                   |[[cio [cx [Hsp [Himm Hop]]]]
                   |[[cnt [ctp [ca [co [Hsp [Himm Hop]]]]]]
                   |[[cnt [ctp [ca [co [Hsp [Himm Hop]]]]]]
                   |[[cls [cx2 [cmid [Hsp [Hvec [Himm Hop]]]]]]
                   | [cy [Hsp [Himm Hop]]]]]]]]]]]]]]]];
      rewrite Hsp2 in Hsp; try discriminate Hsp.
    injection Hsp as Hbe. subst cbe. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (plain_effect_consume _ _ _ _ _ _ Heff Hct) as [ct1 Hcon].
    destruct (read_conversion_complete C0 st1 pre f from to ct1 Hinv1
                Hcon Hroom1) as [st2 Hrd].
    exists st2. split;
      [eapply visit_wrap_accept;
         [exact Hrd | intros; apply visit_numeric_accept; exact Hacc]|].
    unfold step_shape.
    destruct (step_conversion C0 st1 (pre ++ [f]) pre f from to be st2 Hinv1
                (eq_refl _) (plain_effect_in C0 _ _ _ Heff) Hrd)
      as [seg' Hinv2].
    eexists. unfold adv_plain.
    exists pre, f,
      {| fv_ctrl := fv_ctrl f; fv_seg := seg';
         fv_done := fv_done f ++ [be];
         fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [exact Hflat | exact Hinv2]. }
  destruct (binary_types_ok b) as [o1 Hbt]. rewrite Hbt. cbn [bind].
  destruct o1 as [[ty res]|].
  { destruct (binary_types_spec b ty res Hbt)
      as [be [Hsp2 [Heff Hflat]]].
    destruct Hd as [[cbe [Hsp [Hop Hr]]]
                   |[[Hsp [Hop Hr]]
                   |[[cbtb [cbt [cr [Hsp [Hbs2 [Hbtspec [Hop Hr]]]]]]]
                   |[[cbtb [cbt [cr [Hsp [Hbs2 [Hbtspec [Hop Hr]]]]]]]
                   |[[cbtb [cbt [cr [Hsp [Hbs2 [Hbtspec [Hop Hr]]]]]]]
                   |[[Hsp [Hop Hr]]
                   |[[crbe [crr [Hsp [Hbs2 [Hop Hr]]]]]
                   |[[cnt2 [cz [Hsp [Himm Hop]]]]
                   |[[cnt3 [cbits [Hsp [Himm Hop]]]]
                   |[[cio [cx [Hsp [Himm Hop]]]]
                   |[[cnt [ctp [ca [co [Hsp [Himm Hop]]]]]]
                   |[[cnt [ctp [ca [co [Hsp [Himm Hop]]]]]]
                   |[[cls [cx2 [cmid [Hsp [Hvec [Himm Hop]]]]]]
                   | [cy [Hsp [Himm Hop]]]]]]]]]]]]]]]];
      rewrite Hsp2 in Hsp; try discriminate Hsp.
    injection Hsp as Hbe. subst cbe. subst op.
    cbn [op_typed] in Hty0. destruct Hty0 as [ct Hct].
    destruct (plain_effect_consume _ _ _ _ _ _ Heff Hct) as [ct1 Hcon].
    destruct (read_binary_complete C0 st1 pre f ty res ct1 Hinv1
                Hcon Hroom1) as [st2 Hrd].
    exists st2. split;
      [eapply visit_wrap_accept;
         [exact Hrd | intros; apply visit_numeric_accept; exact Hacc]|].
    unfold step_shape.
    destruct (step_binary C0 st1 (pre ++ [f]) pre f ty res be st2 Hinv1
                (eq_refl _) (plain_effect_in C0 _ _ _ Heff) Hrd)
      as [seg' Hinv2].
    eexists. unfold adv_plain.
    exists pre, f,
      {| fv_ctrl := fv_ctrl f; fv_seg := seg';
         fv_done := fv_done f ++ [be];
         fv_then := fv_then f |}.
    split; [reflexivity|]. split; [reflexivity|].
    cbn [fv_ctrl fv_seg fv_done]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [exact Hflat | exact Hinv2]. }
  (* no row anywhere, so the code recognises nothing and the specification has
     no derivation either *)
  exfalso.
  assert (Hnh : handled b = false).
  { unfold handled. rewrite E1. rewrite E2. rewrite E3. rewrite E3b.
    rewrite E3c. rewrite E3d. rewrite E5. rewrite E5s. rewrite E6. rewrite E7.
    rewrite E7i. rewrite E7e. rewrite E8. rewrite E9. rewrite E10. rewrite E11.
    rewrite E12. rewrite E13. rewrite E14. rewrite E15. rewrite E16.
    rewrite E17. rewrite E18. rewrite E19. rewrite E20. rewrite E21.
    rewrite E22. rewrite E23. rewrite E24. rewrite E25. rewrite E26.
    rewrite E27. rewrite E28. rewrite E29. rewrite E30. rewrite E31.
    rewrite E32. rewrite EM1. rewrite EM2. rewrite E9b. rewrite E9t.
    rewrite E9r.
    rewrite EC1. rewrite EC2. rewrite EL1. rewrite EL2. rewrite EL3.
    rewrite EG1. rewrite EG2.
    rewrite Hcv. rewrite Hbt. reflexivity. }
  rewrite (op_spec_handled b sh Hsp0) in Hnh. discriminate Hnh.
Qed.

(* ================================================================== *)
(** ** The loop invariant: one remaining instruction list per frame    *)
(* ================================================================== *)

(** What is left to check inside one frame: the instructions still to come and,
    for an open then-branch only, the else-branch stashed behind them. [None]
    for every other kind of frame, which is what puts the [FO_else] in
    [todo_ops] exactly where the operator stream has one. *)
(** An abbreviation rather than a definition: [rewrite]'s keyed matching
    compares the implicit type arguments of [cons] syntactically, and a
    definition would leave two spellings of the same type in play. *)
Notation todo := (list basic_instruction * option (list basic_instruction))%type.

(** The stashed else-branch's own obligation, which is what [else] hands the
    [Else] frame it opens. Same context and same empty starting stack as the
    then-branch, per WasmCert's [BI_if] rule. *)
Definition else_todo_ok (C0 : t_context) (labels : list (list value_type))
                        (f : fview) (els : list basic_instruction) : Prop :=
  exists ct,
    List.fold_left
      (check_single (with_labels C0 (ctrl_label (fv_ctrl f) :: labels))) els
      (Some <<[], false>>) = Some ct
    /\ c_types_agree ct (ctrl_results (fv_ctrl f)) = true.

(** [child] is the results the frame currently open inside this one will push
    when it closes; [[]] when nothing is open. Stating it that way is the point
    of the whole invariant: an enclosing frame's obligation never mentions the
    child's body, only its block type, so closing the child transports the
    obligation by a rewrite. *)
Definition frame_todo_ok (C0 : t_context) (labels : list (list value_type))
                         (f : fview) (td : todo)
                         (child : list value_type) : Prop :=
  (exists ct,
     List.fold_left
       (check_single (with_labels C0 (ctrl_label (fv_ctrl f) :: labels)))
       (fst td) (Some (produce (fv_ct f) child)) = Some ct
     /\ c_types_agree ct (ctrl_results (fv_ctrl f)) = true)
  /\ (match snd td with
      | Some els =>
          (fv_ctrl f).(opiter_Ctrl_kind) = Opiter_LabelKind_Then
          /\ else_todo_ok C0 labels f els
      | None => (fv_ctrl f).(opiter_Ctrl_kind) <> Opiter_LabelKind_Then
      end).

Definition child_results (fs : list fview) : list value_type :=
  match fs with
  | [] => []
  | g :: _ => ctrl_results (fv_ctrl g)
  end.

Fixpoint todo_ok (C0 : t_context) (labels : list (list value_type))
                 (fs : list fview) (tds : list todo) : Prop :=
  match fs, tds with
  | [], [] => True
  | f :: fs', td :: tds' =>
      frame_todo_ok C0 labels f td (child_results fs')
      /\ todo_ok C0 (ctrl_label (fv_ctrl f) :: labels) fs' tds'
  | _, _ => False
  end.

(** The operators still to come: innermost frame first, each frame's remaining
    instructions, then -- for an open then-branch -- the [else] and the
    else-branch, and then the [end] that closes it. A bare [if] writes no
    [0x05], which is [else_sugar]'s business rather than this function's. *)
Definition todo_else_ops (td : todo) : list flat_op :=
  match snd td with
  | Some els => [FO_else] ++ flat_of els
  | None => []
  end.

Fixpoint todo_ops (tds : list todo) : list flat_op :=
  match tds with
  | [] => []
  | td :: tds' =>
      todo_ops tds' ++ flat_of (fst td) ++ todo_else_ops td ++ [FO_end]
  end.

Lemma produce_nil : forall ct, produce ct [] = ct.
Proof. intros [ts unr]. reflexivity. Qed.

Lemma todo_ops_snoc : forall tds td,
  todo_ops (tds ++ [td])
    = flat_of (fst td) ++ todo_else_ops td ++ [FO_end] ++ todo_ops tds.
Proof.
  induction tds as [|t tds IH]; intros td.
  - cbn [List.app todo_ops]. repeat rewrite List.app_nil_r.
    repeat rewrite <- List.app_assoc. reflexivity.
  - cbn [List.app todo_ops]. rewrite IH.
    repeat rewrite <- List.app_assoc. reflexivity.
Qed.

Lemma todo_ok_length : forall fs C0 labels tds,
  todo_ok C0 labels fs tds -> List.length fs = List.length tds.
Proof.
  induction fs as [|f fs IH]; intros C0 labels tds H;
    destruct tds as [|td tds]; cbn [todo_ok List.length] in H |- *;
    [reflexivity | contradiction | contradiction |].
  destruct H as [_ Hrest]. f_equal.
  apply (IH C0 (ctrl_label (fv_ctrl f) :: labels) tds). exact Hrest.
Qed.

(** [check_single] is a fixpoint on the instruction, so this needs the case
    analysis; WasmCert proves the same thing as [check_single_None]. *)
Lemma check_single_none : forall C be, check_single C None be = None.
Proof. intros C be. destruct be; reflexivity. Qed.

Lemma fold_check_single_none : forall C es,
  List.fold_left (check_single C) es None = None.
Proof.
  intros C es. induction es as [|e es IH]; [reflexivity|].
  cbn [List.fold_left]. rewrite check_single_none. exact IH.
Qed.

Lemma fold_check_single_cons_inv : forall C be es ts ct,
  List.fold_left (check_single C) (be :: es) (Some ts) = Some ct ->
  exists ct1, check_single C (Some ts) be = Some ct1.
Proof.
  intros C be es ts ct H. cbn [List.fold_left] in H.
  destruct (check_single C (Some ts) be) as [ct1|] eqn:Hc;
    [exists ct1; reflexivity|].
  exfalso. rewrite fold_check_single_none in H. discriminate H.
Qed.

(** The innermost frame's obligation, read off the invariant. *)
Lemma todo_ok_last : forall pre C0 labels f tds td,
  todo_ok C0 labels (pre ++ [f]) (tds ++ [td]) ->
  frame_todo_ok C0 (labels_after labels pre) f td [].
Proof.
  induction pre as [|h pre IH]; intros C0 labels f tds td Hok.
  - destruct tds as [|t0 tds].
    + cbn [List.app] in Hok. cbn [todo_ok] in Hok. destruct Hok as [Hf _].
      cbn [child_results] in Hf. cbn [labels_after]. exact Hf.
    + exfalso. pose proof (todo_ok_length _ _ _ _ Hok) as Hlen.
      cbn [List.app List.length] in Hlen. rewrite List.app_length in Hlen.
      cbn [List.length] in Hlen. lia.
  - destruct tds as [|t0 tds].
    + exfalso. pose proof (todo_ok_length _ _ _ _ Hok) as Hlen.
      cbn [List.app List.length] in Hlen. rewrite List.app_length in Hlen.
      cbn [List.length] in Hlen. lia.
    + cbn [List.app] in Hok. cbn [todo_ok] in Hok. destruct Hok as [_ Hrest].
      cbn [labels_after].
      apply (IH C0 (ctrl_label (fv_ctrl h) :: labels) f tds td). exact Hrest.
Qed.

Lemma todo_ok_plain_typed : forall pre C0 labels f tds be rest tdo,
  todo_ok C0 labels (pre ++ [f]) (tds ++ [(be :: rest, tdo)]) ->
  exists ct, check_single (with_labels C0 (ctrl_label (fv_ctrl f)
                                          :: labels_after labels pre))
                          (Some (fv_ct f)) be = Some ct.
Proof.
  intros pre C0 labels f tds be rest tdo Hok.
  pose proof (todo_ok_last pre C0 labels f tds (be :: rest, tdo) Hok) as Hf.
  destruct Hf as [[ct [Hfold Hagree]] _]. cbn [fst] in Hfold.
  rewrite produce_nil in Hfold.
  apply (fold_check_single_cons_inv _ be rest (fv_ct f) ct). exact Hfold.
Qed.

(* ================================================================== *)
(** ** Moving the invariant across one operator                         *)
(* ================================================================== *)

Lemma ctrl_label_eq : forall c c',
  c'.(opiter_Ctrl_kind) = c.(opiter_Ctrl_kind) ->
  c'.(opiter_Ctrl_block_type) = c.(opiter_Ctrl_block_type) ->
  ctrl_label c' = ctrl_label c.
Proof.
  intros c c' Hk Hb. unfold ctrl_label, ctrl_target, branch_target_bt_of.
  rewrite Hk. rewrite Hb. reflexivity.
Qed.

Lemma ctrl_results_eq : forall c c',
  c'.(opiter_Ctrl_block_type) = c.(opiter_Ctrl_block_type) ->
  ctrl_results c' = ctrl_results c.
Proof. intros c c' Hb. unfold ctrl_results. rewrite Hb. reflexivity. Qed.

Lemma ctrl_label_block : forall c,
  c.(opiter_Ctrl_kind) = Opiter_LabelKind_Block ->
  ctrl_label c = ctrl_results c.
Proof.
  intros c Hk. unfold ctrl_label, ctrl_results, ctrl_target,
    branch_target_bt_of. rewrite Hk.
  destruct (c.(opiter_Ctrl_block_type)); reflexivity.
Qed.

Lemma ctrl_label_loop_nil : forall c,
  c.(opiter_Ctrl_kind) = Opiter_LabelKind_Loop -> ctrl_label c = [].
Proof.
  intros c Hk. unfold ctrl_label, ctrl_target, branch_target_bt_of. rewrite Hk.
  reflexivity.
Qed.

(** The instruction a step appended, read out of the two invariants: the fold
    over the longer ghost list is the fold over the shorter one followed by one
    [check_single]. *)
Lemma frames_ok_step_last : forall C0 labels pre f f' be,
  ctrl_label (fv_ctrl f') = ctrl_label (fv_ctrl f) ->
  fv_done f' = fv_done f ++ [be] ->
  frames_ok C0 labels (pre ++ [f]) ->
  frames_ok C0 labels (pre ++ [f']) ->
  check_single (with_labels C0 (ctrl_label (fv_ctrl f)
                               :: labels_after labels pre))
              (Some (fv_ct f)) be = Some (fv_ct f').
Proof.
  intros C0 labels pre f f' be Hlbl Hdone Hok Hok'.
  destruct (frames_ok_last_fold C0 labels pre f Hok) as [Hfold _].
  destruct (frames_ok_last_fold C0 labels pre f' Hok') as [Hfold' _].
  rewrite Hdone in Hfold'. rewrite Hlbl in Hfold'.
  rewrite List.fold_left_app in Hfold'. rewrite Hfold in Hfold'.
  cbn [List.fold_left] in Hfold'. exact Hfold'.
Qed.

Lemma fv_ct_after_end : forall f g f',
  fv_ctrl f' = fv_ctrl f ->
  fv_seg f' = fv_seg f ++ results_seg (fv_ctrl g).(opiter_Ctrl_block_type) ->
  fv_ct f' = produce (fv_ct f) (ctrl_results (fv_ctrl g)).
Proof.
  intros f g f' Hc Hs. unfold fv_ct, produce, ctrl_results.
  cbn [CT_type CT_unr]. rewrite Hs. rewrite Hc.
  rewrite translate_vals_results. reflexivity.
Qed.

Lemma child_results_snoc_eq : forall (pre : list fview) f f',
  ctrl_results (fv_ctrl f') = ctrl_results (fv_ctrl f) ->
  child_results (pre ++ [f']) = child_results (pre ++ [f]).
Proof.
  intros pre f f' H. destruct pre as [|h t]; cbn [List.app child_results];
    [exact H | reflexivity].
Qed.

Lemma child_results_app_snoc : forall (pre : list fview) f g,
  child_results ((pre ++ [f]) ++ [g]) = child_results (pre ++ [f]).
Proof.
  intros pre f g. destruct pre as [|h t]; cbn [List.app child_results];
    reflexivity.
Qed.

Lemma child_results_end : forall (pre : list fview) f g f',
  ctrl_results (fv_ctrl f') = ctrl_results (fv_ctrl f) ->
  child_results (pre ++ [f']) = child_results (pre ++ [f] ++ [g]).
Proof.
  intros pre f g f' H. destruct pre as [|h t]; cbn [List.app child_results];
    [exact H | reflexivity].
Qed.

(** A plain step: the innermost frame's remaining list loses its head. The
    frame's kind and block type survive, so its stashed else-branch -- if it is
    an open then-branch -- keeps its obligation verbatim. *)
Lemma todo_ok_plain : forall pre C0 labels f f' tds be rest tdo,
  ctrl_label (fv_ctrl f') = ctrl_label (fv_ctrl f) ->
  ctrl_results (fv_ctrl f') = ctrl_results (fv_ctrl f) ->
  (fv_ctrl f').(opiter_Ctrl_kind) = (fv_ctrl f).(opiter_Ctrl_kind) ->
  check_single (with_labels C0 (ctrl_label (fv_ctrl f)
                               :: labels_after labels pre))
              (Some (fv_ct f)) be = Some (fv_ct f') ->
  todo_ok C0 labels (pre ++ [f]) (tds ++ [(be :: rest, tdo)]) ->
  todo_ok C0 labels (pre ++ [f']) (tds ++ [(rest, tdo)]).
Proof.
  induction pre as [|h pre IH]; intros C0 labels f f' tds be rest tdo
                    Hlbl Hres Hkind Hstep Hok.
  - destruct tds as [|t0 tds].
    + cbn [List.app todo_ops] in Hok |- *. cbn [todo_ok] in Hok |- *.
      destruct Hok as [Hf _]. split; [|exact I].
      cbn [child_results] in Hf |- *.
      destruct Hf as [[ct [Hfold Hagree]] Hels]. cbn [fst snd] in Hfold, Hels.
      split.
      * exists ct. cbn [fst].
        rewrite produce_nil in Hfold. rewrite produce_nil.
        cbn [List.fold_left] in Hfold. cbn [labels_after] in Hstep.
        rewrite Hstep in Hfold. rewrite Hlbl. rewrite Hres.
        split; [exact Hfold | exact Hagree].
      * cbn [snd]. destruct tdo as [els|].
        -- destruct Hels as [Hk Hobl]. split; [rewrite Hkind; exact Hk|].
           unfold else_todo_ok in Hobl |- *. rewrite Hlbl. rewrite Hres.
           exact Hobl.
        -- rewrite Hkind. exact Hels.
    + exfalso. pose proof (todo_ok_length _ _ _ _ Hok) as Hlen.
      cbn [List.app List.length] in Hlen. rewrite List.app_length in Hlen.
      cbn [List.length] in Hlen. lia.
  - destruct tds as [|t0 tds].
    + exfalso. pose proof (todo_ok_length _ _ _ _ Hok) as Hlen.
      cbn [List.app List.length] in Hlen. rewrite List.app_length in Hlen.
      cbn [List.length] in Hlen. lia.
    + cbn [List.app] in Hok |- *. cbn [todo_ok] in Hok |- *.
      destruct Hok as [Hh Hrest]. split.
      * rewrite (child_results_snoc_eq pre f f' Hres). exact Hh.
      * apply (IH C0 (ctrl_label (fv_ctrl h) :: labels) f f' tds be rest tdo);
          [exact Hlbl | exact Hres | exact Hkind | | exact Hrest].
        cbn [labels_after] in Hstep. exact Hstep.
Qed.

(** [check_single] on a structured instruction, taken apart: the inner body's
    obligation and the results the enclosing frame gains. The condition is matched
    rather than named, because [cbn] is free to present [[tm] ++ tc_labels C]
    either way round and a named [destruct] would then not fire. *)
Lemma check_single_block_inv : forall C ts bt es ct,
  check_single C (Some ts) (BI_block (translate_bt bt) es) = Some ct ->
  (exists ct1,
     List.fold_left
       (check_single (with_labels C
          (translate_typelist (block_results_of bt) :: tc_labels C)))
       es (Some <<[], false>>) = Some ct1
     /\ c_types_agree ct1 (translate_typelist (block_results_of bt)) = true)
  /\ ct = produce ts (translate_typelist (block_results_of bt)).
Proof.
  intros C ts bt es ct H.
  assert (Hexp : expand_t C (translate_bt bt)
                 = Some (Tf [] (translate_typelist (block_results_of bt))))
    by (destruct bt; reflexivity).
  cbn [check_single] in H. rewrite Hexp in H. cbn beta iota in H.
  match type of H with
  | (if ?c then _ else _) = _ => destruct c eqn:Hc
  end; [|discriminate H].
  match type of Hc with
  | (match ?e with | Some _ => _ | None => _ end) = true =>
      destruct e as [ct1|] eqn:Hf
  end; [|discriminate Hc].
  split; [exists ct1; split; [exact Hf | exact Hc]|].
  unfold type_update in H. cbn [consume] in H. injection H as Hct.
  rewrite <- Hct. reflexivity.
Qed.

Lemma check_single_loop_inv : forall C ts bt es ct,
  check_single C (Some ts) (BI_loop (translate_bt bt) es) = Some ct ->
  (exists ct1,
     List.fold_left (check_single (with_labels C ([] :: tc_labels C))) es
       (Some <<[], false>>) = Some ct1
     /\ c_types_agree ct1 (translate_typelist (block_results_of bt)) = true)
  /\ ct = produce ts (translate_typelist (block_results_of bt)).
Proof.
  intros C ts bt es ct H.
  assert (Hexp : expand_t C (translate_bt bt)
                 = Some (Tf [] (translate_typelist (block_results_of bt))))
    by (destruct bt; reflexivity).
  cbn [check_single] in H. rewrite Hexp in H. cbn beta iota in H.
  match type of H with
  | (if ?c then _ else _) = _ => destruct c eqn:Hc
  end; [|discriminate H].
  match type of Hc with
  | (match ?e with | Some _ => _ | None => _ end) = true =>
      destruct e as [ct1|] eqn:Hf
  end; [|discriminate Hc].
  split; [exists ct1; split; [exact Hf | exact Hc]|].
  unfold type_update in H. cbn [consume] in H. injection H as Hct.
  rewrite <- Hct. reflexivity.
Qed.

(** Entering a block: the innermost frame's remaining list loses the [BI_block],
    which becomes the new frame's whole remaining list, and the frame it came from
    now expects the block's results. *)
Lemma todo_ok_push_block : forall pre C0 labels f g tds inner rest tdo,
  fv_seg g = [] ->
  (fv_ctrl g).(opiter_Ctrl_polymorphic_base) = false ->
  (fv_ctrl g).(opiter_Ctrl_kind) = Opiter_LabelKind_Block ->
  todo_ok C0 labels (pre ++ [f])
    (tds ++ [(BI_block (translate_bt (fv_ctrl g).(opiter_Ctrl_block_type)) inner
              :: rest, tdo)]) ->
  todo_ok C0 labels ((pre ++ [f]) ++ [g])
    ((tds ++ [(rest, tdo)]) ++ [(inner, None)]).
Proof.
  induction pre as [|h pre IH]; intros C0 labels f g tds inner rest tdo
                    Hseg Hpoly Hkind Hok.
  - destruct tds as [|t0 tds].
    2: { exfalso. pose proof (todo_ok_length _ _ _ _ Hok) as Hlen.
         cbn [List.app List.length] in Hlen. rewrite List.app_length in Hlen.
         cbn [List.length] in Hlen. lia. }
    cbn [List.app] in Hok |- *. cbn [todo_ok] in Hok |- *.
    destruct Hok as [Hf _]. cbn [child_results] in Hf |- *.
    destruct Hf as [[ct [Hfold Hagree]] Hels]. cbn [fst snd] in Hfold, Hels.
    rewrite produce_nil in Hfold.
    destruct (fold_check_single_cons_inv _ _ _ _ _ Hfold) as [ct2 Hcs].
    destruct (check_single_block_inv _ _ _ _ _ Hcs) as [[ct1 [Hif Hia]] Hct2].
    cbn [List.fold_left] in Hfold. rewrite Hcs in Hfold. rewrite Hct2 in Hfold.
    split.
    + split; [|cbn [snd]; exact Hels].
      exists ct. cbn [fst]. unfold ctrl_results.
      split; [exact Hfold | exact Hagree].
    + split; [|exact I]. split.
      * exists ct1. cbn [fst]. rewrite (ctrl_label_block (fv_ctrl g) Hkind).
        assert (Hg : produce (fv_ct g) [] = <<[], false>>).
        { rewrite produce_nil. unfold fv_ct. rewrite Hseg. rewrite Hpoly.
          reflexivity. }
        rewrite Hg. unfold ctrl_results. split; [exact Hif | exact Hia].
      * cbn [snd]. rewrite Hkind. discriminate.
  - destruct tds as [|t0 tds].
    { exfalso. pose proof (todo_ok_length _ _ _ _ Hok) as Hlen.
      cbn [List.app List.length] in Hlen. rewrite List.app_length in Hlen.
      cbn [List.length] in Hlen. lia. }
    cbn [List.app] in Hok |- *. cbn [todo_ok] in Hok |- *.
    destruct Hok as [Hh Hrest]. split.
    + rewrite child_results_app_snoc. exact Hh.
    + apply (IH C0 (ctrl_label (fv_ctrl h) :: labels) f g tds inner rest tdo);
        assumption.
Qed.

Lemma todo_ok_push_loop : forall pre C0 labels f g tds inner rest tdo,
  fv_seg g = [] ->
  (fv_ctrl g).(opiter_Ctrl_polymorphic_base) = false ->
  (fv_ctrl g).(opiter_Ctrl_kind) = Opiter_LabelKind_Loop ->
  todo_ok C0 labels (pre ++ [f])
    (tds ++ [(BI_loop (translate_bt (fv_ctrl g).(opiter_Ctrl_block_type)) inner
              :: rest, tdo)]) ->
  todo_ok C0 labels ((pre ++ [f]) ++ [g])
    ((tds ++ [(rest, tdo)]) ++ [(inner, None)]).
Proof.
  induction pre as [|h pre IH]; intros C0 labels f g tds inner rest tdo
                    Hseg Hpoly Hkind Hok.
  - destruct tds as [|t0 tds].
    2: { exfalso. pose proof (todo_ok_length _ _ _ _ Hok) as Hlen.
         cbn [List.app List.length] in Hlen. rewrite List.app_length in Hlen.
         cbn [List.length] in Hlen. lia. }
    cbn [List.app] in Hok |- *. cbn [todo_ok] in Hok |- *.
    destruct Hok as [Hf _]. cbn [child_results] in Hf |- *.
    destruct Hf as [[ct [Hfold Hagree]] Hels]. cbn [fst snd] in Hfold, Hels.
    rewrite produce_nil in Hfold.
    destruct (fold_check_single_cons_inv _ _ _ _ _ Hfold) as [ct2 Hcs].
    destruct (check_single_loop_inv _ _ _ _ _ Hcs) as [[ct1 [Hif Hia]] Hct2].
    cbn [List.fold_left] in Hfold. rewrite Hcs in Hfold. rewrite Hct2 in Hfold.
    split.
    + split; [|cbn [snd]; exact Hels].
      exists ct. cbn [fst]. unfold ctrl_results.
      split; [exact Hfold | exact Hagree].
    + split; [|exact I]. split.
      * exists ct1. cbn [fst]. rewrite (ctrl_label_loop_nil (fv_ctrl g) Hkind).
        assert (Hg : produce (fv_ct g) [] = <<[], false>>).
        { rewrite produce_nil. unfold fv_ct. rewrite Hseg. rewrite Hpoly.
          reflexivity. }
        rewrite Hg. unfold ctrl_results. split; [exact Hif | exact Hia].
      * cbn [snd]. rewrite Hkind. discriminate.
  - destruct tds as [|t0 tds].
    { exfalso. pose proof (todo_ok_length _ _ _ _ Hok) as Hlen.
      cbn [List.app List.length] in Hlen. rewrite List.app_length in Hlen.
      cbn [List.length] in Hlen. lia. }
    cbn [List.app] in Hok |- *. cbn [todo_ok] in Hok |- *.
    destruct Hok as [Hh Hrest]. split.
    + rewrite child_results_app_snoc. exact Hh.
    + apply (IH C0 (ctrl_label (fv_ctrl h) :: labels) f g tds inner rest tdo);
        assumption.
Qed.

Lemma ctrl_label_then : forall c,
  c.(opiter_Ctrl_kind) = Opiter_LabelKind_Then ->
  ctrl_label c = ctrl_results c.
Proof.
  intros c Hk. unfold ctrl_label, ctrl_results, ctrl_target,
    branch_target_bt_of. rewrite Hk.
  destruct (c.(opiter_Ctrl_block_type)); reflexivity.
Qed.

Lemma ctrl_label_else : forall c,
  c.(opiter_Ctrl_kind) = Opiter_LabelKind_Else ->
  ctrl_label c = ctrl_results c.
Proof.
  intros c Hk. unfold ctrl_label, ctrl_results, ctrl_target,
    branch_target_bt_of. rewrite Hk.
  destruct (c.(opiter_Ctrl_block_type)); reflexivity.
Qed.

(** Entering an [if]: the then-branch becomes the new frame's remaining list and
    the else-branch is stashed behind it, exactly as [fv_then] will stash the
    then-branch once [else] fires. The frame below loses the condition, which is
    what the [consume] hypothesis records -- [frames_ok]'s carry conjunct is
    where it comes from, since the [BI_if] itself reaches that frame's ghost
    list only at [end]. *)
Lemma todo_ok_push_if : forall pre C0 labels f f' g tds es1 es2 rest tdo,
  fv_ctrl f' = fv_ctrl f ->
  consume (fv_ct f) [T_num T_i32] = Some (fv_ct f') ->
  fv_seg g = [] ->
  (fv_ctrl g).(opiter_Ctrl_polymorphic_base) = false ->
  (fv_ctrl g).(opiter_Ctrl_kind) = Opiter_LabelKind_Then ->
  todo_ok C0 labels (pre ++ [f])
    (tds ++ [(BI_if (translate_bt (fv_ctrl g).(opiter_Ctrl_block_type)) es1 es2
              :: rest, tdo)]) ->
  todo_ok C0 labels ((pre ++ [f']) ++ [g])
    ((tds ++ [(rest, tdo)]) ++ [(es1, Some es2)]).
Proof.
  induction pre as [|h pre IH]; intros C0 labels f f' g tds es1 es2 rest tdo
                    Hc Hcon Hseg Hpoly Hkind Hok.
  - destruct tds as [|t0 tds].
    2: { exfalso. pose proof (todo_ok_length _ _ _ _ Hok) as Hlen.
         cbn [List.app List.length] in Hlen. rewrite List.app_length in Hlen.
         cbn [List.length] in Hlen. lia. }
    cbn [List.app] in Hok |- *. cbn [todo_ok] in Hok |- *.
    destruct Hok as [Hf _]. cbn [child_results] in Hf |- *.
    destruct Hf as [[ct [Hfold Hagree]] Hels]. cbn [fst snd] in Hfold, Hels.
    rewrite produce_nil in Hfold.
    destruct (fold_check_single_cons_inv _ _ _ _ _ Hfold) as [ct2 Hcs].
    destruct (check_single_if_inv _ _ _ _ _ _ Hcs)
      as [[ct1 [Hthen Hta]] [[ct3 [Helse Hea]] [ct0 [Hcon0 Hct2]]]].
    cbn [List.fold_left] in Hfold. rewrite Hcs in Hfold.
    assert (Hct0 : ct0 = fv_ct f')
      by (rewrite Hcon in Hcon0; injection Hcon0 as Hc0; symmetry; exact Hc0).
    rewrite Hct0 in Hct2. rewrite Hct2 in Hfold.
    assert (Hlbl : ctrl_label (fv_ctrl f') = ctrl_label (fv_ctrl f))
      by (rewrite Hc; reflexivity).
    assert (Hres : ctrl_results (fv_ctrl f') = ctrl_results (fv_ctrl f))
      by (rewrite Hc; reflexivity).
    split.
    + split.
      * exists ct. cbn [fst]. rewrite Hlbl. rewrite Hres.
        unfold ctrl_results. split; [exact Hfold | exact Hagree].
      * cbn [snd]. destruct tdo as [els|].
        -- destruct Hels as [Hk Hobl]. split; [rewrite Hc; exact Hk|].
           unfold else_todo_ok in Hobl |- *. rewrite Hlbl. rewrite Hres.
           exact Hobl.
        -- rewrite Hc. exact Hels.
    + split; [|exact I].
      assert (Hg : produce (fv_ct g) [] = <<[], false>>).
      { rewrite produce_nil. unfold fv_ct. rewrite Hseg. rewrite Hpoly.
        reflexivity. }
      cbn [labels_after]. split.
      * exists ct1. cbn [fst]. rewrite Hlbl.
        rewrite (ctrl_label_then (fv_ctrl g) Hkind). rewrite Hg.
        unfold ctrl_results. split; [exact Hthen | exact Hta].
      * cbn [snd]. split; [exact Hkind|].
        exists ct3. rewrite Hlbl.
        rewrite (ctrl_label_then (fv_ctrl g) Hkind). unfold ctrl_results.
        split; [exact Helse | exact Hea].
  - destruct tds as [|t0 tds].
    { exfalso. pose proof (todo_ok_length _ _ _ _ Hok) as Hlen.
      cbn [List.app List.length] in Hlen. rewrite List.app_length in Hlen.
      cbn [List.length] in Hlen. lia. }
    cbn [List.app] in Hok |- *. cbn [todo_ok] in Hok |- *.
    destruct Hok as [Hh Hrest]. split.
    + rewrite child_results_app_snoc.
      rewrite (child_results_snoc_eq pre f f'
                 (ctrl_results_eq (fv_ctrl f) (fv_ctrl f')
                    (ltac:(rewrite Hc; reflexivity)))).
      exact Hh.
    + apply (IH C0 (ctrl_label (fv_ctrl h) :: labels) f f' g tds es1 es2 rest
               tdo); assumption.
Qed.

(** [else]: the stashed else-branch becomes the [Else] frame's remaining list,
    and its obligation -- which [frame_todo_ok] has been carrying since the
    [if] -- becomes the frame's own. *)
Lemma todo_ok_switch_else : forall pre C0 labels g g' tds els,
  (fv_ctrl g).(opiter_Ctrl_kind) = Opiter_LabelKind_Then ->
  (fv_ctrl g').(opiter_Ctrl_kind) = Opiter_LabelKind_Else ->
  (fv_ctrl g').(opiter_Ctrl_block_type)
    = (fv_ctrl g).(opiter_Ctrl_block_type) ->
  fv_seg g' = [] ->
  (fv_ctrl g').(opiter_Ctrl_polymorphic_base) = false ->
  todo_ok C0 labels (pre ++ [g]) (tds ++ [([], Some els)]) ->
  todo_ok C0 labels (pre ++ [g']) (tds ++ [(els, None)]).
Proof.
  induction pre as [|h pre IH]; intros C0 labels g g' tds els
                    Hkind Hkind' Hbt Hseg Hpoly Hok.
  - destruct tds as [|t0 tds].
    2: { exfalso. pose proof (todo_ok_length _ _ _ _ Hok) as Hlen.
         cbn [List.app List.length] in Hlen. rewrite List.app_length in Hlen.
         cbn [List.length] in Hlen. lia. }
    cbn [List.app] in Hok |- *. cbn [todo_ok] in Hok |- *.
    destruct Hok as [Hf _]. cbn [child_results] in Hf |- *.
    destruct Hf as [_ Hels]. cbn [snd] in Hels.
    destruct Hels as [_ [ct [Hfold Hagree]]].
    assert (Hlbl : ctrl_label (fv_ctrl g') = ctrl_label (fv_ctrl g)).
    { rewrite (ctrl_label_then (fv_ctrl g) Hkind).
      rewrite (ctrl_label_else (fv_ctrl g') Hkind').
      unfold ctrl_results. rewrite Hbt. reflexivity. }
    assert (Hres : ctrl_results (fv_ctrl g') = ctrl_results (fv_ctrl g))
      by (unfold ctrl_results; rewrite Hbt; reflexivity).
    split; [|exact I]. split.
    + exists ct. cbn [fst]. rewrite Hlbl. rewrite Hres.
      assert (Hg : produce (fv_ct g') [] = <<[], false>>).
      { rewrite produce_nil. unfold fv_ct. rewrite Hseg. rewrite Hpoly.
        reflexivity. }
      rewrite Hg. cbn [labels_after] in Hfold.
      split; [exact Hfold | exact Hagree].
    + cbn [snd]. rewrite Hkind'. discriminate.
  - destruct tds as [|t0 tds].
    { exfalso. pose proof (todo_ok_length _ _ _ _ Hok) as Hlen.
      cbn [List.app List.length] in Hlen. rewrite List.app_length in Hlen.
      cbn [List.length] in Hlen. lia. }
    cbn [List.app] in Hok |- *. cbn [todo_ok] in Hok |- *.
    destruct Hok as [Hh Hrest]. split.
    + rewrite (child_results_snoc_eq pre g g'
                 (ltac:(unfold ctrl_results; rewrite Hbt; reflexivity))).
      exact Hh.
    + assert (Hlbl : ctrl_label (fv_ctrl g') = ctrl_label (fv_ctrl g)).
      { rewrite (ctrl_label_then (fv_ctrl g) Hkind).
        rewrite (ctrl_label_else (fv_ctrl g') Hkind').
        unfold ctrl_results. rewrite Hbt. reflexivity. }
      apply (IH C0 (ctrl_label (fv_ctrl h) :: labels) g g' tds els);
        assumption.
Qed.

(** Closing a frame: the frame below it now has no child, and the checker type it
    reaches is the one it was already expecting. *)
Lemma todo_ok_end : forall pre C0 labels f g f' tds td tdg,
  fv_ctrl f' = fv_ctrl f ->
  fv_seg f' = fv_seg f ++ results_seg (fv_ctrl g).(opiter_Ctrl_block_type) ->
  todo_ok C0 labels (pre ++ [f] ++ [g]) (tds ++ [td] ++ [([], tdg)]) ->
  todo_ok C0 labels (pre ++ [f']) (tds ++ [td]).
Proof.
  induction pre as [|h pre IH]; intros C0 labels f g f' tds td tdg Hc Hs Hok.
  all: assert (Hlbl : ctrl_label (fv_ctrl f') = ctrl_label (fv_ctrl f))
         by (rewrite Hc; reflexivity).
  all: assert (Hres : ctrl_results (fv_ctrl f') = ctrl_results (fv_ctrl f))
         by (rewrite Hc; reflexivity).
  - destruct tds as [|t0 tds].
    2: { exfalso. pose proof (todo_ok_length _ _ _ _ Hok) as Hlen.
         cbn [List.app List.length] in Hlen.
         repeat rewrite List.app_length in Hlen.
         cbn [List.length] in Hlen. lia. }
    cbn [List.app] in Hok |- *. cbn [todo_ok] in Hok |- *.
    destruct Hok as [Hf _]. split; [|exact I].
    cbn [child_results] in Hf |- *.
    destruct td as [tdf tdo]. cbn [fst snd] in Hf |- *.
    destruct Hf as [[ct [Hfold Hagree]] Hels].
    split.
    + exists ct.
      rewrite produce_nil. rewrite (fv_ct_after_end f g f' Hc Hs). rewrite Hlbl.
      rewrite Hres. split; [exact Hfold | exact Hagree].
    + destruct tdo as [els|].
      * destruct Hels as [Hk Hobl]. split; [rewrite Hc; exact Hk|].
        unfold else_todo_ok in Hobl |- *. rewrite Hlbl. rewrite Hres.
        exact Hobl.
      * rewrite Hc. exact Hels.
  - destruct tds as [|t0 tds].
    { exfalso. pose proof (todo_ok_length _ _ _ _ Hok) as Hlen.
      cbn [List.app List.length] in Hlen.
      repeat rewrite List.app_length in Hlen.
      cbn [List.length] in Hlen. lia. }
    cbn [List.app] in Hok |- *. cbn [todo_ok] in Hok |- *.
    destruct Hok as [Hh Hrest]. split.
    + rewrite (child_results_end pre f g f'
                 (ctrl_results_eq (fv_ctrl f) (fv_ctrl f')
                    (ltac:(rewrite Hc; reflexivity)))).
      exact Hh.
    + apply (IH C0 (ctrl_label (fv_ctrl h) :: labels) f g f' tds td tdg);
        assumption.
Qed.

(* ================================================================== *)
(** ** The loop                                                        *)
(* ================================================================== *)

Lemma list_cons_or_nil : forall {A} (l : list A),
  l = [] \/ exists x r, l = x :: r.
Proof.
  intros A l. destruct l as [|x r];
    [left; reflexivity | right; exists x, r; reflexivity].
Qed.

Lemma repr_ops_cons_inv : forall bs op ops rest,
  repr_ops bs (op :: ops) rest ->
  exists mid, repr_op bs op mid /\ repr_ops mid ops rest.
Proof.
  intros bs op ops rest H. inversion H. subst. eexists. split; eassumption.
Qed.

Lemma repr_ops_nil_rest : forall bs rest, repr_ops bs [] rest -> rest = bs.
Proof. intros bs rest H. inversion H. reflexivity. Qed.

Lemma repr_ops_nil_bytes : forall ops rest, repr_ops [] ops rest -> ops = [].
Proof.
  intros ops rest H. destruct ops as [|op ops']; [reflexivity|].
  exfalso. destruct (repr_ops_cons_inv _ _ _ _ H) as [mid [Hrop _]].
  apply (repr_op_nonempty _ _ _ Hrop). reflexivity.
Qed.

Lemma todo_ops_nonnil : forall tds0 td, todo_ops (tds0 ++ [td]) <> [].
Proof.
  intros tds0 td. rewrite todo_ops_snoc.
  destruct (flat_of (fst td)) as [|o os]; [|discriminate].
  cbn [List.app]. unfold todo_else_ops. destruct (snd td); discriminate.
Qed.

Lemma bytes_from_past_end : forall data p,
  to_Z (slice_len data) <= to_Z p -> bytes_from data p = [].
Proof.
  intros data p H. unfold bytes_from, byte_list. apply List.skipn_all2.
  rewrite List.map_length. rewrite slice_len_spec in H.
  apply (proj2 (Nat2Z.inj_le _ _)).
  rewrite Z2Nat.id; [exact H | apply usize_nonneg].
Qed.

Lemma bytes_from_nil_ge : forall data p,
  bytes_from data p = [] -> to_Z (slice_len data) <= to_Z p.
Proof.
  intros data p H. unfold bytes_from, byte_list in H.
  apply (f_equal (@List.length _)) in H.
  rewrite List.skipn_length in H. rewrite List.map_length in H.
  cbn [List.length] in H. rewrite slice_len_spec.
  apply (proj1 (Nat.sub_0_le _ _)) in H.
  apply (proj1 (Nat2Z.inj_le _ _)) in H. rename H into Hle.
  rewrite Z2Nat.id in Hle; [exact Hle | apply usize_nonneg].
Qed.

(** The cursor never passes the end of the body, which is what pins the final
    position at [end] rather than merely bounding it below. *)
Lemma read_op_pos_le : forall st data b st',
  opiter_read_op st data = Ok (Core_result_Result_Ok b, st') ->
  to_Z st'.(opiter_OpIterState_pos) <= to_Z (slice_len data).
Proof.
  intros st data b st' H.
  pose proof (read_op_sound st data b st' H) as Hbytes.
  destruct (bytes_from_uncons data st.(opiter_OpIterState_pos) (to_Z b)
              (bytes_from data st'.(opiter_OpIterState_pos)) Hbytes)
    as [b2 [p2 [_ [_ [_ [_ Hlt]]]]]].
  pose proof (read_op_advance st data b st' H) as Hadv. lia.
Qed.

Lemma max_bytes_fits : 7654321 + 2 <= usize_max.
Proof. pose proof usize_max_bound as H. rewrite u32_max_val in H. lia. Qed.

(** The bytes a step consumed, borrowed from the soundness direction: which
    operator they encode is settled there, and [repr_op_det] then identifies it
    with the one the stream named. *)
Lemma step_bytes : forall V (inst : visit_OpVisitor_t V) vis vis2
                           C0 bt0 module ctx data st fs b st1 st2,
  Inv C0 st fs -> body_first bt0 fs ->
  mems_agree module C0 -> locals_agree ctx C0 -> globals_agree module C0 ->
  return_agree ctx C0 -> funcs_agree module C0 -> types_agree module C0 ->
  tables_agree module C0 ->
  opiter_read_op st data = Ok (Core_result_Result_Ok b, st1) ->
  opiter_step inst st1 data module ctx b vis
    = Ok (Core_result_Result_Ok tt, st2, vis2) ->
  exists op, repr_op (bytes_from data st.(opiter_OpIterState_pos)) op
                     (bytes_from data st2.(opiter_OpIterState_pos)).
Proof.
  intros V inst vis vis2 C0 bt0 module ctx data st fs b st1 st2 Hinv Hbfirst
         Hmems Hlocals
         Hglobals Hret Hfuncs Htypes Htables Hro Hstep.
  destruct (step_op_step V inst vis vis2 C0 bt0 module ctx data st fs b st1 st2
              Hinv Hbfirst Hmems
              Hlocals Hglobals Hret Hfuncs Htypes Htables Hro Hstep)
    as [[fs' [op [_ [_ [_ [_ Hrop]]]]]]
       | [[fs' [_ [_ [_ [_ Hrop]]]]] | Hdone]].
  - exists op. exact Hrop.
  - exists FO_end. exact Hrop.
  - destruct Hdone as [_ [f0 [_ [_ [_ [_ [_ Hrop]]]]]]].
    exists FO_end. exact Hrop.
Qed.

Lemma frame_todo_ok_nil : forall C0 labels f tdo,
  frame_todo_ok C0 labels f ([], tdo) [] ->
  c_types_agree (fv_ct f) (ctrl_results (fv_ctrl f)) = true.
Proof.
  intros C0 labels f tdo [[ct [Hfold Hagree]] _]. cbn [fst] in Hfold.
  cbn [List.fold_left] in Hfold.
  rewrite produce_nil in Hfold. injection Hfold as Hct.
  rewrite <- Hct in Hagree. exact Hagree.
Qed.

(** A [Then] frame's entry always stashes an else-branch, and the sugared form
    of an [if] -- the one with no [0x05] at all -- is the case where that
    else-branch is empty. Then the frame declares no results, which is what
    [read_end] insists on before it closes a then-branch. *)
Lemma frame_todo_ok_bare_if : forall C0 labels f,
  frame_todo_ok C0 labels f ([], Some []) [] ->
  block_results_of (fv_ctrl f).(opiter_Ctrl_block_type) = [].
Proof.
  intros C0 labels f [_ [_ [ct [Hfold Hagree]]]].
  cbn [List.fold_left] in Hfold. injection Hfold as Hct.
  rewrite <- Hct in Hagree.
  pose proof (c_types_agree_nil_inv _ Hagree) as Hnil.
  unfold ctrl_results, translate_typelist in Hnil.
  destruct ((fv_ctrl f).(opiter_Ctrl_block_type)); [reflexivity|].
  cbn in Hnil. discriminate Hnil.
Qed.

Lemma todo_ops_end : forall tds0,
  todo_ops (tds0 ++ [([], None)]) = FO_end :: todo_ops tds0.
Proof. intros tds0. rewrite todo_ops_snoc. reflexivity. Qed.

(** The [else] boundary: what follows it is the frame with the else-branch as
    its remaining list, which is exactly the entry [read_else] moves it to. *)
Lemma todo_ops_else : forall tds0 els,
  todo_ops (tds0 ++ [([], Some els)])
    = FO_else :: todo_ops (tds0 ++ [(els, None)]).
Proof.
  intros tds0 els. rewrite todo_ops_snoc. rewrite todo_ops_snoc.
  cbn [fst snd todo_else_ops flat_of List.concat List.map].
  repeat rewrite <- List.app_assoc. reflexivity.
Qed.

(** One instruction off the innermost frame's remaining list. Everything below
    is this plus [flat_of_one]'s equation for the instruction, and stays inside
    append algebra: [rewrite] cannot reassociate past a [cons], which is why
    the [_app] forms of those equations exist. *)
Lemma todo_ops_cons : forall tds0 be tdrest tdo,
  todo_ops (tds0 ++ [(be :: tdrest, tdo)])
    = flat_of_one be ++ todo_ops (tds0 ++ [(tdrest, tdo)]).
Proof.
  intros tds0 be tdrest tdo.
  rewrite todo_ops_snoc. rewrite todo_ops_snoc. cbn [fst snd todo_else_ops].
  rewrite flat_of_cons. repeat rewrite <- List.app_assoc. reflexivity.
Qed.

Lemma todo_ops_plain : forall tds0 be tdrest tdo,
  flat_of_one be = [FO_plain be] ->
  todo_ops (tds0 ++ [(be :: tdrest, tdo)])
    = FO_plain be :: todo_ops (tds0 ++ [(tdrest, tdo)]).
Proof.
  intros tds0 be tdrest tdo Hfo. rewrite todo_ops_cons. rewrite Hfo.
  reflexivity.
Qed.

Lemma todo_ops_block : forall tds0 bt inner tdrest tdo,
  todo_ops (tds0 ++ [(BI_block bt inner :: tdrest, tdo)])
    = FO_block bt :: todo_ops ((tds0 ++ [(tdrest, tdo)]) ++ [(inner, None)]).
Proof.
  intros tds0 bt inner tdrest tdo.
  rewrite todo_ops_cons. rewrite flat_of_one_block_app.
  repeat rewrite todo_ops_snoc. cbn [fst snd todo_else_ops].
  repeat rewrite <- List.app_assoc. reflexivity.
Qed.

Lemma todo_ops_loop : forall tds0 bt inner tdrest tdo,
  todo_ops (tds0 ++ [(BI_loop bt inner :: tdrest, tdo)])
    = FO_loop bt :: todo_ops ((tds0 ++ [(tdrest, tdo)]) ++ [(inner, None)]).
Proof.
  intros tds0 bt inner tdrest tdo.
  rewrite todo_ops_cons. rewrite flat_of_one_loop_app.
  repeat rewrite todo_ops_snoc. cbn [fst snd todo_else_ops].
  repeat rewrite <- List.app_assoc. reflexivity.
Qed.

(** The [if] boundary. The two bodies go to the new frame's entry: the
    then-branch as what remains, the else-branch stashed. *)
Lemma todo_ops_if : forall tds0 bt es1 es2 tdrest tdo,
  todo_ops (tds0 ++ [(BI_if bt es1 es2 :: tdrest, tdo)])
    = FO_if bt :: todo_ops ((tds0 ++ [(tdrest, tdo)]) ++ [(es1, Some es2)]).
Proof.
  intros tds0 bt es1 es2 tdrest tdo.
  rewrite todo_ops_cons. rewrite flat_of_one_if_app.
  repeat rewrite todo_ops_snoc. cbn [fst snd todo_else_ops].
  repeat rewrite <- List.app_assoc. reflexivity.
Qed.

(** Reading the head of the operator stream off the bytes. The stream the
    validator must keep up with is the sugared one, so every step goes through
    [else_sugar] first; for every operator but [FO_else] that is a no-op. *)
Lemma sugar_head : forall op ops bytes lean,
  else_sugar (op :: ops) lean ->
  repr_ops bytes lean [] ->
  op <> FO_else ->
  exists mid lean',
    repr_op bytes op mid /\ else_sugar ops lean' /\ repr_ops mid lean' [].
Proof.
  intros op ops bytes lean Hsug Hops Hne.
  destruct (else_sugar_keep_inv _ _ _ Hsug Hne) as [lean' [Hlean Hsug']].
  rewrite Hlean in Hops.
  destruct (repr_ops_cons_inv _ _ _ _ Hops) as [mid [Hrop Hops']].
  exists mid, lean'. split; [exact Hrop|]. split; [exact Hsug' | exact Hops'].
Qed.

(** The run, by induction on the bytes left, but driven by the operator stream:
    while an operator remains the loop cannot stop, and each iteration consumes
    exactly the one the stream names. The body's [end] is where the stream runs
    out and the cursor is at the end of the body, which is the accepting branch's
    condition. *)
Lemma validate_body_loop_complete : forall m V (inst : visit_OpVisitor_t V) vis
                                           C0 bt0 module ctx data st fs tds,
  hooks_accept inst ->
  Inv C0 st fs -> body_first bt0 fs ->
  mems_agree module C0 -> locals_agree ctx C0 ->
  globals_agree module C0 -> return_agree ctx C0 ->
  funcs_agree module C0 -> types_agree module C0 -> tables_agree module C0 ->
  funcs_wasm10 module -> types_wasm10 module ->
  todo_ok C0 [] fs tds ->
  (exists ops, else_sugar (todo_ops tds) ops
               /\ repr_ops (bytes_from data st.(opiter_OpIterState_pos)) ops []) ->
  to_Z (slice_len data) - to_Z st.(opiter_OpIterState_pos) <= Z.of_nat m ->
  Z.of_nat (stack_size st) + Z.of_nat m <= to_Z (slice_len data) + 1 ->
  to_Z (slice_len data) <= 7654321 ->
  exists vis', opiter_validate_body_with_loop inst data module
                 ctx.(opiter_Context_locals) ctx.(opiter_Context_results) vis st
               = Ok (Core_result_Result_Ok tt, vis').
Proof.
  induction m as [|m IH]; intros V inst vis C0 bt0 module ctx data st fs tds
                  Hacc Hinv Hbfirst Hmems Hlocals Hglobals Hret
                  Hfuncs Htypes Htables Hfw10 Htw10
                  Hok [ops [Hsug Hops]] Hmeas
                  Hbudget Hlim;
    destruct (body_first_snoc bt0 fs Hbfirst) as [pre [f Hfs]];
    (assert (Hne : tds <> [])
       by (pose proof (todo_ok_length _ _ _ _ Hok) as Hlen;
           rewrite Hfs in Hlen; rewrite List.app_length in Hlen;
           intros Hz; rewrite Hz in Hlen; cbn [List.length] in Hlen; lia));
    destruct (List.exists_last Hne) as [tds0 [td Htds]];
    subst fs; subst tds.
  - (* the byte budget is spent, so the operator that remains has no bytes *)
    exfalso.
    assert (Hnil : bytes_from data st.(opiter_OpIterState_pos) = [])
      by (apply bytes_from_past_end; lia).
    rewrite Hnil in Hops.
    apply (todo_ops_nonnil tds0 td).
    apply (else_sugar_nil_out _ _ Hsug). apply (repr_ops_nil_bytes _ _ Hops).
  - (* one operator *)
    assert (Hroomst : room st).
    { unfold room. pose proof max_bytes_fits. lia. }
    assert (Hcons : exists c cs,
              vec_list st.(opiter_OpIterState_ctrls) = c :: cs).
    { destruct Hinv as [K1 _]. rewrite K1.
      destruct pre as [|h t];
        [exists (fv_ctrl f), []; reflexivity
        | exists (fv_ctrl h), (List.map fv_ctrl (t ++ [f]));
          cbn [List.app List.map]; reflexivity]. }
    destruct Hcons as [c [cs Hcons]].
    unfold opiter_validate_body_with_loop. rewrite loop_unfold. cbn beta iota.
    unfold opiter_control_stack_empty. rewrite vec_is_empty_spec.
    rewrite Hcons. cbn [bind]. rewrite ctx_eta.
    destruct (list_cons_or_nil (bytes_from data st.(opiter_OpIterState_pos)))
      as [Hnil | [z [rest0 Hbs]]].
    { exfalso. rewrite Hnil in Hops.
      apply (todo_ops_nonnil tds0 td).
      apply (else_sugar_nil_out _ _ Hsug). apply (repr_ops_nil_bytes _ _ Hops). }
    destruct (read_op_complete st data z rest0 Hbs)
      as [b [st1 [Hro [Hzb [Hrest [Hv1 Hc1]]]]]].
    rewrite Hro. cbn [bind]. rewrite branch_ok. cbn [bind].
    pose proof (read_op_advance st data b st1 Hro) as Hadv.
    pose proof (read_op_size st data _ st1 Hro) as Hsz1.
    destruct td as [tdf tdo].
    destruct (list_cons_or_nil tdf) as [Htd | [be [tdrest Htd]]].
    + (* nothing left inside this frame *)
      subst tdf.
      pose proof (todo_ok_last pre C0 [] f tds0 ([], tdo) Hok) as Hftd.
      assert (Hagree : c_types_agree (fv_ct f) (ctrl_results (fv_ctrl f)) = true)
        by (apply (frame_todo_ok_nil C0 (labels_after [] pre) f tdo); exact Hftd).
      destruct tdo as [els|].
      * (* an open then-branch. Either the [0x05] is there, or the [if] was
           written in spec 5.4.1's sugared form and the [0x0B] closes the frame
           with the [FO_else] never encoded at all. *)
        assert (Hkindf : (fv_ctrl f).(opiter_Ctrl_kind) = Opiter_LabelKind_Then)
          by (destruct Hftd as [_ [Hk _]]; exact Hk).
        rewrite todo_ops_else in Hsug.
        destruct (else_sugar_else_inv _ _ Hsug)
          as [[lean' [Hlean Hsug']] | [ops0 [Heq Hsug']]].
        -- (* the [else] was written *)
           rewrite Hlean in Hops.
           destruct (repr_ops_cons_inv _ _ _ _ Hops) as [mid [Hrop Hops']].
           assert (Hty : op_typed C0 (labels_after [] pre) f FO_else)
             by (cbn [op_typed]; split; [exact Hkindf | exact Hagree]).
           destruct (step_complete V inst vis C0 bt0 module ctx data st (pre ++ [f]) pre f b st1
                       FO_else mid Hacc Hinv Hbfirst (eq_refl _) Hroomst Hmems
                       Hlocals Hglobals Hret Hfuncs Htypes Htables
                       Hfw10 Htw10 Hro Hrop Hty)
             as [st2 [[vis2 Hstep] Hshape]].
           rewrite Hstep. cbn [bind]. rewrite branch_ok. cbn [bind].
           destruct (step_bytes V inst vis vis2 C0 bt0 module ctx data st (pre ++ [f]) b st1 st2 Hinv
                       Hbfirst Hmems Hlocals Hglobals Hret Hfuncs Htypes Htables
                       Hro Hstep) as [op' Hrop'].
           destruct (repr_op_det _ _ _ _ _ Hrop Hrop') as [_ Hmid].
           pose proof (step_mono V inst vis st1 data module ctx b _ st2 vis2 Hstep)
             as Hmono.
           pose proof (step_size V inst vis st1 data module ctx b _ st2 vis2 Hstep)
             as Hsz2.
           destruct Hshape as [fs' Hae].
           destruct Hae as [pre2 [g2 [g' [Hfs2 [Hfs2' [Hk' [Hbt'
                             [Hpoly' [Hseg' [Hdone' Hinv2]]]]]]]]]].
           destruct (List.app_inj_tail _ _ _ _ Hfs2) as [Hpe Hge].
           subst pre. subst f. subst fs'.
           (* a then-branch is never the body's frame, so there is one below it *)
           destruct pre2 as [|h pre3].
           { exfalso. cbn [List.app body_first] in Hbfirst.
             destruct Hbfirst as [Hb' _]. rewrite Hkindf in Hb'. discriminate. }
           pose proof (todo_ok_switch_else (h :: pre3) C0 [] g2 g' tds0 els
                         Hkindf Hk' Hbt' Hseg' Hpoly' Hok) as Hok'.
           apply (IH V inst vis2 C0 bt0 module ctx data st2 ((h :: pre3) ++ [g'])
                    (tds0 ++ [(els, None)])); try assumption.
           ++ apply (body_first_switch bt0 h pre3 g2);
                [right; right; right; exact Hk' | exact Hbfirst].
           ++ exists lean'. split; [exact Hsug'|].
              rewrite <- Hmid. exact Hops'.
           ++ cbn [Z.of_nat] in Hmeas. lia.
           ++ cbn [Z.of_nat] in Hbudget. lia.
        -- (* the sugared form: the elided [FO_else] is followed by the [FO_end],
              so the else-branch is empty and this [0x0B] closes the frame *)
           assert (Hsplit : FO_end :: ops0
                            = flat_of els ++ ([FO_end] ++ todo_ops tds0)).
           { rewrite <- Heq. rewrite todo_ops_snoc.
             cbn [fst snd todo_else_ops]. rewrite List.app_nil_l. reflexivity. }
           destruct (flat_of_inj_nil els (FO_end :: ops0)
                       ([FO_end] ++ todo_ops tds0) (stops_end _) Hsplit)
             as [Helsnil Hrest0].
           injection Hrest0 as Hops0.
           rewrite Heq in Hsug'.
           destruct (else_sugar_keep_inv _ _ _ Hsug' (ltac:(discriminate)))
             as [lean' [Hlean Hsug'']].
           rewrite Hops0 in Hsug''. subst els.
           rewrite Hlean in Hops.
           destruct (repr_ops_cons_inv _ _ _ _ Hops) as [mid [Hrop Hops']].
           assert (Hty : op_typed C0 (labels_after [] pre) f FO_end).
           { cbn [op_typed]. split; [exact Hagree|].
             intros _. apply (frame_todo_ok_bare_if C0 (labels_after [] pre) f).
             exact Hftd. }
           destruct (step_complete V inst vis C0 bt0 module ctx data st (pre ++ [f]) pre f b st1
                       FO_end mid Hacc Hinv Hbfirst (eq_refl _) Hroomst Hmems
                       Hlocals Hglobals Hret Hfuncs Htypes Htables
                       Hfw10 Htw10 Hro Hrop Hty)
             as [st2 [[vis2 Hstep] Hshape]].
           rewrite Hstep. cbn [bind]. rewrite branch_ok. cbn [bind].
           destruct (step_bytes V inst vis vis2 C0 bt0 module ctx data st (pre ++ [f]) b st1 st2 Hinv
                       Hbfirst Hmems Hlocals Hglobals Hret Hfuncs Htypes Htables
                       Hro Hstep) as [op' Hrop'].
           destruct (repr_op_det _ _ _ _ _ Hrop Hrop') as [_ Hmid].
           pose proof (step_mono V inst vis st1 data module ctx b _ st2 vis2 Hstep)
             as Hmono.
           pose proof (step_size V inst vis st1 data module ctx b _ st2 vis2 Hstep)
             as Hsz2.
           destruct Hshape as [[fs' Hae] | Hbody].
           2: { (* not the body's frame: that one is not a then-branch *)
                exfalso. destruct Hbody as [f0 [Hfs0 _]].
                assert (Hpren : pre = []).
                { destruct pre as [|h t]; [reflexivity|].
                  exfalso. cbn [List.app] in Hfs0. injection Hfs0 as _ Hbad.
                  destruct t; discriminate Hbad. }
                rewrite Hpren in Hbfirst. cbn [List.app body_first] in Hbfirst.
                destruct Hbfirst as [Hb' _]. rewrite Hkindf in Hb'.
                discriminate. }
           destruct Hae as [pre2 [f2 [g2 [f' [Hfs2 [Hfs2' [Hcf [Hsf Hinv2]]]]]]]].
           rewrite List.app_assoc in Hfs2.
           destruct (List.app_inj_tail _ _ _ _ Hfs2) as [Hpe Hge].
           subst g2. subst pre. subst fs'.
           rewrite <- List.app_assoc in Hok. rewrite <- List.app_assoc in Hbfirst.
           assert (Hne0 : tds0 <> []).
           { pose proof (todo_ok_length _ _ _ _ Hok) as Hlen.
             repeat rewrite List.app_length in Hlen. cbn [List.length] in Hlen.
             intros Hz. rewrite Hz in Hlen. cbn [List.length] in Hlen. lia. }
           destruct (List.exists_last Hne0) as [tds1 [td1 Htds1]]. subst tds0.
           rewrite <- List.app_assoc in Hok.
           pose proof (todo_ok_end pre2 C0 [] f2 f f' tds1 td1 (Some [])
                         Hcf Hsf Hok) as Hok'.
           apply (IH V inst vis2 C0 bt0 module ctx data st2 (pre2 ++ [f']) (tds1 ++ [td1]));
             try assumption.
           ++ apply (body_first_end bt0 pre2 f2 f' f);
                [rewrite Hcf; reflexivity | rewrite Hcf; reflexivity
                | exact Hbfirst].
           ++ exists lean'. split; [exact Hsug''|].
              rewrite <- Hmid. exact Hops'.
           ++ cbn [Z.of_nat] in Hmeas. lia.
           ++ cbn [Z.of_nat] in Hbudget. lia.
      * (* [end] closes the frame *)
        rewrite todo_ops_end in Hsug.
        destruct (sugar_head _ _ _ _ Hsug Hops (ltac:(discriminate)))
          as [mid [lean' [Hrop [Hsug' Hops']]]].
        assert (Hty : op_typed C0 (labels_after [] pre) f FO_end).
        { cbn [op_typed]. split; [exact Hagree|].
          intros Hk. exfalso. destruct Hftd as [_ Hnt]. cbn [snd] in Hnt.
          apply Hnt. exact Hk. }
        destruct (step_complete V inst vis C0 bt0 module ctx data st (pre ++ [f]) pre f b st1 FO_end
                    mid Hacc Hinv Hbfirst (eq_refl _) Hroomst Hmems Hlocals
                    Hglobals Hret Hfuncs Htypes Htables Hfw10 Htw10
                    Hro Hrop Hty)
          as [st2 [[vis2 Hstep] Hshape]].
        rewrite Hstep. cbn [bind]. rewrite branch_ok. cbn [bind].
        destruct (step_bytes V inst vis vis2 C0 bt0 module ctx data st (pre ++ [f]) b st1 st2 Hinv
                    Hbfirst Hmems Hlocals Hglobals Hret Hfuncs Htypes Htables
                    Hro Hstep) as [op' Hrop'].
        destruct (repr_op_det _ _ _ _ _ Hrop Hrop') as [_ Hmid].
        pose proof (step_mono V inst vis st1 data module ctx b _ st2 vis2 Hstep)
             as Hmono.
        pose proof (step_size V inst vis st1 data module ctx b _ st2 vis2 Hstep)
             as Hsz2.
        destruct Hshape as [[fs' Hae] | Hbody].
        -- (* a nested frame closed *)
           destruct Hae as [pre2 [f2 [g2 [f' [Hfs2 [Hfs2' [Hcf [Hsf Hinv2]]]]]]]].
           rewrite List.app_assoc in Hfs2.
           destruct (List.app_inj_tail _ _ _ _ Hfs2) as [Hpe Hge].
           subst g2. subst pre. subst fs'.
           rewrite <- List.app_assoc in Hok. rewrite <- List.app_assoc in Hbfirst.
           assert (Hne0 : tds0 <> []).
           { pose proof (todo_ok_length _ _ _ _ Hok) as Hlen.
             repeat rewrite List.app_length in Hlen. cbn [List.length] in Hlen.
             intros Hz. rewrite Hz in Hlen. cbn [List.length] in Hlen. lia. }
           destruct (List.exists_last Hne0) as [tds1 [td1 Htds1]]. subst tds0.
           rewrite <- List.app_assoc in Hok.
           pose proof (todo_ok_end pre2 C0 [] f2 f f' tds1 td1 None
                         Hcf Hsf Hok) as Hok'.
           apply (IH V inst vis2 C0 bt0 module ctx data st2 (pre2 ++ [f']) (tds1 ++ [td1]));
             try assumption.
           ++ apply (body_first_end bt0 pre2 f2 f' f);
                [rewrite Hcf; reflexivity | rewrite Hcf; reflexivity
                | exact Hbfirst].
           ++ exists lean'. split; [exact Hsug'|].
              rewrite <- Hmid. exact Hops'.
           ++ cbn [Z.of_nat] in Hmeas. lia.
           ++ cbn [Z.of_nat] in Hbudget. lia.
        -- (* the body's own [end]: the stream is spent and the cursor is at the
              end of the body *)
           destruct Hbody as [f0 [Hfs0 [Hc2 Hpos2]]].
           assert (Hpren : pre = []).
           { destruct pre as [|h t]; [reflexivity|].
             exfalso. cbn [List.app] in Hfs0. injection Hfs0 as _ Hbad.
             destruct t; discriminate Hbad. }
           subst pre.
           assert (Htds00 : tds0 = []).
           { pose proof (todo_ok_length _ _ _ _ Hok) as Hlen.
             cbn [List.app List.length] in Hlen. rewrite List.app_length in Hlen.
             cbn [List.length] in Hlen.
             destruct tds0 as [|t0 ts0]; [reflexivity|].
             exfalso. cbn [List.length] in Hlen. lia. }
           subst tds0. cbn [todo_ops] in Hsug'.
           rewrite (else_sugar_nil_inv _ Hsug') in Hops'.
           pose proof (repr_ops_nil_rest _ _ Hops') as Hmid0.
           assert (Hnil2 : bytes_from data st2.(opiter_OpIterState_pos) = []).
           { rewrite <- Hmid. rewrite <- Hmid0. reflexivity. }
           rewrite loop_unfold. cbn beta iota.
           unfold opiter_control_stack_empty. rewrite vec_is_empty_spec.
           rewrite Hc2. cbn [bind].
           assert (Heq : (st2.(opiter_OpIterState_pos) s= slice_len data) = true).
           { apply scalar_eqb_of_eq.
             pose proof (bytes_from_nil_ge data _ Hnil2) as Hge.
             pose proof (read_op_pos_le st data b st1 Hro) as Hle. lia. }
           rewrite Heq. eexists. reflexivity.
    + (* one more instruction in this frame *)
      subst tdf.
      destruct (flat_of_one_cases be) as [[bt [inner [Hbe Hfo]]]
                                         |[[bt [inner [Hbe Hfo]]]
                                         |[[bt [es1 [es2 [Hbe Hfo]]]] | Hfo]]].
      * (* a block opens *)
        subst be. rewrite todo_ops_block in Hsug.
        destruct (sugar_head _ _ _ _ Hsug Hops (ltac:(discriminate)))
          as [mid [lean' [Hrop [Hsug' Hops']]]].
        destruct (step_complete V inst vis C0 bt0 module ctx data st (pre ++ [f]) pre f b st1
                    (FO_block bt) mid Hacc Hinv Hbfirst (eq_refl _) Hroomst Hmems
                    Hlocals Hglobals Hret Hfuncs Htypes Htables
                    Hfw10 Htw10 Hro Hrop I)
          as [st2 [[vis2 Hstep] Hshape]].
        rewrite Hstep. cbn [bind]. rewrite branch_ok. cbn [bind].
        destruct (step_bytes V inst vis vis2 C0 bt0 module ctx data st (pre ++ [f]) b st1 st2 Hinv
                    Hbfirst Hmems Hlocals Hglobals Hret Hfuncs Htypes Htables
                    Hro Hstep)
          as [op' Hrop'].
        destruct (repr_op_det _ _ _ _ _ Hrop Hrop') as [_ Hmid].
        pose proof (step_mono V inst vis st1 data module ctx b _ st2 vis2 Hstep)
             as Hmono.
        pose proof (step_size V inst vis st1 data module ctx b _ st2 vis2 Hstep)
             as Hsz2.
        destruct Hshape as [fs' [bt' [Htr Hae]]].
        destruct Hae as [g [Hfs' [Hseg [Hdone [Hkind [Hbt [Hpoly Hinv2]]]]]]].
        subst fs'.
        assert (Hbteq : translate_bt (fv_ctrl g).(opiter_Ctrl_block_type) = bt)
          by (rewrite Hbt; exact Htr).
        rewrite <- Hbteq in Hok.
        pose proof (todo_ok_push_block pre C0 [] f g tds0 inner tdrest tdo
                      Hseg Hpoly Hkind Hok) as Hok'.
        apply (IH V inst vis2 C0 bt0 module ctx data st2 ((pre ++ [f]) ++ [g])
                 ((tds0 ++ [(tdrest, tdo)]) ++ [(inner, None)]));
          try assumption.
        -- apply body_first_push; [left; exact Hkind | exact Hbfirst].
        -- exists lean'. split; [exact Hsug'|]. rewrite <- Hmid. exact Hops'.
        -- cbn [Z.of_nat] in Hmeas. lia.
        -- cbn [Z.of_nat] in Hbudget. lia.
      * (* a loop opens *)
        subst be. rewrite todo_ops_loop in Hsug.
        destruct (sugar_head _ _ _ _ Hsug Hops (ltac:(discriminate)))
          as [mid [lean' [Hrop [Hsug' Hops']]]].
        destruct (step_complete V inst vis C0 bt0 module ctx data st (pre ++ [f]) pre f b st1
                    (FO_loop bt) mid Hacc Hinv Hbfirst (eq_refl _) Hroomst Hmems
                    Hlocals Hglobals Hret Hfuncs Htypes Htables
                    Hfw10 Htw10 Hro Hrop I)
          as [st2 [[vis2 Hstep] Hshape]].
        rewrite Hstep. cbn [bind]. rewrite branch_ok. cbn [bind].
        destruct (step_bytes V inst vis vis2 C0 bt0 module ctx data st (pre ++ [f]) b st1 st2 Hinv
                    Hbfirst Hmems Hlocals Hglobals Hret Hfuncs Htypes Htables
                    Hro Hstep)
          as [op' Hrop'].
        destruct (repr_op_det _ _ _ _ _ Hrop Hrop') as [_ Hmid].
        pose proof (step_mono V inst vis st1 data module ctx b _ st2 vis2 Hstep)
             as Hmono.
        pose proof (step_size V inst vis st1 data module ctx b _ st2 vis2 Hstep)
             as Hsz2.
        destruct Hshape as [fs' [bt' [Htr Hae]]].
        destruct Hae as [g [Hfs' [Hseg [Hdone [Hkind [Hbt [Hpoly Hinv2]]]]]]].
        subst fs'.
        assert (Hbteq : translate_bt (fv_ctrl g).(opiter_Ctrl_block_type) = bt)
          by (rewrite Hbt; exact Htr).
        rewrite <- Hbteq in Hok.
        pose proof (todo_ok_push_loop pre C0 [] f g tds0 inner tdrest tdo
                      Hseg Hpoly Hkind Hok) as Hok'.
        apply (IH V inst vis2 C0 bt0 module ctx data st2 ((pre ++ [f]) ++ [g])
                 ((tds0 ++ [(tdrest, tdo)]) ++ [(inner, None)]));
          try assumption.
        -- apply body_first_push; [right; left; exact Hkind | exact Hbfirst].
        -- exists lean'. split; [exact Hsug'|]. rewrite <- Hmid. exact Hops'.
        -- cbn [Z.of_nat] in Hmeas. lia.
        -- cbn [Z.of_nat] in Hbudget. lia.
      * (* an [if] opens: the then-branch becomes the new frame's remaining list
           and the else-branch is stashed behind it *)
        subst be. rewrite todo_ops_if in Hsug.
        destruct (sugar_head _ _ _ _ Hsug Hops (ltac:(discriminate)))
          as [mid [lean' [Hrop [Hsug' Hops']]]].
        assert (Hty : op_typed C0 (labels_after [] pre) f (FO_if bt)).
        { cbn [op_typed]. exists es1, es2.
          apply (todo_ok_plain_typed pre C0 [] f tds0 (BI_if bt es1 es2) tdrest
                   tdo). exact Hok. }
        destruct (step_complete V inst vis C0 bt0 module ctx data st (pre ++ [f]) pre f b st1
                    (FO_if bt) mid Hacc Hinv Hbfirst (eq_refl _) Hroomst Hmems
                    Hlocals Hglobals Hret Hfuncs Htypes Htables
                    Hfw10 Htw10 Hro Hrop Hty)
          as [st2 [[vis2 Hstep] Hshape]].
        rewrite Hstep. cbn [bind]. rewrite branch_ok. cbn [bind].
        destruct (step_bytes V inst vis vis2 C0 bt0 module ctx data st (pre ++ [f]) b st1 st2 Hinv
                    Hbfirst Hmems Hlocals Hglobals Hret Hfuncs Htypes Htables
                    Hro Hstep)
          as [op' Hrop'].
        destruct (repr_op_det _ _ _ _ _ Hrop Hrop') as [_ Hmid].
        pose proof (step_mono V inst vis st1 data module ctx b _ st2 vis2 Hstep)
             as Hmono.
        pose proof (step_size V inst vis st1 data module ctx b _ st2 vis2 Hstep)
             as Hsz2.
        destruct Hshape as [fs' [bt' [Htr Hae]]].
        destruct Hae as [pre2 [f2 [f' [g [Hfs2 [Hfs2' [Hcf [Hdf
                          [Hseg [Hdone [Hkind [Hbt [Hpoly Hinv2]]]]]]]]]]]]].
        destruct (List.app_inj_tail _ _ _ _ Hfs2) as [Hpe Hfe].
        subst pre. subst f. subst fs'.
        assert (Hbteq : translate_bt (fv_ctrl g).(opiter_Ctrl_block_type) = bt)
          by (rewrite Hbt; exact Htr).
        rewrite <- Hbteq in Hok.
        (* the condition the enclosing frame lost, read off the two invariants *)
        assert (Hcon : consume (fv_ct f2) [T_num T_i32] = Some (fv_ct f')).
        { destruct (frames_ok_last_fold C0 [] pre2 f2
                      (ltac:(destruct Hinv as [_ [_ [_ K4]]]; exact K4)))
            as [Hfold _].
          destruct (frames_ok_last_two_if C0 [] pre2 f' g (or_introl Hkind)
                      (ltac:(destruct Hinv2 as [_ [_ [_ K4]]];
                             rewrite <- List.app_assoc in K4; exact K4))
                      ) as [[ct0 [Hfold' Hcon0]] _].
          rewrite Hcf in Hfold'. rewrite Hdf in Hfold'.
          rewrite Hfold in Hfold'. injection Hfold' as Hct0.
          rewrite <- Hct0 in Hcon0. exact Hcon0. }
        pose proof (todo_ok_push_if pre2 C0 [] f2 f' g tds0 es1 es2 tdrest tdo
                      Hcf Hcon Hseg Hpoly Hkind Hok) as Hok'.
        apply (IH V inst vis2 C0 bt0 module ctx data st2 ((pre2 ++ [f']) ++ [g])
                 ((tds0 ++ [(tdrest, tdo)]) ++ [(es1, Some es2)]));
          try assumption.
        -- apply body_first_push; [right; right; left; exact Hkind|].
           apply (body_first_last bt0 pre2 f2 f');
             [rewrite Hcf; reflexivity | rewrite Hcf; reflexivity
              | exact Hbfirst].
        -- exists lean'. split; [exact Hsug'|]. rewrite <- Hmid. exact Hops'.
        -- cbn [Z.of_nat] in Hmeas. lia.
        -- cbn [Z.of_nat] in Hbudget. lia.
      * (* a plain instruction *)
        rewrite (todo_ops_plain tds0 be tdrest tdo Hfo) in Hsug.
        destruct (sugar_head _ _ _ _ Hsug Hops (ltac:(discriminate)))
          as [mid [lean' [Hrop [Hsug' Hops']]]].
        assert (Hty : op_typed C0 (labels_after [] pre) f (FO_plain be))
          by (cbn [op_typed];
              apply (todo_ok_plain_typed pre C0 [] f tds0 be tdrest tdo);
              exact Hok).
        destruct (step_complete V inst vis C0 bt0 module ctx data st (pre ++ [f]) pre f b st1
                    (FO_plain be) mid Hacc Hinv Hbfirst (eq_refl _) Hroomst
                    Hmems Hlocals Hglobals Hret Hfuncs Htypes
                    Htables Hfw10 Htw10 Hro Hrop Hty)
          as [st2 [[vis2 Hstep] Hshape]].
        rewrite Hstep. cbn [bind]. rewrite branch_ok. cbn [bind].
        destruct (step_bytes V inst vis vis2 C0 bt0 module ctx data st (pre ++ [f]) b st1 st2 Hinv
                    Hbfirst Hmems Hlocals Hglobals Hret Hfuncs Htypes Htables
                    Hro Hstep)
          as [op' Hrop'].
        destruct (repr_op_det _ _ _ _ _ Hrop Hrop') as [_ Hmid].
        pose proof (step_mono V inst vis st1 data module ctx b _ st2 vis2 Hstep)
             as Hmono.
        pose proof (step_size V inst vis st1 data module ctx b _ st2 vis2 Hstep)
             as Hsz2.
        destruct Hshape as [fs' Hae].
        destruct Hae as [pre' [f0 [f' [Hfs1 [Hfs1' [Hk [Hb2 [Hd [Hfo' Hinv2]]]]]]]]].
        destruct (List.app_inj_tail _ _ _ _ Hfs1) as [Hpe Hfe].
        subst pre. subst f. subst fs'.
        pose proof (frames_ok_step_last C0 [] pre' f0 f' be
                      (ctrl_label_eq (fv_ctrl f0) (fv_ctrl f') Hk Hb2) Hd
                      (ltac:(destruct Hinv as [_ [_ [_ K4]]]; exact K4))
                      (ltac:(destruct Hinv2 as [_ [_ [_ K4]]]; exact K4)))
          as Hstep2.
        pose proof (todo_ok_plain pre' C0 [] f0 f' tds0 be tdrest tdo
                      (ctrl_label_eq (fv_ctrl f0) (fv_ctrl f') Hk Hb2)
                      (ctrl_results_eq (fv_ctrl f0) (fv_ctrl f') Hb2)
                      Hk Hstep2 Hok) as Hok'.
        apply (IH V inst vis2 C0 bt0 module ctx data st2 (pre' ++ [f']) (tds0 ++ [(tdrest, tdo)]));
          try assumption.
        -- apply (body_first_last bt0 pre' f0 f'); assumption.
        -- exists lean'. split; [exact Hsug'|]. rewrite <- Hmid. exact Hops'.
        -- cbn [Z.of_nat] in Hmeas. lia.
        -- cbn [Z.of_nat] in Hbudget. lia.
Qed.

(* ================================================================== *)
(** ** The theorem                                                     *)
(* ================================================================== *)

(** The streaming validator accepts every body WasmCert's checker accepts, at the
    function's declared result type.

    Two hypotheses beyond [validate_body_sound]'s, both the module validator's
    business: every function type the context declares has at most one result,
    and the body is within the size limit. The second has to be stated, unlike
    in the soundness direction: the validator rejects a longer body for size, so
    the agreement is with WasmCert *on bodies within the limit*. *)
Theorem validate_body_with_complete : forall V (inst : visit_OpVisitor_t V) vis
                                             C0 module ctx data es,
  hooks_accept inst ->
  mems_agree module C0 -> locals_agree ctx C0 ->
  globals_agree module C0 -> return_agree ctx C0 ->
  funcs_agree module C0 -> types_agree module C0 -> tables_agree module C0 ->
  funcs_wasm10 module -> types_wasm10 module ->
  (List.length (vec_list ctx.(opiter_Context_results)) <= 1)%nat ->
  to_Z (slice_len data) <= 7654321 ->
  repr_expr (byte_list data) es [] ->
  b_e_type_checker_aux
    (upd_label C0 [translate_typelist (vec_list ctx.(opiter_Context_results))]) es
    (Tf [] (translate_typelist (vec_list ctx.(opiter_Context_results)))) = true ->
  exists vis', opiter_validate_body_with inst data module ctx vis
               = Ok (Core_result_Result_Ok tt, vis').
Proof.
  intros V inst vis C0 module ctx data es Hacc Hmems Hlocals Hglobals Hret
         Hfuncs Htypes Htables Hfw10 Htw10 Hlen1 Hlim Hexpr Hchk.
  unfold opiter_validate_body_with.
  assert (Hbig : (slice_len data s> limits_max_function_bytes) = false).
  { unfold scalar_gtb. rewrite Z.gtb_ltb. apply Z.ltb_ge.
    assert (Hm : to_Z limits_max_function_bytes = 7654321) by reflexivity.
    rewrite Hm. exact Hlim. }
  rewrite Hbig. rewrite vec_deref_spec.
  destruct (start_function_total ctx.(opiter_Context_results)) as [st [Hsf [Hpos Hsz]]].
  rewrite Hsf. cbn [bind].
  destruct (Inv_start C0 st ctx.(opiter_Context_results) Hlen1 Hsf) as [bt [Hinv Hbt]].
  (* the loop invariant at the start: the whole body is still to check, and the
     body frame is not a then-branch, so nothing is stashed behind it *)
  assert (Hok : todo_ok C0 [] [body_fview bt] [(es, None)]).
  { cbn [todo_ok child_results]. split; [|exact I].
    rewrite <- Hbt in Hchk. unfold b_e_type_checker_aux in Hchk.
    destruct (List.fold_left
                (check_single (upd_label C0
                   [translate_typelist (block_results_of bt)])) es
                (Some <<[], false>>)) as [ct|] eqn:Hf; [|discriminate Hchk].
    unfold frame_todo_ok. split; [|cbn [snd fv_ctrl body_fview]; discriminate].
    exists ct. cbn [fst]. split; [exact Hf | exact Hchk]. }
  apply (validate_body_loop_complete (Z.to_nat (to_Z (slice_len data)))
           V inst vis
           C0 bt module ctx data st [body_fview bt] [(es, None)] Hacc Hinv
           (body_first_start bt)
           Hmems Hlocals Hglobals Hret
           Hfuncs Htypes Htables Hfw10 Htw10 Hok).
  - rewrite (bytes_from_at_zero data _ Hpos).
    destruct Hexpr as [ops [Hsug Hops]]. exists ops.
    cbn [todo_ops todo_else_ops fst snd List.app]. split; [|exact Hops].
    (* [todo_ops] of the one entry is the body's own stream *)
    exact Hsug.
  - rewrite Hpos. rewrite Z2Nat.id by apply usize_nonneg. lia.
  - rewrite Hsz. rewrite Z2Nat.id by apply usize_nonneg. lia.
  - exact Hlim.
Qed.

(** The validating-only consumer accepts every operator, so completeness for
    [validate_body] itself has no hypothesis about hooks. *)
Corollary validate_body_complete : forall C0 module ctx data es,
  mems_agree module C0 -> locals_agree ctx C0 ->
  globals_agree module C0 -> return_agree ctx C0 ->
  funcs_agree module C0 -> types_agree module C0 -> tables_agree module C0 ->
  funcs_wasm10 module -> types_wasm10 module ->
  (List.length (vec_list ctx.(opiter_Context_results)) <= 1)%nat ->
  to_Z (slice_len data) <= 7654321 ->
  repr_expr (byte_list data) es [] ->
  b_e_type_checker_aux
    (upd_label C0 [translate_typelist (vec_list ctx.(opiter_Context_results))]) es
    (Tf [] (translate_typelist (vec_list ctx.(opiter_Context_results)))) = true ->
  opiter_validate_body data module ctx = Ok (Core_result_Result_Ok tt).
Proof.
  intros C0 module ctx data es Hmems Hlocals Hglobals Hret
         Hfuncs Htypes Htables Hfw10 Htw10 Hlen1 Hlim Hexpr Hchk.
  destruct (validate_body_with_complete _
              visit_NopVisitor_Insts_VeriwasmVisitOpVisitor tt C0 module ctx data
              es nop_hooks_accept Hmems Hlocals Hglobals Hret Hfuncs Htypes
              Htables Hfw10 Htw10 Hlen1 Hlim Hexpr Hchk) as [vis' Hw].
  unfold opiter_validate_body. rewrite Hw. cbn [bind]. reflexivity.
Qed.
