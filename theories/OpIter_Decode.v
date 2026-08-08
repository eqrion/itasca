(** * Decoder correspondence for the streaming validator

    The Rust byte cursor works on [slice u8] plus a [usize] index; the
    specification in Spec_Binary.v works on [list Z]. This file bridges the two
    and proves that each reader consumes exactly the bytes the specification
    relates.

    Nothing here mentions the operand or control stacks: decoding and typing are
    separate obligations, and only the typing half needs the simulation
    invariant. *)

Require Import Primitives.
Import Primitives.
Require Import Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Primitives_scope.
(* Aeneas_Specs already Requires and Includes the three extracted modules.
   Including them again here shadows Primitives constants such as u32_max with
   opaque copies, which blocks [unfold]. *)
Require Import Veriwasm.Aeneas_Specs.
Require Import Veriwasm.Translate.
Require Import Veriwasm.Spec_Binary.
Require Import Veriwasm.OpIter_State.

Open Scope Z_scope.

(* ================================================================== *)
(** ** The byte-list bridge                                            *)
(* ================================================================== *)

(** The specification's view of a slice: the numeric value of each byte. *)
Definition byte_list (data : slice u8) : list Z := List.map to_Z (vec_list data).

(** The bytes still ahead of the cursor. *)
Definition bytes_from (data : slice u8) (pos : usize) : list Z :=
  List.skipn (Z.to_nat (to_Z pos)) (byte_list data).

Lemma skipn_map_nth : forall {A B} (f : A -> B) k (l : list A) x,
  List.nth_error l k = Some x ->
  List.skipn k (List.map f l) = f x :: List.skipn (S k) (List.map f l).
Proof.
  intros A B f k. induction k as [|k IH]; intros l x H.
  - destruct l as [|h t]; [discriminate|]. simpl in H. injection H as ->.
    reflexivity.
  - destruct l as [|h t]; [discriminate|]. simpl in H. simpl.
    apply IH. exact H.
Qed.

(** Every byte value is in range, which the specification's guards need. *)
Lemma byte_list_bounded : forall data z,
  List.In z (byte_list data) -> 0 <= z < 256.
Proof.
  intros data z Hin. unfold byte_list in Hin.
  apply List.in_map_iff in Hin as [b [Heq _]]. subst z.
  destruct b as [bz [Hlo Hhi]].
  unfold scalar_min, u8_min in Hlo. unfold scalar_max, u8_max in Hhi.
  unfold to_Z. simpl. lia.
Qed.

(** The converse of [bytes_from_step], and the bridge every completeness proof
    starts from: the specification says a byte is there, so the code can read it.
    [bytes_from] is a [skipn] of a [map], so a cons means the index is in range,
    which is exactly what [slice_index_usize] and the cursor increment need. *)
Lemma bytes_from_uncons : forall data p z rest,
  bytes_from data p = z :: rest ->
  exists b p2,
    slice_index_usize data p = Ok b
    /\ to_Z b = z
    /\ usize_add p 1%usize = Ok p2
    /\ bytes_from data p2 = rest
    /\ to_Z p < to_Z (slice_len data).
Proof.
  intros data p z rest H. unfold bytes_from, byte_list in H.
  (* the type argument has to be [u8] and not its unfolding [scalar U8], or the
     lookup below will not match the one [slice_index_usize_spec] produces *)
  destruct (@skipn_map_cons_inv u8 Z to_Z _ _ _ _ H)
    as [b [Hnth [Hz [Hlt Hs]]]].
  destruct (usize_add_1_ok p) as [p2 [Hadd Hp2]].
  { pose proof (usize_le_max (slice_len data)) as Hm.
    rewrite slice_len_spec in Hm. pose proof (usize_nonneg p). lia. }
  exists b, p2. split.
  - rewrite slice_index_usize_spec. rewrite Hnth. reflexivity.
  - split; [exact Hz|]. split; [exact Hadd|]. split.
    + unfold bytes_from, byte_list. rewrite Hp2.
      rewrite (Z_to_nat_add1 _ (usize_nonneg p)). exact Hs.
    + rewrite slice_len_spec. pose proof (usize_nonneg p). lia.
Qed.

(** One cursor step, shared by [read_byte] and the LEB128 loop, which inlines
    the index-and-advance rather than calling [read_byte]. *)
Lemma bytes_from_step : forall data p b p2,
  slice_index_usize data p = Ok b ->
  usize_add p 1%usize = Ok p2 ->
  bytes_from data p = to_Z b :: bytes_from data p2 /\ to_Z p2 = to_Z p + 1.
Proof.
  intros data p b p2 Hidx Hadd.
  rewrite slice_index_usize_spec in Hidx.
  destruct (List.nth_error (vec_list data) (Z.to_nat (to_Z p))) as [b0|] eqn:Hnth;
    [|discriminate].
  injection Hidx as <-.
  assert (Hp2 : to_Z p2 = to_Z p + 1).
  { unfold usize_add, scalar_add in Hadd.
    apply mk_scalar_ok_to_Z in Hadd. rewrite Hadd. reflexivity. }
  split; [|exact Hp2].
  unfold bytes_from. rewrite Hp2.
  rewrite (Z_to_nat_add1 _ (usize_nonneg p)).
  unfold byte_list. apply skipn_map_nth. exact Hnth.
Qed.

(* ================================================================== *)
(** ** read_byte                                                       *)
(* ================================================================== *)

Lemma read_byte_ok : forall data pos b pos',
  reader_read_byte data pos = Ok (Core_result_Result_Ok (b, pos')) ->
  bytes_from data pos = to_Z b :: bytes_from data pos'
  /\ to_Z pos' = to_Z pos + 1.
Proof.
  intros data pos b pos' H. unfold reader_read_byte in H.
  destruct (pos s>= slice_len data) eqn:Hge; [discriminate|].
  destruct (slice_index_usize data pos) as [b0|] eqn:Hidx; cbn [bind] in H;
    [|discriminate].
  destruct (usize_add pos 1%usize) as [p1|] eqn:Hadd; cbn [bind] in H;
    [|discriminate].
  destruct (bytes_from_step data pos b0 p1 Hidx Hadd) as [Hbytes Hp1].
  injection H as Hb Hp. rewrite <- Hb, <- Hp. split; assumption.
Qed.

(** A successful read leaves the cursor no further than the end. The module
    decoder needs this of every reader: it subtracts the cursor from the length
    when checking that a section's contents are present, and that subtraction is
    on a [usize]. *)
Lemma read_byte_le_len : forall data pos b pos',
  reader_read_byte data pos = Ok (Core_result_Result_Ok (b, pos')) ->
  to_Z pos' <= to_Z (slice_len data).
Proof.
  intros data pos b pos' H. unfold reader_read_byte in H.
  destruct (pos s>= slice_len data) eqn:Hge; [discriminate|].
  apply scalar_geb_false_lt in Hge.
  destruct (slice_index_usize data pos) as [b0|] eqn:Hidx; cbn [bind] in H;
    [|discriminate].
  destruct (usize_add pos 1%usize) as [p1|] eqn:Hadd; cbn [bind] in H;
    [|discriminate].
  destruct (bytes_from_step data pos b0 p1 Hidx Hadd) as [_ Hp1].
  injection H as _ <-. lia.
Qed.

Lemma read_byte_err_at_end : forall data pos,
  Z.of_nat (List.length (vec_list data)) <= to_Z pos ->
  reader_read_byte data pos
    = Ok (Core_result_Result_Err Error_OpError_UnexpectedEof).
Proof.
  intros data pos Hend. unfold reader_read_byte.
  destruct (pos s>= slice_len data) eqn:Hge; [reflexivity|].
  apply scalar_geb_false_lt in Hge. rewrite slice_len_spec in Hge. lia.
Qed.

(* ================================================================== *)
(** ** LEB128                                                          *)
(* ================================================================== *)

Lemma pow128_le : forall a b, 0 <= a -> a <= b -> 128 ^ a <= 128 ^ b.
Proof. intros a b Ha Hab. apply Z.pow_le_mono_r; lia. Qed.

Lemma pow128_pos : forall a, 0 <= a -> 0 < 128 ^ a.
Proof. intros a Ha. apply Z.pow_pos_nonneg; lia. Qed.

(** Loop invariant: [i] bytes have been folded into [acc], [mult] is the place
    value of the next byte, and [acc] fits in the bits consumed so far.

    The last conjunct is what makes the u32 arithmetic overflow-free, and it is
    tight: at [i = 4] the accumulator reaches exactly [u32_max]. *)
Definition leb_inv (acc mult i : u32) : Prop :=
  0 <= to_Z i <= 4
  /\ to_Z mult = 128 ^ to_Z i
  /\ to_Z acc < 128 ^ to_Z i.

Lemma read_u32_leb_loop_sound : forall n data acc mult p i v p',
  to_Z i + Z.of_nat n = 4 ->
  leb_inv acc mult i ->
  reader_read_u32_leb_loop data acc mult p i
    = Ok (Core_result_Result_Ok (v, p')) ->
  exists m,
    0 <= m
    /\ repr_uN (32 - 7 * Z.to_nat (to_Z i))%nat (bytes_from data p) m
               (bytes_from data p')
    /\ to_Z v = to_Z acc + m * to_Z mult.
Proof.
  induction n as [|n IH]; intros data acc mult p i v p' Hn Hinv H;
    destruct Hinv as [Hi [Hmult Hacc]];
    pose proof (u8_bounds) as _;
    unfold reader_read_u32_leb_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H;
    destruct (p s>= slice_len data) eqn:Hge; [discriminate| |discriminate| ].
  - (* i = 4: the fifth byte must be the last, and carries only four bits. *)
    assert (Hi4 : to_Z i = 4) by (cbn in Hn; lia).
    destruct (slice_index_usize data p) as [b|] eqn:Hidx; cbn [bind] in H;
      [|discriminate];
    destruct (usize_add p 1%usize) as [p2|] eqn:Hadd; cbn [bind] in H;
      [|discriminate];
    destruct (u8_rem_128_ok b) as [low [Hrem [Hlowval Hlowbd]]];
    rewrite Hrem in H; cbn [bind] in H;
    destruct (bytes_from_step data p b p2 Hidx Hadd) as [Hbytes _].
    assert (Heq4 : (i s= 4%u32) = true).
    { unfold scalar_eqb. apply Z.eqb_eq. rewrite Hi4. reflexivity. }
    rewrite Heq4 in H. cbn beta iota in H.
    destruct (low s> 15%u8) eqn:Hgt; [discriminate|].
    apply scalar_gtb_false in Hgt.
    assert (H15 : to_Z 15%u8 = 15) by reflexivity. rewrite H15 in Hgt.
    pose proof (u8_bounds b) as [Hblo Hbhi].
    (* casts and arithmetic, with the bounds that keep them in range *)
    destruct (cast_u8_u32_ok low) as [c [Hcast Hcval]].
    rewrite Hcast in H. cbn [bind] in H.
    assert (Hmult4 : to_Z mult = 268435456) by (rewrite Hmult, Hi4; reflexivity).
    destruct (u32_mul_ok c mult) as [prod [Hmul Hmulval]].
    { rewrite Hcval, Hmult4. rewrite u32_max_val. lia. }
    rewrite Hmul in H. cbn [bind] in H.
    assert (Hacc4 : to_Z acc < 268435456) by (rewrite Hi4 in Hacc; exact Hacc).
    destruct (u32_add_ok acc prod) as [sum [Hadd2 Hsumval]].
    { rewrite Hmulval, Hcval, Hmult4. rewrite u32_max_val. lia. }
    rewrite Hadd2 in H. cbn [bind] in H.
    destruct (b s< 128%u8) eqn:Hlt.
    + (* last byte: build the base rule *)
      apply scalar_ltb_true in Hlt.
      assert (H128 : to_Z 128%u8 = 128) by reflexivity. rewrite H128 in Hlt.
      injection H as <- <-.
      exists (to_Z low). rewrite Hi4. cbn [Z.to_nat].
      assert (Hlowb : to_Z low = to_Z b).
      { rewrite Hlowval. apply Z.rem_small. lia. }
      split; [lia|]. split.
      * rewrite Hbytes, <- Hlowb. apply repr_uN_last; [lia | crunch_pow].
      * rewrite Hsumval, Hmulval, Hcval. lia.
    + (* a continuation bit on the fifth byte is rejected. The earlier
         [rewrite Heq4] already fired on this occurrence too. *)
      cbn beta iota in H. discriminate.
  - (* i < 4 *)
    assert (Hilt : to_Z i <= 3) by (cbn in Hn; lia).
    destruct (slice_index_usize data p) as [b|] eqn:Hidx; cbn [bind] in H;
      [|discriminate];
    destruct (usize_add p 1%usize) as [p2|] eqn:Hadd; cbn [bind] in H;
      [|discriminate];
    destruct (u8_rem_128_ok b) as [low [Hrem [Hlowval Hlowbd]]];
    rewrite Hrem in H; cbn [bind] in H;
    destruct (bytes_from_step data p b p2 Hidx Hadd) as [Hbytes _].
    assert (Heq4 : (i s= 4%u32) = false).
    { unfold scalar_eqb. apply Z.eqb_neq.
      assert (to_Z 4%u32 = 4) by reflexivity. lia. }
    rewrite Heq4 in H. cbn beta iota in H.
    pose proof (u8_bounds b) as [Hblo Hbhi].
    pose proof (pow128_pos (to_Z i) (proj1 Hi)) as Hmpos.
    pose proof (pow128_le (to_Z i) 3 (proj1 Hi) Hilt) as Hmle.
    assert (Hp3 : (128:Z) ^ 3 = 2097152) by reflexivity.
    assert (Hmle3 : 128 ^ to_Z i <= 2097152) by (rewrite <- Hp3; exact Hmle).
    (* [lia] is linear, so the products of two symbolic quantities below need
       their monotonicity steps supplied by hand. *)
    assert (Hprod : to_Z low * 128 ^ to_Z i <= 127 * 128 ^ to_Z i)
      by (apply Z.mul_le_mono_nonneg_r; lia).
    destruct (cast_u8_u32_ok low) as [c [Hcast Hcval]].
    rewrite Hcast in H. cbn [bind] in H.
    destruct (u32_mul_ok c mult) as [prod [Hmul Hmulval]].
    { rewrite Hcval, Hmult, u32_max_val. lia. }
    rewrite Hmul in H. cbn [bind] in H.
    destruct (u32_add_ok acc prod) as [sum [Hadd2 Hsumval]].
    { rewrite Hmulval, Hcval, Hmult, u32_max_val. lia. }
    rewrite Hadd2 in H. cbn [bind] in H.
    assert (Hbits : (7 < 32 - 7 * Z.to_nat (to_Z i))%nat).
    { assert (Z.to_nat (to_Z i) <= 3)%nat by lia. lia. }
    destruct (b s< 128%u8) eqn:Hlt.
    + (* last byte *)
      apply scalar_ltb_true in Hlt.
      assert (H128 : to_Z 128%u8 = 128) by reflexivity. rewrite H128 in Hlt.
      injection H as <- <-.
      assert (Hlowb : to_Z low = to_Z b).
      { rewrite Hlowval. apply Z.rem_small. lia. }
      exists (to_Z low). split; [lia|]. split.
      * rewrite Hbytes, <- Hlowb. apply repr_uN_last; [lia|].
        apply Z.lt_le_trans with (m := 128).
        { lia. }
        replace (128:Z) with (2 ^ 7) by reflexivity.
        apply Z.pow_le_mono_r; lia.
      * rewrite Hsumval, Hmulval, Hcval. lia.
    + (* continuation: recurse, then wrap with the inductive rule *)
      apply scalar_ltb_false in Hlt.
      assert (H128 : to_Z 128%u8 = 128) by reflexivity. rewrite H128 in Hlt.
      cbn beta iota in H.
      destruct (u32_mul_ok mult 128%u32) as [mult2 [Hm2 Hm2val]].
      { rewrite Hmult, u32_max_val.
        assert (to_Z 128%u32 = 128) by reflexivity. lia. }
      rewrite Hm2 in H. cbn [bind] in H.
      destruct (u32_add_ok i 1%u32) as [i5 [Hi5 Hi5val]].
      { rewrite u32_max_val. assert (to_Z 1%u32 = 1) by reflexivity. lia. }
      rewrite Hi5 in H. cbn [bind] in H.
      assert (Hi5v : to_Z i5 = to_Z i + 1).
      { rewrite Hi5val. assert (to_Z 1%u32 = 1) by reflexivity. lia. }
      assert (Hm2v : to_Z mult2 = 128 ^ (to_Z i + 1)).
      { rewrite Hm2val, Hmult.
        assert (to_Z 128%u32 = 128) by reflexivity.
        rewrite Z.pow_add_r by lia. lia. }
      assert (Hlowb : to_Z low = to_Z b - 128).
      { rewrite Hlowval, Z.rem_mod_nonneg by lia.
        replace (to_Z b) with ((to_Z b - 128) + 1 * 128) at 1 by lia.
        rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
      destruct (IH data sum mult2 p2 i5 v p') as [m' [Hm'nn [Hm'rel Hm'val]]].
      { rewrite Hi5v. cbn in Hn |- *. lia. }
      { unfold leb_inv. rewrite Hi5v, Hm2v. split; [lia|]. split; [reflexivity|].
        rewrite Hsumval, Hmulval, Hcval, Hmult, Z.pow_add_r by lia. lia. }
      { exact H. }
      exists (128 * m' + (to_Z b - 128)). split; [lia|]. split.
      * rewrite Hbytes. apply repr_uN_more; [lia | exact Hbits |].
        replace (32 - 7 * Z.to_nat (to_Z i) - 7)%nat
           with (32 - 7 * Z.to_nat (to_Z i5))%nat.
        { exact Hm'rel. }
        rewrite Hi5v, (Z_to_nat_add1 _ (proj1 Hi)). lia.
      * rewrite Hm'val, Hsumval, Hmulval, Hcval, Hlowb, Hm2v, Hmult.
        rewrite Z.pow_add_r by lia. ring.
Qed.

(** P1: the Rust LEB128 reader agrees with the specification. Entering the loop
    at [i = 0] means four further iterations are permitted, and the invariant
    holds trivially since [128 ^ 0 = 1]. *)
Theorem read_u32_leb_sound : forall data pos v pos',
  reader_read_u32_leb data pos = Ok (Core_result_Result_Ok (v, pos')) ->
  repr_u32 (bytes_from data pos) (to_Z v) (bytes_from data pos').
Proof.
  intros data pos v pos' H. unfold reader_read_u32_leb in H.
  destruct (read_u32_leb_loop_sound 4 data 0%u32 1%u32 pos 0%u32 v pos')
    as [m [Hmnn [Hrel Hval]]].
  - reflexivity.
  - unfold leb_inv. cbn. lia.
  - exact H.
  - unfold repr_u32.
    replace (32 - 7 * Z.to_nat (to_Z 0%u32))%nat with 32%nat in Hrel
      by reflexivity.
    assert (Hv : to_Z v = m).
    { rewrite Hval. cbn. lia. }
    rewrite Hv. exact Hrel.
Qed.

(* ================================================================== *)
(** ** The remaining immediate decoders                                *)
(* ================================================================== *)

(** [read_op] consumes exactly the opcode byte. *)
Lemma read_op_sound : forall st data b st',
  opiter_read_op st data = Ok (Core_result_Result_Ok b, st') ->
  bytes_from data st.(opiter_OpIterState_pos)
    = to_Z b :: bytes_from data st'.(opiter_OpIterState_pos).
Proof.
  intros st data b st' H. unfold opiter_read_op in H.
  destruct (reader_read_byte data st.(opiter_OpIterState_pos)) as [r|] eqn:Hrb;
    cbn [bind] in H; [|discriminate].
  destruct r as [[b0 p0]|e].
  - rewrite branch_ok in H. cbn [bind] in H. injection H as <- <-.
    cbn [opiter_OpIterState_pos].
    destruct (read_byte_ok data st.(opiter_OpIterState_pos) b0 p0 Hrb) as [Hb _].
    exact Hb.
  - rewrite branch_err in H. cbn [bind] in H.
    rewrite from_residual_err in H. cbn [bind] in H. discriminate.
Qed.

(** The reserved byte [memory.size] and [memory.grow] carry: exactly one byte,
    and it is the literal zero the specification writes. *)
Lemma read_reserved_zero_sound : forall st data st',
  opiter_read_reserved_zero st data = Ok (Core_result_Result_Ok tt, st') ->
  bytes_from data st.(opiter_OpIterState_pos)
    = 0 :: bytes_from data st'.(opiter_OpIterState_pos).
Proof.
  intros st data st' H. unfold opiter_read_reserved_zero in H.
  destruct (reader_read_byte data st.(opiter_OpIterState_pos)) as [r|] eqn:Hrb;
    cbn [bind] in H; [|discriminate].
  destruct r as [[b p]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (b s<> 0%u8) eqn:Hz; [discriminate|].
  injection H as <-. cbn [opiter_OpIterState_pos].
  destruct (read_byte_ok data st.(opiter_OpIterState_pos) b p Hrb) as [Hb _].
  rewrite Hb. apply scalar_neqb_false in Hz.
  assert (Hz0 : to_Z b = 0) by (rewrite Hz; reflexivity).
  rewrite Hz0. reflexivity.
Qed.

(** The two readers consume the opcode and the reserved byte and nothing else:
    the memory check and the stack work leave the cursor alone. *)
Lemma read_memory_size_reserved : forall st data module st',
  opiter_read_memory_size st data module = Ok (Core_result_Result_Ok tt, st') ->
  bytes_from data st.(opiter_OpIterState_pos)
    = 0 :: bytes_from data st'.(opiter_OpIterState_pos).
Proof.
  intros st data module st' H. unfold opiter_read_memory_size in H.
  destruct (opiter_take_pending st opiter_op_memory_size) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st _ r0 st1 Htp) as Hp1. unfold pos_of in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_read_reserved_zero st1 data) as [[r1 st2]|] eqn:Hrz;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [u1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u1. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_require_memory module) as [r2|] eqn:Hrm; cbn [bind] in H;
    [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val st2 (Opiter_StackType_Val Types_ValueType_I32))
    as [st3|] eqn:Hpv; cbn [bind] in H; [|discriminate].
  injection H as <-.
  pose proof (push_val_pos st2 _ st3 Hpv) as Hp3. unfold pos_of in Hp3.
  rewrite Hp3. rewrite <- Hp1.
  apply (read_reserved_zero_sound st1 data st2 Hrz).
Qed.

Lemma read_memory_grow_reserved : forall st data module st',
  opiter_read_memory_grow st data module = Ok (Core_result_Result_Ok tt, st') ->
  bytes_from data st.(opiter_OpIterState_pos)
    = 0 :: bytes_from data st'.(opiter_OpIterState_pos).
Proof.
  intros st data module st' H. unfold opiter_read_memory_grow in H.
  destruct (opiter_take_pending st opiter_op_memory_grow) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st _ r0 st1 Htp) as Hp1. unfold pos_of in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_read_reserved_zero st1 data) as [[r1 st2]|] eqn:Hrz;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [u1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u1. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_require_memory module) as [r2|] eqn:Hrm; cbn [bind] in H;
    [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_pop_with_type st2 Types_ValueType_I32) as [[r3 st3]|] eqn:Hp3;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos st2 _ r3 st3 Hp3) as Hpp. unfold pos_of in Hpp.
  destruct r3 as [t3|e3].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val st3 (Opiter_StackType_Val Types_ValueType_I32))
    as [st4|] eqn:Hpv; cbn [bind] in H; [|discriminate].
  injection H as <-.
  pose proof (push_val_pos st3 _ st4 Hpv) as Hp4. unfold pos_of in Hp4.
  rewrite Hp4. rewrite Hpp. rewrite <- Hp1.
  apply (read_reserved_zero_sound st1 data st2 Hrz).
Qed.

(** Spec 5.3.3 is a one-byte table, and the Rust is the same table written as a
    comparison chain, so each accepted byte has to line up with
    [blocktype_spec]. *)
Lemma read_block_type_sound : forall data pos bt pos',
  opiter_read_block_type data pos = Ok (Core_result_Result_Ok (bt, pos')) ->
  exists bb,
    bytes_from data pos = bb :: bytes_from data pos'
    /\ blocktype_spec bb = Some (translate_bt bt).
Proof.
  intros data pos bt pos' H. unfold opiter_read_block_type in H.
  destruct (reader_read_byte data pos) as [r|] eqn:Hrb; cbn [bind] in H;
    [|discriminate].
  destruct r as [[b0 p0]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (read_byte_ok data pos b0 p0 Hrb) as [Hbytes _].
  exists (to_Z b0).
  (* One case per row of the table; each fixes the byte to a literal. *)
  destruct (b0 s= 64%u8) eqn:E64;
    [ apply scalar_eqb_true in E64; injection H as <- <-;
      split; [exact Hbytes|];
      unfold blocktype_spec; rewrite E64; reflexivity | ].
  destruct (b0 s= 127%u8) eqn:E127;
    [ apply scalar_eqb_true in E127; injection H as <- <-;
      split; [exact Hbytes|];
      unfold blocktype_spec, valtype_spec; rewrite E127; reflexivity | ].
  destruct (b0 s= 126%u8) eqn:E126;
    [ apply scalar_eqb_true in E126; injection H as <- <-;
      split; [exact Hbytes|];
      unfold blocktype_spec, valtype_spec; rewrite E126; reflexivity | ].
  destruct (b0 s= 125%u8) eqn:E125;
    [ apply scalar_eqb_true in E125; injection H as <- <-;
      split; [exact Hbytes|];
      unfold blocktype_spec, valtype_spec; rewrite E125; reflexivity | ].
  destruct (b0 s= 124%u8) eqn:E124;
    [ apply scalar_eqb_true in E124; injection H as <- <-;
      split; [exact Hbytes|];
      unfold blocktype_spec, valtype_spec; rewrite E124; reflexivity | ].
  discriminate.
Qed.

(** Spec 5.4.6: two u32s back to back. *)
Lemma read_memarg_sound : forall st data m st',
  opiter_read_memarg st data = Ok (Core_result_Result_Ok m, st') ->
  repr_memarg (bytes_from data st.(opiter_OpIterState_pos))
              (to_Z m.(opiter_MemArg_align), to_Z m.(opiter_MemArg_offset))
              (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros st data m st' H. unfold opiter_read_memarg in H.
  destruct (reader_read_u32_leb data st.(opiter_OpIterState_pos)) as [r1|] eqn:H1;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [[a p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_u32_leb data p1) as [r2|] eqn:H2; cbn [bind] in H;
    [|discriminate].
  destruct r2 as [[o p2]|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  injection H as <- <-.
  cbn [opiter_OpIterState_pos opiter_MemArg_align opiter_MemArg_offset].
  apply repr_memarg_intro with (mid := bytes_from data p1).
  - apply read_u32_leb_sound. exact H1.
  - apply read_u32_leb_sound. exact H2.
Qed.

(* ================================================================== *)
(** ** Signed LEB128                                                   *)
(* ================================================================== *)

Lemma pow128_as_pow2 : forall a, 0 <= a -> 128 ^ a = 2 ^ (7 * a).
Proof.
  intros a Ha. replace (128:Z) with (2 ^ 7) by reflexivity.
  rewrite <- Z.pow_mul_r; [reflexivity | lia | lia].
Qed.

Lemma pow2_split : forall w a, 0 <= a -> 7 * a <= w - 1 ->
  2 ^ (w - 1 - 7 * a) * 2 ^ (7 * a) = 2 ^ (w - 1).
Proof.
  intros w a Ha Hle. rewrite <- Z.pow_add_r; [|lia|lia]. f_equal. lia.
Qed.

(** The specification indexes its guards by remaining bit width; the Rust works
    with the byte index. *)
Lemma sbits_eq : forall bits (i : u32),
  0 <= to_Z i -> 7 * to_Z i <= Z.of_nat bits ->
  Z.of_nat (bits - 7 * Z.to_nat (to_Z i))%nat - 1
    = Z.of_nat bits - 1 - 7 * to_Z i.
Proof. intros bits i Hi Hle. lia. Qed.

(** One signed reader serves both widths, so one set of proofs does too: [last]
    is the index of the final permitted byte and [lo]/[hi] the value bounds, and
    this is what ties them to the specification's [bits].

    [1 <= bits - 7 * last <= 7] says [last] is the right byte budget: at least one
    bit is left for the final byte, and not enough for another byte after it. For
    32 bits that is [last = 4] with four bits left, for 64 bits [last = 9] with
    one. The last conjunct keeps the accumulator inside [i128], where the place
    value reaches [128 ^ 9 = 2 ^ 63] and an [i64] would overflow. *)
Definition sleb_params (bits : nat) (last : u32) (lo hi : i128) : Prop :=
  1 <= Z.of_nat bits - 7 * to_Z last <= 7
  /\ to_Z lo = - 2 ^ (Z.of_nat bits - 1)
  /\ to_Z hi = 2 ^ (Z.of_nat bits - 1) - 1
  /\ 128 ^ (to_Z last + 1) <= i128_max.

Lemma sleb_params_32 : sleb_params 32 4%u32 (-2147483648)%i128 2147483647%i128.
Proof.
  unfold sleb_params. repeat split; vm_compute; first [reflexivity|discriminate].
Qed.

Lemma sleb_params_64 :
  sleb_params 64 9%u32 (-9223372036854775808)%i128 9223372036854775807%i128.
Proof.
  unfold sleb_params. repeat split; vm_compute; first [reflexivity|discriminate].
Qed.

(** The accumulator holds the payload read so far; [mult] is the place value the
    next byte gets. *)
Definition sleb_inv (last : u32) (acc mult : i128) (i : u32) : Prop :=
  0 <= to_Z i <= to_Z last
  /\ to_Z mult = 128 ^ to_Z i
  /\ 0 <= to_Z acc < 128 ^ to_Z i.

(** The bounds every arithmetic step of the loop needs. The place value and the
    accumulator are both under [128 ^ last], so every product and sum stays under
    [128 ^ (last + 1)], which [sleb_params] puts inside [i128]. *)
Lemma sleb_bounds : forall bits last lo hi acc mult i,
  sleb_params bits last lo hi -> sleb_inv last acc mult i ->
  0 < to_Z mult
  /\ to_Z mult <= 128 ^ to_Z last
  /\ 0 <= to_Z acc < to_Z mult
  /\ 128 * 128 ^ to_Z last <= i128_max
  /\ i128_min = - i128_max - 1.
Proof.
  intros bits last lo hi acc mult i [_ [_ [_ Hbig]]] [Hi [Hmult Hacc]].
  assert (Hstep : 128 ^ (to_Z last + 1) = 128 * 128 ^ to_Z last).
  { rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r. ring. }
  assert (Hmpos : 0 < to_Z mult) by (rewrite Hmult; apply pow128_pos; lia).
  assert (Hmle : to_Z mult <= 128 ^ to_Z last)
    by (rewrite Hmult; apply pow128_le; lia).
  assert (Haccm : 0 <= to_Z acc < to_Z mult) by (rewrite Hmult; exact Hacc).
  assert (Hbig2 : 128 * 128 ^ to_Z last <= i128_max)
    by (rewrite <- Hstep; exact Hbig).
  assert (Hmm : i128_min = - i128_max - 1)
    by (rewrite i128_min_val; rewrite i128_max_val; lia).
  split; [exact Hmpos|]. split; [exact Hmle|]. split; [exact Haccm|].
  split; [exact Hbig2 | exact Hmm].
Qed.

Lemma read_sn_leb_loop_sound : forall n bits data last lo hi acc mult p i v p',
  sleb_params bits last lo hi ->
  to_Z i + Z.of_nat n = to_Z last ->
  sleb_inv last acc mult i ->
  reader_read_sn_leb_loop data last lo hi acc mult p i
    = Ok (Core_result_Result_Ok (v, p')) ->
  exists m,
    repr_sN (bits - 7 * Z.to_nat (to_Z i))%nat (bytes_from data p) m
            (bytes_from data p')
    /\ to_Z v = to_Z acc + m * to_Z mult
    /\ to_Z lo <= to_Z v <= to_Z hi.
Proof.
  induction n as [|n IH];
    intros bits data last lo hi acc mult p i v p' Hpar Hn Hinv H;
    pose proof (sleb_bounds bits last lo hi acc mult i Hpar Hinv)
      as [Hmpos [Hmle [Haccm [Hbig' Hminmax]]]];
    pose proof Hpar as Hpar2; destruct Hpar2 as [Hbits [Hlov [Hhiv _]]];
    pose proof Hinv as Hinv2; destruct Hinv2 as [Hi [Hmult Hacc]];
    unfold reader_read_sn_leb_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H;
    destruct (p s>= slice_len data) eqn:Hge; [discriminate| |discriminate| ].
  (* the byte, the payload and the fold are the same in both *)
  all: destruct (slice_index_usize data p) as [b|] eqn:Hidx; cbn [bind] in H;
         [|discriminate].
  all: destruct (usize_add p 1%usize) as [p2|] eqn:Hadd; cbn [bind] in H;
         [|discriminate].
  all: destruct (u8_rem_128_ok b) as [low [Hrem [Hlowval Hlowbd]]].
  all: rewrite Hrem in H; cbn [bind] in H.
  all: destruct (bytes_from_step data p b p2 Hidx Hadd) as [Hbytes _].
  all: pose proof (u8_bounds b) as [Hblo Hbhi].
  all: assert (Hlm0 : 0 <= to_Z low * to_Z mult)
         by (apply Z.mul_nonneg_nonneg; lia).
  all: assert (Hlm : to_Z low * to_Z mult <= 127 * to_Z mult)
         by (apply Z.mul_le_mono_nonneg_r; lia).
  all: destruct (cast_u8_i128_ok low) as [c [Hcast Hcval]].
  all: rewrite Hcast in H; cbn [bind] in H.
  all: assert (Hmulb : i128_min <= to_Z c * to_Z mult <= i128_max)
         by (rewrite Hcval; lia).
  all: destruct (i128_mul_ok c mult Hmulb) as [prod [Hmul Hmulval]].
  all: rewrite Hmul in H; cbn [bind] in H.
  all: assert (Haddb : i128_min <= to_Z acc + to_Z prod <= i128_max)
         by (rewrite Hmulval; rewrite Hcval; lia).
  all: destruct (i128_add_ok acc prod Haddb) as [sum [Hadd2 Hsumval]].
  all: rewrite Hadd2 in H; cbn [bind] in H.
  all: assert (Hsumv : to_Z sum = to_Z acc + to_Z low * to_Z mult)
         by (rewrite Hsumval; rewrite Hmulval; rewrite Hcval; reflexivity).
  (* the last byte, whichever iteration it falls on: fold the payload in,
     apply the sign, and read the range check backwards. A byte without the
     continuation bit is the final one at any [i], so the two goals share a
     script. *)
  all: destruct (b s< 128%u8) eqn:Hlt.
  1,3:
apply scalar_ltb_true in Hlt;
  assert (H128u : to_Z 128%u8 = 128) by reflexivity; rewrite H128u in Hlt;
  assert (Hlowb : to_Z low = to_Z b)
    by (rewrite Hlowval; apply Z.rem_small; lia);
  assert (Hexp : 7 * to_Z i <= Z.of_nat bits - 1) by lia;
  assert (Hpow : to_Z mult = 2 ^ (7 * to_Z i))
    by (rewrite Hmult; apply pow128_as_pow2; lia);
  assert (Hsb : Z.of_nat (bits - 7 * Z.to_nat (to_Z i))%nat - 1
                = Z.of_nat bits - 1 - 7 * to_Z i)
    by (apply sbits_eq; lia);
  assert (Hsplit : 2 ^ (Z.of_nat bits - 1 - 7 * to_Z i) * 2 ^ (7 * to_Z i)
                   = 2 ^ (Z.of_nat bits - 1))
    by (apply pow2_split; lia);
  assert (Hpnn : 0 <= 2 ^ (7 * to_Z i)) by (apply Z.pow_nonneg; lia);
  destruct (low s>= 64%u8) eqn:Hsign;
  [ (* negative: one place value is subtracted *)
    apply scalar_geb_true_ge in Hsign;
    assert (H64u : to_Z 64%u8 = 64) by reflexivity; rewrite H64u in Hsign;
    assert (Hmb : i128_min <= to_Z mult * to_Z 128%i128 <= i128_max)
      by (assert (H128i : to_Z 128%i128 = 128) by reflexivity; lia);
    destruct (i128_mul_ok mult 128%i128 Hmb) as [m128 [Hm128 Hm128val]];
    rewrite Hm128 in H; cbn [bind] in H;
    assert (Hm128v : to_Z m128 = to_Z mult * 128)
      by (rewrite Hm128val; reflexivity);
    assert (Hsb2 : i128_min <= to_Z sum - to_Z m128 <= i128_max) by lia;
    destruct (i128_sub_ok sum m128 Hsb2) as [acc3 [Hsub Hacc3val]];
    rewrite Hsub in H; cbn [bind] in H;
    assert (Hacc3 : to_Z acc3 = to_Z acc + (to_Z b - 128) * to_Z mult)
      by (rewrite Hacc3val; rewrite Hm128v; rewrite Hsumv; rewrite Hlowb; ring);
    destruct (acc3 s< lo) eqn:Hc1; [discriminate|];
    apply scalar_ltb_false in Hc1;
    destruct (acc3 s> hi) eqn:Hc2; [discriminate|];
    apply scalar_gtb_false in Hc2;
    injection H as <- <-;
    exists (to_Z b - 128);
    split;
    [ rewrite Hbytes; apply repr_sN_neg; [lia|]; rewrite Hsb;
      apply Z.nlt_ge; intro Hcon;
      assert (Hprod : (to_Z b - 128) * 2 ^ (7 * to_Z i)
                <= (- 2 ^ (Z.of_nat bits - 1 - 7 * to_Z i) - 1)
                   * 2 ^ (7 * to_Z i))
        by (apply Z.mul_le_mono_nonneg_r; lia);
      assert (Hopen : (- 2 ^ (Z.of_nat bits - 1 - 7 * to_Z i) - 1)
                      * 2 ^ (7 * to_Z i)
                = - (2 ^ (Z.of_nat bits - 1 - 7 * to_Z i) * 2 ^ (7 * to_Z i))
                  - 2 ^ (7 * to_Z i)) by ring;
      rewrite Hsplit in Hopen; rewrite Hpow in Hacc3; lia
    | split; [rewrite Hacc3; ring | lia] ]
  | (* non-negative: the fold is the value *)
    apply scalar_geb_false_lt in Hsign;
    assert (H64u : to_Z 64%u8 = 64) by reflexivity; rewrite H64u in Hsign;
    cbn [bind] in H;
    destruct (sum s< lo) eqn:Hc1; [discriminate|];
    apply scalar_ltb_false in Hc1;
    destruct (sum s> hi) eqn:Hc2; [discriminate|];
    apply scalar_gtb_false in Hc2;
    injection H as <- <-;
    exists (to_Z b);
    split;
    [ rewrite Hbytes; apply repr_sN_pos; [lia|]; rewrite Hsb;
      apply Z.nle_gt; intro Hcon;
      assert (Hprod : 2 ^ (Z.of_nat bits - 1 - 7 * to_Z i) * 2 ^ (7 * to_Z i)
                <= to_Z b * 2 ^ (7 * to_Z i))
        by (apply Z.mul_le_mono_nonneg_r; lia);
      rewrite Hsplit in Hprod; rewrite Hpow in Hsumv; rewrite Hlowb in Hsumv;
      lia
    | split; [rewrite Hsumv; rewrite Hlowb; ring | lia] ] ].
  - (* the budget is spent, so a continuation byte is rejected *)
    assert (Hilast : to_Z i = to_Z last) by (cbn in Hn; lia).
    assert (Heq : (i s= last) = true)
      by (unfold scalar_eqb; apply Z.eqb_eq; exact Hilast).
    rewrite Heq in H. cbn beta iota in H. discriminate.
  - (* a continuation byte: fold it in and go round again *)
    apply scalar_ltb_false in Hlt.
    assert (H128u : to_Z 128%u8 = 128) by reflexivity. rewrite H128u in Hlt.
    assert (Hilt : to_Z i < to_Z last) by (cbn in Hn; lia).
    assert (Heq : (i s= last) = false)
      by (unfold scalar_eqb; apply Z.eqb_neq; lia).
    rewrite Heq in H. cbn beta iota in H.
    assert (Hlowb : to_Z low = to_Z b - 128).
    { rewrite Hlowval. rewrite Z.rem_mod_nonneg by lia.
      replace (to_Z b) with ((to_Z b - 128) + 1 * 128) at 1 by lia.
      rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
    assert (H128i : to_Z 128%i128 = 128) by reflexivity.
    assert (Hmb : i128_min <= to_Z mult * to_Z 128%i128 <= i128_max) by lia.
    destruct (i128_mul_ok mult 128%i128 Hmb) as [mult2 [Hm2 Hm2val]].
    rewrite Hm2 in H. cbn [bind] in H.
    assert (H1u : to_Z 1%u32 = 1) by reflexivity.
    destruct (u32_add_ok i 1%u32) as [i5 [Hi5 Hi5val]].
    { rewrite H1u. pose proof (u32_bounds last) as [_ Hlm2]. lia. }
    rewrite Hi5 in H. cbn [bind] in H.
    assert (Hi5v : to_Z i5 = to_Z i + 1) by (rewrite Hi5val; rewrite H1u; lia).
    assert (Hm2v : to_Z mult2 = 128 ^ (to_Z i + 1)).
    { rewrite Hm2val. rewrite H128i. rewrite Hmult.
      rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r. ring. }
    destruct (IH bits data last lo hi sum mult2 p2 i5 v p')
      as [m' [Hm'rel [Hm'val Hm'rng]]].
    + exact Hpar.
    + rewrite Hi5v. cbn in Hn |- *. lia.
    + unfold sleb_inv. rewrite Hi5v. rewrite Hm2v. split; [lia|].
      split; [reflexivity|]. rewrite Hsumv. rewrite Z.pow_add_r by lia.
      rewrite Z.pow_1_r. rewrite <- Hmult. lia.
    + exact H.
    + exists (128 * m' + (to_Z b - 128)). split.
      * rewrite Hbytes. apply repr_sN_more; [lia | lia |].
        replace (bits - 7 * Z.to_nat (to_Z i) - 7)%nat
           with (bits - 7 * Z.to_nat (to_Z i5))%nat; [exact Hm'rel|].
        rewrite Hi5v. rewrite (Z_to_nat_add1 _ (proj1 Hi)). lia.
      * split; [|exact Hm'rng].
        rewrite Hm'val. rewrite Hsumv. rewrite Hlowb. rewrite Hm2v.
        rewrite Hmult. rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r. ring.
Qed.

(** The two instances. Each is the loop at [i = 0] plus the narrowing cast, whose
    precondition is the range the loop already checked. *)
Theorem read_s32_leb_sound : forall data pos v pos',
  reader_read_s32_leb data pos = Ok (Core_result_Result_Ok (v, pos')) ->
  repr_s32 (bytes_from data pos) (to_Z v) (bytes_from data pos').
Proof.
  intros data pos v pos' H. unfold reader_read_s32_leb, reader_read_sn_leb in H.
  destruct (reader_read_sn_leb_loop data 4%u32 (-2147483648)%i128
              2147483647%i128 0%i128 1%i128 pos 0%u32) as [r|] eqn:Hleb;
    cbn [bind] in H; [|discriminate].
  destruct r as [[v0 p0]|e].
  2: { rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
       cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (scalar_cast I128 I32 v0) as [v1|] eqn:Hc; cbn [bind] in H;
    [|discriminate].
  injection H as <- <-.
  unfold scalar_cast in Hc. apply mk_scalar_ok_to_Z in Hc.
  destruct (read_sn_leb_loop_sound 4 32 data 4%u32 (-2147483648)%i128
              2147483647%i128 0%i128 1%i128 pos 0%u32 v0 p0)
    as [m [Hrel [Hval _]]].
  - apply sleb_params_32.
  - reflexivity.
  - unfold sleb_inv. cbn. lia.
  - exact Hleb.
  - unfold repr_s32.
    replace (32 - 7 * Z.to_nat (to_Z 0%u32))%nat with 32%nat in Hrel
      by reflexivity.
    assert (Hv : to_Z v1 = m) by (rewrite Hc; rewrite Hval; cbn; lia).
    rewrite Hv. exact Hrel.
Qed.

Theorem read_s64_leb_sound : forall data pos v pos',
  reader_read_s64_leb data pos = Ok (Core_result_Result_Ok (v, pos')) ->
  repr_sN 64 (bytes_from data pos) (to_Z v) (bytes_from data pos').
Proof.
  intros data pos v pos' H. unfold reader_read_s64_leb, reader_read_sn_leb in H.
  destruct (reader_read_sn_leb_loop data 9%u32 (-9223372036854775808)%i128
              9223372036854775807%i128 0%i128 1%i128 pos 0%u32) as [r|] eqn:Hleb;
    cbn [bind] in H; [|discriminate].
  destruct r as [[v0 p0]|e].
  2: { rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
       cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (scalar_cast I128 I64 v0) as [v1|] eqn:Hc; cbn [bind] in H;
    [|discriminate].
  injection H as <- <-.
  unfold scalar_cast in Hc. apply mk_scalar_ok_to_Z in Hc.
  destruct (read_sn_leb_loop_sound 9 64 data 9%u32 (-9223372036854775808)%i128
              9223372036854775807%i128 0%i128 1%i128 pos 0%u32 v0 p0)
    as [m [Hrel [Hval _]]].
  - apply sleb_params_64.
  - reflexivity.
  - unfold sleb_inv. cbn. lia.
  - exact Hleb.
  - replace (64 - 7 * Z.to_nat (to_Z 0%u32))%nat with 64%nat in Hrel
      by reflexivity.
    assert (Hv : to_Z v1 = m) by (rewrite Hc; rewrite Hval; cbn; lia).
    rewrite Hv. exact Hrel.
Qed.

(* ================================================================== *)
(** ** Little-endian byte patterns                                     *)
(* ================================================================== *)

Lemma pow256_pos : forall a, 0 <= a -> 0 < 256 ^ a.
Proof. intros a Ha. apply Z.pow_pos_nonneg; lia. Qed.

Lemma pow256_le : forall a b, 0 <= a -> a <= b -> 256 ^ a <= 256 ^ b.
Proof. intros a b Ha Hb. apply Z.pow_le_mono_r; lia. Qed.

(** [n] is the byte count asked for and [i] how many have been read, so [mult] is
    the place value the next byte gets. The loop stops multiplying after the last
    byte because [256 ^ 8] does not fit in a [u64], which is what keeps
    [mult = 256 ^ i] an invariant rather than a special case. *)
Definition fbits_inv (n acc mult i : Z) : Prop :=
  0 <= i <= n
  /\ n <= 8
  /\ mult = 256 ^ i
  /\ 0 <= acc < 256 ^ i.

(** Every step's arithmetic bound: after [i] bytes the accumulator is under
    [256 ^ i], so folding one more byte in stays under [256 ^ (i+1)], and
    [i + 1 <= n <= 8] puts that inside a [u64]. *)
Lemma fbits_step_bound : forall n acc mult i b,
  fbits_inv n acc mult i -> i < n -> 0 <= b <= 255 ->
  0 <= b * mult
  /\ b * mult <= 255 * mult
  /\ acc + b * mult <= u64_max
  /\ 256 ^ i * 256 = 256 ^ (i + 1)
  /\ 256 ^ (i + 1) <= 256 ^ 8
  /\ (256:Z) ^ 8 = 18446744073709551616.
Proof.
  intros n acc mult i b [Hi [Hn [Hmult Hacc]]] Hlt Hb.
  assert (Hmpos : 0 < mult) by (rewrite Hmult; apply pow256_pos; lia).
  assert (Hstep : 256 ^ i * 256 = 256 ^ (i + 1))
    by (rewrite Z.pow_add_r by lia; rewrite Z.pow_1_r; reflexivity).
  assert (Hle : 256 ^ (i + 1) <= 256 ^ 8) by (apply pow256_le; lia).
  assert (H8 : (256:Z) ^ 8 = 18446744073709551616) by reflexivity.
  assert (Hbm0 : 0 <= b * mult) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hbm : b * mult <= 255 * mult)
    by (apply Z.mul_le_mono_nonneg_r; lia).
  split; [exact Hbm0|]. split; [exact Hbm|].
  split; [|split; [exact Hstep | split; [exact Hle | exact H8]]].
  rewrite u64_max_val. lia.
Qed.

Lemma read_fn_bits_loop_sound : forall k data n acc mult p i v p',
  to_Z i + Z.of_nat k = to_Z n ->
  fbits_inv (to_Z n) (to_Z acc) (to_Z mult) (to_Z i) ->
  reader_read_fn_bits_loop data n acc mult p i
    = Ok (Core_result_Result_Ok (v, p')) ->
  exists m,
    repr_bytes_le k (bytes_from data p) m (bytes_from data p')
    /\ to_Z v = to_Z acc + m * to_Z mult.
Proof.
  induction k as [|k IH]; intros data n acc mult p i v p' Hn Hinv H;
    pose proof Hinv as Hinv2; destruct Hinv2 as [Hi [Hnle [Hmult Hacc]]];
    unfold reader_read_fn_bits_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H.
  - (* the count is reached, so the loop returns what it has *)
    assert (Heq : (i s= n) = true)
      by (unfold scalar_eqb; apply Z.eqb_eq; cbn in Hn; lia).
    rewrite Heq in H. cbn beta iota in H. injection H as <- <-.
    exists 0. split; [apply repr_bytes_le_nil | lia].
  - assert (Hilt : to_Z i < to_Z n) by (cbn in Hn; lia).
    assert (Heq : (i s= n) = false)
      by (unfold scalar_eqb; apply Z.eqb_neq; lia).
    rewrite Heq in H. cbn beta iota in H.
    destruct (p s>= slice_len data) eqn:Hge; [discriminate|].
    destruct (slice_index_usize data p) as [b|] eqn:Hidx; cbn [bind] in H;
      [|discriminate].
    destruct (usize_add p 1%usize) as [p2|] eqn:Hadd; cbn [bind] in H;
      [|discriminate].
    destruct (bytes_from_step data p b p2 Hidx Hadd) as [Hbytes _].
    pose proof (u8_bounds b) as [Hblo Hbhi].
    destruct (fbits_step_bound (to_Z n) (to_Z acc) (to_Z mult) (to_Z i) (to_Z b)
                Hinv Hilt (conj Hblo Hbhi)) as [Hbm0 [Hbm [Hsum [Hstep [Hple H8]]]]].
    destruct (cast_u8_u64_ok b) as [c [Hcast Hcval]].
    rewrite Hcast in H. cbn [bind] in H.
    destruct (u64_mul_ok c mult) as [prod [Hmul Hmulval]].
    { rewrite Hcval. rewrite u64_max_val. rewrite u64_max_val in Hsum. lia. }
    rewrite Hmul in H. cbn [bind] in H.
    destruct (u64_add_ok acc prod) as [sum [Hadd2 Hsumval]].
    { rewrite Hmulval. rewrite Hcval. exact Hsum. }
    rewrite Hadd2 in H. cbn [bind] in H.
    assert (Hsumv : to_Z sum = to_Z acc + to_Z b * to_Z mult)
      by (rewrite Hsumval; rewrite Hmulval; rewrite Hcval; reflexivity).
    assert (H1u : to_Z 1%u32 = 1) by reflexivity.
    destruct (u32_add_ok i 1%u32) as [i5 [Hi5 Hi5val]].
    { rewrite H1u. pose proof (u32_bounds n) as [_ Hnm]. lia. }
    rewrite Hi5 in H. cbn [bind] in H.
    assert (Hi5v : to_Z i5 = to_Z i + 1) by (rewrite Hi5val; rewrite H1u; lia).
    destruct (i5 s= n) eqn:Hlast.
    + (* the byte just read was the last one *)
      apply scalar_eqb_true in Hlast.
      assert (Hk0 : k = 0%nat) by (cbn in Hn; lia). subst k.
      injection H as <- <-.
      exists (to_Z b + 256 * 0). split.
      * rewrite Hbytes. apply repr_bytes_le_cons; [lia | apply repr_bytes_le_nil].
      * rewrite Hsumv. lia.
    + (* fold the place value up and go round again *)
      apply scalar_eqb_false in Hlast.
      assert (H256u : to_Z 256%u64 = 256) by reflexivity.
      destruct (u64_mul_ok mult 256%u64) as [mult2 [Hm2 Hm2val]].
      { (* one place value further is at most 256^7 here, since the byte just
           read was not the last: 256^8 would not fit *)
        assert (Hple7 : 256 ^ (to_Z i + 1) <= 256 ^ 7)
          by (apply pow256_le; cbn in Hn; lia).
        assert (H7 : (256:Z) ^ 7 = 72057594037927936) by reflexivity.
        rewrite H256u. rewrite u64_max_val. rewrite Hmult. lia. }
      rewrite Hm2 in H. cbn [bind] in H.
      assert (Hm2v : to_Z mult2 = 256 ^ (to_Z i + 1))
        by (rewrite Hm2val; rewrite H256u; rewrite Hmult; exact Hstep).
      destruct (IH data n sum mult2 p2 i5 v p') as [m' [Hrel Hval]].
      * rewrite Hi5v. cbn in Hn |- *. lia.
      * unfold fbits_inv. rewrite Hi5v. rewrite Hm2v.
        split; [lia|]. split; [lia|]. split; [reflexivity|].
        rewrite Hsumv. lia.
      * exact H.
      * exists (to_Z b + 256 * m'). split.
        -- rewrite Hbytes. apply repr_bytes_le_cons; [lia | exact Hrel].
        -- rewrite Hval. rewrite Hsumv. rewrite Hm2v. rewrite Hmult.
           rewrite <- Hstep. ring.
Qed.

Lemma read_fn_bits_loop_ok : forall k data n acc mult p i,
  to_Z i + Z.of_nat k = to_Z n ->
  fbits_inv (to_Z n) (to_Z acc) (to_Z mult) (to_Z i) ->
  exists r, reader_read_fn_bits_loop data n acc mult p i = Ok r.
Proof.
  induction k as [|k IH]; intros data n acc mult p i Hn Hinv;
    pose proof Hinv as Hinv2; destruct Hinv2 as [Hi [Hnle [Hmult Hacc]]];
    unfold reader_read_fn_bits_loop; rewrite loop_unfold; cbn beta iota.
  - assert (Heq : (i s= n) = true)
      by (unfold scalar_eqb; apply Z.eqb_eq; cbn in Hn; lia).
    rewrite Heq. cbn beta iota. eexists. reflexivity.
  - assert (Hilt : to_Z i < to_Z n) by (cbn in Hn; lia).
    assert (Heq : (i s= n) = false)
      by (unfold scalar_eqb; apply Z.eqb_neq; lia).
    rewrite Heq. cbn beta iota.
    destruct (p s>= slice_len data) eqn:Hge; [eexists; reflexivity|].
    apply scalar_geb_false_lt in Hge. rewrite slice_len_spec in Hge.
    destruct (slice_index_usize_ok data p Hge) as [b Hb].
    rewrite Hb. cbn [bind].
    assert (Hpmax : to_Z p + 1 <= usize_max)
      by (pose proof (usize_le_max (slice_len data)) as Hm;
          rewrite slice_len_spec in Hm; lia).
    destruct (usize_add_1_ok p Hpmax) as [p2 [Hadd Hp2]].
    rewrite Hadd. cbn [bind].
    pose proof (u8_bounds b) as [Hblo Hbhi].
    destruct (fbits_step_bound (to_Z n) (to_Z acc) (to_Z mult) (to_Z i) (to_Z b)
                Hinv Hilt (conj Hblo Hbhi)) as [Hbm0 [Hbm [Hsum [Hstep [Hple H8]]]]].
    destruct (cast_u8_u64_ok b) as [c [Hcast Hcval]].
    rewrite Hcast. cbn [bind].
    destruct (u64_mul_ok c mult) as [prod [Hmul Hmulval]].
    { rewrite Hcval. rewrite u64_max_val. rewrite u64_max_val in Hsum. lia. }
    rewrite Hmul. cbn [bind].
    destruct (u64_add_ok acc prod) as [sum [Hadd2 Hsumval]].
    { rewrite Hmulval. rewrite Hcval. exact Hsum. }
    rewrite Hadd2. cbn [bind].
    assert (Hsumv : to_Z sum = to_Z acc + to_Z b * to_Z mult)
      by (rewrite Hsumval; rewrite Hmulval; rewrite Hcval; reflexivity).
    assert (H1u : to_Z 1%u32 = 1) by reflexivity.
    destruct (u32_add_ok i 1%u32) as [i5 [Hi5 Hi5val]].
    { rewrite H1u. pose proof (u32_bounds n) as [_ Hnm]. lia. }
    rewrite Hi5. cbn [bind].
    assert (Hi5v : to_Z i5 = to_Z i + 1) by (rewrite Hi5val; rewrite H1u; lia).
    destruct (i5 s= n) eqn:Hlast; [eexists; reflexivity|].
    apply scalar_eqb_false in Hlast.
    assert (H256u : to_Z 256%u64 = 256) by reflexivity.
    destruct (u64_mul_ok mult 256%u64) as [mult2 [Hm2 Hm2val]].
    { assert (Hple7 : 256 ^ (to_Z i + 1) <= 256 ^ 7)
        by (apply pow256_le; cbn in Hn; lia).
      assert (H7 : (256:Z) ^ 7 = 72057594037927936) by reflexivity.
      rewrite H256u. rewrite u64_max_val. rewrite Hmult. lia. }
    rewrite Hm2. cbn [bind].
    assert (Hm2v : to_Z mult2 = 256 ^ (to_Z i + 1))
      by (rewrite Hm2val; rewrite H256u; rewrite Hmult; exact Hstep).
    apply (IH data n sum mult2 p2 i5).
    + rewrite Hi5v. cbn in Hn |- *. lia.
    + unfold fbits_inv. rewrite Hi5v. rewrite Hm2v.
      split; [lia|]. split; [lia|]. split; [reflexivity|].
      rewrite Hsumv. lia.
Qed.

(** Where the loop leaves the cursor: never behind where it started, and never
    past the end of the input as long as it has at least one byte left to read.
    That proviso is what the [k = 0] case costs: with the byte count already met
    the loop returns the cursor it was handed, wherever that is. Both wrappers
    enter with [i = 0] and [n] positive, so neither pays for it. *)
Lemma read_fn_bits_loop_range : forall k data n acc mult p i v p',
  to_Z i + Z.of_nat k = to_Z n ->
  reader_read_fn_bits_loop data n acc mult p i
    = Ok (Core_result_Result_Ok (v, p')) ->
  to_Z p <= to_Z p'
  /\ ((0 < k)%nat -> to_Z p' <= to_Z (slice_len data)).
Proof.
  induction k as [|k IH]; intros data n acc mult p i v p' Hn H;
    unfold reader_read_fn_bits_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (i s= n) eqn:Heq.
  - injection H as _ <-. split; [lia | intros; lia].
  - exfalso. apply scalar_eqb_false in Heq. cbn in Hn. lia.
  - injection H as _ <-. split; [lia|]. intros _.
    apply scalar_eqb_true in Heq. cbn in Hn. lia.
  - destruct (p s>= slice_len data) eqn:Hge; [discriminate|].
    apply scalar_geb_false_lt in Hge.
    destruct (slice_index_usize data p) as [b|] eqn:Hidx; cbn [bind] in H;
      [|discriminate].
    destruct (usize_add p 1%usize) as [p2|] eqn:Hadd; cbn [bind] in H;
      [|discriminate].
    destruct (bytes_from_step data p b p2 Hidx Hadd) as [_ Hp2].
    destruct (scalar_cast U8 U64 b) as [c|] eqn:Hcast; cbn [bind] in H;
      [|discriminate].
    destruct (u64_mul c mult) as [prod|] eqn:Hmul; cbn [bind] in H;
      [|discriminate].
    destruct (u64_add acc prod) as [sum|] eqn:Hadd2; cbn [bind] in H;
      [|discriminate].
    destruct (u32_add i 1%u32) as [i5|] eqn:Hi5; cbn [bind] in H;
      [|discriminate].
    assert (Hi5v : to_Z i5 = to_Z i + 1).
    { unfold u32_add, scalar_add in Hi5. apply mk_scalar_ok_to_Z in Hi5.
      assert (H1 : to_Z 1%u32 = 1) by reflexivity. rewrite Hi5. lia. }
    destruct (i5 s= n) eqn:Hlast.
    + injection H as _ <-. split; [lia | intros; lia].
    + destruct (u64_mul mult 256%u64) as [mult2|] eqn:Hm2; cbn [bind] in H;
        [|discriminate].
      (* the byte count is not met yet, so the recursive call still has one *)
      apply scalar_eqb_false in Hlast.
      assert (Hk : (0 < k)%nat) by (cbn in Hn; lia).
      destruct (IH data n sum mult2 p2 i5 v p' (ltac:(cbn in Hn; lia)) H)
        as [Hmono Hend].
      split; [lia | intros _; exact (Hend Hk)].
Qed.

Lemma read_fn_bits_loop_mono : forall k data n acc mult p i v p',
  to_Z i + Z.of_nat k = to_Z n ->
  reader_read_fn_bits_loop data n acc mult p i
    = Ok (Core_result_Result_Ok (v, p')) ->
  to_Z p <= to_Z p'.
Proof.
  intros k data n acc mult p i v p' Hn H.
  exact (proj1 (read_fn_bits_loop_range k data n acc mult p i v p' Hn H)).
Qed.

(** The completeness direction. The specification's byte count drives the loop,
    so this is an induction on it rather than on a byte budget. *)
Lemma read_fn_bits_loop_complete : forall k data n acc mult p i m rest,
  to_Z i + Z.of_nat k = to_Z n ->
  fbits_inv (to_Z n) (to_Z acc) (to_Z mult) (to_Z i) ->
  repr_bytes_le k (bytes_from data p) m rest ->
  exists v p',
    reader_read_fn_bits_loop data n acc mult p i
      = Ok (Core_result_Result_Ok (v, p'))
    /\ to_Z v = to_Z acc + m * to_Z mult
    /\ bytes_from data p' = rest.
Proof.
  induction k as [|k IH]; intros data n acc mult p i m rest Hn Hinv Hrep;
    pose proof Hinv as Hinv2; destruct Hinv2 as [Hi [Hnle [Hmult Hacc]]];
    destruct (repr_bytes_le_inv _ _ _ _ Hrep)
      as [[Hk [Hm Hr]] | [k' [b [more [m' [Hk [Hbs [Hm [Hb Hsub]]]]]]]]];
    try discriminate Hk;
    unfold reader_read_fn_bits_loop; rewrite loop_unfold; cbn beta iota.
  - (* nothing left to read *)
    assert (Heq : (i s= n) = true)
      by (unfold scalar_eqb; apply Z.eqb_eq; cbn in Hn; lia).
    rewrite Heq. cbn beta iota. exists acc, p.
    split; [reflexivity|]. split; [rewrite Hm; lia | symmetry; exact Hr].
  - (* one more byte, which the specification says is there *)
    injection Hk as <-.
    assert (Hilt : to_Z i < to_Z n) by (cbn in Hn; lia).
    assert (Heq : (i s= n) = false)
      by (unfold scalar_eqb; apply Z.eqb_neq; lia).
    rewrite Heq. cbn beta iota.
    destruct (bytes_from_uncons data p b more Hbs)
      as [bu [p2 [Hidx [Hz [Hadd [Hrest2 Hltp]]]]]].
    destruct (p s>= slice_len data) eqn:Hge;
      [exfalso; apply scalar_geb_true_ge in Hge; lia|].
    rewrite Hidx. cbn [bind]. rewrite Hadd. cbn [bind].
    assert (Hb255 : 0 <= b <= 255) by lia.
    destruct (fbits_step_bound (to_Z n) (to_Z acc) (to_Z mult) (to_Z i) b
                Hinv Hilt Hb255) as [Hbm0 [Hbm [Hsum [Hstep [Hple H8]]]]].
    destruct (cast_u8_u64_ok bu) as [c [Hcast Hcval]].
    rewrite Hcast. cbn [bind].
    destruct (u64_mul_ok c mult) as [prod [Hmul Hmulval]].
    { rewrite Hcval. rewrite Hz. rewrite u64_max_val.
      rewrite u64_max_val in Hsum. lia. }
    rewrite Hmul. cbn [bind].
    destruct (u64_add_ok acc prod) as [sum [Hadd2 Hsumval]].
    { rewrite Hmulval. rewrite Hcval. rewrite Hz. exact Hsum. }
    rewrite Hadd2. cbn [bind].
    assert (Hsumv : to_Z sum = to_Z acc + b * to_Z mult)
      by (rewrite Hsumval; rewrite Hmulval; rewrite Hcval; rewrite Hz;
          reflexivity).
    assert (H1u : to_Z 1%u32 = 1) by reflexivity.
    destruct (u32_add_ok i 1%u32) as [i5 [Hi5 Hi5val]].
    { rewrite H1u. pose proof (u32_bounds n) as [_ Hnm]. lia. }
    rewrite Hi5. cbn [bind].
    assert (Hi5v : to_Z i5 = to_Z i + 1) by (rewrite Hi5val; rewrite H1u; lia).
    destruct (i5 s= n) eqn:Hlast.
    + (* the last byte, so the sub-derivation is the empty one *)
      apply scalar_eqb_true in Hlast.
      assert (Hk0 : k = 0%nat) by (cbn in Hn; lia). subst k.
      destruct (repr_bytes_le_inv _ _ _ _ Hsub)
        as [[_ [Hm0 Hr0]] | [k2 [_ [_ [_ [Hk2 _]]]]]]; [|discriminate Hk2].
      exists sum, p2. split; [reflexivity|].
      split; [rewrite Hsumv; rewrite Hm; rewrite Hm0; lia|].
      rewrite Hrest2. rewrite Hr0. reflexivity.
    + apply scalar_eqb_false in Hlast.
      assert (H256u : to_Z 256%u64 = 256) by reflexivity.
      destruct (u64_mul_ok mult 256%u64) as [mult2 [Hm2 Hm2val]].
      { (* one place value further is at most 256^7 here, since the byte just
           read was not the last: 256^8 would not fit *)
        assert (Hple7 : 256 ^ (to_Z i + 1) <= 256 ^ 7)
          by (apply pow256_le; cbn in Hn; lia).
        assert (H7 : (256:Z) ^ 7 = 72057594037927936) by reflexivity.
        rewrite H256u. rewrite u64_max_val. rewrite Hmult. lia. }
      rewrite Hm2. cbn [bind].
      assert (Hm2v : to_Z mult2 = 256 ^ (to_Z i + 1))
        by (rewrite Hm2val; rewrite H256u; rewrite Hmult; exact Hstep).
      destruct (IH data n sum mult2 p2 i5 m' rest) as [v [p' [Hrun [Hval Hb2]]]].
      * rewrite Hi5v. cbn in Hn |- *. lia.
      * unfold fbits_inv. rewrite Hi5v. rewrite Hm2v.
        split; [lia|]. split; [lia|]. split; [reflexivity|].
        rewrite Hsumv. lia.
      * rewrite Hrest2. exact Hsub.
      * exists v, p'. split; [exact Hrun|]. split; [|exact Hb2].
        rewrite Hval. rewrite Hsumv. rewrite Hm2v. rewrite Hmult.
        rewrite Hm. rewrite <- Hstep. ring.
Qed.

(** The two instances. Both start the loop at [i = 0], and [f32] then narrows the
    accumulator, which four bytes always fit. *)
Lemma fbits_start : forall (n : u32), to_Z n <= 8 ->
  fbits_inv (to_Z n) (to_Z 0%u64) (to_Z 1%u64) (to_Z 0%u32).
Proof.
  intros n Hn. unfold fbits_inv. cbn. pose proof (u32_bounds n) as [Hlo _].
  split; [lia|]. split; [lia|]. split; [reflexivity | lia].
Qed.

Theorem read_f32_bits_sound : forall data pos v pos',
  reader_read_f32_bits data pos = Ok (Core_result_Result_Ok (v, pos')) ->
  repr_bytes_le 4 (bytes_from data pos) (to_Z v) (bytes_from data pos').
Proof.
  intros data pos v pos' H. unfold reader_read_f32_bits, reader_read_fn_bits in H.
  destruct (reader_read_fn_bits_loop data 4%u32 0%u64 1%u64 pos 0%u32) as [r|]
    eqn:Hrun; cbn [bind] in H; [|discriminate].
  destruct r as [[v0 p0]|e].
  2: { rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
       cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (scalar_cast U64 U32 v0) as [v1|] eqn:Hc; cbn [bind] in H;
    [|discriminate].
  injection H as <- <-.
  unfold scalar_cast in Hc. apply mk_scalar_ok_to_Z in Hc.
  destruct (read_fn_bits_loop_sound 4 data 4%u32 0%u64 1%u64 pos 0%u32 v0 p0)
    as [m [Hrel Hval]].
  - reflexivity.
  - apply fbits_start. cbn. lia.
  - exact Hrun.
  - rewrite Hc. rewrite Hval. cbn. rewrite Z.mul_1_r. exact Hrel.
Qed.

Theorem read_f64_bits_sound : forall data pos v pos',
  reader_read_f64_bits data pos = Ok (Core_result_Result_Ok (v, pos')) ->
  repr_bytes_le 8 (bytes_from data pos) (to_Z v) (bytes_from data pos').
Proof.
  intros data pos v pos' H.
  unfold reader_read_f64_bits, reader_read_fn_bits in H.
  destruct (read_fn_bits_loop_sound 8 data 8%u32 0%u64 1%u64 pos 0%u32 v pos')
    as [m [Hrel Hval]].
  - reflexivity.
  - apply fbits_start. cbn. lia.
  - exact H.
  - rewrite Hval. cbn. rewrite Z.mul_1_r. exact Hrel.
Qed.

Lemma read_f32_bits_ok : forall data pos,
  exists r, reader_read_f32_bits data pos = Ok r.
Proof.
  intros data pos. unfold reader_read_f32_bits, reader_read_fn_bits.
  destruct (read_fn_bits_loop_ok 4 data 4%u32 0%u64 1%u64 pos 0%u32) as [r Hrun].
  - reflexivity.
  - apply fbits_start. cbn. lia.
  - rewrite Hrun. cbn [bind].
    destruct r as [[v0 p0]|e].
    2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
         eexists. reflexivity. }
    rewrite branch_ok. cbn [bind].
    destruct (read_fn_bits_loop_sound 4 data 4%u32 0%u64 1%u64 pos 0%u32 v0 p0
                (ltac:(reflexivity)) (fbits_start 4%u32 (ltac:(cbn; lia))) Hrun)
      as [m [Hrel Hval]].
    pose proof (repr_bytes_le_bound _ _ _ _ Hrel) as Hbnd.
    destruct (cast_u64_u32_ok v0) as [v1 [Hc _]].
    { rewrite u32_max_val. rewrite Hval. cbn in Hbnd |- *. lia. }
    rewrite Hc. cbn [bind]. eexists. reflexivity.
Qed.

Lemma read_f64_bits_ok : forall data pos,
  exists r, reader_read_f64_bits data pos = Ok r.
Proof.
  intros data pos. unfold reader_read_f64_bits, reader_read_fn_bits.
  apply (read_fn_bits_loop_ok 8 data 8%u32 0%u64 1%u64 pos 0%u32).
  - reflexivity.
  - apply fbits_start. cbn. lia.
Qed.

Lemma read_f32_bits_mono : forall data pos v pos',
  reader_read_f32_bits data pos = Ok (Core_result_Result_Ok (v, pos')) ->
  to_Z pos <= to_Z pos'.
Proof.
  intros data pos v pos' H. unfold reader_read_f32_bits, reader_read_fn_bits in H.
  destruct (reader_read_fn_bits_loop data 4%u32 0%u64 1%u64 pos 0%u32) as [r|]
    eqn:Hrun; cbn [bind] in H; [|discriminate].
  destruct r as [[v0 p0]|e].
  2: { rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
       cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (scalar_cast U64 U32 v0) as [v1|] eqn:Hc; cbn [bind] in H;
    [|discriminate].
  injection H as <- <-.
  apply (read_fn_bits_loop_mono 4 data 4%u32 0%u64 1%u64 pos 0%u32 v0 p0);
    [reflexivity | exact Hrun].
Qed.

Lemma read_f64_bits_mono : forall data pos v pos',
  reader_read_f64_bits data pos = Ok (Core_result_Result_Ok (v, pos')) ->
  to_Z pos <= to_Z pos'.
Proof.
  intros data pos v pos' H.
  apply (read_fn_bits_loop_mono 8 data 8%u32 0%u64 1%u64 pos 0%u32 v pos');
    [reflexivity | exact H].
Qed.

Lemma read_f32_bits_le_len : forall data pos v pos',
  reader_read_f32_bits data pos = Ok (Core_result_Result_Ok (v, pos')) ->
  to_Z pos' <= to_Z (slice_len data).
Proof.
  intros data pos v pos' H. unfold reader_read_f32_bits, reader_read_fn_bits in H.
  destruct (reader_read_fn_bits_loop data 4%u32 0%u64 1%u64 pos 0%u32) as [r|]
    eqn:Hrun; cbn [bind] in H; [|discriminate].
  destruct r as [[v0 p0]|e].
  2: { rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
       cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (scalar_cast U64 U32 v0) as [v1|] eqn:Hc; cbn [bind] in H;
    [|discriminate].
  injection H as <- <-.
  destruct (read_fn_bits_loop_range 4 data 4%u32 0%u64 1%u64 pos 0%u32 v0 p0
              (ltac:(reflexivity)) Hrun) as [_ Hend].
  apply Hend. lia.
Qed.

Lemma read_f64_bits_le_len : forall data pos v pos',
  reader_read_f64_bits data pos = Ok (Core_result_Result_Ok (v, pos')) ->
  to_Z pos' <= to_Z (slice_len data).
Proof.
  intros data pos v pos' H.
  destruct (read_fn_bits_loop_range 8 data 8%u32 0%u64 1%u64 pos 0%u32 v pos'
              (ltac:(reflexivity)) H) as [_ Hend].
  apply Hend. lia.
Qed.

Theorem read_f32_bits_complete : forall data pos m rest,
  repr_bytes_le 4 (bytes_from data pos) m rest ->
  exists v pos',
    reader_read_f32_bits data pos = Ok (Core_result_Result_Ok (v, pos'))
    /\ to_Z v = m
    /\ bytes_from data pos' = rest.
Proof.
  intros data pos m rest Hrep.
  destruct (read_fn_bits_loop_complete 4 data 4%u32 0%u64 1%u64 pos 0%u32 m rest)
    as [v0 [p0 [Hrun [Hval Hb]]]].
  - reflexivity.
  - apply fbits_start. cbn. lia.
  - exact Hrep.
  - destruct (read_f32_bits_ok data pos) as [r Hr].
    unfold reader_read_f32_bits, reader_read_fn_bits in Hr |- *.
    rewrite Hrun in Hr |- *. cbn [bind] in Hr |- *.
    rewrite branch_ok in Hr |- *. cbn [bind] in Hr |- *.
    destruct (scalar_cast U64 U32 v0) as [v1|] eqn:Hc; cbn [bind] in Hr |- *;
      [|discriminate Hr].
    unfold scalar_cast in Hc. apply mk_scalar_ok_to_Z in Hc.
    exists v1, p0. split; [reflexivity|].
    split; [rewrite Hc; rewrite Hval; cbn; lia | exact Hb].
Qed.

Theorem read_f64_bits_complete : forall data pos m rest,
  repr_bytes_le 8 (bytes_from data pos) m rest ->
  exists v pos',
    reader_read_f64_bits data pos = Ok (Core_result_Result_Ok (v, pos'))
    /\ to_Z v = m
    /\ bytes_from data pos' = rest.
Proof.
  intros data pos m rest Hrep.
  destruct (read_fn_bits_loop_complete 8 data 8%u32 0%u64 1%u64 pos 0%u32 m rest)
    as [v0 [p0 [Hrun [Hval Hb]]]].
  - reflexivity.
  - apply fbits_start. cbn. lia.
  - exact Hrep.
  - exists v0, p0. split; [exact Hrun|].
    split; [rewrite Hval; cbn; lia | exact Hb].
Qed.

(* ================================================================== *)
(** ** What each reader consumes                                       *)
(* ================================================================== *)

(** The immediate-reading readers, lifted from the immediate decoders to the
    reader that calls them. Each says exactly which bytes the reader took, which
    is what the top-level theorem needs in order to assemble a [repr_op] out of
    the opcode byte [read_op] consumed and the immediates the reader consumed.

    The readers with no immediates are in [OpIter_State.v] instead, since for
    those there is nothing to say about bytes beyond "the cursor did not move".

    Each proof is the same walk: the prologue leaves the cursor alone, the
    immediate decoder moves it, and everything after it is stack work that copies
    it. *)

Theorem read_i32_const_sound : forall st data v st',
  opiter_read_i32_const st data = Ok (Core_result_Result_Ok v, st') ->
  repr_s32 (bytes_from data st.(opiter_OpIterState_pos)) (to_Z v)
           (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros st data v st' H. unfold opiter_read_i32_const in H.
  destruct (opiter_take_pending st opiter_op_i32_const) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opiter_op_i32_const r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_s32_leb data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[v0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending := st1.(opiter_OpIterState_pending)
              |} (Opiter_StackType_Val Types_ValueType_I32)) as [st2|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as Hv Hst.
  pose proof (push_val_pos _ _ st2 Hpv) as Hp2.
  unfold pos_of in Hp2. cbn [opiter_OpIterState_pos] in Hp2.
  rewrite <- Hst. rewrite Hp2. rewrite <- Hp1. rewrite <- Hv.
  apply read_s32_leb_sound. exact Hleb.
Qed.

Theorem read_f32_const_sound : forall st data v st',
  opiter_read_f32_const st data = Ok (Core_result_Result_Ok v, st') ->
  repr_bytes_le 4 (bytes_from data st.(opiter_OpIterState_pos)) (to_Z v)
           (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros st data v st' H. unfold opiter_read_f32_const in H.
  destruct (opiter_take_pending st opiter_op_f32_const) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opiter_op_f32_const r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_f32_bits data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[v0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending := st1.(opiter_OpIterState_pending)
              |} (Opiter_StackType_Val Types_ValueType_F32)) as [st2|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as Hv Hst.
  pose proof (push_val_pos _ _ st2 Hpv) as Hp2.
  unfold pos_of in Hp2. cbn [opiter_OpIterState_pos] in Hp2.
  rewrite <- Hst. rewrite Hp2. rewrite <- Hp1. rewrite <- Hv.
  apply read_f32_bits_sound. exact Hleb.
Qed.

Theorem read_f64_const_sound : forall st data v st',
  opiter_read_f64_const st data = Ok (Core_result_Result_Ok v, st') ->
  repr_bytes_le 8 (bytes_from data st.(opiter_OpIterState_pos)) (to_Z v)
           (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros st data v st' H. unfold opiter_read_f64_const in H.
  destruct (opiter_take_pending st opiter_op_f64_const) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opiter_op_f64_const r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_f64_bits data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[v0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending := st1.(opiter_OpIterState_pending)
              |} (Opiter_StackType_Val Types_ValueType_F64)) as [st2|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as Hv Hst.
  pose proof (push_val_pos _ _ st2 Hpv) as Hp2.
  unfold pos_of in Hp2. cbn [opiter_OpIterState_pos] in Hp2.
  rewrite <- Hst. rewrite Hp2. rewrite <- Hp1. rewrite <- Hv.
  apply read_f64_bits_sound. exact Hleb.
Qed.

Theorem read_i64_const_sound : forall st data v st',
  opiter_read_i64_const st data = Ok (Core_result_Result_Ok v, st') ->
  repr_sN 64 (bytes_from data st.(opiter_OpIterState_pos)) (to_Z v)
           (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros st data v st' H. unfold opiter_read_i64_const in H.
  destruct (opiter_take_pending st opiter_op_i64_const) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opiter_op_i64_const r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_s64_leb data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[v0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending := st1.(opiter_OpIterState_pending)
              |} (Opiter_StackType_Val Types_ValueType_I64)) as [st2|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as Hv Hst.
  pose proof (push_val_pos _ _ st2 Hpv) as Hp2.
  unfold pos_of in Hp2. cbn [opiter_OpIterState_pos] in Hp2.
  rewrite <- Hst. rewrite Hp2. rewrite <- Hp1. rewrite <- Hv.
  apply read_s64_leb_sound. exact Hleb.
Qed.

(** [block] and [loop] differ only in the kind they push, which is invisible
    here, so the two proofs are the same walk. *)
Theorem read_block_sound : forall st data bt st',
  opiter_read_block st data = Ok (Core_result_Result_Ok bt, st') ->
  exists bb,
    bytes_from data st.(opiter_OpIterState_pos)
      = bb :: bytes_from data st'.(opiter_OpIterState_pos)
    /\ blocktype_spec bb = Some (translate_bt bt).
Proof.
  intros st data bt st' H. unfold opiter_read_block in H.
  destruct (opiter_take_pending st opiter_op_block) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opiter_op_block r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_read_block_type data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hbt; cbn [bind] in H; [|discriminate].
  destruct r1 as [[bt0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_ctrl
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending := st1.(opiter_OpIterState_pending)
              |} Opiter_LabelKind_Block bt0) as [st2|] eqn:Hpc;
    cbn [bind] in H; [|discriminate].
  injection H as Hbteq Hst.
  pose proof (push_ctrl_pos _ _ _ st2 Hpc) as Hp2.
  unfold pos_of in Hp2. cbn [opiter_OpIterState_pos] in Hp2.
  destruct (read_block_type_sound data st1.(opiter_OpIterState_pos) bt0 p1 Hbt)
    as [bb [Hbytes Hspec]].
  exists bb. rewrite <- Hst. rewrite Hp2. rewrite <- Hp1. rewrite <- Hbteq.
  split; [exact Hbytes | exact Hspec].
Qed.

Theorem read_loop_sound : forall st data bt st',
  opiter_read_loop st data = Ok (Core_result_Result_Ok bt, st') ->
  exists bb,
    bytes_from data st.(opiter_OpIterState_pos)
      = bb :: bytes_from data st'.(opiter_OpIterState_pos)
    /\ blocktype_spec bb = Some (translate_bt bt).
Proof.
  intros st data bt st' H. unfold opiter_read_loop in H.
  destruct (opiter_take_pending st opiter_op_loop) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opiter_op_loop r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_read_block_type data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hbt; cbn [bind] in H; [|discriminate].
  destruct r1 as [[bt0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_ctrl
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending := st1.(opiter_OpIterState_pending)
              |} Opiter_LabelKind_Loop bt0) as [st2|] eqn:Hpc;
    cbn [bind] in H; [|discriminate].
  injection H as Hbteq Hst.
  pose proof (push_ctrl_pos _ _ _ st2 Hpc) as Hp2.
  unfold pos_of in Hp2. cbn [opiter_OpIterState_pos] in Hp2.
  destruct (read_block_type_sound data st1.(opiter_OpIterState_pos) bt0 p1 Hbt)
    as [bb [Hbytes Hspec]].
  exists bb. rewrite <- Hst. rewrite Hp2. rewrite <- Hp1. rewrite <- Hbteq.
  split; [exact Hbytes | exact Hspec].
Qed.

(** [if] reads the same block type byte, then pops the condition. The pop is
    invisible to the cursor, so the bytes consumed are [block]'s. *)
Theorem read_if_sound : forall st data bt st',
  opiter_read_if st data = Ok (Core_result_Result_Ok bt, st') ->
  exists bb,
    bytes_from data st.(opiter_OpIterState_pos)
      = bb :: bytes_from data st'.(opiter_OpIterState_pos)
    /\ blocktype_spec bb = Some (translate_bt bt).
Proof.
  intros st data bt st' H. unfold opiter_read_if in H.
  destruct (opiter_take_pending st opiter_op_if) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opiter_op_if r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_read_block_type data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hbt; cbn [bind] in H; [|discriminate].
  destruct r1 as [[bt0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_pop_with_type
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending := st1.(opiter_OpIterState_pending)
              |} Types_ValueType_I32) as [[r2 st2]|] eqn:Hpw;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos _ _ r2 st2 Hpw) as Hp2.
  unfold pos_of in Hp2. cbn [opiter_OpIterState_pos] in Hp2.
  destruct r2 as [t2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_ctrl st2 Opiter_LabelKind_Then bt0) as [st3|] eqn:Hpc;
    cbn [bind] in H; [|discriminate].
  injection H as Hbteq Hst.
  pose proof (push_ctrl_pos _ _ _ st3 Hpc) as Hp3.
  unfold pos_of in Hp3.
  destruct (read_block_type_sound data st1.(opiter_OpIterState_pos) bt0 p1 Hbt)
    as [bb [Hbytes Hspec]].
  exists bb. rewrite <- Hst. rewrite Hp3. rewrite Hp2. rewrite <- Hp1.
  rewrite <- Hbteq. split; [exact Hbytes | exact Hspec].
Qed.

(** The local operators' shared prologue consumes exactly the index's bytes:
    [take_pending] does not move the cursor and the lookup is pure. *)
Theorem take_local_sound : forall st data ctx opcode idx t st',
  opiter_take_local st data ctx opcode
    = Ok (Core_result_Result_Ok (idx, t), st') ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) (to_Z idx)
           (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros st data ctx opcode idx t st' H. unfold opiter_take_local in H.
  destruct (opiter_take_pending st opcode) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opcode r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_u32_leb data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[idx0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_local_type ctx idx0) as [r2|] eqn:Hlt;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [t0|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  injection H as Hidx _ <-.
  cbn [opiter_OpIterState_pos].
  rewrite <- Hp1. rewrite <- Hidx.
  apply (read_u32_leb_sound data st1.(opiter_OpIterState_pos) idx0 p1 Hleb).
Qed.

(** The global operators' prologue, byte for byte the local one's. *)
Theorem take_global_sound : forall st data module opcode idx g st',
  opiter_take_global st data module opcode
    = Ok (Core_result_Result_Ok (idx, g), st') ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) (to_Z idx)
           (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros st data module opcode idx g st' H. unfold opiter_take_global in H.
  destruct (opiter_take_pending st opcode) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opcode r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_u32_leb data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[idx0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_global_type module idx0) as [r2|] eqn:Hgt;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [g0|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  injection H as Hidx _ <-.
  cbn [opiter_OpIterState_pos].
  rewrite <- Hp1. rewrite <- Hidx.
  apply (read_u32_leb_sound data st1.(opiter_OpIterState_pos) idx0 p1 Hleb).
Qed.

(** A label index is a u32 and nothing else: the bounds check and the frame
    lookup that follow leave the cursor where the depth left it. *)
Theorem read_label_sound : forall st data depth target st',
  opiter_read_label st data = Ok (Core_result_Result_Ok (depth, target), st') ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) (to_Z depth)
           (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros st data depth target st' H. unfold opiter_read_label in H.
  destruct (reader_read_u32_leb data st.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[d0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (scalar_cast U32 Usize d0) as [d|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  destruct (d s>= alloc_vec_Vec_len st.(opiter_OpIterState_ctrls)) eqn:Hge;
    [discriminate|].
  destruct (usize_sub (alloc_vec_Vec_len st.(opiter_OpIterState_ctrls)) 1%usize)
    as [i|] eqn:Hsub1; cbn [bind] in H; [|discriminate].
  destruct (usize_sub i d) as [i1|] eqn:Hsub2; cbn [bind] in H; [|discriminate].
  destruct (alloc_vec_Vec_index
              (core_slice_index_SliceIndexUsizeSliceInst opiter_Ctrl_t)
              st.(opiter_OpIterState_ctrls) i1) as [c|] eqn:Hidx;
    cbn [bind] in H; [|discriminate].
  injection H as Hd _ <-. cbn [opiter_OpIterState_pos].
  rewrite <- Hd. apply read_u32_leb_sound. exact Hleb.
Qed.

(** Which frame the depth named, as a fact about the control stack alone.
    [br_table]'s loop collects one of these per label. *)
Lemma read_label_target : forall st data depth target st',
  opiter_read_label st data = Ok (Core_result_Result_Ok (depth, target), st') ->
  depth_target st (to_Z depth) (branch_target_bt_of target).
Proof.
  intros st data depth target st' H. unfold opiter_read_label in H.
  destruct (reader_read_u32_leb data st.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[d0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (scalar_cast U32 Usize d0) as [d|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  destruct (d s>= alloc_vec_Vec_len st.(opiter_OpIterState_ctrls)) eqn:Hge;
    [discriminate|].
  destruct (usize_sub (alloc_vec_Vec_len st.(opiter_OpIterState_ctrls)) 1%usize)
    as [i|] eqn:Hsub1; cbn [bind] in H; [|discriminate].
  destruct (usize_sub i d) as [i1|] eqn:Hsub2; cbn [bind] in H; [|discriminate].
  rewrite vec_index_spec in H.
  destruct (List.nth_error (vec_list st.(opiter_OpIterState_ctrls))
              (Z.to_nat (to_Z i1))) as [c|] eqn:Hnth;
    cbn [bind] in H; [|discriminate].
  injection H as Hd Hc0 _. rewrite <- Hd. rewrite <- Hc0.
  (* the same index arithmetic [read_label_at] does, without the label context *)
  assert (Hdv : to_Z d = to_Z d0)
    by (unfold scalar_cast in Hcast; apply mk_scalar_ok_to_Z in Hcast;
        exact Hcast).
  apply scalar_geb_false_lt in Hge. rewrite vec_len_spec in Hge.
  assert (Hi : to_Z i
               = Z.of_nat (List.length (vec_list st.(opiter_OpIterState_ctrls)))
                 - 1).
  { unfold usize_sub, scalar_sub in Hsub1. apply mk_scalar_ok_to_Z in Hsub1.
    rewrite Hsub1. rewrite vec_len_spec. reflexivity. }
  assert (Hi1 : to_Z i1 = to_Z i - to_Z d).
  { unfold usize_sub, scalar_sub in Hsub2. apply mk_scalar_ok_to_Z in Hsub2.
    exact Hsub2. }
  pose proof (u32_nonneg d0) as Hd0.
  exists c. split; [lia|]. split; [|reflexivity].
  assert (Hidx : (List.length (vec_list st.(opiter_OpIterState_ctrls)) - 1
                  - Z.to_nat (to_Z d0))%nat = Z.to_nat (to_Z i1)) by lia.
  rewrite Hidx. exact Hnth.
Qed.

(** [br] reads its depth and then does stack work: the label bounds check, the
    target pops and [mark_unreachable] all leave the cursor where the depth left
    it. *)
Theorem take_branch_target_sound : forall st data opcode depth target st',
  opiter_take_branch_target st data opcode
    = Ok (Core_result_Result_Ok (depth, target), st') ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) (to_Z depth)
           (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros st data opcode depth target st' H.
  unfold opiter_take_branch_target in H.
  destruct (opiter_take_pending st opcode) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opcode r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  rewrite <- Hp1. apply (read_label_sound st1 data depth target st' H).
Qed.

(** [br] does stack work after the prologue: the target pops and
    [mark_unreachable] leave the cursor where the depth left it. *)
Theorem read_br_sound : forall st data depth bt st',
  opiter_read_br st data = Ok (Core_result_Result_Ok (depth, bt), st') ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) (to_Z depth)
           (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros st data depth bt st' H. unfold opiter_read_br in H.
  destruct (opiter_take_branch_target st data opiter_op_br) as [[r0 st1]|]
    eqn:Htb; cbn [bind] in H; [|discriminate].
  destruct r0 as [[d0 target]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_branch_target_types target) as [types|] eqn:Hbtt;
    cbn [bind] in H; [|discriminate].
  destruct (opiter_pop_types st1 (alloc_vec_Vec_deref types)) as [[r2 st2]|]
    eqn:Hpt; cbn [bind] in H; [|discriminate].
  pose proof (pop_types_pos _ _ r2 st2 Hpt) as Hp2. unfold pos_of in Hp2.
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_mark_unreachable st2) as [st3|] eqn:Hmu; cbn [bind] in H;
    [|discriminate].
  injection H as Hd _ <-.
  pose proof (mark_unreachable_pos st2 st3 Hmu) as Hp3. unfold pos_of in Hp3.
  rewrite Hp3. rewrite Hp2. rewrite <- Hd.
  apply (take_branch_target_sound st data _ d0 target st1 Htb).
Qed.

(** [br_if] does the same reading and more stack work. *)
Theorem read_br_if_sound : forall st data depth bt st',
  opiter_read_br_if st data = Ok (Core_result_Result_Ok (depth, bt), st') ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) (to_Z depth)
           (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros st data depth bt st' H. unfold opiter_read_br_if in H.
  destruct (opiter_take_branch_target st data opiter_op_br_if) as [[r0 st1]|]
    eqn:Htb; cbn [bind] in H; [|discriminate].
  destruct r0 as [[d0 target]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_branch_target_types target) as [types|] eqn:Hbtt;
    cbn [bind] in H; [|discriminate].
  destruct (opiter_pop_with_type st1 Types_ValueType_I32) as [[r1 st2]|] eqn:Hp1;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos st1 _ r1 st2 Hp1) as Hp2. unfold pos_of in Hp2.
  destruct r1 as [t1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_pop_types st2 (alloc_vec_Vec_deref types)) as [[r2 st3]|]
    eqn:Hpt; cbn [bind] in H; [|discriminate].
  pose proof (pop_types_pos _ _ r2 st3 Hpt) as Hp3. unfold pos_of in Hp3.
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_types st3 (alloc_vec_Vec_deref types)) as [st4|]
    eqn:Hpush; cbn [bind] in H; [|discriminate].
  injection H as Hd _ <-.
  pose proof (push_types_pos st3 _ st4 Hpush) as Hp4. unfold pos_of in Hp4.
  rewrite Hp4. rewrite Hp3. rewrite Hp2. rewrite <- Hd.
  apply (take_branch_target_sound st data _ d0 target st1 Htb).
Qed.

(** Merging a target into the running one yields that target, and if the running
    one was already set, the two were equal. So the value the loop carries never
    changes once set, which is why comparing each entry against the previous is
    the same as comparing them all against the first. *)
Lemma merge_target_ok : forall e bt r,
  opiter_merge_target e bt = Ok (Core_result_Result_Ok r) ->
  r = bt /\ (forall e0, e = Some e0 -> e0 = bt).
Proof.
  intros e bt r H. unfold opiter_merge_target in H. destruct e as [e0|].
  - rewrite bt_eq_spec in H. cbn [bind] in H.
    destruct (opiter_BlockType_t_beq bt e0) eqn:Hbeq; [|discriminate].
    injection H as <-. split; [reflexivity|].
    intros e1 He1. injection He1 as <-. symmetry. apply (bt_beq_eq _ _ Hbeq).
  - injection H as <-. split; [reflexivity|]. intros e0 He0. discriminate.
Qed.

(** The converse, for the completeness direction: merging a target the running
    value already agrees with succeeds and leaves it alone. *)
Lemma merge_target_same : forall e bt,
  (e = None \/ e = Some bt) ->
  opiter_merge_target e bt = Ok (Core_result_Result_Ok bt).
Proof.
  intros e bt [-> | ->]; unfold opiter_merge_target; [reflexivity|].
  rewrite bt_eq_spec. rewrite bt_beq_refl. reflexivity.
Qed.

(** The vector immediate, in both senses at once: the bytes the loop consumed
    encode a list of u32s, and each of them names a frame whose branch target is
    the block type the loop settled on.

    Both come out of the same run, which is what lets the two halves of
    [br_table]'s correspondence agree on a label list the reader does not
    return. *)
Lemma read_table_labels_loop_sound : forall n st data count expect i st' res,
  to_Z i + Z.of_nat n = to_Z count ->
  opiter_read_table_labels_loop st data count expect i
    = Ok (Core_result_Result_Ok res, st') ->
  exists ls,
    repr_u32_rep n (bytes_from data st.(opiter_OpIterState_pos)) ls
                 (bytes_from data st'.(opiter_OpIterState_pos))
    /\ (forall bt, res = Some bt ->
          List.Forall (fun d => depth_target st d bt) ls)
    /\ (forall e, expect = Some e -> res = Some e)
    /\ (res = None -> ls = []).
Proof.
  induction n as [|n IH]; intros st data count expect i st' res Hn H;
    unfold opiter_read_table_labels_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (i s= count) eqn:Heq.
  - injection H as <- <-. exists []. split; [apply repr_u32_rep_nil|].
    split; [intros bt _; apply List.Forall_nil|].
    split; [intros e He; exact He | reflexivity].
  - exfalso. apply scalar_eqb_false in Heq. cbn in Hn. lia.
  - exfalso. apply scalar_eqb_true in Heq. cbn in Hn. lia.
  - destruct (opiter_read_label st data) as [[r0 st1]|] eqn:Hrl;
      cbn [bind] in H; [|discriminate].
    destruct r0 as [[d0 target]|e].
    2: { rewrite branch_err in H. cbn [bind] in H.
         rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
    rewrite branch_ok in H. cbn [bind] in H.
    rewrite branch_target_bt_spec in H. cbn [bind] in H.
    destruct (opiter_merge_target expect (branch_target_bt_of target)) as [r1|]
      eqn:Hmt; cbn [bind] in H; [|discriminate].
    destruct r1 as [bt|e1].
    2: { rewrite branch_err in H. cbn [bind] in H.
         rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (u32_add i 1%u32) as [i1|] eqn:Hadd; cbn [bind] in H;
      [|discriminate].
    destruct (merge_target_ok _ _ _ Hmt) as [Hbt Hprev]. subst bt.
    assert (Hi1 : to_Z i1 = to_Z i + 1).
    { unfold u32_add, scalar_add in Hadd. apply mk_scalar_ok_to_Z in Hadd.
      assert (H1 : to_Z 1%u32 = 1) by reflexivity. rewrite Hadd. lia. }
    destruct (IH st1 data count (Some (branch_target_bt_of target)) i1 st' res
                (ltac:(cbn in Hn; lia)) H)
      as [ls [Hrep [Hall [Hkeep _]]]].
    (* the loop's running value is set from here on, so the result is it *)
    pose proof (Hkeep _ eq_refl) as Hres.
    destruct (read_label_fields st data _ st1 Hrl) as [_ Hc1].
    exists (to_Z d0 :: ls). split.
    + apply repr_u32_rep_cons with (mid := bytes_from data
                                            st1.(opiter_OpIterState_pos));
        [apply (read_label_sound st data d0 target st1 Hrl) | exact Hrep].
    + split; [|split; [intros e0 He0; rewrite (Hprev e0 He0); exact Hres
                      | intros Hnone; rewrite Hres in Hnone; discriminate]].
      intros bt Hbt. rewrite Hres in Hbt. injection Hbt as <-.
      apply List.Forall_cons.
      * apply (read_label_target st data d0 target st1 Hrl).
      * apply (List.Forall_impl _
                 (fun d Hd => depth_target_ctrls st1 st d _ (eq_sym Hc1) Hd)).
        apply (Hall _ Hres).
Qed.

Lemma read_table_labels_sound : forall st data count st' res,
  opiter_read_table_labels st data count = Ok (Core_result_Result_Ok res, st') ->
  exists ls,
    repr_u32_rep (Z.to_nat (to_Z count))
                 (bytes_from data st.(opiter_OpIterState_pos)) ls
                 (bytes_from data st'.(opiter_OpIterState_pos))
    /\ (forall bt, res = Some bt ->
          List.Forall (fun d => depth_target st d bt) ls)
    /\ (res = None -> ls = []).
Proof.
  intros st data count st' res H. unfold opiter_read_table_labels in H.
  destruct (read_table_labels_loop_sound (Z.to_nat (to_Z count)) st data count
              None 0%u32 st' res
              (ltac:(assert (H0 : to_Z 0%u32 = 0) by reflexivity; rewrite H0;
                     rewrite Z2Nat.id by apply u32_nonneg; reflexivity)) H)
    as [ls [Hrep [Hall [_ Hnone]]]].
  exists ls. split; [exact Hrep | split; [exact Hall | exact Hnone]].
Qed.

(** [br_table]'s whole immediate: the vector, then the default label, and every
    one of the labels names a frame whose branch target is the block type the
    reader returned. *)
Theorem read_br_table_sound : forall st data common st',
  opiter_read_br_table st data = Ok (Core_result_Result_Ok common, st') ->
  exists ls x mid,
    repr_vec_u32 (bytes_from data st.(opiter_OpIterState_pos)) ls mid
    /\ repr_u32 mid x (bytes_from data st'.(opiter_OpIterState_pos))
    /\ List.Forall (fun d => depth_target st d common) (ls ++ [x]).
Proof.
  intros st data common st' H. unfold opiter_read_br_table in H.
  destruct (opiter_take_pending st opiter_op_br_table) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st _ r0 st1 Htp) as Hp1. unfold pos_of in Hp1.
  destruct (take_pending_stacks st _ r0 st1 Htp) as [_ Hc1].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_u32_leb data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[count p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_u32_leb_sound data _ count p1 Hleb) as Hcount.
  destruct (opiter_read_table_labels
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending := st1.(opiter_OpIterState_pending)
              |} data count) as [[r2 st2]|] eqn:Htl;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [expect|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (read_table_labels_sound _ data count st2 expect Htl)
    as [ls [Hrep [Hall Hnone]]].
  cbn [opiter_OpIterState_pos] in Hrep.
  assert (Hc2 : vec_list st2.(opiter_OpIterState_ctrls)
                = vec_list st.(opiter_OpIterState_ctrls)).
  { destruct (read_table_labels_fields _ data count _ st2 Htl) as [_ Hc].
    rewrite Hc. cbn [opiter_OpIterState_ctrls]. exact Hc1. }
  destruct (opiter_read_label st2 data) as [[r3 st3]|] eqn:Hrl;
    cbn [bind] in H; [|discriminate].
  destruct r3 as [[d0 target]|e3].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  rewrite branch_target_bt_spec in H. cbn [bind] in H.
  destruct (opiter_merge_target expect (branch_target_bt_of target)) as [r4|]
    eqn:Hmt; cbn [bind] in H; [|discriminate].
  destruct r4 as [common0|e4].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (merge_target_ok _ _ _ Hmt) as [Hcommon Hprev]. subst common0.
  destruct (read_label_fields st2 data _ st3 Hrl) as [_ Hc3].
  pose proof (read_label_sound st2 data d0 target st3 Hrl) as Hdef.
  pose proof (read_label_target st2 data d0 target st3 Hrl) as Hdt.
  (* the stack work after the immediates leaves the cursor alone *)
  destruct (opiter_pop_with_type st3 Types_ValueType_I32) as [[r5 st4]|] eqn:Hp5;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos st3 _ r5 st4 Hp5) as Hq4. unfold pos_of in Hq4.
  destruct r5 as [t5|e5].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_block_results (branch_target_bt_of target)) as [types|]
    eqn:Hbr; cbn [bind] in H; [|discriminate].
  destruct (opiter_pop_types st4 (alloc_vec_Vec_deref types)) as [[r6 st5]|]
    eqn:Hpt; cbn [bind] in H; [|discriminate].
  pose proof (pop_types_pos _ _ r6 st5 Hpt) as Hq5. unfold pos_of in Hq5.
  destruct r6 as [u6|e6].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u6. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_mark_unreachable st5) as [st6|] eqn:Hmu;
    cbn [bind] in H; [|discriminate].
  injection H as Hc0 <-.
  pose proof (mark_unreachable_pos st5 st6 Hmu) as Hq6. unfold pos_of in Hq6.
  rewrite Hq6. rewrite Hq5. rewrite Hq4. rewrite <- Hc0.
  exists ls, (to_Z d0), (bytes_from data st2.(opiter_OpIterState_pos)).
  split.
  { eapply repr_vec_u32_intro with (n := to_Z count);
      [rewrite <- Hp1; exact Hcount | exact Hrep]. }
  split; [exact Hdef|].
  apply List.Forall_app. split.
  - (* every entry of the vector, transported to [st]'s control stack: the loop
       ran from a state that differs from [st] only in the cursor *)
    destruct expect as [e0|].
    + rewrite <- (Hprev e0 eq_refl).
      apply (List.Forall_impl _
               (fun d Hd => depth_target_ctrls _ st d _ (eq_sym Hc1) Hd)).
      apply (Hall _ eq_refl).
    + rewrite (Hnone eq_refl). apply List.Forall_nil.
  - apply List.Forall_cons; [|apply List.Forall_nil].
    apply (depth_target_ctrls st2 st _ _ (eq_sym Hc2) Hdt).
Qed.

(** The two call operators. [take_index] is the shared prologue, so the index's
    encoding is what it consumed; [call_indirect] then swallows the reserved
    zero byte, which is why its remainder is the one after that byte. *)
Theorem take_index_sound : forall st data opcode idx st',
  opiter_take_index st data opcode = Ok (Core_result_Result_Ok idx, st') ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) (to_Z idx)
           (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros st data opcode idx st' H. unfold opiter_take_index in H.
  destruct (opiter_take_pending st opcode) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opcode r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_u32_leb data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[idx0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  injection H as Hidx <-. cbn [opiter_OpIterState_pos].
  rewrite <- Hp1. rewrite <- Hidx.
  apply (read_u32_leb_sound data st1.(opiter_OpIterState_pos) idx0 p1 Hleb).
Qed.

Theorem read_call_sound : forall st data module idx st',
  opiter_read_call st data module = Ok (Core_result_Result_Ok idx, st') ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) (to_Z idx)
           (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros st data module idx st' H. unfold opiter_read_call in H.
  destruct (opiter_take_index st data opiter_op_call) as [[r0 st1]|] eqn:Hti;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [idx0|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (scalar_cast U32 Usize idx0) as [i|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  destruct (i s>= alloc_vec_Vec_len module.(env_Env_func_types));
    [discriminate|].
  destruct (alloc_vec_Vec_index
              (core_slice_index_SliceIndexUsizeSliceInst types_FuncType_t)
              module.(env_Env_func_types) i) as [ft|] eqn:Hidx;
    cbn [bind] in H; [|discriminate].
  destruct (opiter_require_single_result
              (alloc_vec_Vec_deref ft.(types_FuncType_results))) as [r1|] eqn:Hrs;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [u1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u1. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_pop_types st1 (alloc_vec_Vec_deref ft.(types_FuncType_params)))
    as [[r2 st2]|] eqn:Hpt; cbn [bind] in H; [|discriminate].
  pose proof (pop_types_pos _ _ r2 st2 Hpt) as Hp2. unfold pos_of in Hp2.
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_types st2
              (alloc_vec_Vec_deref ft.(types_FuncType_results))) as [st3|]
    eqn:Hpu; cbn [bind] in H; [|discriminate].
  injection H as Hidx0 <-.
  pose proof (push_types_pos st2 _ st3 Hpu) as Hp3. unfold pos_of in Hp3.
  rewrite Hp3. rewrite Hp2. rewrite <- Hidx0.
  apply (take_index_sound st data _ idx0 st1 Hti).
Qed.

Theorem read_call_indirect_sound : forall st data module idx st',
  opiter_read_call_indirect st data module
    = Ok (Core_result_Result_Ok idx, st') ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) (to_Z idx)
           (0 :: bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros st data module idx st' H. unfold opiter_read_call_indirect in H.
  destruct (opiter_take_index st data opiter_op_call_indirect) as [[r0 st1]|]
    eqn:Hti; cbn [bind] in H; [|discriminate].
  destruct r0 as [idx0|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_read_reserved_zero st1 data) as [[r1 st2]|] eqn:Hrz;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [u1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u1. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_reserved_zero_sound st1 data st2 Hrz) as Hrzb.
  destruct (alloc_vec_Vec_is_empty alloc_alloc_Global
              module.(env_Env_table_types)) as [emp|] eqn:Hemp;
    cbn [bind] in H; [|discriminate].
  destruct emp; [discriminate|].
  destruct (scalar_cast U32 Usize idx0) as [i|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  destruct (i s>= alloc_vec_Vec_len module.(env_Env_types));
    [discriminate|].
  destruct (alloc_vec_Vec_index
              (core_slice_index_SliceIndexUsizeSliceInst types_FuncType_t)
              module.(env_Env_types) i) as [ft|] eqn:Hidx;
    cbn [bind] in H; [|discriminate].
  destruct (opiter_require_single_result
              (alloc_vec_Vec_deref ft.(types_FuncType_results))) as [r2|] eqn:Hrs;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_pop_with_type st2 Types_ValueType_I32) as [[r3 st3]|] eqn:Hpw;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos st2 _ r3 st3 Hpw) as Hp3. unfold pos_of in Hp3.
  destruct r3 as [t3|e3].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_pop_types st3 (alloc_vec_Vec_deref ft.(types_FuncType_params)))
    as [[r4 st4]|] eqn:Hpt; cbn [bind] in H; [|discriminate].
  pose proof (pop_types_pos _ _ r4 st4 Hpt) as Hp4. unfold pos_of in Hp4.
  destruct r4 as [u4|e4].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u4. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_types st4
              (alloc_vec_Vec_deref ft.(types_FuncType_results))) as [st5|]
    eqn:Hpu; cbn [bind] in H; [|discriminate].
  injection H as Hidx0 <-.
  pose proof (push_types_pos st4 _ st5 Hpu) as Hp5. unfold pos_of in Hp5.
  rewrite Hp5. rewrite Hp4. rewrite Hp3. rewrite <- Hrzb. rewrite <- Hidx0.
  apply (take_index_sound st data _ idx0 st1 Hti).
Qed.

(** [load] and [store] read a memarg and then pop and push; the memory and
    alignment checks take no state at all. *)
Theorem read_load_sound : forall st data module opcode ty natural m st',
  opiter_read_load st data module opcode ty natural
    = Ok (Core_result_Result_Ok m, st') ->
  repr_memarg (bytes_from data st.(opiter_OpIterState_pos))
              (to_Z m.(opiter_MemArg_align), to_Z m.(opiter_MemArg_offset))
              (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros st data module opcode ty natural m st' H. unfold opiter_read_load in H.
  destruct (opiter_take_pending st opcode) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opcode r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_read_memarg st1 data) as [[r1 st2]|] eqn:Hma;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [m0|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_check_memory_and_alignment module m0 natural) as [r2|] eqn:Hck;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_pop_with_type st2 Types_ValueType_I32) as [[r3 st3]|] eqn:Hp;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos st2 _ r3 st3 Hp) as Hp3. unfold pos_of in Hp3.
  destruct r3 as [t3|e3].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val st3 (Opiter_StackType_Val ty)) as [st4|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as Hmeq Hst.
  pose proof (push_val_pos st3 _ st4 Hpv) as Hp4. unfold pos_of in Hp4.
  rewrite <- Hst. rewrite Hp4. rewrite Hp3. rewrite <- Hp1. rewrite <- Hmeq.
  apply read_memarg_sound. exact Hma.
Qed.

Theorem read_store_sound : forall st data module opcode ty natural m st',
  opiter_read_store st data module opcode ty natural
    = Ok (Core_result_Result_Ok m, st') ->
  repr_memarg (bytes_from data st.(opiter_OpIterState_pos))
              (to_Z m.(opiter_MemArg_align), to_Z m.(opiter_MemArg_offset))
              (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros st data module opcode ty natural m st' H. unfold opiter_read_store in H.
  destruct (opiter_take_pending st opcode) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opcode r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_read_memarg st1 data) as [[r1 st2]|] eqn:Hma;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [m0|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_check_memory_and_alignment module m0 natural) as [r2|] eqn:Hck;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_pop_with_type st2 ty) as [[r3 st3]|] eqn:Hpop1;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos st2 ty r3 st3 Hpop1) as Hp3.
  unfold pos_of in Hp3.
  destruct r3 as [t3|e3].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_pop_with_type st3 Types_ValueType_I32) as [[r4 st4]|] eqn:Hpop2;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos st3 _ r4 st4 Hpop2) as Hp4.
  unfold pos_of in Hp4.
  destruct r4 as [t4|e4].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  injection H as Hmeq Hst.
  rewrite <- Hst. rewrite Hp4. rewrite Hp3. rewrite <- Hp1. rewrite <- Hmeq.
  apply read_memarg_sound. exact Hma.
Qed.

(** Assembling a [repr_op] out of the opcode byte and the immediates.

    For a reader that consumes immediates there is nothing to assemble: its
    lemma above states exactly the hypothesis of the matching [repr_op]
    constructor, so the caller applies [repr_op_const], [repr_op_block],
    [repr_op_idx], [repr_op_load] or [repr_op_store] and discharges it directly.

    A reader that consumes none needs the cursor equality turned into "the
    remainder is what followed the opcode byte", which is these two. What is left
    for the caller either way is the [op_spec] row, and that is a computation once
    the opcode is a literal. *)

Lemma repr_op_of_inert : forall data (b : u8) be st st',
  op_spec (to_Z b) = Some (Sh_nullary be) ->
  pos_of st' = pos_of st ->
  repr_op (to_Z b :: bytes_from data st.(opiter_OpIterState_pos))
          (FO_plain be)
          (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros data b be st st' Hspec Hpos. unfold pos_of in Hpos. rewrite Hpos.
  apply repr_op_nullary. exact Hspec.
Qed.

(** The same for an operator whose only immediate is the reserved zero byte:
    the reader consumed exactly that byte, which is what [repr_op_reserved]
    asks for. *)
Lemma repr_op_of_reserved : forall data (b : u8) be st st',
  op_spec (to_Z b) = Some (Sh_reserved be) ->
  bytes_from data st.(opiter_OpIterState_pos)
    = 0 :: bytes_from data st'.(opiter_OpIterState_pos) ->
  repr_op (to_Z b :: bytes_from data st.(opiter_OpIterState_pos))
          (FO_plain be)
          (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros data b be st st' Hspec Hbytes. rewrite Hbytes.
  apply repr_op_reserved. exact Hspec.
Qed.

Lemma repr_op_of_end : forall data (b : u8) st st',
  op_spec (to_Z b) = Some Sh_end ->
  pos_of st' = pos_of st ->
  repr_op (to_Z b :: bytes_from data st.(opiter_OpIterState_pos))
          FO_end
          (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros data b st st' Hspec Hpos. unfold pos_of in Hpos. rewrite Hpos.
  apply repr_op_end. exact Hspec.
Qed.

Lemma repr_op_of_else : forall data (b : u8) st st',
  op_spec (to_Z b) = Some Sh_else ->
  pos_of st' = pos_of st ->
  repr_op (to_Z b :: bytes_from data st.(opiter_OpIterState_pos))
          FO_else
          (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros data b st st' Hspec Hpos. unfold pos_of in Hpos. rewrite Hpos.
  apply repr_op_else. exact Hspec.
Qed.

(** The two boundary conditions of the validation loop.

    [start_function] leaves the cursor at 0, so the stream the loop accounts for
    starts as the whole body; and the loop accepts only when the cursor has
    reached the end, which is what makes the top-level theorem's operator stream
    consume every byte rather than a prefix. *)

Lemma bytes_from_zero : forall data, bytes_from data 0%usize = byte_list data.
Proof. intros data. reflexivity. Qed.

Lemma bytes_from_at_zero : forall data pos,
  to_Z pos = 0 -> bytes_from data pos = byte_list data.
Proof.
  intros data pos Hpos. unfold bytes_from. rewrite Hpos. reflexivity.
Qed.

Lemma bytes_from_end : forall data pos,
  to_Z pos = to_Z (slice_len data) -> bytes_from data pos = [].
Proof.
  intros data pos Hpos. unfold bytes_from.
  apply List.skipn_all2. unfold byte_list. rewrite List.map_length.
  rewrite slice_len_spec in Hpos. rewrite Hpos.
  rewrite Z_to_nat_of_nat. apply Nat.le_refl.
Qed.

(* ================================================================== *)
(** ** The immediate decoders cannot fail                              *)
(* ================================================================== *)

(** Panic-freedom for the LEB128 readers. Not the same statement as soundness:
    that one says what the result means *if* there is one, this one says there is
    one. Both directions need the same bounds, so this mirrors
    [read_u32_leb_loop_sound] step for step, using the [_ok] arithmetic lemmas
    where that proof used the [_ok] value lemmas.

    No hypothesis about the body length is needed. The cursor is only advanced
    after the bounds check, so [p < slice_len data <= usize_max] already rules the
    increment out of range. What [MAX_FUNCTION_BYTES] is needed for is the stacks,
    not the cursor. *)
Lemma read_u32_leb_loop_ok : forall n data acc mult p i,
  to_Z i + Z.of_nat n = 4 ->
  leb_inv acc mult i ->
  exists r, reader_read_u32_leb_loop data acc mult p i = Ok r.
Proof.
  induction n as [|n IH]; intros data acc mult p i Hn Hinv;
    destruct Hinv as [Hi [Hmult Hacc]];
    unfold reader_read_u32_leb_loop; rewrite loop_unfold; cbn beta iota;
    destruct (p s>= slice_len data) eqn:Hge;
    [eexists; reflexivity | | eexists; reflexivity | ].
  - (* i = 4: the fifth byte is the last one, and carries only four bits *)
    assert (Hi4 : to_Z i = 4) by (cbn in Hn; lia).
    apply scalar_geb_false_lt in Hge. rewrite slice_len_spec in Hge.
    destruct (slice_index_usize_ok data p Hge) as [b Hb].
    rewrite Hb. cbn [bind].
    destruct (usize_add_1_ok p) as [p2 [Hadd _]].
    { pose proof (usize_le_max (slice_len data)) as Hmax.
      rewrite slice_len_spec in Hmax. lia. }
    rewrite Hadd. cbn [bind].
    destruct (u8_rem_128_ok b) as [low [Hrem [Hlowval Hlowbd]]].
    rewrite Hrem. cbn [bind].
    assert (Heq4 : (i s= 4%u32) = true).
    { unfold scalar_eqb. apply Z.eqb_eq. rewrite Hi4. reflexivity. }
    rewrite Heq4. cbn beta iota.
    destruct (low s> 15%u8) eqn:Hgt; [eexists; reflexivity|].
    apply scalar_gtb_false in Hgt.
    assert (H15 : to_Z 15%u8 = 15) by reflexivity. rewrite H15 in Hgt.
    destruct (cast_u8_u32_ok low) as [c [Hcast Hcval]].
    rewrite Hcast. cbn [bind].
    assert (Hmult4 : to_Z mult = 268435456).
    { rewrite Hmult. rewrite Hi4. reflexivity. }
    destruct (u32_mul_ok c mult) as [prod [Hmul Hmulval]].
    { rewrite Hcval. rewrite Hmult4. rewrite u32_max_val. lia. }
    rewrite Hmul. cbn [bind].
    assert (Hacc4 : to_Z acc < 268435456) by (rewrite Hi4 in Hacc; exact Hacc).
    destruct (u32_add_ok acc prod) as [sum [Hadd2 _]].
    { rewrite Hmulval. rewrite Hcval. rewrite Hmult4. rewrite u32_max_val. lia. }
    rewrite Hadd2. cbn [bind].
    (* either the byte was the last, or the fifth byte's continuation bit is
       rejected; the earlier rewrite already fired on that occurrence too *)
    destruct (b s< 128%u8); [eexists; reflexivity|].
    cbn beta iota. eexists. reflexivity.
  - (* i < 4: fold the byte in and go round again *)
    assert (Hilt : to_Z i <= 3) by (cbn in Hn; lia).
    apply scalar_geb_false_lt in Hge. rewrite slice_len_spec in Hge.
    destruct (slice_index_usize_ok data p Hge) as [b Hb].
    rewrite Hb. cbn [bind].
    destruct (usize_add_1_ok p) as [p2 [Hadd Hp2]].
    { pose proof (usize_le_max (slice_len data)) as Hmax.
      rewrite slice_len_spec in Hmax. lia. }
    rewrite Hadd. cbn [bind].
    destruct (u8_rem_128_ok b) as [low [Hrem [Hlowval Hlowbd]]].
    rewrite Hrem. cbn [bind].
    assert (Heq4 : (i s= 4%u32) = false).
    { unfold scalar_eqb. apply Z.eqb_neq.
      assert (to_Z 4%u32 = 4) by reflexivity. lia. }
    rewrite Heq4. cbn beta iota.
    (* the place value is at most 128^3, and the accumulator is below it *)
    pose proof (pow128_pos (to_Z i) (proj1 Hi)) as Hmpos.
    pose proof (pow128_le (to_Z i) 3 (proj1 Hi) Hilt) as Hmle.
    assert (Hp3 : (128:Z) ^ 3 = 2097152) by reflexivity.
    rewrite Hp3 in Hmle.
    assert (Hmultle : to_Z mult <= 2097152) by (rewrite Hmult; exact Hmle).
    assert (Hmultpos : 0 < to_Z mult) by (rewrite Hmult; exact Hmpos).
    assert (Haccle : to_Z acc < to_Z mult) by (rewrite Hmult; exact Hacc).
    assert (Hlm : to_Z low * to_Z mult <= 127 * 2097152).
    { apply Z.mul_le_mono_nonneg; lia. }
    assert (Hlm2 : to_Z low * to_Z mult <= 127 * to_Z mult).
    { apply Z.mul_le_mono_nonneg_r; lia. }
    destruct (cast_u8_u32_ok low) as [c [Hcast Hcval]].
    rewrite Hcast. cbn [bind].
    destruct (u32_mul_ok c mult) as [prod [Hmul Hmulval]].
    { rewrite Hcval. rewrite u32_max_val. lia. }
    rewrite Hmul. cbn [bind].
    destruct (u32_add_ok acc prod) as [sum [Hadd2 Hsumval]].
    { rewrite Hmulval. rewrite Hcval. rewrite u32_max_val. lia. }
    rewrite Hadd2. cbn [bind].
    (* the earlier [rewrite Heq4] already fired on this occurrence too *)
    destruct (b s< 128%u8) eqn:Hlt; [eexists; reflexivity|]. cbn beta iota.
    assert (H1 : to_Z 1%u32 = 1) by reflexivity.
    assert (H128 : to_Z 128%u32 = 128) by reflexivity.
    destruct (u32_mul_ok mult 128%u32) as [mult2 [Hmul2 Hmul2val]].
    { rewrite H128. rewrite u32_max_val. lia. }
    rewrite Hmul2. cbn [bind].
    destruct (u32_add_ok i 1%u32) as [i5 [Hadd3 Hi5val]].
    { rewrite H1. rewrite u32_max_val. lia. }
    rewrite Hadd3. cbn [bind].
    (* the loop continues on a state one byte further along *)
    apply (IH data sum mult2 p2 i5).
    + rewrite Hi5val. rewrite H1. cbn in Hn. lia.
    + unfold leb_inv. repeat split.
      * rewrite Hi5val. rewrite H1. lia.
      * rewrite Hi5val. rewrite H1. lia.
      * rewrite Hmul2val. rewrite H128. rewrite Hi5val. rewrite H1.
        rewrite Z.pow_add_r; [|apply (proj1 Hi) | lia].
        rewrite Hmult. ring.
      * rewrite Hsumval. rewrite Hmulval. rewrite Hcval. rewrite Hi5val.
        rewrite H1. rewrite Z.pow_add_r; [|apply (proj1 Hi) | lia].
        rewrite <- Hmult. lia.
Qed.

Theorem read_u32_leb_ok : forall data pos,
  exists r, reader_read_u32_leb data pos = Ok r.
Proof.
  intros data pos. unfold reader_read_u32_leb.
  apply (read_u32_leb_loop_ok 4 data 0%u32 1%u32 pos 0%u32).
  - reflexivity.
  - unfold leb_inv. cbn. lia.
Qed.

(** The tail of the signed loop's last byte: the two range checks. Written as a
    tactic rather than a lemma because it sits under the loop combinator's match,
    where the [bind]s have already been unfolded. *)
Local Ltac sn_tail x l h :=
  destruct (x s< l); [eexists; reflexivity|];
  destruct (x s> h); eexists; reflexivity.

(** The signed reader cannot fail either. The place value peaks at [128 ^ last]
    and the accumulator below it, so every product and sum stays under
    [128 ^ (last + 1)], which [sleb_params] puts inside [i128]; there is no
    narrowing step left inside the loop, since the cast moved to the wrappers.

    The arithmetic prologue is common to both cases, so it runs on both goals at
    once and only the continuation branch is written twice. *)
Lemma read_sn_leb_loop_ok : forall n bits data last lo hi acc mult p i,
  sleb_params bits last lo hi ->
  to_Z i + Z.of_nat n = to_Z last ->
  sleb_inv last acc mult i ->
  exists r, reader_read_sn_leb_loop data last lo hi acc mult p i = Ok r.
Proof.
  induction n as [|n IH];
    intros bits data last lo hi acc mult p i Hpar Hn Hinv;
    pose proof (sleb_bounds bits last lo hi acc mult i Hpar Hinv)
      as [Hmpos [Hmle [Haccm [Hbig' Hminmax]]]];
    pose proof Hinv as Hinv2; destruct Hinv2 as [Hi [Hmult Hacc]];
    unfold reader_read_sn_leb_loop; rewrite loop_unfold; cbn beta iota;
    destruct (p s>= slice_len data) eqn:Hge;
    [eexists; reflexivity | | eexists; reflexivity | ].
  (* the byte, the cursor step, the payload and the fold, all shared *)
  all: apply scalar_geb_false_lt in Hge; rewrite slice_len_spec in Hge.
  all: destruct (slice_index_usize_ok data p Hge) as [b Hb].
  all: rewrite Hb; cbn [bind].
  all: assert (Hpmax : to_Z p + 1 <= usize_max)
         by (pose proof (usize_le_max (slice_len data)) as Hm;
             rewrite slice_len_spec in Hm; lia).
  all: destruct (usize_add_1_ok p Hpmax) as [p2 [Hadd Hp2]].
  all: rewrite Hadd; cbn [bind].
  all: destruct (u8_rem_128_ok b) as [low [Hrem [Hlowval Hlowbd]]].
  all: rewrite Hrem; cbn [bind].
  all: assert (H128i : to_Z 128%i128 = 128) by reflexivity.
  all: destruct (cast_u8_i128_ok low) as [c [Hcast Hcval]].
  all: rewrite Hcast; cbn [bind].
  all: assert (Hlm0 : 0 <= to_Z low * to_Z mult)
         by (apply Z.mul_nonneg_nonneg; lia).
  all: assert (Hlm : to_Z low * to_Z mult <= 127 * to_Z mult)
         by (apply Z.mul_le_mono_nonneg_r; lia).
  all: assert (Hmulb : i128_min <= to_Z c * to_Z mult <= i128_max)
         by (rewrite Hcval; lia).
  all: destruct (i128_mul_ok c mult Hmulb) as [prod [Hmul Hmulval]].
  all: rewrite Hmul; cbn [bind].
  all: assert (Haddb : i128_min <= to_Z acc + to_Z prod <= i128_max)
         by (rewrite Hmulval; rewrite Hcval; lia).
  all: destruct (i128_add_ok acc prod Haddb) as [sum [Hadd2 Hsumval]].
  all: rewrite Hadd2; cbn [bind].
  all: assert (Hsumlo : 0 <= to_Z sum)
         by (rewrite Hsumval; rewrite Hmulval; rewrite Hcval; lia).
  all: assert (Hsumhi : to_Z sum <= 128 * to_Z mult)
         by (rewrite Hsumval; rewrite Hmulval; rewrite Hcval; lia).
  all: assert (Hmb : i128_min <= to_Z mult * to_Z 128%i128 <= i128_max)
         by lia.
  - (* the budget is spent: the byte must be the last one *)
    assert (Hilast : to_Z i = to_Z last) by (cbn in Hn; lia).
    destruct (b s< 128%u8) eqn:Hlt.
    + destruct (low s>= 64%u8) eqn:Hneg.
      * destruct (i128_mul_ok mult 128%i128 Hmb) as [m128 [Hm128 Hm128val]].
        rewrite Hm128. cbn [bind].
        assert (Hsb : i128_min <= to_Z sum - to_Z m128 <= i128_max)
          by (rewrite Hm128val; rewrite H128i; lia).
        destruct (i128_sub_ok sum m128 Hsb) as [acc3 [Hsub _]].
        rewrite Hsub. cbn [bind]. sn_tail acc3 lo hi.
      * cbn [bind]. sn_tail sum lo hi.
    + (* a continuation bit past the budget is rejected *)
      assert (Heq : (i s= last) = true)
        by (unfold scalar_eqb; apply Z.eqb_eq; exact Hilast).
      rewrite Heq. cbn beta iota. eexists. reflexivity.
  - (* budget left *)
    assert (Hilt : to_Z i < to_Z last) by (cbn in Hn; lia).
    destruct (b s< 128%u8) eqn:Hlt.
    + destruct (low s>= 64%u8) eqn:Hneg.
      * destruct (i128_mul_ok mult 128%i128 Hmb) as [m128 [Hm128 Hm128val]].
        rewrite Hm128. cbn [bind].
        assert (Hsb : i128_min <= to_Z sum - to_Z m128 <= i128_max)
          by (rewrite Hm128val; rewrite H128i; lia).
        destruct (i128_sub_ok sum m128 Hsb) as [acc3 [Hsub _]].
        rewrite Hsub. cbn [bind]. sn_tail acc3 lo hi.
      * cbn [bind]. sn_tail sum lo hi.
    + (* multiply the place value up and go round again *)
      assert (Heq : (i s= last) = false)
        by (unfold scalar_eqb; apply Z.eqb_neq; lia).
      rewrite Heq. cbn beta iota.
      assert (H1 : to_Z 1%u32 = 1) by reflexivity.
      destruct (i128_mul_ok mult 128%i128 Hmb) as [mult2 [Hmul2 Hmul2val]].
      rewrite Hmul2. cbn [bind].
      destruct (u32_add_ok i 1%u32) as [i5 [Hadd3 Hi5val]].
      { rewrite H1. pose proof (u32_bounds last) as [_ Hlm2]. lia. }
      rewrite Hadd3. cbn [bind].
      apply (IH bits data last lo hi sum mult2 p2 i5).
      * exact Hpar.
      * rewrite Hi5val. rewrite H1. cbn in Hn. lia.
      * unfold sleb_inv. repeat split.
        -- rewrite Hi5val. rewrite H1. lia.
        -- rewrite Hi5val. rewrite H1. lia.
        -- rewrite Hmul2val. rewrite H128i. rewrite Hi5val. rewrite H1.
           rewrite Z.pow_add_r; [|apply (proj1 Hi) | lia].
           rewrite Z.pow_1_r. rewrite Hmult. ring.
        -- exact Hsumlo.
        -- rewrite Hi5val. rewrite H1.
           rewrite Z.pow_add_r; [|apply (proj1 Hi) | lia].
           rewrite Z.pow_1_r. rewrite <- Hmult. lia.
Qed.

(** The wrappers. The narrowing cast is the only step the loop does not already
    justify, and the range it checked is exactly the cast's precondition, which
    [read_sn_leb_loop_sound] reports. *)
Theorem read_s32_leb_ok : forall data pos,
  exists r, reader_read_s32_leb data pos = Ok r.
Proof.
  intros data pos. unfold reader_read_s32_leb, reader_read_sn_leb.
  assert (Hstart : sleb_inv 4%u32 0%i128 1%i128 0%u32)
    by (unfold sleb_inv; cbn; lia).
  assert (Hn : to_Z 0%u32 + Z.of_nat 4 = to_Z 4%u32) by reflexivity.
  destruct (read_sn_leb_loop_ok 4 32 data 4%u32 (-2147483648)%i128
              2147483647%i128 0%i128 1%i128 pos 0%u32 sleb_params_32 Hn Hstart)
    as [r Hleb].
  rewrite Hleb. cbn [bind].
  destruct r as [[v0 p0]|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (read_sn_leb_loop_sound 4 32 data 4%u32 (-2147483648)%i128
              2147483647%i128 0%i128 1%i128 pos 0%u32 v0 p0
              sleb_params_32 Hn Hstart Hleb) as [m [_ [_ Hrng]]].
  assert (Hlov : to_Z (-2147483648)%i128 = -2147483648) by reflexivity.
  assert (Hhiv : to_Z 2147483647%i128 = 2147483647) by reflexivity.
  destruct (cast_i128_i32_ok v0) as [v1 [Hc _]].
  { rewrite i32_min_val. rewrite i32_max_val. lia. }
  rewrite Hc. cbn [bind]. eexists. reflexivity.
Qed.

Theorem read_s64_leb_ok : forall data pos,
  exists r, reader_read_s64_leb data pos = Ok r.
Proof.
  intros data pos. unfold reader_read_s64_leb, reader_read_sn_leb.
  assert (Hstart : sleb_inv 9%u32 0%i128 1%i128 0%u32)
    by (unfold sleb_inv; cbn; lia).
  assert (Hn : to_Z 0%u32 + Z.of_nat 9 = to_Z 9%u32) by reflexivity.
  destruct (read_sn_leb_loop_ok 9 64 data 9%u32 (-9223372036854775808)%i128
              9223372036854775807%i128 0%i128 1%i128 pos 0%u32 sleb_params_64
              Hn Hstart) as [r Hleb].
  rewrite Hleb. cbn [bind].
  destruct r as [[v0 p0]|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (read_sn_leb_loop_sound 9 64 data 9%u32 (-9223372036854775808)%i128
              9223372036854775807%i128 0%i128 1%i128 pos 0%u32 v0 p0
              sleb_params_64 Hn Hstart Hleb) as [m [_ [_ Hrng]]].
  assert (Hlov : to_Z (-9223372036854775808)%i128 = -9223372036854775808)
    by reflexivity.
  assert (Hhiv : to_Z 9223372036854775807%i128 = 9223372036854775807)
    by reflexivity.
  destruct (cast_i128_i64_ok v0) as [v1 [Hc _]].
  { rewrite i64_min_val. rewrite i64_max_val. lia. }
  rewrite Hc. cbn [bind]. eexists. reflexivity.
Qed.

(** The readers that consume immediates cannot fail either. Same shape as the
    ones in [OpIter_State.v]: walk the reader, discharge each step with its
    totality lemma, and thread [room] through the pops with the size bounds. *)

Lemma read_byte_total : forall data pos,
  exists r, reader_read_byte data pos = Ok r.
Proof.
  intros data pos. unfold reader_read_byte.
  destruct (pos s>= slice_len data) eqn:Hge; [eexists; reflexivity|].
  apply scalar_geb_false_lt in Hge. rewrite slice_len_spec in Hge.
  destruct (slice_index_usize_ok data pos Hge) as [b Hb].
  rewrite Hb. cbn [bind].
  destruct (usize_add_1_ok pos) as [p2 [Hadd _]].
  { pose proof (usize_le_max (slice_len data)) as Hm.
    rewrite slice_len_spec in Hm. lia. }
  rewrite Hadd. cbn [bind]. eexists. reflexivity.
Qed.

Lemma read_block_type_total : forall data pos,
  exists r, opiter_read_block_type data pos = Ok r.
Proof.
  intros data pos. unfold opiter_read_block_type.
  destruct (read_byte_total data pos) as [r0 Hrb]. rewrite Hrb. cbn [bind].
  destruct r0 as [[b p]|e].
  - rewrite branch_ok. cbn [bind].
    destruct (b s= 64%u8); [eexists; reflexivity|].
    destruct (b s= 127%u8); [eexists; reflexivity|].
    destruct (b s= 126%u8); [eexists; reflexivity|].
    destruct (b s= 125%u8); [eexists; reflexivity|].
    destruct (b s= 124%u8); eexists; reflexivity.
  - rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
    eexists. reflexivity.
Qed.

Lemma read_memarg_total : forall st data,
  exists r st', opiter_read_memarg st data = Ok (r, st').
Proof.
  intros st data. unfold opiter_read_memarg.
  destruct (read_u32_leb_ok data st.(opiter_OpIterState_pos)) as [r0 H0].
  rewrite H0. cbn [bind].
  destruct r0 as [[a p1]|e0].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (read_u32_leb_ok data p1) as [r1 H1]. rewrite H1. cbn [bind].
  destruct r1 as [[o p2]|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma require_memory_total : forall module,
  exists r, opiter_require_memory module = Ok r.
Proof.
  intros module. unfold opiter_require_memory.
  rewrite vec_is_empty_spec. cbn [bind].
  destruct (vec_list module.(env_Env_mem_types)); eexists; reflexivity.
Qed.

Lemma check_memory_and_alignment_total : forall module memarg natural,
  exists r, opiter_check_memory_and_alignment module memarg natural = Ok r.
Proof.
  intros module memarg natural. unfold opiter_check_memory_and_alignment.
  destruct (require_memory_total module) as [r0 Hrm]. rewrite Hrm. cbn [bind].
  destruct r0 as [u|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err.
       eexists. reflexivity. }
  destruct u. rewrite branch_ok. cbn [bind].
  destruct (memarg.(opiter_MemArg_align) s> natural); eexists; reflexivity.
Qed.

Lemma read_reserved_zero_total : forall st data,
  exists r st', opiter_read_reserved_zero st data = Ok (r, st').
Proof.
  intros st data. unfold opiter_read_reserved_zero.
  destruct (read_byte_total data st.(opiter_OpIterState_pos)) as [r0 Hrb].
  rewrite Hrb. cbn [bind].
  destruct r0 as [[b p]|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (b s<> 0%u8); eexists; eexists; reflexivity.
Qed.


Lemma read_memory_size_total : forall st data module,
  room st -> exists r st', opiter_read_memory_size st data module = Ok (r, st').
Proof.
  intros st data module Hroom. unfold opiter_read_memory_size.
  destruct (take_pending_total st opiter_op_memory_size) as [r0 [st1 Htp]].
  rewrite Htp. cbn [bind].
  pose proof (take_pending_size st _ r0 st1 Htp) as Hs1.
  destruct r0 as [u|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u. rewrite branch_ok. cbn [bind].
  destruct (read_reserved_zero_total st1 data) as [r1 [st2 Hrz]].
  rewrite Hrz. cbn [bind].
  pose proof (read_reserved_zero_size st1 data r1 st2 Hrz) as Hs2.
  destruct r1 as [u1|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u1. rewrite branch_ok. cbn [bind].
  destruct (require_memory_total module) as [r2 Hrm]. rewrite Hrm. cbn [bind].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u2. rewrite branch_ok. cbn [bind].
  destruct (push_val_total st2 (Opiter_StackType_Val Types_ValueType_I32))
    as [st3 Hpv].
  { apply room_vals. unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma read_memory_grow_total : forall st data module,
  room st -> exists r st', opiter_read_memory_grow st data module = Ok (r, st').
Proof.
  intros st data module Hroom. unfold opiter_read_memory_grow.
  destruct (take_pending_total st opiter_op_memory_grow) as [r0 [st1 Htp]].
  rewrite Htp. cbn [bind].
  pose proof (take_pending_size st _ r0 st1 Htp) as Hs1.
  destruct r0 as [u|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u. rewrite branch_ok. cbn [bind].
  destruct (read_reserved_zero_total st1 data) as [r1 [st2 Hrz]].
  rewrite Hrz. cbn [bind].
  pose proof (read_reserved_zero_size st1 data r1 st2 Hrz) as Hs2.
  destruct r1 as [u1|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u1. rewrite branch_ok. cbn [bind].
  destruct (require_memory_total module) as [r2 Hrm]. rewrite Hrm. cbn [bind].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u2. rewrite branch_ok. cbn [bind].
  destruct (pop_with_type_total st2 Types_ValueType_I32) as [r3 [st3 Hp3]].
  rewrite Hp3. cbn [bind].
  pose proof (pop_with_type_size st2 _ r3 st3 Hp3) as Hs3.
  destruct r3 as [t3|e3].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (push_val_total st3 (Opiter_StackType_Val Types_ValueType_I32))
    as [st4 Hpv].
  { apply room_vals. unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma read_i32_const_total : forall st data,
  room st -> exists r st', opiter_read_i32_const st data = Ok (r, st').
Proof.
  intros st data Hroom. unfold opiter_read_i32_const.
  destruct (take_pending_total st opiter_op_i32_const) as [r0 [st1 Htp]].
  rewrite Htp. cbn [bind].
  pose proof (take_pending_size st opiter_op_i32_const r0 st1 Htp) as Hs1.
  destruct r0 as [u|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u. rewrite branch_ok. cbn [bind].
  destruct (read_s32_leb_ok data st1.(opiter_OpIterState_pos)) as [r1 Hleb].
  rewrite Hleb. cbn [bind].
  destruct r1 as [[v p1]|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (push_val_total
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending := st1.(opiter_OpIterState_pending)
              |} (Opiter_StackType_Val Types_ValueType_I32)) as [st2 Hpv].
  { cbn [opiter_OpIterState_vals].
    unfold room, stack_size in Hroom. unfold stack_size in Hs1. lia. }
  rewrite Hpv. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma read_f32_const_total : forall st data,
  room st -> exists r st', opiter_read_f32_const st data = Ok (r, st').
Proof.
  intros st data Hroom. unfold opiter_read_f32_const.
  destruct (take_pending_total st opiter_op_f32_const) as [r0 [st1 Htp]].
  rewrite Htp. cbn [bind].
  pose proof (take_pending_size st opiter_op_f32_const r0 st1 Htp) as Hs1.
  destruct r0 as [u|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u. rewrite branch_ok. cbn [bind].
  destruct (read_f32_bits_ok data st1.(opiter_OpIterState_pos)) as [r1 Hleb].
  rewrite Hleb. cbn [bind].
  destruct r1 as [[v p1]|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (push_val_total
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending := st1.(opiter_OpIterState_pending)
              |} (Opiter_StackType_Val Types_ValueType_F32)) as [st2 Hpv].
  { cbn [opiter_OpIterState_vals].
    unfold room, stack_size in Hroom. unfold stack_size in Hs1. lia. }
  rewrite Hpv. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma read_f64_const_total : forall st data,
  room st -> exists r st', opiter_read_f64_const st data = Ok (r, st').
Proof.
  intros st data Hroom. unfold opiter_read_f64_const.
  destruct (take_pending_total st opiter_op_f64_const) as [r0 [st1 Htp]].
  rewrite Htp. cbn [bind].
  pose proof (take_pending_size st opiter_op_f64_const r0 st1 Htp) as Hs1.
  destruct r0 as [u|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u. rewrite branch_ok. cbn [bind].
  destruct (read_f64_bits_ok data st1.(opiter_OpIterState_pos)) as [r1 Hleb].
  rewrite Hleb. cbn [bind].
  destruct r1 as [[v p1]|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (push_val_total
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending := st1.(opiter_OpIterState_pending)
              |} (Opiter_StackType_Val Types_ValueType_F64)) as [st2 Hpv].
  { cbn [opiter_OpIterState_vals].
    unfold room, stack_size in Hroom. unfold stack_size in Hs1. lia. }
  rewrite Hpv. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma read_i64_const_total : forall st data,
  room st -> exists r st', opiter_read_i64_const st data = Ok (r, st').
Proof.
  intros st data Hroom. unfold opiter_read_i64_const.
  destruct (take_pending_total st opiter_op_i64_const) as [r0 [st1 Htp]].
  rewrite Htp. cbn [bind].
  pose proof (take_pending_size st opiter_op_i64_const r0 st1 Htp) as Hs1.
  destruct r0 as [u|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u. rewrite branch_ok. cbn [bind].
  destruct (read_s64_leb_ok data st1.(opiter_OpIterState_pos)) as [r1 Hleb].
  rewrite Hleb. cbn [bind].
  destruct r1 as [[v p1]|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (push_val_total
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending := st1.(opiter_OpIterState_pending)
              |} (Opiter_StackType_Val Types_ValueType_I64)) as [st2 Hpv].
  { cbn [opiter_OpIterState_vals].
    unfold room, stack_size in Hroom. unfold stack_size in Hs1. lia. }
  rewrite Hpv. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma read_block_total : forall st data,
  room st -> exists r st', opiter_read_block st data = Ok (r, st').
Proof.
  intros st data Hroom. unfold opiter_read_block.
  destruct (take_pending_total st opiter_op_block) as [r0 [st1 Htp]].
  rewrite Htp. cbn [bind].
  pose proof (take_pending_size st opiter_op_block r0 st1 Htp) as Hs1.
  destruct r0 as [u|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u. rewrite branch_ok. cbn [bind].
  destruct (read_block_type_total data st1.(opiter_OpIterState_pos)) as [r1 Hbt].
  rewrite Hbt. cbn [bind].
  destruct r1 as [[bt p1]|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (push_ctrl_total
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending := st1.(opiter_OpIterState_pending)
              |} Opiter_LabelKind_Block bt) as [st2 Hpc].
  { cbn [opiter_OpIterState_ctrls].
    unfold room, stack_size in Hroom. unfold stack_size in Hs1. lia. }
  rewrite Hpc. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma read_loop_total : forall st data,
  room st -> exists r st', opiter_read_loop st data = Ok (r, st').
Proof.
  intros st data Hroom. unfold opiter_read_loop.
  destruct (take_pending_total st opiter_op_loop) as [r0 [st1 Htp]].
  rewrite Htp. cbn [bind].
  pose proof (take_pending_size st opiter_op_loop r0 st1 Htp) as Hs1.
  destruct r0 as [u|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u. rewrite branch_ok. cbn [bind].
  destruct (read_block_type_total data st1.(opiter_OpIterState_pos)) as [r1 Hbt].
  rewrite Hbt. cbn [bind].
  destruct r1 as [[bt p1]|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (push_ctrl_total
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending := st1.(opiter_OpIterState_pending)
              |} Opiter_LabelKind_Loop bt) as [st2 Hpc].
  { cbn [opiter_OpIterState_ctrls].
    unfold room, stack_size in Hroom. unfold stack_size in Hs1. lia. }
  rewrite Hpc. cbn [bind]. eexists. eexists. reflexivity.
Qed.

(** [if] is [read_block] with one [pop_with_type] between the block type read
    and the [push_ctrl]; the pop can only shrink the operand stack, so [room]
    transports through it unchanged. *)
Lemma read_if_total : forall st data,
  room st -> exists r st', opiter_read_if st data = Ok (r, st').
Proof.
  intros st data Hroom. unfold opiter_read_if.
  destruct (take_pending_total st opiter_op_if) as [r0 [st1 Htp]].
  rewrite Htp. cbn [bind].
  pose proof (take_pending_size st opiter_op_if r0 st1 Htp) as Hs1.
  destruct r0 as [u|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u. rewrite branch_ok. cbn [bind].
  destruct (read_block_type_total data st1.(opiter_OpIterState_pos)) as [r1 Hbt].
  rewrite Hbt. cbn [bind].
  destruct r1 as [[bt p1]|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (pop_with_type_total
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending := st1.(opiter_OpIterState_pending)
              |} Types_ValueType_I32) as [r2 [st2 Hpw]].
  rewrite Hpw. cbn [bind].
  pose proof (pop_with_type_ctrls _ _ _ _ Hpw) as Hcc.
  cbn [opiter_OpIterState_ctrls] in Hcc.
  destruct r2 as [t2|e2].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (push_ctrl_total st2 Opiter_LabelKind_Then bt) as [st3 Hpc].
  { rewrite Hcc. unfold room, stack_size in Hroom. unfold stack_size in Hs1.
    lia. }
  rewrite Hpc. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma take_local_total : forall st data ctx opcode,
  exists r st', opiter_take_local st data ctx opcode = Ok (r, st').
Proof.
  intros st data ctx opcode. unfold opiter_take_local.
  destruct (take_pending_total st opcode) as [r0 [st1 Htp]].
  rewrite Htp. cbn [bind].
  destruct r0 as [u|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u. rewrite branch_ok. cbn [bind].
  destruct (read_u32_leb_ok data st1.(opiter_OpIterState_pos)) as [r1 Hleb].
  rewrite Hleb. cbn [bind].
  destruct r1 as [[idx0 p1]|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (local_type_ok ctx idx0) as [r2 Hlt]. rewrite Hlt. cbn [bind].
  destruct r2 as [t|e2].
  - rewrite branch_ok. cbn [bind]. eexists. eexists. reflexivity.
  - rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
    eexists. eexists. reflexivity.
Qed.

(** Each reader's cursor movement is its prologue's: the stack work that follows
    leaves the cursor alone. *)
Lemma take_local_sound_of_get : forall st data ctx idx st',
  opiter_read_local_get st data ctx = Ok (Core_result_Result_Ok idx, st') ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) (to_Z idx)
           (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros st data ctx idx st' H. unfold opiter_read_local_get in H.
  destruct (opiter_take_local st data ctx opiter_op_local_get) as [[r0 st1]|]
    eqn:Htl; cbn [bind] in H; [|discriminate].
  destruct r0 as [[idx0 t]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val st1 (Opiter_StackType_Val t)) as [st2|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as Hidx <-.
  pose proof (push_val_pos st1 _ st2 Hpv) as Hp. unfold pos_of in Hp.
  rewrite Hp. rewrite <- Hidx.
  apply (take_local_sound st data ctx _ idx0 t st1 Htl).
Qed.

Lemma take_local_sound_of_set : forall st data ctx idx st',
  opiter_read_local_set st data ctx = Ok (Core_result_Result_Ok idx, st') ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) (to_Z idx)
           (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros st data ctx idx st' H. unfold opiter_read_local_set in H.
  destruct (opiter_take_local st data ctx opiter_op_local_set) as [[r0 st1]|]
    eqn:Htl; cbn [bind] in H; [|discriminate].
  destruct r0 as [[idx0 t]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_pop_with_type st1 t) as [[r1 st2]|] eqn:Hp1;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [t1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H. injection H as Hidx <-.
  pose proof (pop_with_type_pos st1 t _ st2 Hp1) as Hp. unfold pos_of in Hp.
  rewrite Hp. rewrite <- Hidx.
  apply (take_local_sound st data ctx _ idx0 t st1 Htl).
Qed.

Lemma take_local_sound_of_tee : forall st data ctx idx st',
  opiter_read_local_tee st data ctx = Ok (Core_result_Result_Ok idx, st') ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) (to_Z idx)
           (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros st data ctx idx st' H. unfold opiter_read_local_tee in H.
  destruct (opiter_take_local st data ctx opiter_op_local_tee) as [[r0 st1]|]
    eqn:Htl; cbn [bind] in H; [|discriminate].
  destruct r0 as [[idx0 t]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_pop_with_type st1 t) as [[r1 st2]|] eqn:Hp1;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [t1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val st2 (Opiter_StackType_Val t)) as [st3|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as Hidx <-.
  pose proof (pop_with_type_pos st1 t _ st2 Hp1) as Hp2. unfold pos_of in Hp2.
  pose proof (push_val_pos st2 _ st3 Hpv) as Hp3. unfold pos_of in Hp3.
  rewrite Hp3. rewrite Hp2. rewrite <- Hidx.
  apply (take_local_sound st data ctx _ idx0 t st1 Htl).
Qed.

(** The three readers, each the prologue followed by its stack effect. *)
Lemma read_local_get_total : forall st data ctx,
  room st -> exists r st', opiter_read_local_get st data ctx = Ok (r, st').
Proof.
  intros st data ctx Hroom. unfold opiter_read_local_get.
  destruct (take_local_total st data ctx opiter_op_local_get) as [r0 [st1 Htl]].
  rewrite Htl. cbn [bind].
  pose proof (take_local_size st data ctx _ r0 st1 Htl) as Hs1.
  destruct r0 as [[idx t]|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (push_val_total st1 (Opiter_StackType_Val t)) as [st2 Hpv].
  { apply room_vals. unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma read_local_set_total : forall st data ctx,
  exists r st', opiter_read_local_set st data ctx = Ok (r, st').
Proof.
  intros st data ctx. unfold opiter_read_local_set.
  destruct (take_local_total st data ctx opiter_op_local_set) as [r0 [st1 Htl]].
  rewrite Htl. cbn [bind].
  destruct r0 as [[idx t]|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (pop_with_type_total st1 t) as [r1 [st2 Hp1]].
  rewrite Hp1. cbn [bind].
  destruct r1 as [t1|e1].
  - rewrite branch_ok. cbn [bind]. eexists. eexists. reflexivity.
  - rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
    eexists. eexists. reflexivity.
Qed.

Lemma read_local_tee_total : forall st data ctx,
  room st -> exists r st', opiter_read_local_tee st data ctx = Ok (r, st').
Proof.
  intros st data ctx Hroom. unfold opiter_read_local_tee.
  destruct (take_local_total st data ctx opiter_op_local_tee) as [r0 [st1 Htl]].
  rewrite Htl. cbn [bind].
  pose proof (take_local_size st data ctx _ r0 st1 Htl) as Hs1.
  destruct r0 as [[idx t]|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (pop_with_type_total st1 t) as [r1 [st2 Hp1]].
  rewrite Hp1. cbn [bind].
  pose proof (pop_with_type_size st1 t r1 st2 Hp1) as Hs2.
  destruct r1 as [t1|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (push_val_total st2 (Opiter_StackType_Val t)) as [st3 Hpv].
  { apply room_vals. unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma take_global_total : forall st data module opcode,
  exists r st', opiter_take_global st data module opcode = Ok (r, st').
Proof.
  intros st data module opcode. unfold opiter_take_global.
  destruct (take_pending_total st opcode) as [r0 [st1 Htp]].
  rewrite Htp. cbn [bind].
  destruct r0 as [u|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u. rewrite branch_ok. cbn [bind].
  destruct (read_u32_leb_ok data st1.(opiter_OpIterState_pos)) as [r1 Hleb].
  rewrite Hleb. cbn [bind].
  destruct r1 as [[idx0 p1]|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (global_type_ok module idx0) as [r2 Hgt]. rewrite Hgt. cbn [bind].
  destruct r2 as [g|e2].
  - rewrite branch_ok. cbn [bind]. eexists. eexists. reflexivity.
  - rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
    eexists. eexists. reflexivity.
Qed.

Lemma take_global_sound_of_get : forall st data module idx st',
  opiter_read_global_get st data module = Ok (Core_result_Result_Ok idx, st') ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) (to_Z idx)
           (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros st data module idx st' H. unfold opiter_read_global_get in H.
  destruct (opiter_take_global st data module opiter_op_global_get) as [[r0 st1]|]
    eqn:Htg; cbn [bind] in H; [|discriminate].
  destruct r0 as [[idx0 g]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val st1
              (Opiter_StackType_Val g.(types_GlobalType_valtype))) as [st2|]
    eqn:Hpv; cbn [bind] in H; [|discriminate].
  injection H as Hidx <-.
  pose proof (push_val_pos st1 _ st2 Hpv) as Hp. unfold pos_of in Hp.
  rewrite Hp. rewrite <- Hidx.
  apply (take_global_sound st data module _ idx0 g st1 Htg).
Qed.

Lemma take_global_sound_of_set : forall st data module idx st',
  opiter_read_global_set st data module = Ok (Core_result_Result_Ok idx, st') ->
  repr_u32 (bytes_from data st.(opiter_OpIterState_pos)) (to_Z idx)
           (bytes_from data st'.(opiter_OpIterState_pos)).
Proof.
  intros st data module idx st' H. unfold opiter_read_global_set in H.
  destruct (opiter_take_global st data module opiter_op_global_set) as [[r0 st1]|]
    eqn:Htg; cbn [bind] in H; [|discriminate].
  destruct r0 as [[idx0 g]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (g.(types_GlobalType_mutability)); [discriminate|].
  destruct (opiter_pop_with_type st1 g.(types_GlobalType_valtype))
    as [[r1 st2]|] eqn:Hp1; cbn [bind] in H; [|discriminate].
  destruct r1 as [t1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H. injection H as Hidx <-.
  pose proof (pop_with_type_pos st1 _ _ st2 Hp1) as Hp. unfold pos_of in Hp.
  rewrite Hp. rewrite <- Hidx.
  apply (take_global_sound st data module _ idx0 g st1 Htg).
Qed.

Lemma read_global_get_total : forall st data module,
  room st -> exists r st', opiter_read_global_get st data module = Ok (r, st').
Proof.
  intros st data module Hroom. unfold opiter_read_global_get.
  destruct (take_global_total st data module opiter_op_global_get)
    as [r0 [st1 Htg]].
  rewrite Htg. cbn [bind].
  pose proof (take_global_size st data module _ r0 st1 Htg) as Hs1.
  destruct r0 as [[idx g]|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (push_val_total st1
              (Opiter_StackType_Val g.(types_GlobalType_valtype))) as [st2 Hpv].
  { apply room_vals. unfold room in Hroom |- *. lia. }
  rewrite Hpv. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma read_global_set_total : forall st data module,
  exists r st', opiter_read_global_set st data module = Ok (r, st').
Proof.
  intros st data module. unfold opiter_read_global_set.
  destruct (take_global_total st data module opiter_op_global_set)
    as [r0 [st1 Htg]].
  rewrite Htg. cbn [bind].
  destruct r0 as [[idx g]|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (g.(types_GlobalType_mutability));
    [eexists; eexists; reflexivity|].
  destruct (pop_with_type_total st1 g.(types_GlobalType_valtype))
    as [r1 [st2 Hp1]].
  rewrite Hp1. cbn [bind].
  destruct r1 as [t1|e1].
  - rewrite branch_ok. cbn [bind]. eexists. eexists. reflexivity.
  - rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
    eexists. eexists. reflexivity.
Qed.

(** The label lookup is where the guards earn their keep: the depth is checked
    against the control stack's height, so both subtractions stay non-negative
    and the frame lookup is in range. *)
Lemma read_label_total : forall st data,
  exists r st', opiter_read_label st data = Ok (r, st').
Proof.
  intros st data. unfold opiter_read_label.
  destruct (read_u32_leb_ok data st.(opiter_OpIterState_pos)) as [r1 Hleb].
  rewrite Hleb. cbn [bind].
  destruct r1 as [[d0 p1]|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (cast_u32_usize_ok d0) as [d [Hcast Hdval]].
  rewrite Hcast. cbn [bind].
  destruct (d s>= alloc_vec_Vec_len st.(opiter_OpIterState_ctrls)) eqn:Hge;
    [eexists; eexists; reflexivity|].
  (* past the bounds check both subtractions stay non-negative and the frame
     lookup is in range *)
  apply scalar_geb_false_lt in Hge. rewrite vec_len_spec in Hge.
  pose proof (usize_nonneg d) as Hdpos.
  destruct (usize_sub_1_ok (alloc_vec_Vec_len st.(opiter_OpIterState_ctrls)))
    as [i [Hsub1 Hival]]; [rewrite vec_len_spec; lia|].
  rewrite vec_len_spec in Hival.
  rewrite Hsub1. cbn [bind].
  destruct (usize_sub_ok i d) as [i1 [Hsub2 Hi1val]]; [lia|].
  rewrite Hsub2. cbn [bind]. rewrite vec_index_spec.
  assert (Hlt : (Z.to_nat (to_Z i1)
                 < List.length (vec_list st.(opiter_OpIterState_ctrls)))%nat).
  { rewrite Hi1val. lia. }
  destruct (List.nth_error (vec_list st.(opiter_OpIterState_ctrls))
              (Z.to_nat (to_Z i1))) as [target|] eqn:Hnth.
  2: { exfalso. apply List.nth_error_None in Hnth. lia. }
  cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma take_branch_target_total : forall st data opcode,
  exists r st', opiter_take_branch_target st data opcode = Ok (r, st').
Proof.
  intros st data opcode. unfold opiter_take_branch_target.
  destruct (take_pending_total st opcode) as [r0 [st1 Htp]].
  rewrite Htp. cbn [bind].
  destruct r0 as [u|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u. rewrite branch_ok. cbn [bind]. apply read_label_total.
Qed.

Lemma read_br_total : forall st data,
  exists r st', opiter_read_br st data = Ok (r, st').
Proof.
  intros st data. unfold opiter_read_br.
  destruct (take_branch_target_total st data opiter_op_br) as [r0 [st1 Htb]].
  rewrite Htb. cbn [bind].
  destruct r0 as [[d0 target]|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (branch_target_types_total target) as [types Hbtt].
  rewrite Hbtt. cbn [bind].
  destruct (pop_types_total st1 (alloc_vec_Vec_deref types)) as [r2 [st2 Hpt]].
  rewrite Hpt. cbn [bind].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u2. rewrite branch_ok. cbn [bind].
  destruct (mark_unreachable_total st2) as [st3 Hmu].
  rewrite Hmu. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma read_br_if_total : forall st data,
  room st -> exists r st', opiter_read_br_if st data = Ok (r, st').
Proof.
  intros st data Hroom. unfold opiter_read_br_if.
  destruct (take_branch_target_total st data opiter_op_br_if) as [r0 [st1 Htb]].
  rewrite Htb. cbn [bind].
  pose proof (take_branch_target_size st data _ r0 st1 Htb) as Hs1.
  destruct r0 as [[d0 target]|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (branch_target_types_total target) as [types Hbtt].
  rewrite Hbtt. cbn [bind].
  pose proof (branch_target_types_len _ types Hbtt) as Hlen.
  destruct (pop_with_type_total st1 Types_ValueType_I32) as [r1 [st2 Hp1]].
  rewrite Hp1. cbn [bind].
  pose proof (pop_with_type_size st1 _ r1 st2 Hp1) as Hs2.
  destruct r1 as [t1|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (pop_types_total st2 (alloc_vec_Vec_deref types)) as [r2 [st3 Hpt]].
  rewrite Hpt. cbn [bind].
  pose proof (pop_types_size st2 _ r2 st3 Hpt) as Hs3.
  destruct r2 as [u2|e2].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u2. rewrite branch_ok. cbn [bind].
  (* the condition pop paid for the push, so the room hypothesis suffices *)
  destruct (push_types_total st3 (alloc_vec_Vec_deref types)) as [st4 Hpush].
  { rewrite vec_deref_spec.
    assert (Hb : (List.length (vec_list st3.(opiter_OpIterState_vals))
                  + List.length (vec_list types) <= stack_size st + 1)%nat).
    { unfold stack_size in Hs1, Hs2, Hs3 |- *. lia. }
    apply (proj1 (Nat2Z.inj_le _ _)) in Hb.
    rewrite Nat2Z.inj_add in Hb. rewrite Nat2Z.inj_add in Hb.
    unfold room in Hroom. lia. }
  rewrite Hpush. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma merge_target_total : forall e bt,
  exists r, opiter_merge_target e bt = Ok r.
Proof.
  intros e bt. unfold opiter_merge_target. destruct e as [e0|].
  - rewrite bt_eq_spec. cbn [bind].
    destruct (opiter_BlockType_t_beq bt e0); eexists; reflexivity.
  - eexists. reflexivity.
Qed.

(** The table's loop is bounded by the count it read, not by the byte budget:
    each round increments [i] by one and stops at [count]. Every round is total
    because [read_label] is, so no measure over the input is needed here. *)
Lemma read_table_labels_loop_total : forall n st data count expect i,
  to_Z i + Z.of_nat n = to_Z count ->
  exists r st', opiter_read_table_labels_loop st data count expect i
                  = Ok (r, st').
Proof.
  induction n as [|n IH]; intros st data count expect i Hn;
    unfold opiter_read_table_labels_loop; rewrite loop_unfold; cbn beta iota;
    destruct (i s= count) eqn:Heq;
    [eexists; eexists; reflexivity | | eexists; eexists; reflexivity |].
  - (* the budget is spent, so [i] is [count] and the guard fired *)
    exfalso. apply scalar_eqb_false in Heq. cbn in Hn. lia.
  - destruct (read_label_total st data) as [r0 [st1 Hrl]].
    rewrite Hrl. cbn [bind].
    destruct r0 as [[d0 target]|e].
    2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
         eexists. eexists. reflexivity. }
    rewrite branch_ok. cbn [bind].
    rewrite branch_target_bt_spec. cbn [bind].
    destruct (merge_target_total expect (branch_target_bt_of target)) as [r1 Hm].
    rewrite Hm. cbn [bind].
    destruct r1 as [bt|e1].
    2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
         eexists. eexists. reflexivity. }
    rewrite branch_ok. cbn [bind].
    (* [i] is below [count], so the increment cannot overflow *)
    apply scalar_eqb_false in Heq.
    pose proof (u32_bounds i) as Hi. pose proof (u32_bounds count) as Hc.
    destruct (u32_add_ok i 1%u32) as [i1 [Hadd Hi1]].
    { assert (H1 : to_Z 1%u32 = 1) by reflexivity. rewrite H1. lia. }
    rewrite Hadd. cbn [bind].
    apply (IH st1 data count (Some bt) i1).
    assert (H1 : to_Z 1%u32 = 1) by reflexivity. rewrite Hi1. rewrite H1.
    cbn in Hn. lia.
Qed.

Lemma read_table_labels_total : forall st data count,
  exists r st', opiter_read_table_labels st data count = Ok (r, st').
Proof.
  intros st data count. unfold opiter_read_table_labels.
  apply (read_table_labels_loop_total (Z.to_nat (to_Z count)) st data count
           None 0%u32).
  assert (H0 : to_Z 0%u32 = 0) by reflexivity. rewrite H0.
  rewrite Z2Nat.id by apply u32_nonneg. reflexivity.
Qed.

(** [br_table] pops and truncates, so the stack cannot grow and the room
    hypothesis is not needed. *)
Lemma read_br_table_total : forall st data,
  exists r st', opiter_read_br_table st data = Ok (r, st').
Proof.
  intros st data. unfold opiter_read_br_table.
  destruct (take_pending_total st opiter_op_br_table) as [r0 [st1 Htp]].
  rewrite Htp. cbn [bind].
  destruct r0 as [u|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u. rewrite branch_ok. cbn [bind].
  destruct (read_u32_leb_ok data st1.(opiter_OpIterState_pos)) as [r1 Hleb].
  rewrite Hleb. cbn [bind].
  destruct r1 as [[count p1]|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (read_table_labels_total
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending := st1.(opiter_OpIterState_pending)
              |} data count) as [r2 [st2 Htl]].
  rewrite Htl. cbn [bind].
  destruct r2 as [expect|e2].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (read_label_total st2 data) as [r3 [st3 Hrl]].
  rewrite Hrl. cbn [bind].
  destruct r3 as [[d0 target]|e3].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind]. rewrite branch_target_bt_spec. cbn [bind].
  destruct (merge_target_total expect (branch_target_bt_of target)) as [r4 Hm].
  rewrite Hm. cbn [bind].
  destruct r4 as [common|e4].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (pop_with_type_total st3 Types_ValueType_I32) as [r5 [st4 Hp1]].
  rewrite Hp1. cbn [bind].
  destruct r5 as [t5|e5].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (block_results_total common) as [types Hbr].
  rewrite Hbr. cbn [bind].
  destruct (pop_types_total st4 (alloc_vec_Vec_deref types)) as [r6 [st5 Hpt]].
  rewrite Hpt. cbn [bind].
  destruct r6 as [u6|e6].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u6. rewrite branch_ok. cbn [bind].
  destruct (mark_unreachable_total st5) as [st6 Hmu].
  rewrite Hmu. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma take_index_total : forall st data opcode,
  exists r st', opiter_take_index st data opcode = Ok (r, st').
Proof.
  intros st data opcode. unfold opiter_take_index.
  destruct (take_pending_total st opcode) as [r0 [st1 Htp]].
  rewrite Htp. cbn [bind].
  destruct r0 as [u|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u. rewrite branch_ok. cbn [bind].
  destruct (read_u32_leb_ok data st1.(opiter_OpIterState_pos)) as [r1 Hleb].
  rewrite Hleb. cbn [bind].
  destruct r1 as [[idx0 p1]|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind]. eexists. eexists. reflexivity.
Qed.

(** The arity guard is what makes the room hypothesis enough: the pops can only
    shrink the stack and at most one result goes back on. *)
Lemma read_call_total : forall st data module,
  room st -> exists r st', opiter_read_call st data module = Ok (r, st').
Proof.
  intros st data module Hroom. unfold opiter_read_call.
  destruct (take_index_total st data opiter_op_call) as [r0 [st1 Hti]].
  rewrite Hti. cbn [bind].
  pose proof (take_index_size st data _ r0 st1 Hti) as Hs1.
  destruct r0 as [idx|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (scalar_cast_u32_usize idx) as [i [Hcast _]].
  rewrite Hcast. cbn [bind].
  destruct (i s>= alloc_vec_Vec_len module.(env_Env_func_types)) eqn:Hge;
    [eexists; eexists; reflexivity|].
  destruct (vec_index_ok module.(env_Env_func_types) i Hge) as [ft Hidx].
  rewrite Hidx. cbn [bind].
  destruct (require_single_result_ok
              (alloc_vec_Vec_deref ft.(types_FuncType_results))) as [r1 Hrs].
  rewrite Hrs. cbn [bind].
  destruct r1 as [u1|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u1. rewrite branch_ok. cbn [bind].
  pose proof (require_single_result_le _ Hrs) as Hlen.
  rewrite vec_deref_spec in Hlen.
  destruct (pop_types_total st1
              (alloc_vec_Vec_deref ft.(types_FuncType_params))) as [r2 [st2 Hpt]].
  rewrite Hpt. cbn [bind].
  pose proof (pop_types_size st1 _ r2 st2 Hpt) as Hs2.
  destruct r2 as [u2|e2].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u2. rewrite branch_ok. cbn [bind].
  destruct (push_types_total st2
              (alloc_vec_Vec_deref ft.(types_FuncType_results))) as [st3 Hpu].
  { rewrite vec_deref_spec.
    assert (Hb : (List.length (vec_list st2.(opiter_OpIterState_vals))
                  + List.length (vec_list ft.(types_FuncType_results))
                  <= stack_size st + 1)%nat).
    { unfold stack_size in Hs1, Hs2 |- *. lia. }
    apply (proj1 (Nat2Z.inj_le _ _)) in Hb.
    rewrite Nat2Z.inj_add in Hb. rewrite Nat2Z.inj_add in Hb.
    unfold room in Hroom. lia. }
  rewrite Hpu. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma read_call_indirect_total : forall st data module,
  room st -> exists r st', opiter_read_call_indirect st data module = Ok (r, st').
Proof.
  intros st data module Hroom. unfold opiter_read_call_indirect.
  destruct (take_index_total st data opiter_op_call_indirect) as [r0 [st1 Hti]].
  rewrite Hti. cbn [bind].
  pose proof (take_index_size st data _ r0 st1 Hti) as Hs1.
  destruct r0 as [idx|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (read_reserved_zero_total st1 data) as [r1 [st2 Hrz]].
  rewrite Hrz. cbn [bind].
  pose proof (read_reserved_zero_size st1 data r1 st2 Hrz) as Hs2.
  destruct r1 as [u1|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u1. rewrite branch_ok. cbn [bind].
  rewrite vec_is_empty_spec. cbn [bind].
  destruct (vec_list module.(env_Env_table_types));
    [eexists; eexists; reflexivity|].
  destruct (scalar_cast_u32_usize idx) as [i [Hcast _]].
  rewrite Hcast. cbn [bind].
  destruct (i s>= alloc_vec_Vec_len module.(env_Env_types)) eqn:Hge;
    [eexists; eexists; reflexivity|].
  destruct (vec_index_ok module.(env_Env_types) i Hge) as [ft Hidx].
  rewrite Hidx. cbn [bind].
  destruct (require_single_result_ok
              (alloc_vec_Vec_deref ft.(types_FuncType_results))) as [r2 Hrs].
  rewrite Hrs. cbn [bind].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u2. rewrite branch_ok. cbn [bind].
  pose proof (require_single_result_le _ Hrs) as Hlen.
  rewrite vec_deref_spec in Hlen.
  destruct (pop_with_type_total st2 Types_ValueType_I32) as [r3 [st3 Hpw]].
  rewrite Hpw. cbn [bind].
  pose proof (pop_with_type_size st2 _ r3 st3 Hpw) as Hs3.
  destruct r3 as [t3|e3].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (pop_types_total st3
              (alloc_vec_Vec_deref ft.(types_FuncType_params))) as [r4 [st4 Hpt]].
  rewrite Hpt. cbn [bind].
  pose proof (pop_types_size st3 _ r4 st4 Hpt) as Hs4.
  destruct r4 as [u4|e4].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u4. rewrite branch_ok. cbn [bind].
  destruct (push_types_total st4
              (alloc_vec_Vec_deref ft.(types_FuncType_results))) as [st5 Hpu].
  { rewrite vec_deref_spec.
    assert (Hb : (List.length (vec_list st4.(opiter_OpIterState_vals))
                  + List.length (vec_list ft.(types_FuncType_results))
                  <= stack_size st + 1)%nat).
    { unfold stack_size in Hs1, Hs2, Hs3, Hs4 |- *. lia. }
    apply (proj1 (Nat2Z.inj_le _ _)) in Hb.
    rewrite Nat2Z.inj_add in Hb. rewrite Nat2Z.inj_add in Hb.
    unfold room in Hroom. lia. }
  rewrite Hpu. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma read_load_total : forall st data module opcode ty natural,
  room st ->
  exists r st', opiter_read_load st data module opcode ty natural = Ok (r, st').
Proof.
  intros st data module opcode ty natural Hroom. unfold opiter_read_load.
  destruct (take_pending_total st opcode) as [r0 [st1 Htp]].
  rewrite Htp. cbn [bind].
  pose proof (take_pending_size st opcode r0 st1 Htp) as Hs1.
  destruct r0 as [u|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u. rewrite branch_ok. cbn [bind].
  destruct (read_memarg_total st1 data) as [r1 [st2 Hma]].
  rewrite Hma. cbn [bind].
  pose proof (read_memarg_size st1 data r1 st2 Hma) as Hs2.
  destruct r1 as [m0|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (check_memory_and_alignment_total module m0 natural) as [r2 Hck].
  rewrite Hck. cbn [bind].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u2. rewrite branch_ok. cbn [bind].
  destruct (pop_with_type_total st2 Types_ValueType_I32) as [r3 [st3 Hpop]].
  rewrite Hpop. cbn [bind].
  pose proof (pop_with_type_size st2 _ r3 st3 Hpop) as Hs3.
  destruct r3 as [t3|e3].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (push_val_total st3 (Opiter_StackType_Val ty)) as [st4 Hpv].
  { apply room_vals. unfold room in Hroom |- *. unfold stack_size in *. lia. }
  rewrite Hpv. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma read_store_total : forall st data module opcode ty natural,
  exists r st', opiter_read_store st data module opcode ty natural = Ok (r, st').
Proof.
  intros st data module opcode ty natural. unfold opiter_read_store.
  destruct (take_pending_total st opcode) as [r0 [st1 Htp]].
  rewrite Htp. cbn [bind].
  destruct r0 as [u|e].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u. rewrite branch_ok. cbn [bind].
  destruct (read_memarg_total st1 data) as [r1 [st2 Hma]].
  rewrite Hma. cbn [bind].
  destruct r1 as [m0|e1].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (check_memory_and_alignment_total module m0 natural) as [r2 Hck].
  rewrite Hck. cbn [bind].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  destruct u2. rewrite branch_ok. cbn [bind].
  destruct (pop_with_type_total st2 ty) as [r3 [st3 Hpop1]].
  rewrite Hpop1. cbn [bind].
  destruct r3 as [t3|e3].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind].
  destruct (pop_with_type_total st3 Types_ValueType_I32) as [r4 [st4 Hpop2]].
  rewrite Hpop2. cbn [bind].
  destruct r4 as [t4|e4].
  2: { rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
       eexists. eexists. reflexivity. }
  rewrite branch_ok. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma read_op_total : forall st data,
  exists r st', opiter_read_op st data = Ok (r, st').
Proof.
  intros st data. unfold opiter_read_op.
  destruct (read_byte_total data st.(opiter_OpIterState_pos)) as [r0 Hrb].
  rewrite Hrb. cbn [bind].
  destruct r0 as [[b p]|e].
  - rewrite branch_ok. cbn [bind]. eexists. eexists. reflexivity.
  - rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
    eexists. eexists. reflexivity.
Qed.

(* ================================================================== *)
(** ** The cursor never moves backwards                                *)
(* ================================================================== *)

(** What the validation loop's termination measure needs. [read_op] advances the
    cursor by exactly one byte, so as long as no reader moves it back, the bytes
    remaining strictly decrease each iteration.

    Nothing here needs the cursor to stay inside the body: if it ran past the end
    the next [read_op] would report [UnexpectedEof] and the loop would stop, so
    only monotonicity is load-bearing. *)
(** The LEB loops read a byte before they can return, so unlike the float
    reader they need no proviso: an accepting run always moves the cursor on by
    at least that byte, and leaves it inside the input. *)
Lemma read_u32_leb_loop_range : forall n data acc mult p i v p',
  to_Z i + Z.of_nat n = 4 ->
  reader_read_u32_leb_loop data acc mult p i
    = Ok (Core_result_Result_Ok (v, p')) ->
  to_Z p < to_Z p' /\ to_Z p' <= to_Z (slice_len data).
Proof.
  induction n as [|n IH]; intros data acc mult p i v p' Hn H;
    unfold reader_read_u32_leb_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H;
    destruct (p s>= slice_len data) eqn:Hge; [discriminate| |discriminate| ].
  (* the byte and the cursor step, shared; [all:] rather than a [;] chain so the
     selectors below see one goal's worth of subgoals at a time *)
  all: apply scalar_geb_false_lt in Hge.
  all: destruct (slice_index_usize data p) as [b|] eqn:Hidx; cbn [bind] in H;
         [|discriminate].
  all: destruct (usize_add p 1%usize) as [p2|] eqn:Hadd; cbn [bind] in H;
         [|discriminate].
  all: destruct (bytes_from_step data p b p2 Hidx Hadd) as [_ Hp2].
  all: destruct (u8_rem b 128%u8) as [low|] eqn:Hrem; cbn [bind] in H;
         [|discriminate].
  - (* i = 4: whatever happens, the cursor only moved forward one byte *)
    assert (Heq4 : (i s= 4%u32) = true).
    { unfold scalar_eqb. apply Z.eqb_eq.
      assert (H4 : to_Z 4%u32 = 4) by reflexivity. rewrite H4.
      cbn in Hn. lia. }
    rewrite Heq4 in H. cbn beta iota in H.
    destruct (low s> 15%u8); [discriminate|].
    destruct (scalar_cast U8 U32 low) as [c|] eqn:Hcast; cbn [bind] in H;
      [|discriminate].
    destruct (u32_mul c mult) as [prod|] eqn:Hmul; cbn [bind] in H;
      [|discriminate].
    destruct (u32_add acc prod) as [sum|] eqn:Hadd2; cbn [bind] in H;
      [|discriminate].
    destruct (b s< 128%u8); [injection H as _ <-; split; lia|].
    cbn beta iota in H. discriminate.
  - (* i < 4 *)
    assert (Heq4 : (i s= 4%u32) = false).
    { unfold scalar_eqb. apply Z.eqb_neq.
      assert (H4 : to_Z 4%u32 = 4) by reflexivity. cbn in Hn. lia. }
    rewrite Heq4 in H. cbn beta iota in H.
    destruct (scalar_cast U8 U32 low) as [c|] eqn:Hcast; cbn [bind] in H;
      [|discriminate].
    destruct (u32_mul c mult) as [prod|] eqn:Hmul; cbn [bind] in H;
      [|discriminate].
    destruct (u32_add acc prod) as [sum|] eqn:Hadd2; cbn [bind] in H;
      [|discriminate].
    destruct (b s< 128%u8); [injection H as _ <-; split; lia|].
    cbn beta iota in H.
    destruct (u32_mul mult 128%u32) as [mult2|] eqn:Hmul2; cbn [bind] in H;
      [|discriminate].
    destruct (u32_add i 1%u32) as [i5|] eqn:Hadd3; cbn [bind] in H;
      [|discriminate].
    assert (Hi5 : to_Z i5 = to_Z i + 1).
    { unfold u32_add, scalar_add in Hadd3. apply mk_scalar_ok_to_Z in Hadd3.
      assert (H1 : to_Z 1%u32 = 1) by reflexivity. rewrite Hadd3. lia. }
    destruct (IH data sum mult2 p2 i5 v p' (ltac:(cbn in Hn; lia)) H). lia.
Qed.

Lemma read_u32_leb_lt : forall data pos v pos',
  reader_read_u32_leb data pos = Ok (Core_result_Result_Ok (v, pos')) ->
  to_Z pos < to_Z pos'.
Proof.
  intros data pos v pos' H. unfold reader_read_u32_leb in H.
  exact (proj1 (read_u32_leb_loop_range 4 data 0%u32 1%u32 pos 0%u32 v pos'
                  (ltac:(reflexivity)) H)).
Qed.

Lemma read_u32_leb_mono : forall data pos v pos',
  reader_read_u32_leb data pos = Ok (Core_result_Result_Ok (v, pos')) ->
  to_Z pos <= to_Z pos'.
Proof. intros data pos v pos' H. pose proof (read_u32_leb_lt _ _ _ _ H). lia. Qed.

Lemma read_u32_leb_le_len : forall data pos v pos',
  reader_read_u32_leb data pos = Ok (Core_result_Result_Ok (v, pos')) ->
  to_Z pos' <= to_Z (slice_len data).
Proof.
  intros data pos v pos' H. unfold reader_read_u32_leb in H.
  exact (proj2 (read_u32_leb_loop_range 4 data 0%u32 1%u32 pos 0%u32 v pos'
                  (ltac:(reflexivity)) H)).
Qed.

Lemma read_sn_leb_loop_range : forall n data last lo hi acc mult p i v p',
  to_Z i + Z.of_nat n = to_Z last ->
  reader_read_sn_leb_loop data last lo hi acc mult p i
    = Ok (Core_result_Result_Ok (v, p')) ->
  to_Z p < to_Z p' /\ to_Z p' <= to_Z (slice_len data).
Proof.
  induction n as [|n IH]; intros data last lo hi acc mult p i v p' Hn H;
    unfold reader_read_sn_leb_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H;
    destruct (p s>= slice_len data) eqn:Hge; [discriminate| |discriminate| ].
  all: apply scalar_geb_false_lt in Hge.
  all: destruct (slice_index_usize data p) as [b|] eqn:Hidx; cbn [bind] in H;
         [|discriminate].
  all: destruct (usize_add p 1%usize) as [p2|] eqn:Hadd; cbn [bind] in H;
         [|discriminate].
  all: destruct (bytes_from_step data p b p2 Hidx Hadd) as [_ Hp2].
  all: destruct (u8_rem b 128%u8) as [low|] eqn:Hrem; cbn [bind] in H;
         [|discriminate].
  all: destruct (scalar_cast U8 I128 low) as [c|] eqn:Hcast; cbn [bind] in H;
         [|discriminate].
  all: destruct (i128_mul c mult) as [prod|] eqn:Hmul; cbn [bind] in H;
         [|discriminate].
  all: destruct (i128_add acc prod) as [sum|] eqn:Hadd2; cbn [bind] in H;
         [|discriminate].
  all: destruct (b s< 128%u8) eqn:Hlt.
  - (* last byte, budget spent *)
    destruct (if low s>= 64%u8
              then (i5 <- i128_mul mult 128%i128; i128_sub sum i5)
              else Ok sum) as [acc3|] eqn:Hsx; cbn [bind] in H; [|discriminate].
    destruct (acc3 s< lo); [discriminate|].
    destruct (acc3 s> hi); [discriminate|].
    injection H as _ <-. split; lia.
  - (* continuation with the budget spent: rejected *)
    assert (Heq : (i s= last) = true).
    { unfold scalar_eqb. apply Z.eqb_eq. cbn in Hn. lia. }
    rewrite Heq in H. cbn beta iota in H. discriminate.
  - (* last byte, budget left *)
    destruct (if low s>= 64%u8
              then (i5 <- i128_mul mult 128%i128; i128_sub sum i5)
              else Ok sum) as [acc3|] eqn:Hsx; cbn [bind] in H; [|discriminate].
    destruct (acc3 s< lo); [discriminate|].
    destruct (acc3 s> hi); [discriminate|].
    injection H as _ <-. split; lia.
  - (* continuation: go round again *)
    assert (Heq : (i s= last) = false).
    { unfold scalar_eqb. apply Z.eqb_neq. cbn in Hn. lia. }
    rewrite Heq in H. cbn beta iota in H.
    destruct (i128_mul mult 128%i128) as [mult2|] eqn:Hmul2; cbn [bind] in H;
      [|discriminate].
    destruct (u32_add i 1%u32) as [i5|] eqn:Hadd3; cbn [bind] in H;
      [|discriminate].
    assert (Hi5 : to_Z i5 = to_Z i + 1).
    { unfold u32_add, scalar_add in Hadd3. apply mk_scalar_ok_to_Z in Hadd3.
      assert (H1 : to_Z 1%u32 = 1) by reflexivity. rewrite Hadd3. lia. }
    destruct (IH data last lo hi sum mult2 p2 i5 v p'
                (ltac:(cbn in Hn; lia)) H). lia.
Qed.

Lemma read_s32_leb_mono : forall data pos v pos',
  reader_read_s32_leb data pos = Ok (Core_result_Result_Ok (v, pos')) ->
  to_Z pos <= to_Z pos'.
Proof.
  intros data pos v pos' H. unfold reader_read_s32_leb, reader_read_sn_leb in H.
  destruct (reader_read_sn_leb_loop data 4%u32 (-2147483648)%i128
              2147483647%i128 0%i128 1%i128 pos 0%u32) as [r|] eqn:Hleb;
    cbn [bind] in H; [|discriminate].
  destruct r as [[v0 p0]|e].
  2: { rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
       cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (scalar_cast I128 I32 v0) as [v1|] eqn:Hc; cbn [bind] in H;
    [|discriminate].
  injection H as <- <-.
  pose proof (proj1 (read_sn_leb_loop_range 4 data 4%u32 (-2147483648)%i128
                  2147483647%i128 0%i128 1%i128 pos 0%u32 v0 p0
                       (ltac:(reflexivity)) Hleb)). lia.
Qed.

Lemma read_s64_leb_mono : forall data pos v pos',
  reader_read_s64_leb data pos = Ok (Core_result_Result_Ok (v, pos')) ->
  to_Z pos <= to_Z pos'.
Proof.
  intros data pos v pos' H. unfold reader_read_s64_leb, reader_read_sn_leb in H.
  destruct (reader_read_sn_leb_loop data 9%u32 (-9223372036854775808)%i128
              9223372036854775807%i128 0%i128 1%i128 pos 0%u32) as [r|] eqn:Hleb;
    cbn [bind] in H; [|discriminate].
  destruct r as [[v0 p0]|e].
  2: { rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
       cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (scalar_cast I128 I64 v0) as [v1|] eqn:Hc; cbn [bind] in H;
    [|discriminate].
  injection H as <- <-.
  pose proof (proj1 (read_sn_leb_loop_range 9 data 9%u32 (-9223372036854775808)%i128
                  9223372036854775807%i128 0%i128 1%i128 pos 0%u32 v0 p0
                       (ltac:(reflexivity)) Hleb)). lia.
Qed.

Lemma read_s32_leb_le_len : forall data pos v pos',
  reader_read_s32_leb data pos = Ok (Core_result_Result_Ok (v, pos')) ->
  to_Z pos' <= to_Z (slice_len data).
Proof.
  intros data pos v pos' H. unfold reader_read_s32_leb, reader_read_sn_leb in H.
  destruct (reader_read_sn_leb_loop data 4%u32 (-2147483648)%i128
              2147483647%i128 0%i128 1%i128 pos 0%u32) as [r|] eqn:Hleb;
    cbn [bind] in H; [|discriminate].
  destruct r as [[v0 p0]|e].
  2: { rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
       cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (scalar_cast I128 I32 v0) as [v1|] eqn:Hc; cbn [bind] in H;
    [|discriminate].
  injection H as <- <-.
  exact (proj2 (read_sn_leb_loop_range 4 data 4%u32 (-2147483648)%i128
                  2147483647%i128 0%i128 1%i128 pos 0%u32 v0 p0
                  (ltac:(reflexivity)) Hleb)).
Qed.

Lemma read_s64_leb_le_len : forall data pos v pos',
  reader_read_s64_leb data pos = Ok (Core_result_Result_Ok (v, pos')) ->
  to_Z pos' <= to_Z (slice_len data).
Proof.
  intros data pos v pos' H. unfold reader_read_s64_leb, reader_read_sn_leb in H.
  destruct (reader_read_sn_leb_loop data 9%u32 (-9223372036854775808)%i128
              9223372036854775807%i128 0%i128 1%i128 pos 0%u32) as [r|] eqn:Hleb;
    cbn [bind] in H; [|discriminate].
  destruct r as [[v0 p0]|e].
  2: { rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
       cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (scalar_cast I128 I64 v0) as [v1|] eqn:Hc; cbn [bind] in H;
    [|discriminate].
  injection H as <- <-.
  exact (proj2 (read_sn_leb_loop_range 9 data 9%u32 (-9223372036854775808)%i128
                  9223372036854775807%i128 0%i128 1%i128 pos 0%u32 v0 p0
                  (ltac:(reflexivity)) Hleb)).
Qed.

Lemma read_block_type_mono : forall data pos bt pos',
  opiter_read_block_type data pos = Ok (Core_result_Result_Ok (bt, pos')) ->
  to_Z pos <= to_Z pos'.
Proof.
  intros data pos bt pos' H.
  destruct (read_block_type_sound data pos bt pos' H) as [bb [Hbytes _]].
  (* the sound lemma is about bytes; the cursor step comes from [read_byte] *)
  unfold opiter_read_block_type in H.
  destruct (reader_read_byte data pos) as [r0|] eqn:Hrb; cbn [bind] in H;
    [|discriminate].
  destruct r0 as [[b p]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (read_byte_ok data pos b p Hrb) as [_ Hp].
  destruct (b s= 64%u8); [injection H as _ <-; lia|].
  destruct (b s= 127%u8); [injection H as _ <-; lia|].
  destruct (b s= 126%u8); [injection H as _ <-; lia|].
  destruct (b s= 125%u8); [injection H as _ <-; lia|].
  destruct (b s= 124%u8); [injection H as _ <-; lia|discriminate].
Qed.

Lemma read_memarg_mono : forall st data r st',
  opiter_read_memarg st data = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data r st' H. unfold opiter_read_memarg in H.
  destruct (reader_read_u32_leb data st.(opiter_OpIterState_pos)) as [r1|]
    eqn:H1; cbn [bind] in H; [|discriminate].
  destruct r1 as [[a p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_u32_leb_mono data _ a p1 H1) as Hm1.
  destruct (reader_read_u32_leb data p1) as [r2|] eqn:H2; cbn [bind] in H;
    [|discriminate].
  destruct r2 as [[o p2]|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_u32_leb_mono data p1 o p2 H2) as Hm2.
  injection H as _ <-. cbn [opiter_OpIterState_pos]. lia.
Qed.

(** Each reader, for an arbitrary result: the error branches return the state the
    prologue produced, so monotonicity does not depend on success. *)

Lemma read_i32_const_mono : forall st data r st',
  opiter_read_i32_const st data = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data r st' H. unfold opiter_read_i32_const in H.
  destruct (opiter_take_pending st opiter_op_i32_const) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opiter_op_i32_const r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1. apply (f_equal to_Z) in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_s32_leb data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[v p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_s32_leb_mono data _ v p1 Hleb) as Hm.
  destruct (opiter_push_val _ (Opiter_StackType_Val Types_ValueType_I32))
    as [st2|] eqn:Hpv; cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  pose proof (push_val_pos _ _ st2 Hpv) as Hp2. unfold pos_of in Hp2. apply (f_equal to_Z) in Hp2.
  cbn [opiter_OpIterState_pos] in Hp2. lia.
Qed.

Lemma read_f32_const_mono : forall st data r st',
  opiter_read_f32_const st data = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data r st' H. unfold opiter_read_f32_const in H.
  destruct (opiter_take_pending st opiter_op_f32_const) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opiter_op_f32_const r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1. apply (f_equal to_Z) in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_f32_bits data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[v p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_f32_bits_mono data _ v p1 Hleb) as Hm.
  destruct (opiter_push_val _ (Opiter_StackType_Val Types_ValueType_F32))
    as [st2|] eqn:Hpv; cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  pose proof (push_val_pos _ _ st2 Hpv) as Hp2. unfold pos_of in Hp2. apply (f_equal to_Z) in Hp2.
  cbn [opiter_OpIterState_pos] in Hp2. lia.
Qed.

Lemma read_f64_const_mono : forall st data r st',
  opiter_read_f64_const st data = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data r st' H. unfold opiter_read_f64_const in H.
  destruct (opiter_take_pending st opiter_op_f64_const) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opiter_op_f64_const r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1. apply (f_equal to_Z) in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_f64_bits data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[v p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_f64_bits_mono data _ v p1 Hleb) as Hm.
  destruct (opiter_push_val _ (Opiter_StackType_Val Types_ValueType_F64))
    as [st2|] eqn:Hpv; cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  pose proof (push_val_pos _ _ st2 Hpv) as Hp2. unfold pos_of in Hp2. apply (f_equal to_Z) in Hp2.
  cbn [opiter_OpIterState_pos] in Hp2. lia.
Qed.

Lemma read_i64_const_mono : forall st data r st',
  opiter_read_i64_const st data = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data r st' H. unfold opiter_read_i64_const in H.
  destruct (opiter_take_pending st opiter_op_i64_const) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opiter_op_i64_const r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1. apply (f_equal to_Z) in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_s64_leb data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[v p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_s64_leb_mono data _ v p1 Hleb) as Hm.
  destruct (opiter_push_val _ (Opiter_StackType_Val Types_ValueType_I64))
    as [st2|] eqn:Hpv; cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  pose proof (push_val_pos _ _ st2 Hpv) as Hp2. unfold pos_of in Hp2. apply (f_equal to_Z) in Hp2.
  cbn [opiter_OpIterState_pos] in Hp2. lia.
Qed.

Lemma read_block_mono : forall st data r st',
  opiter_read_block st data = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data r st' H. unfold opiter_read_block in H.
  destruct (opiter_take_pending st opiter_op_block) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opiter_op_block r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1. apply (f_equal to_Z) in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_read_block_type data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hbt; cbn [bind] in H; [|discriminate].
  destruct r1 as [[bt p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_block_type_mono data _ bt p1 Hbt) as Hm.
  destruct (opiter_push_ctrl _ Opiter_LabelKind_Block bt) as [st2|] eqn:Hpc;
    cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  pose proof (push_ctrl_pos _ _ _ st2 Hpc) as Hp2. unfold pos_of in Hp2. apply (f_equal to_Z) in Hp2.
  cbn [opiter_OpIterState_pos] in Hp2. lia.
Qed.

Lemma read_loop_mono : forall st data r st',
  opiter_read_loop st data = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data r st' H. unfold opiter_read_loop in H.
  destruct (opiter_take_pending st opiter_op_loop) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opiter_op_loop r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1. apply (f_equal to_Z) in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_read_block_type data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hbt; cbn [bind] in H; [|discriminate].
  destruct r1 as [[bt p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_block_type_mono data _ bt p1 Hbt) as Hm.
  destruct (opiter_push_ctrl _ Opiter_LabelKind_Loop bt) as [st2|] eqn:Hpc;
    cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  pose proof (push_ctrl_pos _ _ _ st2 Hpc) as Hp2. unfold pos_of in Hp2. apply (f_equal to_Z) in Hp2.
  cbn [opiter_OpIterState_pos] in Hp2. lia.
Qed.

Lemma read_if_mono : forall st data r st',
  opiter_read_if st data = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data r st' H. unfold opiter_read_if in H.
  destruct (opiter_take_pending st opiter_op_if) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opiter_op_if r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1. apply (f_equal to_Z) in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_read_block_type data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hbt; cbn [bind] in H; [|discriminate].
  destruct r1 as [[bt p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_block_type_mono data _ bt p1 Hbt) as Hm.
  destruct (opiter_pop_with_type _ Types_ValueType_I32) as [[r2 st2]|] eqn:Hpw;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos _ _ r2 st2 Hpw) as Hp2. unfold pos_of in Hp2.
  apply (f_equal to_Z) in Hp2. cbn [opiter_OpIterState_pos] in Hp2.
  destruct r2 as [t2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_ctrl st2 Opiter_LabelKind_Then bt) as [st3|] eqn:Hpc;
    cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  pose proof (push_ctrl_pos _ _ _ st3 Hpc) as Hp3. unfold pos_of in Hp3.
  apply (f_equal to_Z) in Hp3. lia.
Qed.

Lemma read_label_mono : forall st data r st',
  opiter_read_label st data = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data r st' H. unfold opiter_read_label in H.
  destruct (reader_read_u32_leb data st.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[d0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_u32_leb_mono data _ d0 p1 Hleb) as Hm.
  destruct (scalar_cast U32 Usize d0) as [d|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  destruct (d s>= alloc_vec_Vec_len st.(opiter_OpIterState_ctrls)) eqn:Hge.
  { injection H as _ <-. cbn [opiter_OpIterState_pos]. lia. }
  destruct (usize_sub (alloc_vec_Vec_len st.(opiter_OpIterState_ctrls)) 1%usize)
    as [i|] eqn:Hsub1; cbn [bind] in H; [|discriminate].
  destruct (usize_sub i d) as [i1|] eqn:Hsub2; cbn [bind] in H; [|discriminate].
  destruct (alloc_vec_Vec_index
              (core_slice_index_SliceIndexUsizeSliceInst opiter_Ctrl_t)
              st.(opiter_OpIterState_ctrls) i1) as [target|] eqn:Hidx;
    cbn [bind] in H; [|discriminate].
  injection H as _ <-. cbn [opiter_OpIterState_pos]. lia.
Qed.

Lemma take_branch_target_mono : forall st data opcode r st',
  opiter_take_branch_target st data opcode = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data opcode r st' H. unfold opiter_take_branch_target in H.
  destruct (opiter_take_pending st opcode) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opcode r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1. apply (f_equal to_Z) in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_label_mono st1 data r st' H). lia.
Qed.

Lemma read_br_mono : forall st data r st',
  opiter_read_br st data = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data r st' H. unfold opiter_read_br in H.
  destruct (opiter_take_branch_target st data opiter_op_br) as [[r0 st1]|]
    eqn:Htb; cbn [bind] in H; [|discriminate].
  pose proof (take_branch_target_mono st data _ r0 st1 Htb) as Hm.
  destruct r0 as [[d0 target]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_branch_target_types target) as [types|] eqn:Hbtt;
    cbn [bind] in H; [|discriminate].
  destruct (opiter_pop_types st1 (alloc_vec_Vec_deref types)) as [[r2 st2]|]
    eqn:Hpt; cbn [bind] in H; [|discriminate].
  pose proof (pop_types_pos _ _ r2 st2 Hpt) as Hp2. unfold pos_of in Hp2.
  apply (f_equal to_Z) in Hp2.
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_mark_unreachable st2) as [st3|] eqn:Hmu; cbn [bind] in H;
    [|discriminate].
  injection H as _ <-.
  pose proof (mark_unreachable_pos st2 st3 Hmu) as Hp3. unfold pos_of in Hp3.
  apply (f_equal to_Z) in Hp3. lia.
Qed.

Lemma read_br_if_mono : forall st data r st',
  opiter_read_br_if st data = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data r st' H. unfold opiter_read_br_if in H.
  destruct (opiter_take_branch_target st data opiter_op_br_if) as [[r0 st1]|]
    eqn:Htb; cbn [bind] in H; [|discriminate].
  pose proof (take_branch_target_mono st data _ r0 st1 Htb) as Hm.
  destruct r0 as [[d0 target]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_branch_target_types target) as [types|] eqn:Hbtt;
    cbn [bind] in H; [|discriminate].
  destruct (opiter_pop_with_type st1 Types_ValueType_I32) as [[r1 st2]|] eqn:Hp1;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos st1 _ r1 st2 Hp1) as Hp2. unfold pos_of in Hp2.
  apply (f_equal to_Z) in Hp2.
  destruct r1 as [t1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_pop_types st2 (alloc_vec_Vec_deref types)) as [[r2 st3]|]
    eqn:Hpt; cbn [bind] in H; [|discriminate].
  pose proof (pop_types_pos _ _ r2 st3 Hpt) as Hp3. unfold pos_of in Hp3.
  apply (f_equal to_Z) in Hp3.
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_types st3 (alloc_vec_Vec_deref types)) as [st4|]
    eqn:Hpush; cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  pose proof (push_types_pos st3 _ st4 Hpush) as Hp4. unfold pos_of in Hp4.
  apply (f_equal to_Z) in Hp4. lia.
Qed.

Lemma read_table_labels_loop_mono : forall n st data count expect i r st',
  to_Z i + Z.of_nat n = to_Z count ->
  opiter_read_table_labels_loop st data count expect i = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  induction n as [|n IH]; intros st data count expect i r st' Hn H;
    unfold opiter_read_table_labels_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (i s= count) eqn:Heq;
    [injection H as _ <-; lia | | injection H as _ <-; lia | ].
  - exfalso. apply scalar_eqb_false in Heq. cbn in Hn. lia.
  - destruct (opiter_read_label st data) as [[r0 st1]|] eqn:Hrl;
      cbn [bind] in H; [|discriminate].
    pose proof (read_label_mono st data r0 st1 Hrl) as Hm.
    destruct r0 as [[d0 target]|e].
    2: { rewrite branch_err in H. cbn [bind] in H.
         rewrite from_residual_err in H. cbn [bind] in H.
         injection H as _ <-. lia. }
    rewrite branch_ok in H. cbn [bind] in H.
    rewrite branch_target_bt_spec in H. cbn [bind] in H.
    destruct (opiter_merge_target expect (branch_target_bt_of target)) as [r1|]
      eqn:Hmt; cbn [bind] in H; [|discriminate].
    destruct r1 as [bt|e1].
    2: { rewrite branch_err in H. cbn [bind] in H.
         rewrite from_residual_err in H. cbn [bind] in H.
         injection H as _ <-. lia. }
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (u32_add i 1%u32) as [i1|] eqn:Hadd; cbn [bind] in H;
      [|discriminate].
    assert (Hi1 : to_Z i1 = to_Z i + 1).
    { unfold u32_add, scalar_add in Hadd. apply mk_scalar_ok_to_Z in Hadd.
      assert (H1 : to_Z 1%u32 = 1) by reflexivity. rewrite Hadd. lia. }
    pose proof (IH st1 data count (Some bt) i1 r st' (ltac:(cbn in Hn; lia)) H).
    lia.
Qed.

Lemma read_table_labels_mono : forall st data count r st',
  opiter_read_table_labels st data count = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data count r st' H. unfold opiter_read_table_labels in H.
  apply (read_table_labels_loop_mono (Z.to_nat (to_Z count)) st data count
           None 0%u32 r st'); [|exact H].
  assert (H0 : to_Z 0%u32 = 0) by reflexivity. rewrite H0.
  rewrite Z2Nat.id by apply u32_nonneg. reflexivity.
Qed.

Lemma read_br_table_mono : forall st data r st',
  opiter_read_br_table st data = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data r st' H. unfold opiter_read_br_table in H.
  destruct (opiter_take_pending st opiter_op_br_table) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st _ r0 st1 Htp) as Hp1. unfold pos_of in Hp1.
  apply (f_equal to_Z) in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_u32_leb data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[count p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_u32_leb_mono data _ count p1 Hleb) as Hm1.
  destruct (opiter_read_table_labels
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending := st1.(opiter_OpIterState_pending)
              |} data count) as [[r2 st2]|] eqn:Htl;
    cbn [bind] in H; [|discriminate].
  pose proof (read_table_labels_mono _ data count r2 st2 Htl) as Hm2.
  cbn [opiter_OpIterState_pos] in Hm2.
  destruct r2 as [expect|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_read_label st2 data) as [[r3 st3]|] eqn:Hrl;
    cbn [bind] in H; [|discriminate].
  pose proof (read_label_mono st2 data r3 st3 Hrl) as Hm3.
  destruct r3 as [[d0 target]|e3].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  rewrite branch_target_bt_spec in H. cbn [bind] in H.
  destruct (opiter_merge_target expect (branch_target_bt_of target)) as [r4|]
    eqn:Hmt; cbn [bind] in H; [|discriminate].
  destruct r4 as [common|e4].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_pop_with_type st3 Types_ValueType_I32) as [[r5 st4]|] eqn:Hp5;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos st3 _ r5 st4 Hp5) as Hp4. unfold pos_of in Hp4.
  apply (f_equal to_Z) in Hp4.
  destruct r5 as [t5|e5].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_block_results common) as [types|] eqn:Hbr;
    cbn [bind] in H; [|discriminate].
  destruct (opiter_pop_types st4 (alloc_vec_Vec_deref types)) as [[r6 st5]|]
    eqn:Hpt; cbn [bind] in H; [|discriminate].
  pose proof (pop_types_pos _ _ r6 st5 Hpt) as Hp6. unfold pos_of in Hp6.
  apply (f_equal to_Z) in Hp6.
  destruct r6 as [u6|e6].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u6. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_mark_unreachable st5) as [st6|] eqn:Hmu;
    cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  pose proof (mark_unreachable_pos st5 st6 Hmu) as Hp7. unfold pos_of in Hp7.
  apply (f_equal to_Z) in Hp7. lia.
Qed.

Lemma read_load_mono : forall st data module opcode ty natural r st',
  opiter_read_load st data module opcode ty natural = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data module opcode ty natural r st' H. unfold opiter_read_load in H.
  destruct (opiter_take_pending st opcode) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opcode r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1. apply (f_equal to_Z) in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_read_memarg st1 data) as [[r1 st2]|] eqn:Hma;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [m0|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-.
       pose proof (read_memarg_mono st1 data _ st2 Hma) as Hp2. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_memarg_mono st1 data _ st2 Hma) as Hm.
  destruct (opiter_check_memory_and_alignment module m0 natural) as [r2|] eqn:Hck;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_pop_with_type st2 Types_ValueType_I32) as [[r3 st3]|] eqn:Hpop;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos st2 _ r3 st3 Hpop) as Hp3. unfold pos_of in Hp3. apply (f_equal to_Z) in Hp3.
  destruct r3 as [t3|e3].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val st3 (Opiter_StackType_Val ty)) as [st4|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  pose proof (push_val_pos st3 _ st4 Hpv) as Hp4. unfold pos_of in Hp4. apply (f_equal to_Z) in Hp4. lia.
Qed.

Lemma read_store_mono : forall st data module opcode ty natural r st',
  opiter_read_store st data module opcode ty natural = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data module opcode ty natural r st' H. unfold opiter_read_store in H.
  destruct (opiter_take_pending st opcode) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opcode r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1. apply (f_equal to_Z) in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_read_memarg st1 data) as [[r1 st2]|] eqn:Hma;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [m0|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-.
       pose proof (read_memarg_mono st1 data _ st2 Hma) as Hp2. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_memarg_mono st1 data _ st2 Hma) as Hm.
  destruct (opiter_check_memory_and_alignment module m0 natural) as [r2|] eqn:Hck;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_pop_with_type st2 ty) as [[r3 st3]|] eqn:Hpop1;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos st2 ty r3 st3 Hpop1) as Hp3.
  unfold pos_of in Hp3. apply (f_equal to_Z) in Hp3.
  destruct r3 as [t3|e3].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_pop_with_type st3 Types_ValueType_I32) as [[r4 st4]|] eqn:Hpop2;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos st3 _ r4 st4 Hpop2) as Hp4.
  unfold pos_of in Hp4. apply (f_equal to_Z) in Hp4.
  destruct r4 as [t4|e4].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  injection H as _ <-. lia.
Qed.

(* ================================================================== *)
(** ** The dispatch                                                    *)
(* ================================================================== *)

(** [step] calls a reader and, for the readers that return a value the checker
    does not need, discards it. Naming that wrapper once turns each of the thirty
    two opcode branches into a single line, three times over: for totality, for
    the cursor and for the stack size. *)
Definition step_wrap {T}
  (m : result (core_result_Result_t T error_OpError_t * opiter_OpIterState_t))
  : result (core_result_Result_t unit error_OpError_t * opiter_OpIterState_t) :=
  p <- m;
  let (r, st1) := p in
  cf <- core_result_Result_Insts_CoreOpsTry_traitTryTResultInfallibleE_branch r;
  match cf with
  | Core_ops_control_flow_ControlFlow_Continue _ =>
      Ok (Core_result_Result_Ok tt, st1)
  | Core_ops_control_flow_ControlFlow_Break residual =>
      r1 <-
        core_result_Result_Insts_CoreOpsTry_traitFromResidualResultInfallibleE_from_residual
          unit (core_convert_From_Blanket error_OpError_t) residual;
      Ok (r1, st1)
  end.

Lemma step_wrap_total : forall T
  (m : result (core_result_Result_t T error_OpError_t * opiter_OpIterState_t)),
  (exists r0 st0, m = Ok (r0, st0)) ->
  exists r st', step_wrap m = Ok (r, st').
Proof.
  intros T m [r0 [st0 Hm]]. unfold step_wrap. rewrite Hm. cbn [bind].
  destruct r0 as [x|e].
  - rewrite branch_ok. cbn [bind]. eexists. eexists. reflexivity.
  - rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
    eexists. eexists. reflexivity.
Qed.

Lemma step_wrap_state : forall T
  (m : result (core_result_Result_t T error_OpError_t * opiter_OpIterState_t))
  r st',
  step_wrap m = Ok (r, st') -> exists r0, m = Ok (r0, st').
Proof.
  intros T m r st' H. unfold step_wrap in H.
  destruct m as [[r0 st0]|] eqn:Hm; cbn [bind] in H; [|discriminate].
  destruct r0 as [x|e].
  - rewrite branch_ok in H. cbn [bind] in H. injection H as _ <-.
    eexists. reflexivity.
  - rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
    cbn [bind] in H. injection H as _ <-. eexists. reflexivity.
Qed.

Lemma read_op_advance : forall st data b st',
  opiter_read_op st data = Ok (Core_result_Result_Ok b, st') ->
  to_Z st'.(opiter_OpIterState_pos) = to_Z st.(opiter_OpIterState_pos) + 1.
Proof.
  intros st data b st' H. unfold opiter_read_op in H.
  destruct (reader_read_byte data st.(opiter_OpIterState_pos)) as [r0|] eqn:Hrb;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [[b0 p0]|e].
  - rewrite branch_ok in H. cbn [bind] in H. injection H as _ <-.
    cbn [opiter_OpIterState_pos].
    destruct (read_byte_ok data _ b0 p0 Hrb) as [_ Hp]. exact Hp.
  - rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
    cbn [bind] in H. discriminate.
Qed.

(** Past the end of the body, [read_op] reports [UnexpectedEof]. This is what
    stops the loop rather than a decreasing measure alone: the cursor is never
    shown to stay inside the body, only to move forward. *)
Lemma read_op_err_at_end : forall st data,
  Z.of_nat (List.length (vec_list data)) <= to_Z st.(opiter_OpIterState_pos) ->
  opiter_read_op st data
    = Ok (Core_result_Result_Err Error_OpError_UnexpectedEof, st).
Proof.
  intros st data Hend. unfold opiter_read_op.
  rewrite (read_byte_err_at_end data _ Hend). cbn [bind].
  rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind].
  reflexivity.
Qed.

(** A successful [step] means the reader it dispatched to succeeded, not merely
    that it returned: the wrapper turns an inner [Err] into an outer [Err]. *)
Lemma step_wrap_ok : forall T
  (m : result (core_result_Result_t T error_OpError_t * opiter_OpIterState_t))
  st',
  step_wrap m = Ok (Core_result_Result_Ok tt, st') ->
  exists x, m = Ok (Core_result_Result_Ok x, st').
Proof.
  intros T m st' H. unfold step_wrap in H.
  destruct m as [[r0 st0]|]; cbn [bind] in H; [|discriminate].
  destruct r0 as [x|e].
  (* the unit payload collapses, so injection yields one equation *)
  - rewrite branch_ok in H. cbn [bind] in H. injection H as <-.
    exists x. reflexivity.
  - rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
    cbn [bind] in H. discriminate.
Qed.

Theorem step_total : forall st data module ctx opcode,
  room st -> exists r st', opiter_step st data module ctx opcode = Ok (r, st').
Proof.
  intros st data module ctx opcode Hroom. unfold opiter_step.
  destruct (opcode s= opiter_op_nop); [apply read_nop_total|].
  destruct (opcode s= opiter_op_unreachable); [apply read_unreachable_total|].
  destruct (opcode s= opiter_op_i32_const).
  { apply step_wrap_total. apply read_i32_const_total. exact Hroom. }
  destruct (opcode s= opiter_op_i64_const).
  { apply step_wrap_total. apply read_i64_const_total. exact Hroom. }
  destruct (opcode s= opiter_op_f32_const).
  { apply step_wrap_total. apply read_f32_const_total. exact Hroom. }
  destruct (opcode s= opiter_op_f64_const).
  { apply step_wrap_total. apply read_f64_const_total. exact Hroom. }
  destruct (opcode s= opiter_op_drop).
  { apply step_wrap_total. apply read_drop_total. }
  destruct (opcode s= opiter_op_select).
  { apply step_wrap_total. apply read_select_total. exact Hroom. }
  destruct (opcode s= opiter_op_block).
  { apply step_wrap_total. apply read_block_total. exact Hroom. }
  destruct (opcode s= opiter_op_loop).
  { apply step_wrap_total. apply read_loop_total. exact Hroom. }
  destruct (opcode s= opiter_op_if).
  { apply step_wrap_total. apply read_if_total. exact Hroom. }
  destruct (opcode s= opiter_op_else).
  { apply step_wrap_total. apply read_else_total. }
  destruct (opcode s= opiter_op_end).
  { apply step_wrap_total. apply read_end_total. exact Hroom. }
  destruct (opcode s= opiter_op_br).
  { apply step_wrap_total. apply read_br_total. }
  destruct (opcode s= opiter_op_br_if).
  { apply step_wrap_total. apply read_br_if_total. exact Hroom. }
  destruct (opcode s= opiter_op_br_table).
  { apply step_wrap_total. apply read_br_table_total. }
  destruct (opcode s= opiter_op_return).
  { apply step_wrap_total. apply read_return_total. }
  destruct (opcode s= opiter_op_call).
  { apply step_wrap_total. apply read_call_total. exact Hroom. }
  destruct (opcode s= opiter_op_call_indirect).
  { apply step_wrap_total. apply read_call_indirect_total. exact Hroom. }
  destruct (opcode s= opiter_op_local_get).
  { apply step_wrap_total. apply read_local_get_total. exact Hroom. }
  destruct (opcode s= opiter_op_local_set).
  { apply step_wrap_total. apply read_local_set_total. }
  destruct (opcode s= opiter_op_local_tee).
  { apply step_wrap_total. apply read_local_tee_total. exact Hroom. }
  destruct (opcode s= opiter_op_global_get).
  { apply step_wrap_total. apply read_global_get_total. exact Hroom. }
  destruct (opcode s= opiter_op_global_set).
  { apply step_wrap_total. apply read_global_set_total. }
  (* the memory opcodes: fourteen loads and nine stores, two shapes *)
  unfold opiter_step_memory.
  destruct (opcode s= opiter_op_i32_load);
    [apply step_wrap_total; apply read_load_total; exact Hroom|].
  destruct (opcode s= opiter_op_i64_load);
    [apply step_wrap_total; apply read_load_total; exact Hroom|].
  destruct (opcode s= opiter_op_f32_load);
    [apply step_wrap_total; apply read_load_total; exact Hroom|].
  destruct (opcode s= opiter_op_f64_load);
    [apply step_wrap_total; apply read_load_total; exact Hroom|].
  destruct (opcode s= opiter_op_i32_load8_s);
    [apply step_wrap_total; apply read_load_total; exact Hroom|].
  destruct (opcode s= opiter_op_i32_load8_u);
    [apply step_wrap_total; apply read_load_total; exact Hroom|].
  destruct (opcode s= opiter_op_i32_load16_s);
    [apply step_wrap_total; apply read_load_total; exact Hroom|].
  destruct (opcode s= opiter_op_i32_load16_u);
    [apply step_wrap_total; apply read_load_total; exact Hroom|].
  destruct (opcode s= opiter_op_i64_load8_s);
    [apply step_wrap_total; apply read_load_total; exact Hroom|].
  destruct (opcode s= opiter_op_i64_load8_u);
    [apply step_wrap_total; apply read_load_total; exact Hroom|].
  destruct (opcode s= opiter_op_i64_load16_s);
    [apply step_wrap_total; apply read_load_total; exact Hroom|].
  destruct (opcode s= opiter_op_i64_load16_u);
    [apply step_wrap_total; apply read_load_total; exact Hroom|].
  destruct (opcode s= opiter_op_i64_load32_s);
    [apply step_wrap_total; apply read_load_total; exact Hroom|].
  destruct (opcode s= opiter_op_i64_load32_u);
    [apply step_wrap_total; apply read_load_total; exact Hroom|].
  destruct (opcode s= opiter_op_i32_store);
    [apply step_wrap_total; apply read_store_total|].
  destruct (opcode s= opiter_op_i64_store);
    [apply step_wrap_total; apply read_store_total|].
  destruct (opcode s= opiter_op_f32_store);
    [apply step_wrap_total; apply read_store_total|].
  destruct (opcode s= opiter_op_f64_store);
    [apply step_wrap_total; apply read_store_total|].
  destruct (opcode s= opiter_op_i32_store8);
    [apply step_wrap_total; apply read_store_total|].
  destruct (opcode s= opiter_op_i32_store16);
    [apply step_wrap_total; apply read_store_total|].
  destruct (opcode s= opiter_op_i64_store8);
    [apply step_wrap_total; apply read_store_total|].
  destruct (opcode s= opiter_op_i64_store16);
    [apply step_wrap_total; apply read_store_total|].
  destruct (opcode s= opiter_op_i64_store32);
    [apply step_wrap_total; apply read_store_total|].
  destruct (opcode s= opiter_op_memory_size).
  { apply step_wrap_total. apply read_memory_size_total. exact Hroom. }
  destruct (opcode s= opiter_op_memory_grow).
  { apply step_wrap_total. apply read_memory_grow_total. exact Hroom. }
  (* the numeric opcodes, through the two tables *)
  unfold opiter_step_numeric.
  destruct (convert_types_ok opcode) as [o Hcv]. rewrite Hcv. cbn [bind].
  destruct o as [[from to]|];
    [apply read_conversion_total; exact Hroom|].
  destruct (binary_types_ok opcode) as [o1 Hbt]. rewrite Hbt. cbn [bind].
  destruct o1 as [[ty res]|];
    [apply read_binary_total; exact Hroom|].
  eexists. eexists. reflexivity.
Qed.

(** The immediate-free readers leave the cursor alone, so their monotonicity is
    their [_pos] lemma read as an inequality. *)
Lemma read_nop_mono : forall st r st',
  opiter_read_nop st = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st r st' H. pose proof (read_nop_pos st r st' H) as Hp.
  unfold pos_of in Hp. apply (f_equal to_Z) in Hp. lia.
Qed.

Lemma read_unreachable_mono : forall st r st',
  opiter_read_unreachable st = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st r st' H. pose proof (read_unreachable_pos st r st' H) as Hp.
  unfold pos_of in Hp. apply (f_equal to_Z) in Hp. lia.
Qed.

Lemma read_drop_mono : forall st r st',
  opiter_read_drop st = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st r st' H. pose proof (read_drop_pos st r st' H) as Hp.
  unfold pos_of in Hp. apply (f_equal to_Z) in Hp. lia.
Qed.

Lemma read_select_mono : forall st r st',
  opiter_read_select st = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st r st' H. pose proof (read_select_pos st r st' H) as Hp.
  unfold pos_of in Hp. apply (f_equal to_Z) in Hp. lia.
Qed.

(** The cursor only ever moves forward through the index. Needed in the error
    branches too, so it is proved directly rather than from
    [take_local_sound]. *)
Lemma take_local_mono : forall st data ctx opcode r st',
  opiter_take_local st data ctx opcode = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data ctx opcode r st' H. unfold opiter_take_local in H.
  destruct (opiter_take_pending st opcode) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opcode r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1. apply (f_equal to_Z) in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_u32_leb data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[idx0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  pose proof (read_u32_leb_mono data st1.(opiter_OpIterState_pos) idx0 p1 Hleb)
    as Hm.
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_local_type ctx idx0) as [r2|] eqn:Hlt;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [t0|e2].
  - rewrite branch_ok in H. cbn [bind] in H. injection H as _ <-.
    cbn [opiter_OpIterState_pos]. lia.
  - rewrite branch_err in H. cbn [bind] in H.
    rewrite from_residual_err in H. cbn [bind] in H. injection H as _ <-.
    cbn [opiter_OpIterState_pos]. lia.
Qed.

Lemma read_local_get_mono : forall st data ctx r st',
  opiter_read_local_get st data ctx = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data ctx r st' H. unfold opiter_read_local_get in H.
  destruct (opiter_take_local st data ctx opiter_op_local_get) as [[r0 st1]|]
    eqn:Htl; cbn [bind] in H; [|discriminate].
  pose proof (take_local_mono st data ctx _ r0 st1 Htl) as Hm.
  destruct r0 as [[idx t]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val st1 (Opiter_StackType_Val t)) as [st2|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  pose proof (push_val_pos st1 _ st2 Hpv) as Hp. unfold pos_of in Hp.
  apply (f_equal to_Z) in Hp. lia.
Qed.

Lemma read_local_set_mono : forall st data ctx r st',
  opiter_read_local_set st data ctx = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data ctx r st' H. unfold opiter_read_local_set in H.
  destruct (opiter_take_local st data ctx opiter_op_local_set) as [[r0 st1]|]
    eqn:Htl; cbn [bind] in H; [|discriminate].
  pose proof (take_local_mono st data ctx _ r0 st1 Htl) as Hm.
  destruct r0 as [[idx t]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_pop_with_type st1 t) as [[r1 st2]|] eqn:Hp1;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos st1 t r1 st2 Hp1) as Hp.
  unfold pos_of in Hp. apply (f_equal to_Z) in Hp.
  destruct r1 as [t1|e1].
  - rewrite branch_ok in H. cbn [bind] in H. injection H as _ <-. lia.
  - rewrite branch_err in H. cbn [bind] in H.
    rewrite from_residual_err in H. cbn [bind] in H.
    injection H as _ <-. lia.
Qed.

Lemma read_local_tee_mono : forall st data ctx r st',
  opiter_read_local_tee st data ctx = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data ctx r st' H. unfold opiter_read_local_tee in H.
  destruct (opiter_take_local st data ctx opiter_op_local_tee) as [[r0 st1]|]
    eqn:Htl; cbn [bind] in H; [|discriminate].
  pose proof (take_local_mono st data ctx _ r0 st1 Htl) as Hm.
  destruct r0 as [[idx t]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_pop_with_type st1 t) as [[r1 st2]|] eqn:Hp1;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos st1 t r1 st2 Hp1) as Hp.
  unfold pos_of in Hp. apply (f_equal to_Z) in Hp.
  destruct r1 as [t1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val st2 (Opiter_StackType_Val t)) as [st3|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  pose proof (push_val_pos st2 _ st3 Hpv) as Hp3. unfold pos_of in Hp3.
  apply (f_equal to_Z) in Hp3. lia.
Qed.

Lemma take_global_mono : forall st data module opcode r st',
  opiter_take_global st data module opcode = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data module opcode r st' H. unfold opiter_take_global in H.
  destruct (opiter_take_pending st opcode) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opcode r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1. apply (f_equal to_Z) in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_u32_leb data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[idx0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  pose proof (read_u32_leb_mono data st1.(opiter_OpIterState_pos) idx0 p1 Hleb)
    as Hm.
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_global_type module idx0) as [r2|] eqn:Hgt;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [g|e2].
  - rewrite branch_ok in H. cbn [bind] in H. injection H as _ <-.
    cbn [opiter_OpIterState_pos]. lia.
  - rewrite branch_err in H. cbn [bind] in H.
    rewrite from_residual_err in H. cbn [bind] in H. injection H as _ <-.
    cbn [opiter_OpIterState_pos]. lia.
Qed.

Lemma read_global_get_mono : forall st data module r st',
  opiter_read_global_get st data module = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data module r st' H. unfold opiter_read_global_get in H.
  destruct (opiter_take_global st data module opiter_op_global_get) as [[r0 st1]|]
    eqn:Htg; cbn [bind] in H; [|discriminate].
  pose proof (take_global_mono st data module _ r0 st1 Htg) as Hm.
  destruct r0 as [[idx g]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val st1
              (Opiter_StackType_Val g.(types_GlobalType_valtype))) as [st2|]
    eqn:Hpv; cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  pose proof (push_val_pos st1 _ st2 Hpv) as Hp. unfold pos_of in Hp.
  apply (f_equal to_Z) in Hp. lia.
Qed.

Lemma read_global_set_mono : forall st data module r st',
  opiter_read_global_set st data module = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data module r st' H. unfold opiter_read_global_set in H.
  destruct (opiter_take_global st data module opiter_op_global_set) as [[r0 st1]|]
    eqn:Htg; cbn [bind] in H; [|discriminate].
  pose proof (take_global_mono st data module _ r0 st1 Htg) as Hm.
  destruct r0 as [[idx g]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (g.(types_GlobalType_mutability)).
  { injection H as _ <-. lia. }
  destruct (opiter_pop_with_type st1 g.(types_GlobalType_valtype))
    as [[r1 st2]|] eqn:Hp1; cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos st1 _ r1 st2 Hp1) as Hp.
  unfold pos_of in Hp. apply (f_equal to_Z) in Hp.
  destruct r1 as [t1|e1].
  - rewrite branch_ok in H. cbn [bind] in H. injection H as _ <-. lia.
  - rewrite branch_err in H. cbn [bind] in H.
    rewrite from_residual_err in H. cbn [bind] in H.
    injection H as _ <-. lia.
Qed.

Lemma read_reserved_zero_mono : forall st data r st',
  opiter_read_reserved_zero st data = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data r st' H. unfold opiter_read_reserved_zero in H.
  destruct (reader_read_byte data st.(opiter_OpIterState_pos)) as [r0|] eqn:Hrb;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [[b p]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (read_byte_ok data st.(opiter_OpIterState_pos) b p Hrb) as [_ Hp].
  destruct (b s<> 0%u8); injection H as _ <-;
    cbn [opiter_OpIterState_pos]; lia.
Qed.

Lemma read_memory_size_mono : forall st data module r st',
  opiter_read_memory_size st data module = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data module r st' H. unfold opiter_read_memory_size in H.
  destruct (opiter_take_pending st opiter_op_memory_size) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st _ r0 st1 Htp) as Hp1. unfold pos_of in Hp1.
  apply (f_equal to_Z) in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_read_reserved_zero st1 data) as [[r1 st2]|] eqn:Hrz;
    cbn [bind] in H; [|discriminate].
  pose proof (read_reserved_zero_mono st1 data r1 st2 Hrz) as Hm2.
  destruct r1 as [u1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u1. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_require_memory module) as [r2|] eqn:Hrm;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val st2 (Opiter_StackType_Val Types_ValueType_I32))
    as [st3|] eqn:Hpv; cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  pose proof (push_val_pos st2 _ st3 Hpv) as Hp3. unfold pos_of in Hp3.
  apply (f_equal to_Z) in Hp3. lia.
Qed.

Lemma read_memory_grow_mono : forall st data module r st',
  opiter_read_memory_grow st data module = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data module r st' H. unfold opiter_read_memory_grow in H.
  destruct (opiter_take_pending st opiter_op_memory_grow) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st _ r0 st1 Htp) as Hp1. unfold pos_of in Hp1.
  apply (f_equal to_Z) in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_read_reserved_zero st1 data) as [[r1 st2]|] eqn:Hrz;
    cbn [bind] in H; [|discriminate].
  pose proof (read_reserved_zero_mono st1 data r1 st2 Hrz) as Hm2.
  destruct r1 as [u1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u1. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_require_memory module) as [r2|] eqn:Hrm;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_pop_with_type st2 Types_ValueType_I32) as [[r3 st3]|] eqn:Hp3;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos st2 _ r3 st3 Hp3) as Hpp. unfold pos_of in Hpp.
  apply (f_equal to_Z) in Hpp.
  destruct r3 as [t3|e3].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val st3 (Opiter_StackType_Val Types_ValueType_I32))
    as [st4|] eqn:Hpv; cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  pose proof (push_val_pos st3 _ st4 Hpv) as Hp4. unfold pos_of in Hp4.
  apply (f_equal to_Z) in Hp4. lia.
Qed.

Lemma read_binary_mono : forall st opcode ty res r st',
  opiter_read_binary st opcode ty res = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st opcode ty res r st' H.
  pose proof (read_binary_pos st opcode ty res r st' H) as Hp.
  unfold pos_of in Hp. apply (f_equal to_Z) in Hp. lia.
Qed.

Lemma read_conversion_mono : forall st opcode from to r st',
  opiter_read_conversion st opcode from to = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st opcode from to r st' H.
  pose proof (read_conversion_pos st opcode from to r st' H) as Hp.
  unfold pos_of in Hp. apply (f_equal to_Z) in Hp. lia.
Qed.

Lemma read_end_mono : forall st r st',
  opiter_read_end st = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st r st' H. pose proof (read_end_pos st r st' H) as Hp.
  unfold pos_of in Hp. apply (f_equal to_Z) in Hp. lia.
Qed.

Lemma read_else_mono : forall st r st',
  opiter_read_else st = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st r st' H. pose proof (read_else_pos st r st' H) as Hp.
  unfold pos_of in Hp. apply (f_equal to_Z) in Hp. lia.
Qed.

Lemma take_index_mono : forall st data opcode r st',
  opiter_take_index st data opcode = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data opcode r st' H. unfold opiter_take_index in H.
  destruct (opiter_take_pending st opcode) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  pose proof (take_pending_pos st opcode r0 st1 Htp) as Hp1.
  unfold pos_of in Hp1. apply (f_equal to_Z) in Hp1.
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_u32_leb data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[idx0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  pose proof (read_u32_leb_mono data st1.(opiter_OpIterState_pos) idx0 p1 Hleb)
    as Hm.
  rewrite branch_ok in H. cbn [bind] in H. injection H as _ <-.
  cbn [opiter_OpIterState_pos]. lia.
Qed.

Lemma read_call_mono : forall st data module r st',
  opiter_read_call st data module = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data module r st' H. unfold opiter_read_call in H.
  destruct (opiter_take_index st data opiter_op_call) as [[r0 st1]|] eqn:Hti;
    cbn [bind] in H; [|discriminate].
  pose proof (take_index_mono st data _ r0 st1 Hti) as Hm1.
  destruct r0 as [idx|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (scalar_cast U32 Usize idx) as [i|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  destruct (i s>= alloc_vec_Vec_len module.(env_Env_func_types));
    [injection H as _ <-; lia|].
  destruct (alloc_vec_Vec_index
              (core_slice_index_SliceIndexUsizeSliceInst types_FuncType_t)
              module.(env_Env_func_types) i) as [ft|] eqn:Hidx;
    cbn [bind] in H; [|discriminate].
  destruct (opiter_require_single_result
              (alloc_vec_Vec_deref ft.(types_FuncType_results))) as [r1|] eqn:Hrs;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [u1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u1. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_pop_types st1 (alloc_vec_Vec_deref ft.(types_FuncType_params)))
    as [[r2 st2]|] eqn:Hpt; cbn [bind] in H; [|discriminate].
  pose proof (pop_types_pos _ _ r2 st2 Hpt) as Hp2. unfold pos_of in Hp2.
  apply (f_equal to_Z) in Hp2.
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_types st2
              (alloc_vec_Vec_deref ft.(types_FuncType_results))) as [st3|]
    eqn:Hpu; cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  pose proof (push_types_pos st2 _ st3 Hpu) as Hp3. unfold pos_of in Hp3.
  apply (f_equal to_Z) in Hp3. lia.
Qed.

Lemma read_call_indirect_mono : forall st data module r st',
  opiter_read_call_indirect st data module = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data module r st' H. unfold opiter_read_call_indirect in H.
  destruct (opiter_take_index st data opiter_op_call_indirect) as [[r0 st1]|]
    eqn:Hti; cbn [bind] in H; [|discriminate].
  pose proof (take_index_mono st data _ r0 st1 Hti) as Hm1.
  destruct r0 as [idx|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_read_reserved_zero st1 data) as [[r1 st2]|] eqn:Hrz;
    cbn [bind] in H; [|discriminate].
  pose proof (read_reserved_zero_mono st1 data r1 st2 Hrz) as Hm2.
  destruct r1 as [u1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u1. rewrite branch_ok in H. cbn [bind] in H.
  destruct (alloc_vec_Vec_is_empty alloc_alloc_Global
              module.(env_Env_table_types)) as [emp|] eqn:Hemp;
    cbn [bind] in H; [|discriminate].
  destruct emp; [injection H as _ <-; lia|].
  destruct (scalar_cast U32 Usize idx) as [i|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  destruct (i s>= alloc_vec_Vec_len module.(env_Env_types));
    [injection H as _ <-; lia|].
  destruct (alloc_vec_Vec_index
              (core_slice_index_SliceIndexUsizeSliceInst types_FuncType_t)
              module.(env_Env_types) i) as [ft|] eqn:Hidx;
    cbn [bind] in H; [|discriminate].
  destruct (opiter_require_single_result
              (alloc_vec_Vec_deref ft.(types_FuncType_results))) as [r2|] eqn:Hrs;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_pop_with_type st2 Types_ValueType_I32) as [[r3 st3]|] eqn:Hpw;
    cbn [bind] in H; [|discriminate].
  pose proof (pop_with_type_pos st2 _ r3 st3 Hpw) as Hp3. unfold pos_of in Hp3.
  apply (f_equal to_Z) in Hp3.
  destruct r3 as [t3|e3].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_pop_types st3 (alloc_vec_Vec_deref ft.(types_FuncType_params)))
    as [[r4 st4]|] eqn:Hpt; cbn [bind] in H; [|discriminate].
  pose proof (pop_types_pos _ _ r4 st4 Hpt) as Hp4. unfold pos_of in Hp4.
  apply (f_equal to_Z) in Hp4.
  destruct r4 as [u4|e4].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H.
       injection H as _ <-. lia. }
  destruct u4. rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_types st4
              (alloc_vec_Vec_deref ft.(types_FuncType_results))) as [st5|]
    eqn:Hpu; cbn [bind] in H; [|discriminate].
  injection H as _ <-.
  pose proof (push_types_pos st4 _ st5 Hpu) as Hp5. unfold pos_of in Hp5.
  apply (f_equal to_Z) in Hp5. lia.
Qed.

Theorem step_mono : forall st data module ctx opcode r st',
  opiter_step st data module ctx opcode = Ok (r, st') ->
  to_Z st.(opiter_OpIterState_pos) <= to_Z st'.(opiter_OpIterState_pos).
Proof.
  intros st data module ctx opcode r st' H. unfold opiter_step in H.
  destruct (opcode s= opiter_op_nop);
    [apply (read_nop_mono st _ st' H)|].
  destruct (opcode s= opiter_op_unreachable);
    [apply (read_unreachable_mono st _ st' H)|].
  destruct (opcode s= opiter_op_i32_const).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_i32_const_mono st data _ st' Hm). }
  destruct (opcode s= opiter_op_i64_const).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_i64_const_mono st data _ st' Hm). }
  destruct (opcode s= opiter_op_f32_const).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_f32_const_mono st data _ st' Hm). }
  destruct (opcode s= opiter_op_f64_const).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_f64_const_mono st data _ st' Hm). }
  destruct (opcode s= opiter_op_drop).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_drop_mono st _ st' Hm). }
  destruct (opcode s= opiter_op_select).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_select_mono st _ st' Hm). }
  destruct (opcode s= opiter_op_block).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_block_mono st data _ st' Hm). }
  destruct (opcode s= opiter_op_loop).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_loop_mono st data _ st' Hm). }
  destruct (opcode s= opiter_op_if).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_if_mono st data _ st' Hm). }
  destruct (opcode s= opiter_op_else).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_else_mono st _ st' Hm). }
  destruct (opcode s= opiter_op_end).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_end_mono st _ st' Hm). }
  destruct (opcode s= opiter_op_br).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_br_mono st data _ st' Hm). }
  destruct (opcode s= opiter_op_br_if).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_br_if_mono st data _ st' Hm). }
  destruct (opcode s= opiter_op_br_table).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_br_table_mono st data _ st' Hm). }
  destruct (opcode s= opiter_op_return).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    pose proof (read_return_pos st ctx _ st' Hm) as Hp. unfold pos_of in Hp.
    apply (f_equal to_Z) in Hp. lia. }
  destruct (opcode s= opiter_op_call).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_call_mono st data module _ st' Hm). }
  destruct (opcode s= opiter_op_call_indirect).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_call_indirect_mono st data module _ st' Hm). }
  destruct (opcode s= opiter_op_local_get).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_local_get_mono st data ctx _ st' Hm). }
  destruct (opcode s= opiter_op_local_set).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_local_set_mono st data ctx _ st' Hm). }
  destruct (opcode s= opiter_op_local_tee).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_local_tee_mono st data ctx _ st' Hm). }
  destruct (opcode s= opiter_op_global_get).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_global_get_mono st data module _ st' Hm). }
  destruct (opcode s= opiter_op_global_set).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_global_set_mono st data module _ st' Hm). }
  (* the memory opcodes *)
  unfold opiter_step_memory in H.
  destruct (opcode s= opiter_op_i32_load).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i64_load).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_f32_load).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_f64_load).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i32_load8_s).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i32_load8_u).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i32_load16_s).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i32_load16_u).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i64_load8_s).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i64_load8_u).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i64_load16_s).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i64_load16_u).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i64_load32_s).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i64_load32_u).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i32_store).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_store_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i64_store).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_store_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_f32_store).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_store_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_f64_store).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_store_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i32_store8).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_store_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i32_store16).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_store_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i64_store8).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_store_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i64_store16).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_store_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i64_store32).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_store_mono st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_memory_size).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_memory_size_mono st data module _ st' Hm). }
  destruct (opcode s= opiter_op_memory_grow).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_memory_grow_mono st data module _ st' Hm). }
  unfold opiter_step_numeric in H.
  destruct (opiter_convert_types opcode) as [o|] eqn:Hcv;
    cbn [bind] in H; [|discriminate].
  destruct o as [[from to]|];
    [apply (read_conversion_mono st _ _ _ _ st' H)|].
  destruct (opiter_binary_types opcode) as [o1|] eqn:Hbt;
    cbn [bind] in H; [|discriminate].
  destruct o1 as [[ty res]|];
    [apply (read_binary_mono st _ _ _ _ st' H)|].
  injection H as _ <-. lia.
Qed.

Theorem step_size : forall st data module ctx opcode r st',
  opiter_step st data module ctx opcode = Ok (r, st') ->
  (stack_size st' <= stack_size st + 1)%nat.
Proof.
  intros st data module ctx opcode r st' H. unfold opiter_step in H.
  destruct (opcode s= opiter_op_nop);
    [apply (read_nop_size st _ st' H)|].
  destruct (opcode s= opiter_op_unreachable);
    [apply (read_unreachable_size st _ st' H)|].
  destruct (opcode s= opiter_op_i32_const).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_i32_const_size st data _ st' Hm). }
  destruct (opcode s= opiter_op_i64_const).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_i64_const_size st data _ st' Hm). }
  destruct (opcode s= opiter_op_f32_const).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_f32_const_size st data _ st' Hm). }
  destruct (opcode s= opiter_op_f64_const).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_f64_const_size st data _ st' Hm). }
  destruct (opcode s= opiter_op_drop).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_drop_size st _ st' Hm). }
  destruct (opcode s= opiter_op_select).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_select_size st _ st' Hm). }
  destruct (opcode s= opiter_op_block).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_block_size st data _ st' Hm). }
  destruct (opcode s= opiter_op_loop).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_loop_size st data _ st' Hm). }
  destruct (opcode s= opiter_op_if).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_if_size st data _ st' Hm). }
  destruct (opcode s= opiter_op_else).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    pose proof (read_else_size st _ st' Hm). lia. }
  destruct (opcode s= opiter_op_end).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_end_size st _ st' Hm). }
  destruct (opcode s= opiter_op_br).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_br_size st data _ st' Hm). }
  destruct (opcode s= opiter_op_br_if).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_br_if_size st data _ st' Hm). }
  destruct (opcode s= opiter_op_br_table).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_br_table_size st data _ st' Hm). }
  destruct (opcode s= opiter_op_return).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_return_size st ctx _ st' Hm). }
  destruct (opcode s= opiter_op_call).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_call_size st data module _ st' Hm). }
  destruct (opcode s= opiter_op_call_indirect).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_call_indirect_size st data module _ st' Hm). }
  destruct (opcode s= opiter_op_local_get).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_local_get_size st data ctx _ st' Hm). }
  destruct (opcode s= opiter_op_local_set).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_local_set_size st data ctx _ st' Hm). }
  destruct (opcode s= opiter_op_local_tee).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_local_tee_size st data ctx _ st' Hm). }
  destruct (opcode s= opiter_op_global_get).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_global_get_size st data module _ st' Hm). }
  destruct (opcode s= opiter_op_global_set).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_global_set_size st data module _ st' Hm). }
  (* the memory opcodes *)
  unfold opiter_step_memory in H.
  destruct (opcode s= opiter_op_i32_load).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i64_load).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_f32_load).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_f64_load).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i32_load8_s).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i32_load8_u).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i32_load16_s).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i32_load16_u).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i64_load8_s).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i64_load8_u).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i64_load16_s).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i64_load16_u).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i64_load32_s).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i64_load32_u).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_load_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i32_store).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_store_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i64_store).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_store_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_f32_store).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_store_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_f64_store).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_store_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i32_store8).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_store_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i32_store16).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_store_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i64_store8).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_store_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i64_store16).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_store_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_i64_store32).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_store_size st data module _ _ _ _ st' Hm). }
  destruct (opcode s= opiter_op_memory_size).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_memory_size_size st data module _ st' Hm). }
  destruct (opcode s= opiter_op_memory_grow).
  { destruct (step_wrap_state _ _ r st' H) as [r0 Hm].
    apply (read_memory_grow_size st data module _ st' Hm). }
  unfold opiter_step_numeric in H.
  destruct (opiter_convert_types opcode) as [o|] eqn:Hcv;
    cbn [bind] in H; [|discriminate].
  destruct o as [[from to]|];
    [apply (read_conversion_size st _ _ _ _ st' H)|].
  destruct (opiter_binary_types opcode) as [o1|] eqn:Hbt;
    cbn [bind] in H; [|discriminate].
  destruct o1 as [[ty res]|];
    [apply (read_binary_size st _ _ _ _ st' H)|].
  injection H as _ <-. lia.
Qed.

(* ================================================================== *)
(** ** The decoders accept what the specification admits              *)
(* ================================================================== *)

(** The other direction of the decode correspondence, and the first half of
    completeness. Soundness says what the result means if there is one; this says
    that when the specification admits the bytes, there is one. Without it a
    decoder that rejected a spec-valid encoding would still be sound. *)

Lemma read_byte_complete : forall data pos z rest,
  bytes_from data pos = z :: rest ->
  exists b pos',
    reader_read_byte data pos = Ok (Core_result_Result_Ok (b, pos'))
    /\ to_Z b = z
    /\ bytes_from data pos' = rest.
Proof.
  intros data pos z rest H.
  destruct (bytes_from_uncons data pos z rest H)
    as [b [p2 [Hidx [Hz [Hadd [Hrest Hlt]]]]]].
  exists b, p2. unfold reader_read_byte.
  destruct (pos s>= slice_len data) eqn:Hge.
  { exfalso. apply scalar_geb_true_ge in Hge. lia. }
  rewrite Hidx. cbn [bind]. rewrite Hadd. cbn [bind].
  split; [reflexivity|]. split; [exact Hz | exact Hrest].
Qed.

(** The unsigned LEB128 reader accepts every encoding the specification admits.

    The guards line up one for one, which is the pleasing part of the design. The
    specification's [b < 2^bits] on a final byte is, at [i = 4] where [bits = 4],
    exactly the code's rejection of a fifth byte above 15; and the specification's
    [7 < bits] on a continuation is, at the same point, exactly the code's
    rejection of a fifth continuation byte. So neither guard can fire on a
    derivation. *)
Lemma read_u32_leb_loop_complete : forall n data acc mult p i v rest,
  to_Z i + Z.of_nat n = 4 ->
  leb_inv acc mult i ->
  repr_uN (32 - 7 * Z.to_nat (to_Z i))%nat (bytes_from data p) v rest ->
  exists v' p',
    reader_read_u32_leb_loop data acc mult p i
      = Ok (Core_result_Result_Ok (v', p'))
    /\ to_Z v' = to_Z acc + v * to_Z mult
    /\ bytes_from data p' = rest.
Proof.
  induction n as [|n IH]; intros data acc mult p i v rest Hn Hinv Hrep;
    destruct Hinv as [Hi [Hmult Hacc]];
    unfold reader_read_u32_leb_loop; rewrite loop_unfold; cbn beta iota.
  - (* the budget is spent, so [i = 4] and the byte must be the last *)
    assert (Hi4 : to_Z i = 4) by (cbn in Hn; lia).
    assert (Hbits : (32 - 7 * Z.to_nat (to_Z i))%nat = 4%nat)
      by (rewrite Hi4; reflexivity).
    rewrite Hbits in Hrep.
    destruct (repr_uN_inv _ _ _ _ Hrep)
      as [[b [rest0 [Hbs [Hv [Hrest [Hblo Hbhi]]]]]]
         |[b [more [m [Hbs [Hv [Hblo [Hbits7 Hsub]]]]]]]]; [|cbn in Hbits7; lia].
    (* the byte is there *)
    destruct (bytes_from_uncons data p b rest0 Hbs)
      as [bu [p2 [Hidx [Hz [Hadd [Hrest2 Hlt]]]]]].
    destruct (p s>= slice_len data) eqn:Hge;
      [exfalso; apply scalar_geb_true_ge in Hge; lia|].
    rewrite Hidx. cbn [bind]. rewrite Hadd. cbn [bind].
    destruct (u8_rem_128_ok bu) as [low [Hrem [Hlowval Hlowbd]]].
    rewrite Hrem. cbn [bind].
    assert (Heq4 : (i s= 4%u32) = true)
      by (unfold scalar_eqb; apply Z.eqb_eq; rewrite Hi4; reflexivity).
    rewrite Heq4. cbn beta iota.
    (* [low = b] since [b < 128], and [b < 16] since this is the fifth byte *)
    assert (Hlowb : to_Z low = to_Z bu)
      by (rewrite Hlowval; apply Z.rem_small; pose proof (u8_bounds bu); lia).
    assert (Hb16 : to_Z bu < 16) by (rewrite Hz; cbn in Hbhi; lia).
    destruct (low s> 15%u8) eqn:Hgt.
    { exfalso. apply scalar_gtb_true in Hgt.
      assert (H15 : to_Z 15%u8 = 15) by reflexivity. lia. }
    destruct (cast_u8_u32_ok low) as [c [Hcast Hcval]].
    rewrite Hcast. cbn [bind].
    assert (Hmult4 : to_Z mult = 268435456)
      by (rewrite Hmult; rewrite Hi4; reflexivity).
    destruct (u32_mul_ok c mult) as [prod [Hmul Hmulval]].
    { rewrite Hcval. rewrite Hmult4. rewrite u32_max_val. lia. }
    rewrite Hmul. cbn [bind].
    assert (Hacc4 : to_Z acc < 268435456) by (rewrite Hi4 in Hacc; exact Hacc).
    destruct (u32_add_ok acc prod) as [sum [Hadd2 Hsumval]].
    { rewrite Hmulval. rewrite Hcval. rewrite Hmult4. rewrite u32_max_val. lia. }
    rewrite Hadd2. cbn [bind].
    assert (Hlt128 : (bu s< 128%u8) = true).
    { unfold scalar_ltb. apply Z.ltb_lt.
      assert (H128 : to_Z 128%u8 = 128) by reflexivity. lia. }
    rewrite Hlt128. cbn beta iota.
    exists sum, p2. split; [reflexivity|]. split.
    + rewrite Hsumval. rewrite Hmulval. rewrite Hcval. rewrite Hlowb.
      rewrite Hz. rewrite Hv. reflexivity.
    + rewrite Hrest2. rewrite Hrest. reflexivity.
  - (* a byte remains in the budget: either it is the last or it continues *)
    assert (Hilt : to_Z i <= 3) by (cbn in Hn; lia).
    assert (Heq4 : (i s= 4%u32) = false).
    { unfold scalar_eqb. apply Z.eqb_neq.
      assert (H4 : to_Z 4%u32 = 4) by reflexivity. lia. }
    pose proof (pow128_pos (to_Z i) (proj1 Hi)) as Hmpos.
    pose proof (pow128_le (to_Z i) 3 (proj1 Hi) Hilt) as Hmle.
    assert (Hp3 : (128:Z) ^ 3 = 2097152) by reflexivity. rewrite Hp3 in Hmle.
    assert (Hmultle : to_Z mult <= 2097152) by (rewrite Hmult; exact Hmle).
    assert (Hmultpos : 0 < to_Z mult) by (rewrite Hmult; exact Hmpos).
    assert (Haccle : to_Z acc < to_Z mult) by (rewrite Hmult; exact Hacc).
    destruct (repr_uN_inv _ _ _ _ Hrep)
      as [[b [rest0 [Hbs [Hv [Hrest [Hblo Hbhi]]]]]]
         |[b [more [m [Hbs [Hv [Hblo [Hbits7 Hsub]]]]]]]].
    + (* the last byte *)
      destruct (bytes_from_uncons data p b rest0 Hbs)
        as [bu [p2 [Hidx [Hz [Hadd [Hrest2 Hlt]]]]]].
      destruct (p s>= slice_len data) eqn:Hge;
        [exfalso; apply scalar_geb_true_ge in Hge; lia|].
      rewrite Hidx. cbn [bind]. rewrite Hadd. cbn [bind].
      destruct (u8_rem_128_ok bu) as [low [Hrem [Hlowval Hlowbd]]].
      rewrite Hrem. cbn [bind]. rewrite Heq4. cbn beta iota.
      assert (Hlowb : to_Z low = to_Z bu)
        by (rewrite Hlowval; apply Z.rem_small; pose proof (u8_bounds bu); lia).
      destruct (cast_u8_u32_ok low) as [c [Hcast Hcval]].
      rewrite Hcast. cbn [bind].
      assert (Hlm : to_Z low * to_Z mult <= 127 * 2097152)
        by (apply Z.mul_le_mono_nonneg; lia).
      destruct (u32_mul_ok c mult) as [prod [Hmul Hmulval]].
      { rewrite Hcval. rewrite u32_max_val. lia. }
      rewrite Hmul. cbn [bind].
      destruct (u32_add_ok acc prod) as [sum [Hadd2 Hsumval]].
      { rewrite Hmulval. rewrite Hcval. rewrite u32_max_val. lia. }
      rewrite Hadd2. cbn [bind].
      assert (Hlt128 : (bu s< 128%u8) = true).
      { unfold scalar_ltb. apply Z.ltb_lt.
        assert (H128 : to_Z 128%u8 = 128) by reflexivity. lia. }
      rewrite Hlt128. cbn beta iota.
      exists sum, p2. split; [reflexivity|]. split.
      * rewrite Hsumval. rewrite Hmulval. rewrite Hcval. rewrite Hlowb.
        rewrite Hz. rewrite Hv. reflexivity.
      * rewrite Hrest2. rewrite Hrest. reflexivity.
    + (* a continuation byte *)
      destruct (bytes_from_uncons data p b more Hbs)
        as [bu [p2 [Hidx [Hz [Hadd [Hrest2 Hlt]]]]]].
      destruct (p s>= slice_len data) eqn:Hge;
        [exfalso; apply scalar_geb_true_ge in Hge; lia|].
      rewrite Hidx. cbn [bind]. rewrite Hadd. cbn [bind].
      destruct (u8_rem_128_ok bu) as [low [Hrem [Hlowval Hlowbd]]].
      rewrite Hrem. cbn [bind]. rewrite Heq4. cbn beta iota.
      (* [low = b - 128] since [128 <= b < 256] *)
      (* a continuation byte's payload is [b - 128] *)
      assert (Hrem128 : forall x, 128 <= x < 256 -> Z.rem x 128 = x - 128).
      { intros x Hx. rewrite Z.rem_mod_nonneg by lia.
        assert (Hy : x mod 128 = (x - 128) mod 128).
        { replace (x - 128) with (x + (-1) * 128) by lia.
          rewrite Z.mod_add by lia. reflexivity. }
        rewrite Hy. apply Z.mod_small. lia. }
      assert (Hlowb : to_Z low = to_Z bu - 128).
      { rewrite Hlowval. rewrite Hz. apply Hrem128. lia. }
      destruct (cast_u8_u32_ok low) as [c [Hcast Hcval]].
      rewrite Hcast. cbn [bind].
      assert (Hlm : to_Z low * to_Z mult <= 127 * 2097152)
        by (apply Z.mul_le_mono_nonneg; lia).
      destruct (u32_mul_ok c mult) as [prod [Hmul Hmulval]].
      { rewrite Hcval. rewrite u32_max_val. lia. }
      rewrite Hmul. cbn [bind].
      destruct (u32_add_ok acc prod) as [sum [Hadd2 Hsumval]].
      { rewrite Hmulval. rewrite Hcval. rewrite u32_max_val. lia. }
      rewrite Hadd2. cbn [bind].
      assert (Hnlt : (bu s< 128%u8) = false).
      { unfold scalar_ltb. apply Z.ltb_ge.
        assert (H128 : to_Z 128%u8 = 128) by reflexivity. lia. }
      (* the earlier [rewrite Heq4] already fired on this occurrence too *)
      rewrite Hnlt. cbn beta iota.
      assert (H128u : to_Z 128%u32 = 128) by reflexivity.
      assert (H1u : to_Z 1%u32 = 1) by reflexivity.
      destruct (u32_mul_ok mult 128%u32) as [mult2 [Hmul2 Hmul2val]].
      { rewrite H128u. rewrite u32_max_val. lia. }
      rewrite Hmul2. cbn [bind].
      destruct (u32_add_ok i 1%u32) as [i5 [Hadd3 Hi5val]].
      { rewrite H1u. rewrite u32_max_val. lia. }
      rewrite Hadd3. cbn [bind].
      (* the sub-derivation drives the next iteration *)
      destruct (IH data sum mult2 p2 i5 m rest) as [v' [p' [Hrun [Hval Hb]]]].
      * rewrite Hi5val. rewrite H1u. cbn in Hn. lia.
      * unfold leb_inv. split; [rewrite Hi5val; rewrite H1u; lia|].
        split.
        -- rewrite Hmul2val. rewrite H128u. rewrite Hi5val. rewrite H1u.
           rewrite Z.pow_add_r; [|apply (proj1 Hi) | lia]. rewrite Hmult. ring.
        -- assert (Hlm2 : to_Z low * to_Z mult <= 127 * to_Z mult)
             by (apply Z.mul_le_mono_nonneg_r; lia).
           assert (Hp1 : (128:Z) ^ 1 = 128) by reflexivity.
           rewrite Hsumval. rewrite Hmulval. rewrite Hcval. rewrite Hi5val.
           rewrite H1u. rewrite Z.pow_add_r; [|apply (proj1 Hi) | lia].
           rewrite <- Hmult. rewrite Hp1. lia.
      * assert (Hbits' : (32 - 7 * Z.to_nat (to_Z i5))%nat
                         = (32 - 7 * Z.to_nat (to_Z i) - 7)%nat).
        { rewrite Hi5val. rewrite H1u.
          assert (Hz' : Z.to_nat (to_Z i + 1) = S (Z.to_nat (to_Z i)))
            by (rewrite (Z_to_nat_add1 _ (proj1 Hi)); reflexivity).
          rewrite Hz'. lia. }
        rewrite Hbits'. rewrite Hrest2. exact Hsub.
      * exists v', p'. split; [exact Hrun|]. split; [|exact Hb].
        rewrite Hval. rewrite Hsumval. rewrite Hmulval. rewrite Hcval.
        rewrite Hmul2val. rewrite H128u. rewrite Hlowb. rewrite Hz.
        rewrite Hv. ring.
Qed.

Theorem read_u32_leb_complete : forall data pos v rest,
  repr_u32 (bytes_from data pos) v rest ->
  exists v' pos',
    reader_read_u32_leb data pos = Ok (Core_result_Result_Ok (v', pos'))
    /\ to_Z v' = v
    /\ bytes_from data pos' = rest.
Proof.
  intros data pos v rest H. unfold reader_read_u32_leb.
  destruct (read_u32_leb_loop_complete 4 data 0%u32 1%u32 pos 0%u32 v rest)
    as [v' [p' [Hrun [Hval Hb]]]].
  - reflexivity.
  - unfold leb_inv. cbn. lia.
  - replace (32 - 7 * Z.to_nat (to_Z 0%u32))%nat with 32%nat by reflexivity.
    exact H.
  - exists v', p'. split; [exact Hrun|]. split; [|exact Hb].
    rewrite Hval. cbn. lia.
Qed.

(** The signed reader's last byte, split by sign so the range check can be argued
    once per case rather than twice per iteration.

    The check is where the specification's bounds on a final byte earn their keep:
    [b < 2 ^ (bits-1)] for a positive byte and [128 - 2 ^ (bits-1) <= b] for a
    negative one are exactly what make it pass, and the positive bound is tight.
    [lia] cannot do the multiplication, so each product bound is built by hand. *)
Lemma sn_loop_last_pos : forall bits data last lo hi acc mult p i b rest0,
  sleb_params bits last lo hi ->
  sleb_inv last acc mult i ->
  bytes_from data p = b :: rest0 ->
  0 <= b < 64 ->
  b < 2 ^ (Z.of_nat (bits - 7 * Z.to_nat (to_Z i))%nat - 1) ->
  exists v' p',
    reader_read_sn_leb_loop data last lo hi acc mult p i
      = Ok (Core_result_Result_Ok (v', p'))
    /\ to_Z v' = to_Z acc + b * to_Z mult
    /\ bytes_from data p' = rest0.
Proof.
  intros bits data last lo hi acc mult p i b rest0 Hpar Hinv Hbs Hblo Hbhi.
  pose proof (sleb_bounds bits last lo hi acc mult i Hpar Hinv)
    as [Hmpos [Hmle [Haccm [Hbig' Hminmax]]]].
  pose proof Hpar as Hpar2. destruct Hpar2 as [Hbits [Hlov [Hhiv _]]].
  pose proof Hinv as Hinv2. destruct Hinv2 as [Hi [Hmult Hacc]].
  assert (Hexp : 7 * to_Z i <= Z.of_nat bits - 1) by lia.
  assert (Hpow : to_Z mult = 2 ^ (7 * to_Z i))
    by (rewrite Hmult; apply pow128_as_pow2; lia).
  assert (Hsb : Z.of_nat (bits - 7 * Z.to_nat (to_Z i))%nat - 1
                = Z.of_nat bits - 1 - 7 * to_Z i) by (apply sbits_eq; lia).
  assert (Hsplit : 2 ^ (Z.of_nat bits - 1 - 7 * to_Z i) * 2 ^ (7 * to_Z i)
                   = 2 ^ (Z.of_nat bits - 1)) by (apply pow2_split; lia).
  assert (Hpnn : 0 <= 2 ^ (7 * to_Z i)) by (apply Z.pow_nonneg; lia).
  assert (Hwnn : 0 <= 2 ^ (Z.of_nat bits - 1)) by (apply Z.pow_nonneg; lia).
  rewrite Hsb in Hbhi.
  (* the tight upper bound on the value *)
  assert (Hbm : b * 2 ^ (7 * to_Z i)
                <= (2 ^ (Z.of_nat bits - 1 - 7 * to_Z i) - 1)
                   * 2 ^ (7 * to_Z i))
    by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (Hexp2 : (2 ^ (Z.of_nat bits - 1 - 7 * to_Z i) - 1) * 2 ^ (7 * to_Z i)
                  = 2 ^ (Z.of_nat bits - 1) - 2 ^ (7 * to_Z i))
    by (rewrite Z.mul_sub_distr_r; rewrite Hsplit; ring).
  unfold reader_read_sn_leb_loop. rewrite loop_unfold. cbn beta iota.
  destruct (bytes_from_uncons data p b rest0 Hbs)
    as [bu [p2 [Hidx [Hz [Hadd [Hrest2 Hltp]]]]]].
  destruct (p s>= slice_len data) eqn:Hge;
    [exfalso; apply scalar_geb_true_ge in Hge; lia|].
  rewrite Hidx. cbn [bind]. rewrite Hadd. cbn [bind].
  destruct (u8_rem_128_ok bu) as [low [Hrem [Hlowval Hlowbd]]].
  rewrite Hrem. cbn [bind].
  assert (Hlowb : to_Z low = b)
    by (rewrite Hlowval; rewrite Hz; apply Z.rem_small; lia).
  destruct (cast_u8_i128_ok low) as [c [Hcast Hcval]].
  rewrite Hcast. cbn [bind].
  assert (Hlm0 : 0 <= to_Z low * to_Z mult) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hlm : to_Z low * to_Z mult <= 127 * to_Z mult)
    by (apply Z.mul_le_mono_nonneg_r; lia).
  destruct (i128_mul_ok c mult) as [prod [Hmul Hmulval]].
  { rewrite Hcval. lia. }
  rewrite Hmul. cbn [bind].
  destruct (i128_add_ok acc prod) as [sum [Hadd2 Hsumval]].
  { rewrite Hmulval. rewrite Hcval. lia. }
  rewrite Hadd2. cbn [bind].
  assert (Hsumv : to_Z sum = to_Z acc + b * to_Z mult)
    by (rewrite Hsumval; rewrite Hmulval; rewrite Hcval; rewrite Hlowb;
        reflexivity).
  assert (Hlt128 : (bu s< 128%u8) = true).
  { unfold scalar_ltb. apply Z.ltb_lt.
    assert (H128 : to_Z 128%u8 = 128) by reflexivity. lia. }
  rewrite Hlt128. cbn beta iota.
  assert (Hnneg : (low s>= 64%u8) = false).
  { apply scalar_lt_geb_false.
    assert (H64 : to_Z 64%u8 = 64) by reflexivity. lia. }
  rewrite Hnneg. cbn [bind].
  (* the value is between 0 and hi, so both checks pass *)
  assert (Hsum2 : to_Z sum = to_Z acc + b * 2 ^ (7 * to_Z i))
    by (rewrite Hsumv; rewrite Hpow; reflexivity).
  assert (Hacc2 : 0 <= to_Z acc < 2 ^ (7 * to_Z i))
    by (rewrite <- Hpow; exact Haccm).
  assert (Hrng : to_Z lo <= to_Z sum <= to_Z hi) by lia.
  assert (Hc1 : (sum s< lo) = false)
    by (unfold scalar_ltb; apply Z.ltb_ge; lia).
  rewrite Hc1.
  assert (Hc2 : (sum s> hi) = false)
    by (unfold scalar_gtb; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  rewrite Hc2. cbn beta iota.
  exists sum, p2. split; [reflexivity|]. split; [exact Hsumv | exact Hrest2].
Qed.

Lemma sn_loop_last_neg : forall bits data last lo hi acc mult p i b rest0,
  sleb_params bits last lo hi ->
  sleb_inv last acc mult i ->
  bytes_from data p = b :: rest0 ->
  64 <= b < 128 ->
  128 - 2 ^ (Z.of_nat (bits - 7 * Z.to_nat (to_Z i))%nat - 1) <= b ->
  exists v' p',
    reader_read_sn_leb_loop data last lo hi acc mult p i
      = Ok (Core_result_Result_Ok (v', p'))
    /\ to_Z v' = to_Z acc + (b - 128) * to_Z mult
    /\ bytes_from data p' = rest0.
Proof.
  intros bits data last lo hi acc mult p i b rest0 Hpar Hinv Hbs Hblo Hbhi.
  pose proof (sleb_bounds bits last lo hi acc mult i Hpar Hinv)
    as [Hmpos [Hmle [Haccm [Hbig' Hminmax]]]].
  pose proof Hpar as Hpar2. destruct Hpar2 as [Hbits [Hlov [Hhiv _]]].
  pose proof Hinv as Hinv2. destruct Hinv2 as [Hi [Hmult Hacc]].
  assert (Hexp : 7 * to_Z i <= Z.of_nat bits - 1) by lia.
  assert (Hpow : to_Z mult = 2 ^ (7 * to_Z i))
    by (rewrite Hmult; apply pow128_as_pow2; lia).
  assert (Hsb : Z.of_nat (bits - 7 * Z.to_nat (to_Z i))%nat - 1
                = Z.of_nat bits - 1 - 7 * to_Z i) by (apply sbits_eq; lia).
  assert (Hsplit : 2 ^ (Z.of_nat bits - 1 - 7 * to_Z i) * 2 ^ (7 * to_Z i)
                   = 2 ^ (Z.of_nat bits - 1)) by (apply pow2_split; lia).
  assert (Hpnn : 0 <= 2 ^ (7 * to_Z i)) by (apply Z.pow_nonneg; lia).
  assert (Hwnn : 0 <= 2 ^ (Z.of_nat bits - 1)) by (apply Z.pow_nonneg; lia).
  rewrite Hsb in Hbhi.
  (* the lower bound on the value *)
  assert (Hbm : - (2 ^ (Z.of_nat bits - 1 - 7 * to_Z i)) * 2 ^ (7 * to_Z i)
                <= (b - 128) * 2 ^ (7 * to_Z i))
    by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (Hexp2 : - (2 ^ (Z.of_nat bits - 1 - 7 * to_Z i)) * 2 ^ (7 * to_Z i)
                  = - 2 ^ (Z.of_nat bits - 1)).
  { replace (- (2 ^ (Z.of_nat bits - 1 - 7 * to_Z i)) * 2 ^ (7 * to_Z i))
       with (- (2 ^ (Z.of_nat bits - 1 - 7 * to_Z i) * 2 ^ (7 * to_Z i)))
       by ring.
    rewrite Hsplit. reflexivity. }
  assert (Hup : (b - 128) * 2 ^ (7 * to_Z i) <= - (2 ^ (7 * to_Z i))).
  { replace (- (2 ^ (7 * to_Z i))) with ((-1) * 2 ^ (7 * to_Z i)) by ring.
    apply Z.mul_le_mono_nonneg_r; lia. }
  unfold reader_read_sn_leb_loop. rewrite loop_unfold. cbn beta iota.
  destruct (bytes_from_uncons data p b rest0 Hbs)
    as [bu [p2 [Hidx [Hz [Hadd [Hrest2 Hltp]]]]]].
  destruct (p s>= slice_len data) eqn:Hge;
    [exfalso; apply scalar_geb_true_ge in Hge; lia|].
  rewrite Hidx. cbn [bind]. rewrite Hadd. cbn [bind].
  destruct (u8_rem_128_ok bu) as [low [Hrem [Hlowval Hlowbd]]].
  rewrite Hrem. cbn [bind].
  assert (Hlowb : to_Z low = b)
    by (rewrite Hlowval; rewrite Hz; apply Z.rem_small; lia).
  destruct (cast_u8_i128_ok low) as [c [Hcast Hcval]].
  rewrite Hcast. cbn [bind].
  assert (Hlm0 : 0 <= to_Z low * to_Z mult) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hlm : to_Z low * to_Z mult <= 127 * to_Z mult)
    by (apply Z.mul_le_mono_nonneg_r; lia).
  destruct (i128_mul_ok c mult) as [prod [Hmul Hmulval]].
  { rewrite Hcval. lia. }
  rewrite Hmul. cbn [bind].
  destruct (i128_add_ok acc prod) as [sum [Hadd2 Hsumval]].
  { rewrite Hmulval. rewrite Hcval. lia. }
  rewrite Hadd2. cbn [bind].
  assert (Hsumv : to_Z sum = to_Z acc + b * to_Z mult)
    by (rewrite Hsumval; rewrite Hmulval; rewrite Hcval; rewrite Hlowb;
        reflexivity).
  assert (Hlt128 : (bu s< 128%u8) = true).
  { unfold scalar_ltb. apply Z.ltb_lt.
    assert (H128 : to_Z 128%u8 = 128) by reflexivity. lia. }
  rewrite Hlt128. cbn beta iota.
  assert (Hneg : (low s>= 64%u8) = true).
  { apply scalar_ge_geb_true.
    assert (H64 : to_Z 64%u8 = 64) by reflexivity. lia. }
  rewrite Hneg. cbn beta iota.
  assert (H128i : to_Z 128%i128 = 128) by reflexivity.
  destruct (i128_mul_ok mult 128%i128) as [m128 [Hm128 Hm128val]].
  { rewrite H128i. lia. }
  rewrite Hm128. cbn [bind].
  assert (Hm128v : to_Z m128 = to_Z mult * 128)
    by (rewrite Hm128val; rewrite H128i; reflexivity).
  destruct (i128_sub_ok sum m128) as [acc3 [Hsub Hacc3val]].
  { rewrite Hm128v. rewrite Hsumv. lia. }
  rewrite Hsub. cbn [bind].
  assert (Hacc3 : to_Z acc3 = to_Z acc + (b - 128) * to_Z mult)
    by (rewrite Hacc3val; rewrite Hm128v; rewrite Hsumv; ring).
  (* the value is between lo and -1, so both checks pass *)
  assert (Hacc32 : to_Z acc3 = to_Z acc + (b - 128) * 2 ^ (7 * to_Z i))
    by (rewrite Hacc3; rewrite Hpow; reflexivity).
  assert (Hacc2 : 0 <= to_Z acc < 2 ^ (7 * to_Z i))
    by (rewrite <- Hpow; exact Haccm).
  assert (Hrng : to_Z lo <= to_Z acc3 <= to_Z hi) by lia.
  assert (Hc1 : (acc3 s< lo) = false)
    by (unfold scalar_ltb; apply Z.ltb_ge; lia).
  rewrite Hc1.
  assert (Hc2 : (acc3 s> hi) = false)
    by (unfold scalar_gtb; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  rewrite Hc2. cbn beta iota.
  exists acc3, p2. split; [reflexivity|]. split; [exact Hacc3 | exact Hrest2].
Qed.

Lemma read_sn_leb_loop_complete :
  forall n bits data last lo hi acc mult p i v rest,
  sleb_params bits last lo hi ->
  to_Z i + Z.of_nat n = to_Z last ->
  sleb_inv last acc mult i ->
  repr_sN (bits - 7 * Z.to_nat (to_Z i))%nat (bytes_from data p) v rest ->
  exists v' p',
    reader_read_sn_leb_loop data last lo hi acc mult p i
      = Ok (Core_result_Result_Ok (v', p'))
    /\ to_Z v' = to_Z acc + v * to_Z mult
    /\ bytes_from data p' = rest.
Proof.
  induction n as [|n IH];
    intros bits data last lo hi acc mult p i v rest Hpar Hn Hinv Hrep;
    destruct (repr_sN_inv _ _ _ _ Hrep)
      as [[b [r [Hbs [Hv [Hrest [Hblo Hbhi]]]]]]
         |[[b [r [Hbs [Hv [Hrest [Hblo Hbhi]]]]]]
          |[b [more [m [Hbs [Hv [Hblo [Hbits7 Hsub]]]]]]]]].
  (* the two last-byte shapes are the helpers, whatever the budget *)
  1,4: destruct (sn_loop_last_pos bits data last lo hi acc mult p i b r
                   Hpar Hinv Hbs Hblo Hbhi) as [v' [p' [Hrun [Hval Hb]]]];
       exists v', p'; split; [exact Hrun|];
       split; [rewrite Hval; rewrite Hv; reflexivity|];
       rewrite Hb; rewrite Hrest; reflexivity.
  1,3: destruct (sn_loop_last_neg bits data last lo hi acc mult p i b r
                   Hpar Hinv Hbs Hblo Hbhi) as [v' [p' [Hrun [Hval Hb]]]];
       exists v', p'; split; [exact Hrun|];
       split; [rewrite Hval; rewrite Hv; reflexivity|];
       rewrite Hb; rewrite Hrest; reflexivity.
  - (* a continuation byte with the budget spent: the specification forbids it,
       because [last] leaves at most seven bits for the final byte *)
    exfalso. destruct Hpar as [Hbits _]. destruct Hinv as [Hi _].
    assert (Hilast : to_Z i = to_Z last) by (cbn in Hn; lia). lia.
  - (* a continuation byte: fold it in and go round again *)
    pose proof (sleb_bounds bits last lo hi acc mult i Hpar Hinv)
      as [Hmpos [Hmle [Haccm [Hbig' Hminmax]]]].
    pose proof Hinv as Hinv2. destruct Hinv2 as [Hi [Hmult Hacc]].
    assert (Hilt : to_Z i < to_Z last) by (cbn in Hn; lia).
    assert (H128i : to_Z 128%i128 = 128) by reflexivity.
    unfold reader_read_sn_leb_loop. rewrite loop_unfold. cbn beta iota.
    destruct (bytes_from_uncons data p b more Hbs)
      as [bu [p2 [Hidx [Hz [Hadd [Hrest2 Hltp]]]]]].
    destruct (p s>= slice_len data) eqn:Hge;
      [exfalso; apply scalar_geb_true_ge in Hge; lia|].
    rewrite Hidx. cbn [bind]. rewrite Hadd. cbn [bind].
    destruct (u8_rem_128_ok bu) as [low [Hrem [Hlowval Hlowbd]]].
    rewrite Hrem. cbn [bind].
    assert (Hrem128 : forall x, 128 <= x < 256 -> Z.rem x 128 = x - 128).
    { intros x Hx. rewrite Z.rem_mod_nonneg by lia.
      assert (Hy : x mod 128 = (x - 128) mod 128).
      { replace (x - 128) with (x + (-1) * 128) by lia.
        rewrite Z.mod_add by lia. reflexivity. }
      rewrite Hy. apply Z.mod_small. lia. }
    assert (Hlowb : to_Z low = b - 128)
      by (rewrite Hlowval; rewrite Hz; apply Hrem128; lia).
    destruct (cast_u8_i128_ok low) as [c [Hcast Hcval]].
    rewrite Hcast. cbn [bind].
    assert (Hlm0 : 0 <= to_Z low * to_Z mult)
      by (apply Z.mul_nonneg_nonneg; lia).
    assert (Hlm : to_Z low * to_Z mult <= 127 * to_Z mult)
      by (apply Z.mul_le_mono_nonneg_r; lia).
    destruct (i128_mul_ok c mult) as [prod [Hmul Hmulval]].
    { rewrite Hcval. lia. }
    rewrite Hmul. cbn [bind].
    destruct (i128_add_ok acc prod) as [sum [Hadd2 Hsumval]].
    { rewrite Hmulval. rewrite Hcval. lia. }
    rewrite Hadd2. cbn [bind].
    assert (Hsumv : to_Z sum = to_Z acc + to_Z low * to_Z mult)
      by (rewrite Hsumval; rewrite Hmulval; rewrite Hcval; reflexivity).
    assert (Hnlt : (bu s< 128%u8) = false).
    { unfold scalar_ltb. apply Z.ltb_ge.
      assert (H128 : to_Z 128%u8 = 128) by reflexivity. lia. }
    rewrite Hnlt. cbn beta iota.
    assert (Heq : (i s= last) = false)
      by (unfold scalar_eqb; apply Z.eqb_neq; lia).
    rewrite Heq. cbn beta iota.
    destruct (i128_mul_ok mult 128%i128) as [mult2 [Hm2 Hm2val]].
    { rewrite H128i. lia. }
    rewrite Hm2. cbn [bind].
    assert (H1u : to_Z 1%u32 = 1) by reflexivity.
    destruct (u32_add_ok i 1%u32) as [i5 [Hi5 Hi5val]].
    { rewrite H1u. pose proof (u32_bounds last) as [_ Hlm2]. lia. }
    rewrite Hi5. cbn [bind].
    assert (Hi5v : to_Z i5 = to_Z i + 1) by (rewrite Hi5val; rewrite H1u; lia).
    assert (Hm2v : to_Z mult2 = 128 ^ (to_Z i + 1)).
    { rewrite Hm2val. rewrite H128i. rewrite Hmult.
      rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r. ring. }
    (* the sub-derivation drives the next iteration *)
    destruct (IH bits data last lo hi sum mult2 p2 i5 m rest)
      as [v' [p' [Hrun [Hval Hb]]]].
    + exact Hpar.
    + rewrite Hi5v. cbn in Hn. lia.
    + unfold sleb_inv. rewrite Hi5v. rewrite Hm2v. split; [lia|].
      split; [reflexivity|]. rewrite Hsumv. rewrite Z.pow_add_r by lia.
      rewrite Z.pow_1_r. rewrite <- Hmult. lia.
    + assert (Hbits' : (bits - 7 * Z.to_nat (to_Z i5))%nat
                       = (bits - 7 * Z.to_nat (to_Z i) - 7)%nat).
      { rewrite Hi5v. rewrite (Z_to_nat_add1 _ (proj1 Hi)). lia. }
      rewrite Hbits'. rewrite Hrest2. exact Hsub.
    + exists v', p'. split; [exact Hrun|]. split; [|exact Hb].
      rewrite Hval. rewrite Hsumv. rewrite Hm2v. rewrite Hlowb.
      rewrite Hmult. rewrite Hv. rewrite Z.pow_add_r by lia.
      rewrite Z.pow_1_r. ring.
Qed.

Theorem read_s32_leb_complete : forall data pos v rest,
  repr_s32 (bytes_from data pos) v rest ->
  exists v' pos',
    reader_read_s32_leb data pos = Ok (Core_result_Result_Ok (v', pos'))
    /\ to_Z v' = v
    /\ bytes_from data pos' = rest.
Proof.
  intros data pos v rest H.
  assert (Hstart : sleb_inv 4%u32 0%i128 1%i128 0%u32)
    by (unfold sleb_inv; cbn; lia).
  assert (Hn : to_Z 0%u32 + Z.of_nat 4 = to_Z 4%u32) by reflexivity.
  destruct (read_sn_leb_loop_complete 4 32 data 4%u32 (-2147483648)%i128
              2147483647%i128 0%i128 1%i128 pos 0%u32 v rest sleb_params_32
              Hn Hstart) as [v0 [p0 [Hleb [Hval Hb]]]].
  { replace (32 - 7 * Z.to_nat (to_Z 0%u32))%nat with 32%nat by reflexivity.
    exact H. }
  destruct (read_sn_leb_loop_sound 4 32 data 4%u32 (-2147483648)%i128
              2147483647%i128 0%i128 1%i128 pos 0%u32 v0 p0
              sleb_params_32 Hn Hstart Hleb) as [m [_ [_ Hrng]]].
  assert (Hlov : to_Z (-2147483648)%i128 = -2147483648) by reflexivity.
  assert (Hhiv : to_Z 2147483647%i128 = 2147483647) by reflexivity.
  destruct (cast_i128_i32_ok v0) as [v1 [Hc Hcv]].
  { rewrite i32_min_val. rewrite i32_max_val. lia. }
  exists v1, p0. split.
  { unfold reader_read_s32_leb, reader_read_sn_leb. rewrite Hleb. cbn [bind].
    rewrite branch_ok. cbn [bind]. rewrite Hc. cbn [bind]. reflexivity. }
  split; [rewrite Hcv; rewrite Hval; cbn; lia | exact Hb].
Qed.

Theorem read_s64_leb_complete : forall data pos v rest,
  repr_sN 64 (bytes_from data pos) v rest ->
  exists v' pos',
    reader_read_s64_leb data pos = Ok (Core_result_Result_Ok (v', pos'))
    /\ to_Z v' = v
    /\ bytes_from data pos' = rest.
Proof.
  intros data pos v rest H.
  assert (Hstart : sleb_inv 9%u32 0%i128 1%i128 0%u32)
    by (unfold sleb_inv; cbn; lia).
  assert (Hn : to_Z 0%u32 + Z.of_nat 9 = to_Z 9%u32) by reflexivity.
  destruct (read_sn_leb_loop_complete 9 64 data 9%u32
              (-9223372036854775808)%i128 9223372036854775807%i128 0%i128
              1%i128 pos 0%u32 v rest sleb_params_64 Hn Hstart)
    as [v0 [p0 [Hleb [Hval Hb]]]].
  { replace (64 - 7 * Z.to_nat (to_Z 0%u32))%nat with 64%nat by reflexivity.
    exact H. }
  destruct (read_sn_leb_loop_sound 9 64 data 9%u32 (-9223372036854775808)%i128
              9223372036854775807%i128 0%i128 1%i128 pos 0%u32 v0 p0
              sleb_params_64 Hn Hstart Hleb) as [m [_ [_ Hrng]]].
  assert (Hlov : to_Z (-9223372036854775808)%i128 = -9223372036854775808)
    by reflexivity.
  assert (Hhiv : to_Z 9223372036854775807%i128 = 9223372036854775807)
    by reflexivity.
  destruct (cast_i128_i64_ok v0) as [v1 [Hc Hcv]].
  { rewrite i64_min_val. rewrite i64_max_val. lia. }
  exists v1, p0. split.
  { unfold reader_read_s64_leb, reader_read_sn_leb. rewrite Hleb. cbn [bind].
    rewrite branch_ok. cbn [bind]. rewrite Hc. cbn [bind]. reflexivity. }
  split; [rewrite Hcv; rewrite Hval; cbn; lia | exact Hb].
Qed.

(** The block type and the memarg. One byte and two [u32]s respectively, so both
    fall straight out of the readers above. The block type's table has to be
    walked in the other direction: the specification's row fixes the byte, and the
    code's comparison chain then has to reach the matching arm. *)
Lemma read_block_type_complete : forall data pos bb bt rest,
  bytes_from data pos = bb :: rest ->
  blocktype_spec bb = Some bt ->
  exists bt' pos',
    opiter_read_block_type data pos = Ok (Core_result_Result_Ok (bt', pos'))
    /\ translate_bt bt' = bt
    /\ bytes_from data pos' = rest.
Proof.
  intros data pos bb bt rest Hbs Hspec.
  destruct (read_byte_complete data pos bb rest Hbs) as [b [p2 [Hrb [Hz Hrest]]]].
  unfold opiter_read_block_type. rewrite Hrb. cbn [bind].
  rewrite branch_ok. cbn [bind].
  (* one arm per row of the table; the specification's row fixes the byte *)
  unfold blocktype_spec, valtype_spec in Hspec.
  destruct (b s= 64%u8) eqn:E64.
  { apply scalar_eqb_true in E64.
    assert (H : bb = 64) by (rewrite <- Hz; exact E64).
    rewrite H in Hspec. cbn in Hspec. injection Hspec as <-.
    exists Opiter_BlockType_Empty, p2. split; [reflexivity|].
    split; [reflexivity | exact Hrest]. }
  destruct (b s= 127%u8) eqn:E127.
  { apply scalar_eqb_true in E127.
    assert (H : bb = 127) by (rewrite <- Hz; exact E127).
    rewrite H in Hspec. cbn in Hspec. injection Hspec as <-.
    exists (Opiter_BlockType_Value Types_ValueType_I32), p2. split; [reflexivity|].
    split; [reflexivity | exact Hrest]. }
  destruct (b s= 126%u8) eqn:E126.
  { apply scalar_eqb_true in E126.
    assert (H : bb = 126) by (rewrite <- Hz; exact E126).
    rewrite H in Hspec. cbn in Hspec. injection Hspec as <-.
    exists (Opiter_BlockType_Value Types_ValueType_I64), p2. split; [reflexivity|].
    split; [reflexivity | exact Hrest]. }
  destruct (b s= 125%u8) eqn:E125.
  { apply scalar_eqb_true in E125.
    assert (H : bb = 125) by (rewrite <- Hz; exact E125).
    rewrite H in Hspec. cbn in Hspec. injection Hspec as <-.
    exists (Opiter_BlockType_Value Types_ValueType_F32), p2. split; [reflexivity|].
    split; [reflexivity | exact Hrest]. }
  destruct (b s= 124%u8) eqn:E124.
  { apply scalar_eqb_true in E124.
    assert (H : bb = 124) by (rewrite <- Hz; exact E124).
    rewrite H in Hspec. cbn in Hspec. injection Hspec as <-.
    exists (Opiter_BlockType_Value Types_ValueType_F64), p2. split; [reflexivity|].
    split; [reflexivity | exact Hrest]. }
  (* no row matched, so the specification cannot have admitted the byte *)
  exfalso. apply scalar_eqb_false in E64. apply scalar_eqb_false in E127.
  apply scalar_eqb_false in E126. apply scalar_eqb_false in E125.
  apply scalar_eqb_false in E124.
  assert (H64 : to_Z 64%u8 = 64) by reflexivity.
  assert (H127 : to_Z 127%u8 = 127) by reflexivity.
  assert (H126 : to_Z 126%u8 = 126) by reflexivity.
  assert (H125 : to_Z 125%u8 = 125) by reflexivity.
  assert (H124 : to_Z 124%u8 = 124) by reflexivity.
  destruct (Z.eqb bb 64) eqn:Q64; [apply Z.eqb_eq in Q64; lia|].
  destruct (Z.eqb bb 127) eqn:Q127; [apply Z.eqb_eq in Q127; lia|].
  destruct (Z.eqb bb 126) eqn:Q126; [apply Z.eqb_eq in Q126; lia|].
  destruct (Z.eqb bb 125) eqn:Q125; [apply Z.eqb_eq in Q125; lia|].
  destruct (Z.eqb bb 124) eqn:Q124; [apply Z.eqb_eq in Q124; lia|].
  discriminate.
Qed.

Lemma read_memarg_complete : forall st data a o rest,
  repr_memarg (bytes_from data st.(opiter_OpIterState_pos)) (a, o) rest ->
  exists m st',
    opiter_read_memarg st data = Ok (Core_result_Result_Ok m, st')
    /\ to_Z m.(opiter_MemArg_align) = a
    /\ to_Z m.(opiter_MemArg_offset) = o
    /\ bytes_from data st'.(opiter_OpIterState_pos) = rest.
Proof.
  intros st data a o rest H.
  destruct (repr_memarg_inv _ _ _ _ H) as [mid [Ha Ho]].
  unfold opiter_read_memarg.
  destruct (read_u32_leb_complete data st.(opiter_OpIterState_pos) a mid Ha)
    as [av [p1 [Hr1 [Hav Hb1]]]].
  rewrite Hr1. cbn [bind]. rewrite branch_ok. cbn [bind].
  rewrite <- Hb1 in Ho.
  destruct (read_u32_leb_complete data p1 o rest Ho)
    as [ov [p2 [Hr2 [Hov Hb2]]]].
  rewrite Hr2. cbn [bind]. rewrite branch_ok. cbn [bind].
  eexists. eexists. split; [reflexivity|].
  cbn [opiter_MemArg_align opiter_MemArg_offset opiter_OpIterState_pos].
  split; [exact Hav|]. split; [exact Hov | exact Hb2].
Qed.

(** [read_op] just takes the byte, so any byte the specification puts there is
    read. What it means is the caller's business. *)
Lemma read_op_complete : forall st data z rest,
  bytes_from data st.(opiter_OpIterState_pos) = z :: rest ->
  exists b st',
    opiter_read_op st data = Ok (Core_result_Result_Ok b, st')
    /\ to_Z b = z
    /\ bytes_from data st'.(opiter_OpIterState_pos) = rest
    /\ vec_list st'.(opiter_OpIterState_vals)
       = vec_list st.(opiter_OpIterState_vals)
    /\ vec_list st'.(opiter_OpIterState_ctrls)
       = vec_list st.(opiter_OpIterState_ctrls).
Proof.
  intros st data z rest H.
  destruct (read_byte_complete data st.(opiter_OpIterState_pos) z rest H)
    as [b [p2 [Hrb [Hz Hrest]]]].
  unfold opiter_read_op. rewrite Hrb. cbn [bind]. rewrite branch_ok.
  cbn [bind]. eexists. eexists. split; [reflexivity|].
  cbn [opiter_OpIterState_pos opiter_OpIterState_vals opiter_OpIterState_ctrls].
  split; [exact Hz|]. split; [exact Hrest|]. split; reflexivity.
Qed.
