(** * The module decoder reads what the format says

    The soundness direction for everything around a function body. Where
    [OpIter_Validate.v] shows an accepting run of [validate_body] means the
    bytes encode a well-typed instruction sequence, this file works up to the
    same statement for [validate_module], against [Spec_Module.repr_module] and
    WasmCert's [module_type_checker].

    Two halves, and this file is the first of them: every decoder reads what
    [Spec_Module.v] says it reads. Each lemma has the same shape,

      decode_x data pos = Ok (Ok (v, p'))
      -> repr_x (bytes_from data pos) (translate_x v) (bytes_from data p')

    which reads "the bytes between the two cursors encode [v]". Positions rather
    than sub-slices is what [module.rs] does, and [bytes_from data pos] is the
    suffix at a cursor, so a decoder's step is a prefix of one suffix leaving
    the next. *)

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
Require Import Itasca.Spec_Expr.
Require Import Itasca.Spec_Module.
Require Import Itasca.OpIter_Visit.
Require Import Itasca.OpIter_Decode.
Require Import Itasca.OpIter_Sim.
Require Import Itasca.OpIter_Validate.
Require Import Itasca.Module_NoPanic.

From Wasm Require Import datatypes typing type_checker.

Local Open Scope list_scope.
Open Scope Z_scope.

(** [lia] does not see through [Z.to_nat], and every vector loop below counts
    down to zero through one. *)
Lemma to_nat_nonpos : forall z, z <= 0 -> Z.to_nat z = 0%nat.
Proof. intros z Hz. destruct z; [reflexivity | lia | reflexivity]. Qed.

(* ================================================================== *)
(** ** The byte stream at a plain [Z]                                  *)
(* ================================================================== *)

(** [bytes_from] is indexed by a cursor, but it only ever looks at the cursor's
    numeric value, and a run of bytes is much easier to walk one step removed
    from the scalars: the offsets in a UTF-8 sequence or a copied range are
    then [z + 1], [z + 2], [z + 3] rather than a chain of [usize_add]s. *)
Definition bytes_at (data : slice u8) (z : Z) : list Z :=
  List.skipn (Z.to_nat z) (byte_list data).

Lemma bytes_from_at : forall data pos,
  bytes_from data pos = bytes_at data (to_Z pos).
Proof. reflexivity. Qed.

Lemma bytes_at_congr : forall data z z',
  z = z' -> bytes_at data z = bytes_at data z'.
Proof. intros data z z' ->. reflexivity. Qed.

(** A byte that indexes reads off the front of the stream at its position. *)
Lemma bytes_at_index : forall data (i : usize) b,
  slice_index_usize data i = Ok b ->
  bytes_at data (to_Z i) = to_Z b :: bytes_at data (to_Z i + 1).
Proof.
  intros data i b H. rewrite slice_index_usize_spec in H.
  destruct (List.nth_error (vec_list data) (Z.to_nat (to_Z i))) as [b0|] eqn:Hnth;
    [|discriminate].
  injection H as <-. unfold bytes_at, byte_list.
  rewrite Z_to_nat_add1 by apply usize_nonneg.
  apply (skipn_map_nth to_Z _ _ _ Hnth).
Qed.

Lemma bytes_at_tail : forall data z b l,
  0 <= z -> bytes_at data z = b :: l -> l = bytes_at data (z + 1).
Proof.
  intros data z b l Hz Heq. unfold bytes_at in *.
  rewrite Z_to_nat_add1 by lia.
  replace (S (Z.to_nat z)) with (1 + Z.to_nat z)%nat by lia.
  rewrite <- List.skipn_skipn. rewrite Heq. reflexivity.
Qed.

Lemma bytes_at_skipn : forall data z k,
  0 <= z -> bytes_at data (z + Z.of_nat k) = List.skipn k (bytes_at data z).
Proof.
  intros data z k Hz. unfold bytes_at. rewrite List.skipn_skipn. f_equal.
  rewrite Z2Nat.inj_add by lia. rewrite Nat2Z.id. lia.
Qed.

(** [byte_list] is a [map] by [to_Z], whose domain Coq spells [scalar U8] where
    a slice's element type is spelt [u8]. The two are convertible but [lia]
    treats them as different atoms, so every length fact goes through this. *)
Lemma byte_list_length : forall data,
  List.length (byte_list data) = List.length (vec_list data).
Proof. intros data. unfold byte_list. apply List.map_length. Qed.

Lemma bytes_at_end : forall data z,
  Z.of_nat (List.length (vec_list data)) <= z -> bytes_at data z = [].
Proof.
  intros data z Hz. unfold bytes_at. apply List.skipn_all2.
  rewrite byte_list_length.
  pose proof (Nat2Z.is_nonneg (List.length (vec_list data))).
  apply Nat2Z.inj_le. rewrite Z2Nat.id by lia. exact Hz.
Qed.

(** A run that fits inside the input is a run the stream really has. *)
Lemma bytes_at_length_ge : forall data z k,
  0 <= z -> 0 <= k ->
  z + k <= Z.of_nat (List.length (vec_list data)) ->
  (Z.to_nat k <= List.length (bytes_at data z))%nat.
Proof.
  intros data z k Hz Hk0 Hk. unfold bytes_at.
  rewrite List.skipn_length. rewrite byte_list_length.
  apply Nat2Z.inj_le.
  rewrite Nat2Z.inj_sub by (apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; lia).
  rewrite Z2Nat.id by lia. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma bytes_at_head_bounded : forall data z b l,
  bytes_at data z = b :: l -> 0 <= b < 256.
Proof.
  intros data z b l Heq. eapply byte_list_bounded.
  unfold bytes_at in Heq.
  rewrite <- (List.firstn_skipn (Z.to_nat z) (byte_list data)).
  apply List.in_or_app. right. rewrite Heq. left. reflexivity.
Qed.

(** [repr_rep repr_byte] over a run that is really there: [vec(byte)]'s
    element relation says nothing but that each byte is a byte, so the whole
    content of the premise is that the stream has that many left. *)
Lemma repr_rep_byte_firstn : forall k data z,
  0 <= z ->
  (k <= List.length (bytes_at data z))%nat ->
  repr_rep repr_byte k (bytes_at data z) (List.firstn k (bytes_at data z))
    (bytes_at data (z + Z.of_nat k)).
Proof.
  induction k as [|k IH]; intros data z Hz Hk.
  - cbn [List.firstn]. rewrite (bytes_at_congr data (z + Z.of_nat 0) z) by lia.
    apply repr_rep_nil.
  - destruct (bytes_at data z) as [|b l] eqn:Hb; [cbn in Hk; lia|].
    assert (Hl : l = bytes_at data (z + 1)) by (eapply bytes_at_tail; eauto).
    cbn [List.firstn].
    rewrite (bytes_at_congr data (z + Z.of_nat (S k)) (z + 1 + Z.of_nat k))
      by lia.
    eapply repr_rep_cons.
    + apply repr_byte_intro. eapply bytes_at_head_bounded. exact Hb.
    + rewrite Hl. apply IH; [lia|].
      rewrite <- Hl. cbn [List.length] in Hk. lia.
Qed.

(* ================================================================== *)
(** ** Copying a byte range                                            *)
(* ================================================================== *)

(** [copy_bytes] is the only allocation the decoder makes that is a byte range
    rather than a decoded item, and it is what a name and a data segment's
    contents are made of. It copies [to - from] bytes, and the second half of
    the conclusion says they were really there: the loop indexes the input, so
    an accepting run is itself the proof that the range is inside it. *)
Lemma copy_bytes_loop_sound : forall m data to out i v,
  to_Z to - to_Z i <= Z.of_nat m ->
  module_copy_bytes_loop data to out i = Ok v ->
  List.map to_Z (vec_list v)
    = List.map to_Z (vec_list out)
      ++ List.firstn (Z.to_nat (to_Z to - to_Z i)) (bytes_at data (to_Z i))
  /\ (Z.to_nat (to_Z to - to_Z i)
        <= List.length (bytes_at data (to_Z i)))%nat.
Proof.
  induction m as [|m IH]; intros data to out i v Hmeas H;
    unfold module_copy_bytes_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (i s>= to) eqn:Hge.
  1,3: injection H as <-; apply scalar_geb_true_ge in Hge;
       rewrite to_nat_nonpos by lia; cbn [List.firstn];
       rewrite app_nil_r; split; [reflexivity | lia].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (slice_index_usize data i) as [b|] eqn:Hidx; cbn [bind] in H;
      [|discriminate].
    destruct (alloc_vec_Vec_push out b) as [out2|] eqn:Hpush; cbn [bind] in H;
      [|discriminate].
    destruct (usize_add i 1%usize) as [i2|] eqn:Hadd; cbn [bind] in H;
      [|discriminate].
    pose proof (scalar_add_val _ _ _ 1 Hadd eq_refl) as Hi2.
    destruct (IH data to out2 i2 v (ltac:(cbn in Hmeas; lia)) H)
      as [Hmap Hlen].
    rewrite Hi2 in Hmap. rewrite Hi2 in Hlen.
    assert (Hcnt : Z.to_nat (to_Z to - to_Z i)
                   = S (Z.to_nat (to_Z to - (to_Z i + 1)))).
    { assert (Hsplit : to_Z to - to_Z i = (to_Z to - (to_Z i + 1)) + 1) by lia.
      rewrite Hsplit. apply Z_to_nat_add1. lia. }
    rewrite Hcnt. rewrite (bytes_at_index data i b Hidx).
    cbn [List.firstn List.length]. split; [|lia].
    rewrite Hmap. rewrite (vec_push_spec _ _ _ Hpush).
    rewrite List.map_app. cbn [List.map]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma copy_bytes_sound : forall data from to v,
  module_copy_bytes data from to = Ok v ->
  List.map to_Z (vec_list v)
    = List.firstn (Z.to_nat (to_Z to - to_Z from)) (bytes_at data (to_Z from))
  /\ (Z.to_nat (to_Z to - to_Z from)
        <= List.length (bytes_at data (to_Z from)))%nat.
Proof.
  intros data from to v H. unfold module_copy_bytes in H.
  destruct (copy_bytes_loop_sound (Z.to_nat (to_Z to)) data to
              (alloc_vec_Vec_new u8) from v) as [Hmap Hlen].
  - rewrite Z2Nat.id by apply usize_nonneg.
    pose proof (usize_nonneg from). lia.
  - exact H.
  - split; [|exact Hlen].
    rewrite Hmap.
    cbn [vec_list alloc_vec_Vec_new proj1_sig List.map List.app]. reflexivity.
Qed.

(* ================================================================== *)
(** ** 5.2.4 Names, and the UTF-8 table                                *)
(* ================================================================== *)

(** One accepted continuation byte. The position it sits at and the position
    after it are both given, so that a sequence's bytes chain without any
    renormalising in between: the reader computes [i+1], [i+2] and [i+3] from
    [i], but a decomposition has to spell each step's tail the way the next
    step's head is spelt. *)
Lemma utf8_cont_at : forall bytes (j : usize) lo hi klo khi z z',
  module_utf8_cont bytes j lo hi = Ok (Core_result_Result_Ok tt) ->
  to_Z lo = klo -> to_Z hi = khi -> to_Z j = z -> z' = z + 1 ->
  exists b, bytes_at bytes z = b :: bytes_at bytes z' /\ klo <= b <= khi.
Proof.
  intros bytes j lo hi klo khi z z' H <- <- <- ->.
  unfold module_utf8_cont in H.
  destruct (j s>= slice_len bytes); [discriminate|].
  destruct (slice_index_usize bytes j) as [b|] eqn:Hidx; cbn [bind] in H;
    [|discriminate].
  destruct (b s< lo) eqn:Hlo; [discriminate|].
  destruct (b s> hi) eqn:Hhi; [discriminate|].
  exists (to_Z b). split; [exact (bytes_at_index _ _ _ Hidx)|].
  apply scalar_ltb_false in Hlo. apply scalar_gtb_false in Hhi. lia.
Qed.

(** *** Walking the ten-arm chain

    [utf8_sequence_len]'s [if] chain is Unicode's table of well-formed byte
    sequences, and each arm is one constructor of [utf8_valid]. The chain is
    not ten arms in the extraction, though: Aeneas compiles [a || b || c] with
    one body by duplicating the body, so [(b >= 0xE1 && b <= 0xEC) || b == 0xEE
    || b == 0xEF] and the [&&]s around it turn the ten arms into a tree with
    the later ones repeated. Writing each out by hand would be writing several
    of them twice, so the four tactics below walk whatever tree the extraction
    produces: destruct every guard, peel every read, then chain the bytes and
    let the constructor be chosen by which one's side conditions hold. *)

(** A guard against a literal, kept as a fact about that literal's *value*:
    [lia] cannot see that [to_Z 127%u8] is [127]. Only the taken branch records
    anything, because that is the only side an arm's constraint comes from. *)
Ltac byte_guard H :=
  match type of H with
  | context [if ?c then _ else _] =>
      match c with
      | (?x s<= ?y) =>
          let E := fresh "E" in
          let v := eval vm_compute in (to_Z y) in
          destruct (x s<= y) eqn:E;
            [pose proof (scalar_leb_val x y v E eq_refl)|]
      | (?x s>= ?y) =>
          let E := fresh "E" in
          let v := eval vm_compute in (to_Z y) in
          destruct (x s>= y) eqn:E;
            [pose proof (scalar_geb_val x y v E eq_refl)|]
      | (?x s= ?y) =>
          let E := fresh "E" in
          let v := eval vm_compute in (to_Z y) in
          destruct (x s= y) eqn:E;
            [pose proof (scalar_eqb_val x y v E eq_refl)|]
      end
  end.

(** One read out of an arm: a continuation byte, or the [usize_add] that
    computes where the next one is. The [utf8_cont] case comes first because
    until its position has been named it sits under a binder and cannot be
    matched, which is what makes the alternation walk the arm in order. *)
Ltac utf8_peel H :=
  match type of H with
  | context [module_utf8_cont ?bs ?j ?lo ?hi] =>
      let r := fresh "r" in let E := fresh "E" in
      let z := fresh "z" in let Hz := fresh "Hz" in let Hr := fresh "Hr" in
      let klo := eval vm_compute in (to_Z lo) in
      let khi := eval vm_compute in (to_Z hi) in
      destruct (module_utf8_cont bs j lo hi) as [r|] eqn:E; cbn [bind] in H;
        [|discriminate];
      destruct r as [[]|?];
      [ rewrite branch_ok in H; cbn [bind] in H;
        destruct (utf8_cont_at bs j lo hi klo khi (to_Z j) (to_Z j + 1)
                    E eq_refl eq_refl eq_refl eq_refl) as [z [Hz Hr]]
      | try_err_rw_in H; discriminate ]
  | context [usize_add ?i ?k] =>
      let j := fresh "j" in let E := fresh "E" in
      let v := eval vm_compute in (to_Z k) in
      destruct (usize_add i k) as [j|] eqn:E; cbn [bind] in H; [|discriminate];
      pose proof (scalar_add_val i j k v E eq_refl)
  end.

(** Splice the byte at the stream's current head onto the front. The two
    positions are equal but not spelt alike, which is what [bytes_at_congr]
    and its [lia] side condition carry. *)
Ltac chain_step bytes :=
  match goal with
  | [ Hz : bytes_at bytes ?p = _ |- context [bytes_at bytes ?q] ] =>
      tryif constr_eq p q then fail else
      rewrite (bytes_at_congr bytes q p ltac:(lia)); rewrite Hz
  end.

Ltac chain_finish bytes Htl :=
  match type of Htl with
  | utf8_valid (bytes_at bytes ?p) =>
      match goal with
      | [ |- context [bytes_at bytes ?q] ] =>
          tryif constr_eq p q then idtac else
          rewrite (bytes_at_congr bytes q p ltac:(lia))
      end
  end.

(** A lead byte the table pins to one value has to appear as that value for
    its constructor to apply. *)
Ltac fix_head :=
  repeat match goal with
         | [ E : to_Z ?x = ?v |- context [to_Z ?x] ] => rewrite E
         end.

Ltac utf8_arm bytes i b n H Hb0 :=
  repeat utf8_peel H;
  let Hn := fresh "Hn" in injection H as Hn;
  (* the length comes back as a [usize] literal, and [subst] on one of those
     loses the notation, so cross to [Z] before touching it *)
  apply (f_equal to_Z) in Hn;
  match type of Hn with
  | ?e = _ => let v := eval vm_compute in e in change e with v in Hn
  end;
  rewrite <- Hn;
  split; [lia|];
  let Htl := fresh "Htl" in intros Htl;
  rewrite Hb0; repeat chain_step bytes; chain_finish bytes Htl; fix_head;
  solve [ apply utf8_one;        [lia | exact Htl]
        | apply utf8_two;        [lia | lia | exact Htl]
        | apply utf8_three_e0;   [lia | lia | exact Htl]
        | apply utf8_three_ed;   [lia | lia | exact Htl]
        | apply utf8_three_mid;  [lia | lia | lia | exact Htl]
        | apply utf8_three_high; [lia | lia | lia | exact Htl]
        | apply utf8_four_f0;    [lia | lia | lia | exact Htl]
        | apply utf8_four_f4;    [lia | lia | lia | exact Htl]
        | apply utf8_four_mid;   [lia | lia | lia | lia | exact Htl] ].

(** Spec 5.2.4's side condition, one sequence at a time. Stated as "the stream
    at [i] is valid if the stream past the sequence is", which is exactly the
    step the loop below takes and needs no prefix to be named. *)
Lemma utf8_sequence_len_sound : forall bytes i n,
  module_utf8_sequence_len bytes i = Ok (Core_result_Result_Ok n) ->
  1 <= to_Z n
  /\ (utf8_valid (bytes_at bytes (to_Z i + to_Z n)) ->
      utf8_valid (bytes_at bytes (to_Z i))).
Proof.
  intros bytes i n H. unfold module_utf8_sequence_len in H.
  destruct (slice_index_usize bytes i) as [b|] eqn:Hidx; cbn [bind] in H;
    [|discriminate].
  pose proof (bytes_at_index bytes i b Hidx) as Hb0.
  pose proof (u8_bounds b) as Hbb.
  repeat byte_guard H.
  all: try discriminate.
  all: utf8_arm bytes i b n H Hb0.
Qed.

(** The loop, which walks the whole vector one sequence at a time. Every
    sequence is at least one byte, which is what makes the measure decrease. *)
Lemma validate_utf8_loop_sound : forall m bytes i,
  Z.of_nat (List.length (vec_list bytes)) - to_Z i <= Z.of_nat m ->
  module_validate_utf8_loop bytes i = Ok (Core_result_Result_Ok tt) ->
  utf8_valid (bytes_at bytes (to_Z i)).
Proof.
  induction m as [|m IH]; intros bytes i Hmeas H;
    unfold module_validate_utf8_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (i s>= slice_len bytes) eqn:Hge.
  1,3: rewrite bytes_at_end; [apply utf8_nil|];
       apply scalar_geb_true_ge in Hge; rewrite slice_len_spec in Hge; lia.
  - exfalso. apply scalar_geb_false_lt in Hge.
    rewrite slice_len_spec in Hge. cbn in Hmeas. lia.
  - destruct (module_utf8_sequence_len bytes i) as [r|] eqn:Hseq;
      cbn [bind] in H; [|discriminate].
    destruct r as [n|]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (usize_add i n) as [i2|] eqn:Hadd; cbn [bind] in H;
      [|discriminate].
    pose proof (scalar_add_val _ _ _ (to_Z n) Hadd eq_refl) as Hi2.
    destruct (utf8_sequence_len_sound _ _ _ Hseq) as [Hn1 Himp].
    apply Himp. rewrite <- Hi2.
    apply IH; [|exact H].
    apply scalar_geb_false_lt in Hge. rewrite slice_len_spec in Hge.
    cbn in Hmeas. lia.
Qed.

Lemma validate_utf8_sound : forall bytes,
  module_validate_utf8 bytes = Ok (Core_result_Result_Ok tt) ->
  utf8_valid (byte_list bytes).
Proof.
  intros bytes H. unfold module_validate_utf8 in H.
  apply (validate_utf8_loop_sound (List.length (vec_list bytes)) bytes 0%usize).
  - assert (H0 : to_Z 0%usize = 0) by reflexivity. lia.
  - exact H.
Qed.

(** Spec 5.1.3's [vec(byte)], which is what a name and a data segment's
    contents are both built on: a length prefix, then that many bytes copied
    out of the input. *)
(* [len] is annotated because WasmCert's [datatypes.v] defines [u32 : Set := N]
   and shadows Primitives' scalar type. *)
Lemma decode_bytevec_sound : forall data (pos p p' : usize) (len : scalar U32) v,
  repr_u32 (bytes_at data (to_Z pos)) (to_Z len) (bytes_at data (to_Z p)) ->
  module_copy_bytes data p p' = Ok v ->
  to_Z p' = to_Z p + to_Z len ->
  repr_vec repr_byte (bytes_at data (to_Z pos))
    (List.map to_Z (vec_list v)) (bytes_at data (to_Z p')).
Proof.
  intros data pos p p' len v Hlen Hcopy Hp'.
  pose proof (u32_nonneg len).
  destruct (copy_bytes_sound _ _ _ _ Hcopy) as [Hmap Hfits].
  apply repr_vec_intro with (n := to_Z len) (mid := bytes_at data (to_Z p)).
  - exact Hlen.
  - rewrite Hmap.
    rewrite (bytes_at_congr data (to_Z p')
               (to_Z p + Z.of_nat (Z.to_nat (to_Z p' - to_Z p))))
      by (rewrite Z2Nat.id; lia).
    replace (Z.to_nat (to_Z len)) with (Z.to_nat (to_Z p' - to_Z p)) by
      (f_equal; lia).
    apply repr_rep_byte_firstn; [apply usize_nonneg | exact Hfits].
Qed.

(* ================================================================== *)
(** ** 5.2.4 Names                                                     *)
(* ================================================================== *)

(** The two byte types line up pointwise. [Byte.of_N] is total below 256, so
    the default in [translate_name_byte] is unreachable. *)
Lemma name_byte_is_translate : forall b : u8,
  name_byte_is (to_Z b) (translate_name_byte b).
Proof.
  intros b. pose proof (u8_bounds b) as Hb.
  unfold name_byte_is, translate_name_byte.
  pose proof (Byte.to_of_N_option_map (Z.to_N (to_Z b))) as Hopt.
  assert (Hle : (Z.to_N (to_Z b) <=? 255)%N = true) by (apply N.leb_le; lia).
  rewrite Hle in Hopt.
  destruct (Byte.of_N (Z.to_N (to_Z b))) as [x|]; [|discriminate].
  cbn [option_map] in Hopt. injection Hopt as <-. reflexivity.
Qed.

Lemma forall2_name_bytes : forall v : alloc_vec_Vec u8,
  Forall2 name_byte_is (List.map to_Z (vec_list v)) (translate_name v).
Proof.
  intros v. unfold translate_name.
  induction (vec_list v) as [|b l IH]; cbn [List.map].
  - apply Forall2_nil.
  - apply Forall2_cons; [apply name_byte_is_translate | exact IH].
Qed.

Lemma decode_name_sound : forall data pos v p',
  module_decode_name data pos = Ok (Core_result_Result_Ok (v, p')) ->
  repr_name (bytes_from data pos) (translate_name v) (bytes_from data p').
Proof.
  intros data pos v p' H. unfold module_decode_name in H.
  destruct (reader_read_u32_leb data pos) as [r|] eqn:Hlen; cbn [bind] in H;
    [|discriminate].
  destruct r as [[len p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (scalar_cast U32 Usize len) as [n|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  destruct (module_have_bytes data p n) as [r1|]; cbn [bind] in H;
    [|discriminate].
  destruct r1 as [[]|e1]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (usize_add p n) as [q|] eqn:Hadd; cbn [bind] in H; [|discriminate].
  destruct (module_copy_bytes data p q) as [w|] eqn:Hcopy; cbn [bind] in H;
    [|discriminate].
  rewrite vec_deref_spec in H.
  destruct (module_validate_utf8 w) as [r2|] eqn:Hutf8; cbn [bind] in H;
    [|discriminate].
  destruct r2 as [[]|e2]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  injection H as -> ->.
  assert (Hn : to_Z n = to_Z len).
  { unfold scalar_cast in Hcast. apply mk_scalar_ok_to_Z in Hcast. exact Hcast. }
  pose proof (scalar_add_val _ _ _ (to_Z n) Hadd eq_refl) as Hq.
  apply repr_name_intro with (zs := List.map to_Z (vec_list v)).
  - rewrite bytes_from_at. rewrite bytes_from_at.
    apply (decode_bytevec_sound data pos p p' len v);
      [ rewrite <- bytes_from_at; rewrite <- bytes_from_at;
        apply (read_u32_leb_sound _ _ _ _ Hlen)
      | exact Hcopy
      | lia ].
  - apply forall2_name_bytes.
  - apply (validate_utf8_sound _ Hutf8).
Qed.

(* ================================================================== *)
(** ** 5.3.1 Value types                                               *)
(* ================================================================== *)

Lemma decode_value_type_sound : forall data pos vt p',
  module_decode_value_type data pos = Ok (Core_result_Result_Ok (vt, p')) ->
  repr_valtype (bytes_from data pos) (translate_vt_v vt) (bytes_from data p').
Proof.
  intros data pos vt p' H. unfold module_decode_value_type in H.
  destruct (reader_read_byte data pos) as [r|] eqn:Hb; cbn [bind] in H;
    [|discriminate].
  destruct r as [[b p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  rewrite (proj1 (read_byte_ok _ _ _ _ Hb)).
  destruct (b s= 127%u8) eqn:E127;
    [ injection H as <- <-; apply repr_valtype_intro;
      rewrite (scalar_eqb_true _ _ E127); reflexivity |].
  destruct (b s= 126%u8) eqn:E126;
    [ injection H as <- <-; apply repr_valtype_intro;
      rewrite (scalar_eqb_true _ _ E126); reflexivity |].
  destruct (b s= 125%u8) eqn:E125;
    [ injection H as <- <-; apply repr_valtype_intro;
      rewrite (scalar_eqb_true _ _ E125); reflexivity |].
  destruct (b s= 124%u8) eqn:E124;
    [ injection H as <- <-; apply repr_valtype_intro;
      rewrite (scalar_eqb_true _ _ E124); reflexivity |].
  discriminate.
Qed.

(* ================================================================== *)
(** ** 5.3.2 Result types, and 5.1.3's vector at that element          *)
(* ================================================================== *)

(** The loop's own statement. It starts from a vector that already holds
    something, so the elements it decodes are what it *appends*, and those are
    the ones the [repr_rep] premise of [repr_vec] talks about. The count still
    to go is [count - i], which is what makes the [repr_rep] index march down
    with the loop. *)
Lemma decode_value_types_loop_sound : forall m data count out q i out' q',
  to_Z count - to_Z i <= Z.of_nat m ->
  module_decode_value_types_loop data count out q i
    = Ok (Core_result_Result_Ok (out', q')) ->
  exists vts,
    vec_list out' = vec_list out ++ vts
    /\ repr_rep repr_valtype (Z.to_nat (to_Z count - to_Z i))
         (bytes_from data q) (List.map translate_vt_v vts) (bytes_from data q').
Proof.
  induction m as [|m IH]; intros data count out q i out' q' Hmeas H;
    unfold module_decode_value_types_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (i s>= count) eqn:Hge.
  1,3: injection H as <- <-; exists []; rewrite app_nil_r;
       split; [reflexivity|];
       apply scalar_geb_true_ge in Hge;
       rewrite to_nat_nonpos by lia; apply repr_rep_nil.
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (module_decode_value_type data q) as [r|] eqn:Hvt;
      cbn [bind] in H; [|discriminate].
    destruct r as [[vt q1]|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (alloc_vec_Vec_push out vt) as [out2|] eqn:Hpush;
      cbn [bind] in H; [|discriminate].
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in H;
      [|discriminate].
    assert (Hi2 : to_Z i2 = to_Z i + 1).
    { unfold u32_add, scalar_add in Hadd. apply mk_scalar_ok_to_Z in Hadd.
      assert (H1 : to_Z 1%u32 = 1) by reflexivity. lia. }
    destruct (IH data count out2 q1 i2 out' q' (ltac:(cbn in Hmeas; lia)) H)
      as [vts [Hout Hrep]].
    exists (vt :: vts). split.
    + rewrite Hout. rewrite (vec_push_spec _ _ _ Hpush).
      rewrite <- app_assoc. reflexivity.
    + assert (Hcnt : to_Z count - to_Z i = (to_Z count - to_Z i2) + 1) by lia.
      rewrite Hcnt. rewrite Z_to_nat_add1 by lia.
      cbn [List.map]. eapply repr_rep_cons; [|exact Hrep].
      apply (decode_value_type_sound _ _ _ _ Hvt).
Qed.

Lemma decode_value_types_sound : forall data pos out p',
  module_decode_value_types data pos = Ok (Core_result_Result_Ok (out, p')) ->
  repr_resulttype (bytes_from data pos)
    (List.map translate_vt_v (vec_list out)) (bytes_from data p').
Proof.
  intros data pos out p' H. unfold module_decode_value_types in H.
  destruct (reader_read_u32_leb data pos) as [r|] eqn:Hn; cbn [bind] in H;
    [|discriminate].
  destruct r as [[count p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (decode_value_types_loop_sound (Z.to_nat (to_Z count)) data count
              (alloc_vec_Vec_new types_ValueType_t) p 0%u32 out p')
    as [vts [Hout Hrep]].
  - assert (H0 : to_Z 0%u32 = 0) by reflexivity.
    pose proof (u32_nonneg count). lia.
  - exact H.
  - apply repr_vec_intro with (n := to_Z count) (mid := bytes_from data p).
    + apply (read_u32_leb_sound _ _ _ _ Hn).
    + rewrite Hout.
      cbn [vec_list alloc_vec_Vec_new proj1_sig]. cbn [List.app].
      assert (H0 : to_Z 0%u32 = 0) by reflexivity.
      rewrite H0 in Hrep. rewrite Z.sub_0_r in Hrep. exact Hrep.
Qed.

(* ================================================================== *)
(** ** 5.3.3 Function types                                            *)
(* ================================================================== *)

(** The result-count check is Wasm 1.0 validation rather than decoding, so
    [repr_functype] does not mention it and the lemma simply drops it. *)
Lemma decode_func_type_sound : forall data pos ft p',
  module_decode_func_type data pos = Ok (Core_result_Result_Ok (ft, p')) ->
  repr_functype (bytes_from data pos) (translate_functype ft)
                (bytes_from data p').
Proof.
  intros data pos ft p' H. unfold module_decode_func_type in H.
  destruct (reader_read_byte data pos) as [r|] eqn:Hb; cbn [bind] in H;
    [|discriminate].
  destruct r as [[tag p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (tag s<> 96%u8) eqn:Etag; [discriminate|].
  apply scalar_neqb_false in Etag.
  destruct (module_decode_value_types data p) as [r1|] eqn:Hp1;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [[params p1]|e1]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (module_decode_value_types data p1) as [r2|] eqn:Hp2;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [[results p2]|e2]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (alloc_vec_Vec_len results s> limits_max_results); [discriminate|].
  injection H as <- <-.
  rewrite (proj1 (read_byte_ok _ _ _ _ Hb)). rewrite Etag.
  unfold translate_functype. cbn [types_FuncType_params types_FuncType_results].
  apply repr_functype_intro with (p1 := bytes_from data p1).
  - apply (decode_value_types_sound _ _ _ _ Hp1).
  - apply (decode_value_types_sound _ _ _ _ Hp2).
Qed.

(* ================================================================== *)
(** ** 5.3.4 to 5.3.8 Limits, memories, tables and globals             *)
(* ================================================================== *)

Lemma decode_limits_sound : forall data pos lim p',
  module_decode_limits data pos = Ok (Core_result_Result_Ok (lim, p')) ->
  repr_limits (bytes_from data pos) (translate_limits lim)
              (bytes_from data p').
Proof.
  intros data pos lim p' H. unfold module_decode_limits in H.
  destruct (reader_read_byte data pos) as [r|] eqn:Hb; cbn [bind] in H;
    [|discriminate].
  destruct r as [[flag p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  rewrite (proj1 (read_byte_ok _ _ _ _ Hb)).
  destruct (flag s= 0%u8) eqn:E0.
  - destruct (reader_read_u32_leb data p) as [r1|] eqn:Hmin; cbn [bind] in H;
      [|discriminate].
    destruct r1 as [[min p1]|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    injection H as <- <-.
    rewrite (scalar_eqb_true _ _ E0). unfold translate_limits.
    cbn [types_Limits_min types_Limits_max option_map].
    apply repr_limits_open. apply (read_u32_leb_sound _ _ _ _ Hmin).
  - destruct (flag s= 1%u8) eqn:E1; [|discriminate].
    destruct (reader_read_u32_leb data p) as [r1|] eqn:Hmin; cbn [bind] in H;
      [|discriminate].
    destruct r1 as [[min p1]|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (reader_read_u32_leb data p1) as [r2|] eqn:Hmax; cbn [bind] in H;
      [|discriminate].
    destruct r2 as [[max p2]|e2]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    injection H as <- <-.
    rewrite (scalar_eqb_true _ _ E1). unfold translate_limits.
    cbn [types_Limits_min types_Limits_max option_map].
    apply repr_limits_closed with (p1 := bytes_from data p1).
    + apply (read_u32_leb_sound _ _ _ _ Hmin).
    + apply (read_u32_leb_sound _ _ _ _ Hmax).
Qed.

(** The range check [validate_limits] performs is spec 3.2.3, again validation
    rather than decoding, so it too is dropped here. *)
Lemma decode_mem_type_sound : forall data pos mt p',
  module_decode_mem_type data pos = Ok (Core_result_Result_Ok (mt, p')) ->
  repr_memtype (bytes_from data pos) (translate_memtype mt)
               (bytes_from data p').
Proof.
  intros data pos mt p' H. unfold module_decode_mem_type in H.
  destruct (module_decode_limits data pos) as [r|] eqn:Hlim; cbn [bind] in H;
    [|discriminate].
  destruct r as [[lim p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (limits_validate_limits lim limits_max_memory_pages) as [r1|];
    cbn [bind] in H; [|discriminate].
  destruct r1 as [u|e1]; [|try_err_rw_in H; discriminate].
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  injection H as <- <-.
  apply (decode_limits_sound _ _ _ _ Hlim).
Qed.

Lemma decode_table_type_sound : forall data pos tt p',
  module_decode_table_type data pos = Ok (Core_result_Result_Ok (tt, p')) ->
  repr_tabletype (bytes_from data pos) (translate_tabletype tt)
                 (bytes_from data p').
Proof.
  intros data pos tt p' H. unfold module_decode_table_type in H.
  destruct (reader_read_byte data pos) as [r|] eqn:Hb; cbn [bind] in H;
    [|discriminate].
  destruct r as [[elem p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (elem s<> 112%u8) eqn:Eelem; [discriminate|].
  apply scalar_neqb_false in Eelem.
  destruct (module_decode_limits data p) as [r1|] eqn:Hlim; cbn [bind] in H;
    [|discriminate].
  destruct r1 as [[lim p1]|e1]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (limits_validate_limits lim limits_max_table_elems) as [r2|];
    cbn [bind] in H; [|discriminate].
  destruct r2 as [u|e2]; [|try_err_rw_in H; discriminate].
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  injection H as <- <-.
  rewrite (proj1 (read_byte_ok _ _ _ _ Hb)). rewrite Eelem.
  apply repr_tabletype_intro. apply (decode_limits_sound _ _ _ _ Hlim).
Qed.

(* ================================================================== *)
(** ** Spec 3.2.1: limits are in range                                 *)
(* ================================================================== *)

(** The first of the type system's own checks to line up with the Rust, and
    the simplest: [validate_limits] is spec 3.2.1 and WasmCert's
    [limit_valid_range] is the same three comparisons. The bounds agree too --
    a memory is at most 2^16 pages and a table is indexed by a [u32]. *)
Lemma validate_limits_valid : forall lim bound k,
  to_Z bound = Z.of_N k ->
  limits_validate_limits lim bound = Ok (Core_result_Result_Ok tt) ->
  limit_valid_range (translate_limits lim) k = true.
Proof.
  intros lim bound k Hk H. unfold limits_validate_limits in H.
  pose proof (u32_nonneg lim.(types_Limits_min)) as Hmin0.
  destruct (lim.(types_Limits_min) s> bound) eqn:Hgt; [discriminate|].
  apply scalar_gtb_false in Hgt.
  unfold limit_valid_range, translate_limits.
  cbn [lim_min lim_max].
  assert (Hlow : (Z.to_N (to_Z lim.(types_Limits_min)) <=? k)%N = true)
    by (apply N.leb_le; apply N2Z.inj_le; rewrite Z2N.id by lia; lia).
  rewrite Hlow. cbn [andb].
  destruct lim.(types_Limits_max) as [max|] eqn:Hmax;
    cbn [option_map]; [|reflexivity].
  pose proof (u32_nonneg max) as Hmax0.
  destruct (max s> bound) eqn:Hgt2; [discriminate|].
  apply scalar_gtb_false in Hgt2.
  destruct (lim.(types_Limits_min) s> max) eqn:Hgt3; [discriminate|].
  apply scalar_gtb_false in Hgt3.
  apply Bool.andb_true_iff. split; apply N.leb_le; apply N2Z.inj_le;
    repeat rewrite Z2N.id by lia; lia.
Qed.

Lemma decode_table_type_valid : forall data pos tt p',
  module_decode_table_type data pos = Ok (Core_result_Result_Ok (tt, p')) ->
  tabletype_valid (translate_tabletype tt) = true.
Proof.
  intros data pos tt p' H. unfold module_decode_table_type in H.
  destruct (reader_read_byte data pos) as [r|]; cbn [bind] in H;
    [|discriminate].
  destruct r as [[elem p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (elem s<> 112%u8); [discriminate|].
  destruct (module_decode_limits data p) as [r1|]; cbn [bind] in H;
    [|discriminate].
  destruct r1 as [[lim p1]|e1]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (limits_validate_limits lim limits_max_table_elems) as [r2|] eqn:Hv;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [u|e2]; [|try_err_rw_in H; discriminate].
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  injection H as <- _.
  unfold tabletype_valid, translate_tabletype. cbn [tt_limits].
  apply (validate_limits_valid lim limits_max_table_elems); [reflexivity | exact Hv].
Qed.

Lemma decode_mem_type_valid : forall data pos mt p',
  module_decode_mem_type data pos = Ok (Core_result_Result_Ok (mt, p')) ->
  memtype_valid (translate_memtype mt) = true.
Proof.
  intros data pos mt p' H. unfold module_decode_mem_type in H.
  destruct (module_decode_limits data pos) as [r|]; cbn [bind] in H;
    [|discriminate].
  destruct r as [[lim p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (limits_validate_limits lim limits_max_memory_pages) as [r1|] eqn:Hv;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [u|e1]; [|try_err_rw_in H; discriminate].
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  injection H as <- _.
  unfold memtype_valid, translate_memtype. cbn [types_MemType_limits].
  apply (validate_limits_valid lim limits_max_memory_pages);
    [reflexivity | exact Hv].
Qed.

(** Every table and memory type in the environment went through one of those
    two decoders, so validity is an invariant of the environment rather than a
    fact about one section. WasmCert wants it in three places, and the three
    fields here are exactly those: [module_table_type_checker] and
    [module_mem_type_checker] read the two index spaces for what the module
    defines, and [module_imports_typer] re-checks what it imports off the
    import entry's own copy of the type.

    Three sections write these fields -- the import section writes all three,
    the table and memory sections one each -- and each hands the invariant on
    in the same shape. *)
Definition import_valid (im : module_Import_t) : Prop :=
  match im.(module_Import_desc) with
  | Module_ImportDesc_Table t => tabletype_valid (translate_tabletype t) = true
  | Module_ImportDesc_Memory m => memtype_valid (translate_memtype m) = true
  | _ => True
  end.

Definition env_limits_valid (env : module_Env_t) : Prop :=
  List.Forall import_valid (vec_list env.(module_Env_imports))
  /\ List.Forall (fun t => tabletype_valid (translate_tabletype t) = true)
       (vec_list env.(module_Env_table_types))
  /\ List.Forall (fun m => memtype_valid (translate_memtype m) = true)
       (vec_list env.(module_Env_mem_types)).

(** A section that leaves all three fields where it found them keeps it. *)
Lemma env_limits_valid_keep : forall env env',
  vec_list env'.(module_Env_imports) = vec_list env.(module_Env_imports) ->
  vec_list env'.(module_Env_table_types) = vec_list env.(module_Env_table_types) ->
  vec_list env'.(module_Env_mem_types) = vec_list env.(module_Env_mem_types) ->
  env_limits_valid env -> env_limits_valid env'.
Proof.
  intros env env' Hi Ht Hm [Hvi [Hvt Hvm]].
  split; [rewrite Hi; exact Hvi|].
  split; [rewrite Ht; exact Hvt | rewrite Hm; exact Hvm].
Qed.

Lemma forall_push : forall A (P : A -> Prop) (v w : alloc_vec_Vec A) x,
  alloc_vec_Vec_push v x = Ok w ->
  List.Forall P (vec_list v) -> P x -> List.Forall P (vec_list w).
Proof.
  intros A P v w x Hpush Hall Hx. rewrite (vec_push_spec _ _ _ Hpush).
  apply List.Forall_app. split; [exact Hall|].
  apply List.Forall_cons; [exact Hx | apply List.Forall_nil].
Qed.

Lemma decode_global_type_sound : forall data pos gt p',
  module_decode_global_type data pos = Ok (Core_result_Result_Ok (gt, p')) ->
  repr_globaltype (bytes_from data pos) (translate_globaltype gt)
                  (bytes_from data p').
Proof.
  intros data pos gt p' H. unfold module_decode_global_type in H.
  destruct (module_decode_value_type data pos) as [r|] eqn:Hvt;
    cbn [bind] in H; [|discriminate].
  destruct r as [[valtype p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_byte data p) as [r1|] eqn:Hm; cbn [bind] in H;
    [|discriminate].
  destruct r1 as [[m p1]|e1]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  assert (Hstep : forall mu,
            repr_mut (bytes_from data p) mu (bytes_from data p1) ->
            repr_globaltype (bytes_from data pos)
              {| tg_mut := mu; tg_t := translate_vt_v valtype |}
              (bytes_from data p1)).
  { intros mu Hmu. apply repr_globaltype_intro with (p1 := bytes_from data p).
    - apply (decode_value_type_sound _ _ _ _ Hvt).
    - exact Hmu. }
  pose proof (proj1 (read_byte_ok _ _ _ _ Hm)) as Hbp.
  destruct (m s= 0%u8) eqn:E0.
  - injection H as <- <-. apply Hstep.
    rewrite Hbp. rewrite (scalar_eqb_true _ _ E0). apply repr_mut_const.
  - destruct (m s= 1%u8) eqn:E1; [|discriminate].
    injection H as <- <-. apply Hstep.
    rewrite Hbp. rewrite (scalar_eqb_true _ _ E1). apply repr_mut_var.
Qed.

(* ================================================================== *)
(** ** 5.4.1 Constant expressions                                      *)
(* ================================================================== *)

(** A constant expression is decoded by a reader of its own rather than by
    giving [code] an init-expression mode, which is where the shape of this
    section comes from: the result is a [ConstExpr] naming one instruction, and
    the expression it stands for is that instruction and the terminating [end].

    That is not a divergence from the format. Spec 3.4.10 restricts an
    initialiser to constant instructions and 3.4.4 types it [[] -> [t]], and
    every constant instruction pushes exactly one value, so an expression of
    that type has exactly one instruction in it. *)
Definition translate_const_expr (e : types_ConstExpr_t) : basic_instruction :=
  match e with
  | Types_ConstExpr_I32 v => BI_const_num (const_val T_i32 (to_Z v))
  | Types_ConstExpr_I64 v => BI_const_num (const_val T_i64 (to_Z v))
  | Types_ConstExpr_F32 b => BI_const_num (fconst_val T_f32 (to_Z b))
  | Types_ConstExpr_F64 b => BI_const_num (fconst_val T_f64 (to_Z b))
  | Types_ConstExpr_GlobalGet x => BI_global_get (Z.to_N (to_Z x))
  end.

(** The terminating [0x0B]. *)
Lemma read_expr_end_sound : forall data pos p',
  module_read_expr_end data pos = Ok (Core_result_Result_Ok p') ->
  repr_op (bytes_from data pos) FO_end (bytes_from data p').
Proof.
  intros data pos p' H. unfold module_read_expr_end in H.
  destruct (reader_read_byte data pos) as [r|] eqn:Hb; cbn [bind] in H;
    [|discriminate].
  destruct r as [[b p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (b s<> code_op_end) eqn:Eend; [discriminate|].
  injection H as <-.
  rewrite (proj1 (read_byte_ok _ _ _ _ Hb)).
  apply repr_op_end.
  rewrite (scalar_neqb_false _ _ Eend). reflexivity.
Qed.

(** An expression of one instruction. [else_sugar] has nothing to do here: the
    instruction is not structured, so the stream is already lean. *)
Lemma repr_expr_single : forall be bs mid rest,
  (forall bt inner, be <> BI_block bt inner) ->
  (forall bt inner, be <> BI_loop bt inner) ->
  (forall bt es1 es2, be <> BI_if bt es1 es2) ->
  repr_op bs (FO_plain be) mid ->
  repr_op mid FO_end rest ->
  repr_expr bs [be] rest.
Proof.
  intros be bs mid rest Hblk Hlp Hif Hop Hend.
  exists [FO_plain be; FO_end]. split.
  - assert (Hflat : flat_of [be] = [FO_plain be]).
    { destruct be; try reflexivity;
        [ exfalso; eapply Hblk | exfalso; exact (Hlp _ _ eq_refl)
        | exfalso; exact (Hif _ _ _ eq_refl) ]; reflexivity. }
    rewrite Hflat. apply else_sugar_refl.
  - apply repr_ops_cons with (mid := mid); [exact Hop|].
    apply repr_ops_cons with (mid := rest); [exact Hend | apply repr_ops_nil].
Qed.

(** What the decoder checked of a constant expression, which is what the type
    system asks of it: spec 3.3.7 says a constant expression is a sequence of
    constant instructions, and the module's initialisers are typed at the
    declared type. A [global.get] may name an imported immutable global and no
    other, so what has to come back is the global's own type and where it sat.

    The four literal arms say only that the declared type is the literal's,
    which is [expect_const_type]. *)
Definition const_expr_ok (env : module_Env_t) (expected : types_ValueType_t)
                         (e : types_ConstExpr_t) : Prop :=
  match e with
  | Types_ConstExpr_I32 _ => expected = Types_ValueType_I32
  | Types_ConstExpr_I64 _ => expected = Types_ValueType_I64
  | Types_ConstExpr_F32 _ => expected = Types_ValueType_F32
  | Types_ConstExpr_F64 _ => expected = Types_ValueType_F64
  | Types_ConstExpr_GlobalGet x =>
      exists gt,
        List.nth_error (vec_list env.(module_Env_global_types))
                       (Z.to_nat (to_Z x)) = Some gt
        /\ gt.(types_GlobalType_mutability) = Types_Mut_Const
        /\ gt.(types_GlobalType_valtype) = expected
        /\ to_Z x < to_Z env.(module_Env_num_imported_globals)
  end.

Lemma expect_const_type_eq : forall a b,
  module_expect_const_type a b = Ok (Core_result_Result_Ok tt) -> a = b.
Proof.
  intros a b H. unfold module_expect_const_type in H.
  rewrite vt_ne_spec in H. cbn [bind] in H.
  destruct a; destruct b; cbn [types_ValueType_t_beq negb] in H;
    solve [reflexivity | discriminate].
Qed.

Lemma const_global_ok : forall env idx gt,
  module_const_global env idx = Ok (Core_result_Result_Ok gt) ->
  List.nth_error (vec_list env.(module_Env_global_types))
                 (Z.to_nat (to_Z idx)) = Some gt
  /\ gt.(types_GlobalType_mutability) = Types_Mut_Const
  /\ to_Z idx < to_Z env.(module_Env_num_imported_globals).
Proof.
  intros env idx gt H. unfold module_const_global in H.
  destruct (scalar_cast U32 Usize idx) as [i|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  assert (Hi : to_Z i = to_Z idx)
    by (unfold scalar_cast in Hcast; apply mk_scalar_ok_to_Z in Hcast;
        exact Hcast).
  destruct (i s>= alloc_vec_Vec_len env.(module_Env_global_types));
    [discriminate|].
  destruct (i s>= env.(module_Env_num_imported_globals)) eqn:Hnig;
    [discriminate|].
  apply scalar_geb_false_lt in Hnig.
  destruct (alloc_vec_Vec_index
              (core_slice_index_SliceIndexUsizeSliceInst types_GlobalType_t)
              env.(module_Env_global_types) i) as [gt0|] eqn:Hgt;
    cbn [bind] in H; [|discriminate].
  rewrite vec_index_spec in Hgt.
  destruct (List.nth_error (vec_list env.(module_Env_global_types))
              (Z.to_nat (to_Z i))) as [gt1|] eqn:Hnth; [|discriminate].
  injection Hgt as <-.
  rewrite mut_ne_spec in H. cbn [bind] in H.
  destruct (types_Mut_t_beq gt1.(types_GlobalType_mutability) Types_Mut_Const)
    eqn:Hm; [|discriminate].
  injection H as <-.
  rewrite Hi in Hnth. split; [exact Hnth|].
  split; [destruct gt1.(types_GlobalType_mutability);
            [reflexivity | discriminate Hm]
         | lia].
Qed.

Lemma decode_const_expr_typed : forall data pos env expected e p',
  module_decode_const_expr data pos env expected
    = Ok (Core_result_Result_Ok (e, p')) ->
  const_expr_ok env expected e.
Proof.
  intros data pos env expected e p' H. unfold module_decode_const_expr in H.
  destruct (reader_read_byte data pos) as [r|]; cbn [bind] in H;
    [|discriminate].
  destruct r as [[op p]|e0]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  (* the four literal arms differ only in which type they expect *)
  destruct (op s= code_op_i32_const).
  { destruct (reader_read_s32_leb data p) as [r1|]; cbn [bind] in H;
      [|discriminate].
    destruct r1 as [[v p1]|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (module_expect_const_type Types_ValueType_I32 expected)
      as [r2|] eqn:Hty; cbn [bind] in H; [|discriminate].
    destruct r2 as [[]|e2]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (module_read_expr_end data p1) as [r3|]; cbn [bind] in H;
      [|discriminate].
    destruct r3 as [p2|e3]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    injection H as <- _. cbn [const_expr_ok].
    symmetry. apply (expect_const_type_eq _ _ Hty). }
  destruct (op s= code_op_i64_const).
  { destruct (reader_read_s64_leb data p) as [r1|]; cbn [bind] in H;
      [|discriminate].
    destruct r1 as [[v p1]|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (module_expect_const_type Types_ValueType_I64 expected)
      as [r2|] eqn:Hty; cbn [bind] in H; [|discriminate].
    destruct r2 as [[]|e2]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (module_read_expr_end data p1) as [r3|]; cbn [bind] in H;
      [|discriminate].
    destruct r3 as [p2|e3]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    injection H as <- _. cbn [const_expr_ok].
    symmetry. apply (expect_const_type_eq _ _ Hty). }
  destruct (op s= code_op_f32_const).
  { destruct (reader_read_f32_bits data p) as [r1|]; cbn [bind] in H;
      [|discriminate].
    destruct r1 as [[v p1]|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (module_expect_const_type Types_ValueType_F32 expected)
      as [r2|] eqn:Hty; cbn [bind] in H; [|discriminate].
    destruct r2 as [[]|e2]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (module_read_expr_end data p1) as [r3|]; cbn [bind] in H;
      [|discriminate].
    destruct r3 as [p2|e3]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    injection H as <- _. cbn [const_expr_ok].
    symmetry. apply (expect_const_type_eq _ _ Hty). }
  destruct (op s= code_op_f64_const).
  { destruct (reader_read_f64_bits data p) as [r1|]; cbn [bind] in H;
      [|discriminate].
    destruct r1 as [[v p1]|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (module_expect_const_type Types_ValueType_F64 expected)
      as [r2|] eqn:Hty; cbn [bind] in H; [|discriminate].
    destruct r2 as [[]|e2]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (module_read_expr_end data p1) as [r3|]; cbn [bind] in H;
      [|discriminate].
    destruct r3 as [p2|e3]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    injection H as <- _. cbn [const_expr_ok].
    symmetry. apply (expect_const_type_eq _ _ Hty). }
  (* [global.get]: an imported immutable global of the declared type *)
  destruct (op s= code_op_global_get); [|discriminate].
  destruct (reader_read_u32_leb data p) as [r1|]; cbn [bind] in H;
    [|discriminate].
  destruct r1 as [[idx p1]|e1]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (module_const_global env idx) as [r2|] eqn:Hg; cbn [bind] in H;
    [|discriminate].
  destruct r2 as [gt|e2]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (module_expect_const_type gt.(types_GlobalType_valtype) expected)
    as [r3|] eqn:Hty; cbn [bind] in H; [|discriminate].
  destruct r3 as [[]|e3]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (module_read_expr_end data p1) as [r4|]; cbn [bind] in H;
    [|discriminate].
  destruct r4 as [p2|e4]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  injection H as <- _. cbn [const_expr_ok].
  destruct (const_global_ok _ _ _ Hg) as [Hnth [Hmut Hlt]].
  exists gt. split; [exact Hnth|]. split; [exact Hmut|].
  split; [apply (expect_const_type_eq _ _ Hty) | exact Hlt].
Qed.

Lemma decode_const_expr_sound : forall data pos env expected e p',
  module_decode_const_expr data pos env expected
    = Ok (Core_result_Result_Ok (e, p')) ->
  repr_expr (bytes_from data pos) [translate_const_expr e] (bytes_from data p').
Proof.
  intros data pos env expected e p' H. unfold module_decode_const_expr in H.
  destruct (reader_read_byte data pos) as [r|] eqn:Hb; cbn [bind] in H;
    [|discriminate].
  destruct r as [[op p]|e0]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (proj1 (read_byte_ok _ _ _ _ Hb)) as Hop.
  (* every arm reads its immediate, checks the type, then reads the [end] *)
  destruct (op s= code_op_i32_const) eqn:A32.
  { destruct (reader_read_s32_leb data p) as [r1|] eqn:Hv; cbn [bind] in H;
      [|discriminate].
    destruct r1 as [[v p1]|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (module_expect_const_type Types_ValueType_I32 expected) as [r2|];
      cbn [bind] in H; [|discriminate].
    destruct r2 as [[]|e2]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (module_read_expr_end data p1) as [r3|] eqn:Hend;
      cbn [bind] in H; [|discriminate].
    destruct r3 as [p2|e3]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    injection H as <- <-. cbn [translate_const_expr].
    apply repr_expr_single with (mid := bytes_from data p1);
      [discriminate | discriminate | discriminate | | ].
    - rewrite Hop. apply repr_op_const with (nt := T_i32) (z := to_Z v).
      + rewrite (scalar_eqb_val _ _ 65 A32 eq_refl). reflexivity.
      + apply (read_s32_leb_sound _ _ _ _ Hv).
    - apply (read_expr_end_sound _ _ _ Hend). }
  destruct (op s= code_op_i64_const) eqn:A64.
  { destruct (reader_read_s64_leb data p) as [r1|] eqn:Hv; cbn [bind] in H;
      [|discriminate].
    destruct r1 as [[v p1]|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (module_expect_const_type Types_ValueType_I64 expected) as [r2|];
      cbn [bind] in H; [|discriminate].
    destruct r2 as [[]|e2]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (module_read_expr_end data p1) as [r3|] eqn:Hend;
      cbn [bind] in H; [|discriminate].
    destruct r3 as [p2|e3]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    injection H as <- <-. cbn [translate_const_expr].
    apply repr_expr_single with (mid := bytes_from data p1);
      [discriminate | discriminate | discriminate | | ].
    - rewrite Hop. apply repr_op_const with (nt := T_i64) (z := to_Z v).
      + rewrite (scalar_eqb_val _ _ 66 A64 eq_refl). reflexivity.
      + apply (read_s64_leb_sound _ _ _ _ Hv).
    - apply (read_expr_end_sound _ _ _ Hend). }
  destruct (op s= code_op_f32_const) eqn:Af32.
  { destruct (reader_read_f32_bits data p) as [r1|] eqn:Hv; cbn [bind] in H;
      [|discriminate].
    destruct r1 as [[v p1]|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (module_expect_const_type Types_ValueType_F32 expected) as [r2|];
      cbn [bind] in H; [|discriminate].
    destruct r2 as [[]|e2]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (module_read_expr_end data p1) as [r3|] eqn:Hend;
      cbn [bind] in H; [|discriminate].
    destruct r3 as [p2|e3]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    injection H as <- <-. cbn [translate_const_expr].
    apply repr_expr_single with (mid := bytes_from data p1);
      [discriminate | discriminate | discriminate | | ].
    - rewrite Hop. apply repr_op_fconst with (nt := T_f32) (bits := to_Z v).
      + rewrite (scalar_eqb_val _ _ 67 Af32 eq_refl). reflexivity.
      + apply (read_f32_bits_sound _ _ _ _ Hv).
    - apply (read_expr_end_sound _ _ _ Hend). }
  destruct (op s= code_op_f64_const) eqn:Af64.
  { destruct (reader_read_f64_bits data p) as [r1|] eqn:Hv; cbn [bind] in H;
      [|discriminate].
    destruct r1 as [[v p1]|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (module_expect_const_type Types_ValueType_F64 expected) as [r2|];
      cbn [bind] in H; [|discriminate].
    destruct r2 as [[]|e2]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (module_read_expr_end data p1) as [r3|] eqn:Hend;
      cbn [bind] in H; [|discriminate].
    destruct r3 as [p2|e3]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    injection H as <- <-. cbn [translate_const_expr].
    apply repr_expr_single with (mid := bytes_from data p1);
      [discriminate | discriminate | discriminate | | ].
    - rewrite Hop. apply repr_op_fconst with (nt := T_f64) (bits := to_Z v).
      + rewrite (scalar_eqb_val _ _ 68 Af64 eq_refl). reflexivity.
      + apply (read_f64_bits_sound _ _ _ _ Hv).
    - apply (read_expr_end_sound _ _ _ Hend). }
  destruct (op s= code_op_global_get) eqn:Agg; [|discriminate].
  destruct (reader_read_u32_leb data p) as [r1|] eqn:Hv; cbn [bind] in H;
    [|discriminate].
  destruct r1 as [[idx p1]|e1]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (module_const_global env idx) as [r2|]; cbn [bind] in H;
    [|discriminate].
  destruct r2 as [gt|e2]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (module_expect_const_type gt.(types_GlobalType_valtype) expected)
    as [r3|]; cbn [bind] in H; [|discriminate].
  destruct r3 as [[]|e3]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (module_read_expr_end data p1) as [r4|] eqn:Hend;
    cbn [bind] in H; [|discriminate].
  destruct r4 as [p2|e4]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  injection H as <- <-. cbn [translate_const_expr].
  apply repr_expr_single with (mid := bytes_from data p1);
    [discriminate | discriminate | discriminate | | ].
  - rewrite Hop. apply repr_op_idx with (io := IO_global_get) (x := to_Z idx).
    + rewrite (scalar_eqb_val _ _ 35 Agg eq_refl). reflexivity.
    + apply (read_u32_leb_sound _ _ _ _ Hv).
  - apply (read_expr_end_sound _ _ _ Hend).
Qed.

(* ================================================================== *)
(** ** 5.5.16 The header, and 5.5.2 a section's frame                  *)
(* ================================================================== *)

(** The cursor form of [bytes_at_skipn]: from here up, positions are cursors
    again, because that is what the readers' soundness lemmas are stated in. *)
Lemma bytes_from_skipn : forall data (p q : usize) k,
  to_Z q = to_Z p + Z.of_nat k ->
  bytes_from data q = List.skipn k (bytes_from data p).
Proof.
  intros data p q k Hq. rewrite bytes_from_at. rewrite bytes_from_at.
  rewrite <- bytes_at_skipn by apply usize_nonneg.
  apply bytes_at_congr. exact Hq.
Qed.

Lemma bytes_from_length_ge : forall data (p : usize) k,
  0 <= k ->
  to_Z p + k <= Z.of_nat (List.length (vec_list data)) ->
  (Z.to_nat k <= List.length (bytes_from data p))%nat.
Proof.
  intros data p k Hk0 Hk. rewrite bytes_from_at.
  apply bytes_at_length_ge; [apply usize_nonneg | exact Hk0 | exact Hk].
Qed.

(** Eight bytes, all of them fixed. Each read splices one byte onto the front
    of the stream and the guard that follows the run fixes its value. *)
Lemma read_header_sound : forall data p,
  module_read_header data = Ok (Core_result_Result_Ok p) ->
  repr_magic_version (byte_list data) (bytes_from data p).
Proof.
  intros data p H. unfold module_read_header in H.
  repeat (match type of H with
          | context [reader_read_byte ?d ?q] =>
              let r := fresh "r" in let E := fresh "E" in
              let b := fresh "b" in let q' := fresh "q" in
              destruct (reader_read_byte d q) as [r|] eqn:E; cbn [bind] in H;
                [|discriminate];
              destruct r as [[b q']|];
              [ rewrite branch_ok in H; cbn [bind] in H;
                pose proof (proj1 (read_byte_ok _ _ _ _ E))
              | try_err_rw_in H; discriminate ]
          | context [if ?c then _ else _] =>
              let E := fresh "E" in
              destruct c eqn:E; [discriminate|];
              apply scalar_neqb_false in E
          end).
  injection H as <-. unfold repr_magic_version.
  rewrite <- bytes_from_zero.
  repeat match goal with
         | [ E : bytes_from data _ = _ |- _ ] => rewrite E; clear E
         end.
  repeat match goal with
         | [ E : to_Z _ = to_Z _ |- _ ] => rewrite E; clear E
         end.
  reflexivity.
Qed.

(** The bytes a section's size prefix frames off. *)
Definition section_content (data : slice u8) (start fin : usize) : list Z :=
  List.firstn (Z.to_nat (to_Z fin - to_Z start)) (bytes_from data start).

(** Spec 5.5.2's framing, packaged as "hand me the contents relation and I hand
    you the section". [repr_section] pins the contents down by *splitting* the
    input, so what it wants is that they are exactly the declared number of
    bytes and that they were there to be read. [have_bytes] is what says the
    second, and it runs before the section is entered. *)
Lemma read_section_header_sound :
  forall data pos id start fin A (R : list Z -> A -> list Z -> Prop) x,
  module_read_section_header data pos
    = Ok (Core_result_Result_Ok (id, start, fin)) ->
  R (section_content data start fin) x [] ->
  repr_section (to_Z id) R (bytes_from data pos) x (bytes_from data fin).
Proof.
  intros data pos id start fin A R x H HR.
  unfold module_read_section_header in H.
  destruct (reader_read_byte data pos) as [r|] eqn:Hb; cbn [bind] in H;
    [|discriminate].
  destruct r as [[b p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_u32_leb data p) as [r1|] eqn:Hsz; cbn [bind] in H;
    [|discriminate].
  destruct r1 as [[size q]|e1]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (scalar_cast U32 Usize size) as [n|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  destruct (module_have_bytes data q n) as [r2|] eqn:Hh; cbn [bind] in H;
    [|discriminate].
  destruct r2 as [[]|e2]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (usize_add q n) as [q2|] eqn:Hadd; cbn [bind] in H; [|discriminate].
  injection H as -> -> ->.
  assert (Hn : to_Z n = to_Z size)
    by (unfold scalar_cast in Hcast; apply mk_scalar_ok_to_Z in Hcast;
        exact Hcast).
  pose proof (scalar_add_val _ _ _ (to_Z n) Hadd eq_refl) as Hfin.
  pose proof (have_bytes_room _ _ _ Hh) as Hroom.
  rewrite slice_len_spec in Hroom.
  pose proof (usize_nonneg n).
  assert (Hfits : (Z.to_nat (to_Z fin - to_Z start)
                     <= List.length (bytes_from data start))%nat)
    by (apply bytes_from_length_ge; lia).
  assert (Hsplit : bytes_from data fin
                   = List.skipn (Z.to_nat (to_Z fin - to_Z start))
                       (bytes_from data start))
    by (apply bytes_from_skipn; rewrite Z2Nat.id; lia).
  rewrite (proj1 (read_byte_ok _ _ _ _ Hb)).
  apply repr_section_intro with (size := to_Z size)
    (content := section_content data start fin).
  - unfold section_content. rewrite Hsplit. rewrite List.firstn_skipn.
    apply (read_u32_leb_sound _ _ _ _ Hsz).
  - unfold section_content. rewrite List.firstn_length_le by exact Hfits.
    rewrite Z2Nat.id; lia.
  - exact HR.
Qed.

(* ================================================================== *)
(** ** The environment's sections                                      *)
(* ================================================================== *)

(** Each section decoder appends to the environment, and the assembly at the
    end needs to know both what it appended and that it left everything else
    alone. The second is one equation rather than twelve, by rebuilding the
    record from the environment it was handed and the one field it wrote: the
    loop puts the record back together exactly that way, so the equation is
    what the code does, spelt out. *)
Definition env_with_types (env : module_Env_t)
                          (v : alloc_vec_Vec types_FuncType_t) : module_Env_t :=
  {| module_Env_types := v;
     module_Env_imports := env.(module_Env_imports);
     module_Env_globals := env.(module_Env_globals);
     module_Env_exports := env.(module_Env_exports);
     module_Env_elements := env.(module_Env_elements);
     module_Env_start := env.(module_Env_start);
     module_Env_func_type_indices := env.(module_Env_func_type_indices);
     module_Env_func_types := env.(module_Env_func_types);
     module_Env_table_types := env.(module_Env_table_types);
     module_Env_mem_types := env.(module_Env_mem_types);
     module_Env_global_types := env.(module_Env_global_types);
     module_Env_num_imported_funcs := env.(module_Env_num_imported_funcs);
     module_Env_num_imported_globals := env.(module_Env_num_imported_globals) |}.

Lemma env_with_types_refl : forall env, env = env_with_types env env.(module_Env_types).
Proof. intros env. destruct env. reflexivity. Qed.

Lemma env_with_types_idem : forall env v w,
  env_with_types (env_with_types env v) w = env_with_types env w.
Proof. intros env v w. reflexivity. Qed.

(** Wasm 1.0's one-result restriction, which [decode_func_type] enforces and
    the code section needs: [validate_body_sound] takes it as a hypothesis and
    the type section is where it becomes true. It is not a format rule, so it
    rides alongside [repr_functype] rather than inside it. *)
Definition ft_wasm10 (ft : types_FuncType_t) : Prop :=
  (List.length (vec_list ft.(types_FuncType_results)) <= 1)%nat.

Lemma decode_func_type_results : forall data pos ft p',
  module_decode_func_type data pos = Ok (Core_result_Result_Ok (ft, p')) ->
  ft_wasm10 ft.
Proof.
  intros data pos ft p' H. unfold module_decode_func_type in H.
  destruct (reader_read_byte data pos) as [r|]; cbn [bind] in H;
    [|discriminate].
  destruct r as [[tag p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (tag s<> 96%u8); [discriminate|].
  destruct (module_decode_value_types data p) as [r1|]; cbn [bind] in H;
    [|discriminate].
  destruct r1 as [[params p1]|e1]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (module_decode_value_types data p1) as [r2|]; cbn [bind] in H;
    [|discriminate].
  destruct r2 as [[results p2]|e2]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (alloc_vec_Vec_len results s> limits_max_results) eqn:Hgt;
    [discriminate|].
  injection H as <- _. unfold ft_wasm10. cbn [types_FuncType_results].
  pose proof (scalar_gtb_false_val _ _ 1 Hgt eq_refl) as Hle.
  rewrite vec_len_spec in Hle. lia.
Qed.

(** Spec 5.5.4: [typesec ::= ft*:vec(functype)]. *)
Lemma decode_type_section_loop_sound : forall m data env count q i q' env',
  to_Z count - to_Z i <= Z.of_nat m ->
  module_decode_type_section_loop data env count q i
    = Ok (Core_result_Result_Ok q', env') ->
  exists tfs,
    vec_list env'.(module_Env_types) = vec_list env.(module_Env_types) ++ tfs
    /\ env' = env_with_types env env'.(module_Env_types)
    /\ List.Forall ft_wasm10 tfs
    /\ repr_rep repr_functype (Z.to_nat (to_Z count - to_Z i))
         (bytes_from data q) (List.map translate_functype tfs)
         (bytes_from data q').
Proof.
  induction m as [|m IH]; intros data env count q i q' env' Hmeas H;
    unfold module_decode_type_section_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (i s>= count) eqn:Hge.
  1,3: injection H as <- <-; exists []; rewrite app_nil_r;
       split; [reflexivity|]; split; [apply env_with_types_refl|];
       split; [apply List.Forall_nil|];
       apply scalar_geb_true_ge in Hge;
       rewrite to_nat_nonpos by lia; apply repr_rep_nil.
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (module_decode_func_type data q) as [r|] eqn:Hft;
      cbn [bind] in H; [|discriminate].
    destruct r as [[ft q1]|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (alloc_vec_Vec_push env.(module_Env_types) ft) as [v|] eqn:Hpush;
      cbn [bind] in H; [|discriminate].
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in H;
      [|discriminate].
    pose proof (scalar_add_val _ _ _ 1 Hadd eq_refl) as Hi2.
    destruct (IH data (env_with_types env v) count q1 i2 q' env'
                (ltac:(cbn in Hmeas; lia)) H)
      as [tfs [Hlist [Henv [Hall Hrep]]]].
    exists (ft :: tfs). split; [|split; [|split]].
    + rewrite Hlist. cbn [env_with_types module_Env_types].
      rewrite (vec_push_spec _ _ _ Hpush). rewrite <- app_assoc. reflexivity.
    + rewrite Henv at 1. apply env_with_types_idem.
    + apply List.Forall_cons;
        [apply (decode_func_type_results _ _ _ _ Hft) | exact Hall].
    + assert (Hcnt : to_Z count - to_Z i = (to_Z count - to_Z i2) + 1) by lia.
      rewrite Hcnt. rewrite Z_to_nat_add1 by lia.
      cbn [List.map]. eapply repr_rep_cons; [|exact Hrep].
      apply (decode_func_type_sound _ _ _ _ Hft).
Qed.

Lemma decode_type_section_sound : forall data pos env q' env',
  module_decode_type_section data pos env
    = Ok (Core_result_Result_Ok q', env') ->
  exists tfs,
    vec_list env'.(module_Env_types) = vec_list env.(module_Env_types) ++ tfs
    /\ env' = env_with_types env env'.(module_Env_types)
    /\ List.Forall ft_wasm10 tfs
    /\ repr_vec repr_functype (bytes_from data pos)
         (List.map translate_functype tfs) (bytes_from data q').
Proof.
  intros data pos env q' env' H. unfold module_decode_type_section in H.
  destruct (reader_read_u32_leb data pos) as [r|] eqn:Hn; cbn [bind] in H;
    [|discriminate].
  destruct r as [[count p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (decode_type_section_loop_sound (Z.to_nat (to_Z count)) data env
              count p 0%u32 q' env') as [tfs [Hlist [Henv [Hall Hrep]]]].
  - assert (H0 : to_Z 0%u32 = 0) by reflexivity.
    pose proof (u32_nonneg count). lia.
  - exact H.
  - exists tfs. split; [exact Hlist|]. split; [exact Henv|].
    split; [exact Hall|].
    apply repr_vec_intro with (n := to_Z count) (mid := bytes_from data p).
    + apply (read_u32_leb_sound _ _ _ _ Hn).
    + assert (H0 : to_Z 0%u32 = 0) by reflexivity.
      rewrite H0 in Hrep. rewrite Z.sub_0_r in Hrep. exact Hrep.
Qed.

(** Spec 5.5.7 and 5.5.8: [tablesec] and [memsec]. Wasm 1.0 allows at most one
    of each, which is a validation rule and so does not appear in the format;
    an accepting run is all the lemma needs, and it rules the check out. *)
Definition translate_table (t : types_TableType_t) : module_table :=
  {| modtab_type := translate_tabletype t |}.

Definition translate_mem (m : types_MemType_t) : module_mem :=
  {| modmem_type := translate_memtype m |}.

Definition env_with_table (env : module_Env_t)
                          (v : alloc_vec_Vec types_TableType_t) : module_Env_t :=
  {| module_Env_types := env.(module_Env_types);
     module_Env_imports := env.(module_Env_imports);
     module_Env_globals := env.(module_Env_globals);
     module_Env_exports := env.(module_Env_exports);
     module_Env_elements := env.(module_Env_elements);
     module_Env_start := env.(module_Env_start);
     module_Env_func_type_indices := env.(module_Env_func_type_indices);
     module_Env_func_types := env.(module_Env_func_types);
     module_Env_table_types := v;
     module_Env_mem_types := env.(module_Env_mem_types);
     module_Env_global_types := env.(module_Env_global_types);
     module_Env_num_imported_funcs := env.(module_Env_num_imported_funcs);
     module_Env_num_imported_globals := env.(module_Env_num_imported_globals) |}.

Lemma env_with_table_refl : forall env,
  env = env_with_table env env.(module_Env_table_types).
Proof. intros env. destruct env. reflexivity. Qed.

Lemma env_with_table_idem : forall env v w,
  env_with_table (env_with_table env v) w = env_with_table env w.
Proof. intros env v w. reflexivity. Qed.

Definition env_with_mem (env : module_Env_t)
                        (v : alloc_vec_Vec types_MemType_t) : module_Env_t :=
  {| module_Env_types := env.(module_Env_types);
     module_Env_imports := env.(module_Env_imports);
     module_Env_globals := env.(module_Env_globals);
     module_Env_exports := env.(module_Env_exports);
     module_Env_elements := env.(module_Env_elements);
     module_Env_start := env.(module_Env_start);
     module_Env_func_type_indices := env.(module_Env_func_type_indices);
     module_Env_func_types := env.(module_Env_func_types);
     module_Env_table_types := env.(module_Env_table_types);
     module_Env_mem_types := v;
     module_Env_global_types := env.(module_Env_global_types);
     module_Env_num_imported_funcs := env.(module_Env_num_imported_funcs);
     module_Env_num_imported_globals := env.(module_Env_num_imported_globals) |}.

Lemma env_with_mem_refl : forall env,
  env = env_with_mem env env.(module_Env_mem_types).
Proof. intros env. destruct env. reflexivity. Qed.

Lemma env_with_mem_idem : forall env v w,
  env_with_mem (env_with_mem env v) w = env_with_mem env w.
Proof. intros env v w. reflexivity. Qed.

Lemma decode_table_section_loop_sound : forall m data env count q i q' env',
  to_Z count - to_Z i <= Z.of_nat m ->
  module_decode_table_section_loop data env count q i
    = Ok (Core_result_Result_Ok q', env') ->
  exists tts,
    vec_list env'.(module_Env_table_types)
      = vec_list env.(module_Env_table_types) ++ tts
    /\ env' = env_with_table env env'.(module_Env_table_types)
    /\ repr_rep repr_table (Z.to_nat (to_Z count - to_Z i))
         (bytes_from data q) (List.map translate_table tts)
         (bytes_from data q')
    /\ (env_limits_valid env -> env_limits_valid env').
Proof.
  induction m as [|m IH]; intros data env count q i q' env' Hmeas H;
    unfold module_decode_table_section_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (i s>= count) eqn:Hge.
  1,3: injection H as <- <-; exists []; rewrite app_nil_r;
       split; [reflexivity|]; split; [apply env_with_table_refl|];
       split; [| exact (fun Hv => Hv)];
       apply scalar_geb_true_ge in Hge;
       rewrite to_nat_nonpos by lia; apply repr_rep_nil.
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (module_decode_table_type data q) as [r|] eqn:Htt;
      cbn [bind] in H; [|discriminate].
    destruct r as [[tt1 q1]|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (alloc_vec_Vec_push env.(module_Env_table_types) tt1) as [v|] eqn:Hpush;
      cbn [bind] in H; [|discriminate].
    destruct (alloc_vec_Vec_len v s> limits_max_tables); [discriminate|].
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in H;
      [|discriminate].
    pose proof (scalar_add_val _ _ _ 1 Hadd eq_refl) as Hi2.
    destruct (IH data (env_with_table env v) count q1 i2 q' env'
                (ltac:(cbn in Hmeas; lia)) H) as [tts [Hlist [Henv [Hrep Hval]]]].
    exists (tt1 :: tts). split; [|split; [|split]].
    + rewrite Hlist. cbn [env_with_table module_Env_table_types].
      rewrite (vec_push_spec _ _ _ Hpush). rewrite <- app_assoc. reflexivity.
    + rewrite Henv at 1. apply env_with_table_idem.
    + assert (Hcnt : to_Z count - to_Z i = (to_Z count - to_Z i2) + 1) by lia.
      rewrite Hcnt. rewrite Z_to_nat_add1 by lia.
      cbn [List.map]. eapply repr_rep_cons; [|exact Hrep].
      apply repr_table_intro. apply (decode_table_type_sound _ _ _ _ Htt).
    + intros [Hvi [Hvt Hvm]]. apply Hval.
      split; [exact Hvi|]. split; [| exact Hvm].
      cbn [env_with_table module_Env_table_types].
      apply (forall_push _ _ _ _ _ Hpush Hvt).
      apply (decode_table_type_valid _ _ _ _ Htt).
Qed.

Lemma decode_table_section_sound : forall data pos env q' env',
  module_decode_table_section data pos env
    = Ok (Core_result_Result_Ok q', env') ->
  exists tts,
    vec_list env'.(module_Env_table_types)
      = vec_list env.(module_Env_table_types) ++ tts
    /\ env' = env_with_table env env'.(module_Env_table_types)
    /\ repr_vec repr_table (bytes_from data pos)
         (List.map translate_table tts) (bytes_from data q')
    /\ (env_limits_valid env -> env_limits_valid env').
Proof.
  intros data pos env q' env' H. unfold module_decode_table_section in H.
  destruct (reader_read_u32_leb data pos) as [r|] eqn:Hn; cbn [bind] in H;
    [|discriminate].
  destruct r as [[count p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (decode_table_section_loop_sound (Z.to_nat (to_Z count)) data env
              count p 0%u32 q' env') as [tts [Hlist [Henv [Hrep Hval]]]].
  - assert (H0 : to_Z 0%u32 = 0) by reflexivity.
    pose proof (u32_nonneg count). lia.
  - exact H.
  - exists tts. split; [exact Hlist|]. split; [exact Henv|].
    split; [| exact Hval].
    apply repr_vec_intro with (n := to_Z count) (mid := bytes_from data p).
    + apply (read_u32_leb_sound _ _ _ _ Hn).
    + assert (H0 : to_Z 0%u32 = 0) by reflexivity.
      rewrite H0 in Hrep. rewrite Z.sub_0_r in Hrep. exact Hrep.
Qed.

Lemma decode_memory_section_loop_sound : forall m data env count q i q' env',
  to_Z count - to_Z i <= Z.of_nat m ->
  module_decode_memory_section_loop data env count q i
    = Ok (Core_result_Result_Ok q', env') ->
  exists mts,
    vec_list env'.(module_Env_mem_types) = vec_list env.(module_Env_mem_types) ++ mts
    /\ env' = env_with_mem env env'.(module_Env_mem_types)
    /\ repr_rep repr_mem (Z.to_nat (to_Z count - to_Z i))
         (bytes_from data q) (List.map translate_mem mts)
         (bytes_from data q')
    /\ (env_limits_valid env -> env_limits_valid env').
Proof.
  induction m as [|m IH]; intros data env count q i q' env' Hmeas H;
    unfold module_decode_memory_section_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (i s>= count) eqn:Hge.
  1,3: injection H as <- <-; exists []; rewrite app_nil_r;
       split; [reflexivity|]; split; [apply env_with_mem_refl|];
       split; [| exact (fun Hv => Hv)];
       apply scalar_geb_true_ge in Hge;
       rewrite to_nat_nonpos by lia; apply repr_rep_nil.
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (module_decode_mem_type data q) as [r|] eqn:Hmt;
      cbn [bind] in H; [|discriminate].
    destruct r as [[mt q1]|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (alloc_vec_Vec_push env.(module_Env_mem_types) mt) as [v|] eqn:Hpush;
      cbn [bind] in H; [|discriminate].
    destruct (alloc_vec_Vec_len v s> limits_max_memories); [discriminate|].
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in H;
      [|discriminate].
    pose proof (scalar_add_val _ _ _ 1 Hadd eq_refl) as Hi2.
    destruct (IH data (env_with_mem env v) count q1 i2 q' env'
                (ltac:(cbn in Hmeas; lia)) H) as [mts [Hlist [Henv [Hrep Hval]]]].
    exists (mt :: mts). split; [|split; [|split]].
    + rewrite Hlist. cbn [env_with_mem module_Env_mem_types].
      rewrite (vec_push_spec _ _ _ Hpush). rewrite <- app_assoc. reflexivity.
    + rewrite Henv at 1. apply env_with_mem_idem.
    + assert (Hcnt : to_Z count - to_Z i = (to_Z count - to_Z i2) + 1) by lia.
      rewrite Hcnt. rewrite Z_to_nat_add1 by lia.
      cbn [List.map]. eapply repr_rep_cons; [|exact Hrep].
      apply repr_mem_intro. apply (decode_mem_type_sound _ _ _ _ Hmt).
    + intros [Hvi [Hvt Hvm]]. apply Hval.
      split; [exact Hvi|]. split; [exact Hvt|].
      cbn [env_with_mem module_Env_mem_types].
      apply (forall_push _ _ _ _ _ Hpush Hvm).
      apply (decode_mem_type_valid _ _ _ _ Hmt).
Qed.

Lemma decode_memory_section_sound : forall data pos env q' env',
  module_decode_memory_section data pos env
    = Ok (Core_result_Result_Ok q', env') ->
  exists mts,
    vec_list env'.(module_Env_mem_types) = vec_list env.(module_Env_mem_types) ++ mts
    /\ env' = env_with_mem env env'.(module_Env_mem_types)
    /\ repr_vec repr_mem (bytes_from data pos)
         (List.map translate_mem mts) (bytes_from data q')
    /\ (env_limits_valid env -> env_limits_valid env').
Proof.
  intros data pos env q' env' H. unfold module_decode_memory_section in H.
  destruct (reader_read_u32_leb data pos) as [r|] eqn:Hn; cbn [bind] in H;
    [|discriminate].
  destruct r as [[count p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (decode_memory_section_loop_sound (Z.to_nat (to_Z count)) data env
              count p 0%u32 q' env') as [mts [Hlist [Henv [Hrep Hval]]]].
  - assert (H0 : to_Z 0%u32 = 0) by reflexivity.
    pose proof (u32_nonneg count). lia.
  - exact H.
  - exists mts. split; [exact Hlist|]. split; [exact Henv|].
    split; [| exact Hval].
    apply repr_vec_intro with (n := to_Z count) (mid := bytes_from data p).
    + apply (read_u32_leb_sound _ _ _ _ Hn).
    + assert (H0 : to_Z 0%u32 = 0) by reflexivity.
      rewrite H0 in Hrep. rewrite Z.sub_0_r in Hrep. exact Hrep.
Qed.

(** Spec 5.5.6: [funcsec ::= x*:vec(typeidx)]. The type each index names is
    resolved and pushed onto the function index space here as well, which is
    why the section writes two fields. *)
Definition env_with_func (env : module_Env_t)
                         (fts : alloc_vec_Vec types_FuncType_t)
                         (fidx : alloc_vec_Vec (scalar U32)) : module_Env_t :=
  {| module_Env_types := env.(module_Env_types);
     module_Env_imports := env.(module_Env_imports);
     module_Env_globals := env.(module_Env_globals);
     module_Env_exports := env.(module_Env_exports);
     module_Env_elements := env.(module_Env_elements);
     module_Env_start := env.(module_Env_start);
     module_Env_func_type_indices := fidx;
     module_Env_func_types := fts;
     module_Env_table_types := env.(module_Env_table_types);
     module_Env_mem_types := env.(module_Env_mem_types);
     module_Env_global_types := env.(module_Env_global_types);
     module_Env_num_imported_funcs := env.(module_Env_num_imported_funcs);
     module_Env_num_imported_globals := env.(module_Env_num_imported_globals) |}.

Lemma env_with_func_refl : forall env,
  env = env_with_func env env.(module_Env_func_types)
                          env.(module_Env_func_type_indices).
Proof. intros env. destruct env. reflexivity. Qed.

Lemma env_with_func_idem : forall env a b c d,
  env_with_func (env_with_func env a b) c d = env_with_func env c d.
Proof. intros. reflexivity. Qed.

(** Copying a slice into a vector. [lookup_type] does it to hand back a copy
    of a type-section entry, and a code entry does it twice more: once for the
    signature's results and once to put the parameters in front of the
    declared locals. *)
Lemma copy_value_types_loop_sound : forall m src out i out',
  Z.of_nat (List.length (vec_list src)) - to_Z i <= Z.of_nat m ->
  0 <= to_Z i ->
  module_copy_value_types_loop src out i = Ok out' ->
  vec_list out' = vec_list out ++ List.skipn (Z.to_nat (to_Z i)) (vec_list src).
Proof.
  induction m as [|m IH]; intros src out i out' Hmeas Hi H;
    unfold module_copy_value_types_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (i s>= slice_len src) eqn:Hge.
  1,3: injection H as <-; apply scalar_geb_true_ge in Hge;
       rewrite slice_len_spec in Hge;
       rewrite List.skipn_all2 by (apply Nat2Z.inj_le;
         rewrite Z2Nat.id by lia; lia);
       rewrite app_nil_r; reflexivity.
  - exfalso. apply scalar_geb_false_lt in Hge.
    rewrite slice_len_spec in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge. rewrite slice_len_spec in Hge.
    destruct (slice_index_usize src i) as [vt|] eqn:Hidx; cbn [bind] in H;
      [|discriminate].
    destruct (alloc_vec_Vec_push out vt) as [out2|] eqn:Hpush;
      cbn [bind] in H; [|discriminate].
    destruct (usize_add i 1%usize) as [i2|] eqn:Hadd; cbn [bind] in H;
      [|discriminate].
    pose proof (scalar_add_val _ _ _ 1 Hadd eq_refl) as Hi2.
    rewrite (IH src out2 i2 out' (ltac:(cbn in Hmeas; lia)) (ltac:(lia)) H).
    rewrite (vec_push_spec _ _ _ Hpush). rewrite <- app_assoc.
    rewrite slice_index_usize_spec in Hidx.
    destruct (List.nth_error (vec_list src) (Z.to_nat (to_Z i))) as [x|] eqn:Hnth;
      [|discriminate].
    injection Hidx as <-.
    rewrite Hi2. rewrite Z_to_nat_add1 by lia.
    rewrite (skipn_nth_error _ _ _ Hnth). reflexivity.
Qed.

Lemma copy_value_types_sound : forall src out',
  module_copy_value_types src = Ok out' -> vec_list out' = vec_list src.
Proof.
  intros src out' H. unfold module_copy_value_types in H.
  assert (H0 : to_Z 0%usize = 0) by reflexivity.
  rewrite (copy_value_types_loop_sound
             (List.length (vec_list src)) src (alloc_vec_Vec_new _) 0%usize
             out' (ltac:(lia)) (ltac:(lia)) H).
  rewrite H0. cbn [vec_list alloc_vec_Vec_new proj1_sig List.app List.skipn].
  reflexivity.
Qed.

Definition translate_idx (x : scalar U32) : N := Z.to_N (to_Z x).

(** [lookup_type] resolves a type index against the type section, and both
    writers of the function index space push what it returned: the function
    section for what the module defines, and the import section for what it
    imports. So the space is a list of type indices resolved, twice over, and
    these two say what that means.

    What is pinned is the *translated* type, not the extracted one, because
    [lookup_type] hands back a copy: two [FuncType]s with the same contents are
    two different values, and the vectors inside them are only equal up to the
    proof each carries. [resolved_types] is total, so an index out of range
    contributes nothing to it and [idx_in_range] is the separate fact that
    there are none of those. *)
Definition idx_in_range (tys : list types_FuncType_t) (idx : scalar U32) : Prop :=
  List.nth_error tys (Z.to_nat (to_Z idx)) <> None.

Definition resolved_types (tys : list types_FuncType_t)
                          (idxs : list (scalar U32)) : list function_type :=
  List.flat_map (fun idx => match List.nth_error tys (Z.to_nat (to_Z idx)) with
                            | Some ft => [translate_functype ft]
                            | None => []
                            end) idxs.

Lemma resolved_types_app : forall tys xs ys,
  resolved_types tys (xs ++ ys) = resolved_types tys xs ++ resolved_types tys ys.
Proof. intros tys xs ys. apply List.flat_map_app. Qed.

(** No [Clone] impl reaches the extraction, so a type-section entry is handed
    out by copying its two vectors. The copy denotes the same WasmCert type,
    which is all anything downstream needs of it. *)
Lemma copy_func_type_same : forall ft ft',
  module_copy_func_type ft = Ok ft' ->
  translate_functype ft' = translate_functype ft.
Proof.
  intros ft ft' H. unfold module_copy_func_type in H.
  destruct (module_copy_value_types
              (alloc_vec_Vec_deref ft.(types_FuncType_params))) as [ps|] eqn:Hp;
    cbn [bind] in H; [|discriminate].
  destruct (module_copy_value_types
              (alloc_vec_Vec_deref ft.(types_FuncType_results))) as [rs|] eqn:Hr;
    cbn [bind] in H; [|discriminate].
  injection H as <-.
  pose proof (copy_value_types_sound _ _ Hp) as Hps.
  pose proof (copy_value_types_sound _ _ Hr) as Hrs.
  (* [translate_functype] reads the vectors through [proj1_sig] *)
  unfold vec_list in Hps, Hrs.
  unfold translate_functype.
  cbn [types_FuncType_params types_FuncType_results].
  rewrite Hps. rewrite Hrs.
  rewrite vec_deref_spec. rewrite vec_deref_spec. reflexivity.
Qed.

Lemma lookup_type_sound : forall env idx ft,
  module_lookup_type env idx = Ok (Core_result_Result_Ok ft) ->
  idx_in_range (vec_list env.(module_Env_types)) idx
  /\ resolved_types (vec_list env.(module_Env_types)) [idx] = [translate_functype ft].
Proof.
  intros env idx ft H. unfold module_lookup_type in H.
  destruct (scalar_cast U32 Usize idx) as [i|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  assert (Hi : to_Z i = to_Z idx)
    by (unfold scalar_cast in Hcast; apply mk_scalar_ok_to_Z in Hcast;
        exact Hcast).
  destruct (i s>= alloc_vec_Vec_len env.(module_Env_types)); [discriminate|].
  destruct (alloc_vec_Vec_index
              (core_slice_index_SliceIndexUsizeSliceInst types_FuncType_t)
              env.(module_Env_types) i) as [ft0|] eqn:Hft; cbn [bind] in H;
    [|discriminate].
  rewrite vec_index_spec in Hft.
  destruct (List.nth_error (vec_list env.(module_Env_types)) (Z.to_nat (to_Z i)))
    as [ft1|] eqn:Hnth; [|discriminate].
  injection Hft as <-.
  rewrite Hi in Hnth.
  destruct (module_copy_func_type ft1) as [ft2|] eqn:Hcopy; cbn [bind] in H;
    [|discriminate].
  injection H as <-.
  split.
  - unfold idx_in_range. rewrite Hnth. discriminate.
  - unfold resolved_types. cbn [List.flat_map]. rewrite Hnth.
    rewrite (copy_func_type_same _ _ Hcopy). reflexivity.
Qed.

(** What a section that writes the function index space did to it: it
    appended the types the indices [xs] name, and every one of them named a
    type that is there. Both writers of the space -- the import section and
    the function section -- report this, and it composes along a run because
    neither of them touches the type section's own vector. *)
Definition func_space (env env' : module_Env_t) (xs : list (scalar U32)) : Prop :=
  List.map translate_functype (vec_list env'.(module_Env_func_types))
    = List.map translate_functype (vec_list env.(module_Env_func_types))
      ++ resolved_types (vec_list env.(module_Env_types)) xs
  /\ List.Forall (idx_in_range (vec_list env.(module_Env_types))) xs.

Lemma func_space_keep : forall env env',
  vec_list env'.(module_Env_func_types) = vec_list env.(module_Env_func_types) ->
  func_space env env' [].
Proof.
  intros env env' Hf. split; [|apply List.Forall_nil].
  rewrite Hf. cbn [resolved_types List.flat_map]. rewrite app_nil_r.
  reflexivity.
Qed.

Lemma func_space_refl : forall env, func_space env env [].
Proof. intros env. apply func_space_keep. reflexivity. Qed.

(** The whole function index space, once the two writers have run: the types
    the imported functions name, then the types the function section's indices
    name. WasmCert builds [tc_funcs] as [ifts ++ fts] out of exactly those two
    lists. *)
Definition env_func_space (env : module_Env_t) (xs : list (scalar U32)) : Prop :=
  List.map translate_functype (vec_list env.(module_Env_func_types))
    = resolved_types (vec_list env.(module_Env_types)) xs
  /\ List.Forall (idx_in_range (vec_list env.(module_Env_types))) xs.

Lemma func_space_trans : forall env mid env' xs ys,
  vec_list mid.(module_Env_types) = vec_list env.(module_Env_types) ->
  func_space env mid xs -> func_space mid env' ys ->
  func_space env env' (xs ++ ys).
Proof.
  intros env mid env' xs ys Hty [Hf Ha] [Hf' Ha']. split.
  - rewrite Hf'. rewrite Hf. rewrite Hty. rewrite resolved_types_app.
    symmetry. apply app_assoc.
  - apply List.Forall_app. split; [exact Ha|]. rewrite Hty in Ha'. exact Ha'.
Qed.

Lemma decode_function_section_loop_sound : forall m data env count q i q' env',
  to_Z count - to_Z i <= Z.of_nat m ->
  module_decode_function_section_loop data env count q i
    = Ok (Core_result_Result_Ok q', env') ->
  exists xs,
    vec_list env'.(module_Env_func_type_indices)
      = vec_list env.(module_Env_func_type_indices) ++ xs
    /\ env' = env_with_func env env'.(module_Env_func_types)
                                env'.(module_Env_func_type_indices)
    /\ repr_rep repr_idx (Z.to_nat (to_Z count - to_Z i))
         (bytes_from data q) (List.map translate_idx xs)
         (bytes_from data q')
    /\ func_space env env' xs.
Proof.
  induction m as [|m IH]; intros data env count q i q' env' Hmeas H;
    unfold module_decode_function_section_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (i s>= count) eqn:Hge.
  1,3: injection H as <- <-; exists []; rewrite app_nil_r;
       split; [reflexivity|]; split; [apply env_with_func_refl|];
       split; [| apply func_space_refl];
       apply scalar_geb_true_ge in Hge;
       rewrite to_nat_nonpos by lia; apply repr_rep_nil.
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (reader_read_u32_leb data q) as [r|] eqn:Hidx; cbn [bind] in H;
      [|discriminate].
    destruct r as [[idx q1]|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (module_lookup_type env idx) as [r1|] eqn:Hlk; cbn [bind] in H;
      [|discriminate].
    destruct r1 as [ft|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (lookup_type_sound _ _ _ Hlk) as [Hrange Hres].
    destruct (alloc_vec_Vec_push env.(module_Env_func_types) ft) as [v|] eqn:Hpv;
      cbn [bind] in H; [|discriminate].
    destruct (alloc_vec_Vec_push env.(module_Env_func_type_indices) idx)
      as [v1|] eqn:Hpv1; cbn [bind] in H; [|discriminate].
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in H;
      [|discriminate].
    pose proof (scalar_add_val _ _ _ 1 Hadd eq_refl) as Hi2.
    destruct (IH data (env_with_func env v v1) count q1 i2 q' env'
                (ltac:(cbn in Hmeas; lia)) H)
      as [xs [Hlist [Henv [Hrep Hfs]]]].
    exists (idx :: xs). split; [|split; [|split]].
    + rewrite Hlist. cbn [env_with_func module_Env_func_type_indices].
      rewrite (vec_push_spec _ _ _ Hpv1). rewrite <- app_assoc. reflexivity.
    + rewrite Henv at 1. apply env_with_func_idem.
    + assert (Hcnt : to_Z count - to_Z i = (to_Z count - to_Z i2) + 1) by lia.
      rewrite Hcnt. rewrite Z_to_nat_add1 by lia.
      cbn [List.map]. eapply repr_rep_cons; [|exact Hrep].
      apply repr_idx_intro. apply (read_u32_leb_sound _ _ _ _ Hidx).
    + replace (idx :: xs) with ([idx] ++ xs) by reflexivity.
      apply (func_space_trans env (env_with_func env v v1) env');
        [reflexivity | | exact Hfs].
      split; [| apply List.Forall_cons; [exact Hrange | apply List.Forall_nil]].
      cbn [env_with_func module_Env_func_types].
      rewrite (vec_push_spec _ _ _ Hpv). rewrite List.map_app.
      rewrite Hres. reflexivity.
Qed.

Lemma decode_function_section_sound : forall data pos env q' env',
  module_decode_function_section data pos env
    = Ok (Core_result_Result_Ok q', env') ->
  exists xs,
    vec_list env'.(module_Env_func_type_indices)
      = vec_list env.(module_Env_func_type_indices) ++ xs
    /\ env' = env_with_func env env'.(module_Env_func_types)
                                env'.(module_Env_func_type_indices)
    /\ repr_vec repr_idx (bytes_from data pos)
         (List.map translate_idx xs) (bytes_from data q')
    /\ func_space env env' xs.
Proof.
  intros data pos env q' env' H. unfold module_decode_function_section in H.
  destruct (reader_read_u32_leb data pos) as [r|] eqn:Hn; cbn [bind] in H;
    [|discriminate].
  destruct r as [[count p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (decode_function_section_loop_sound (Z.to_nat (to_Z count)) data env
              count p 0%u32 q' env') as [xs [Hlist [Henv [Hrep Hfs]]]].
  - assert (H0 : to_Z 0%u32 = 0) by reflexivity.
    pose proof (u32_nonneg count). lia.
  - exact H.
  - exists xs. split; [exact Hlist|]. split; [exact Henv|].
    split; [| exact Hfs].
    apply repr_vec_intro with (n := to_Z count) (mid := bytes_from data p).
    + apply (read_u32_leb_sound _ _ _ _ Hn).
    + assert (H0 : to_Z 0%u32 = 0) by reflexivity.
      rewrite H0 in Hrep. rewrite Z.sub_0_r in Hrep. exact Hrep.
Qed.

(** Spec 5.5.9: [globalsec ::= glob*:vec(global)], [global ::= gt:globaltype
    e:expr]. The initialiser is decoded against the global's own type, which
    is spec 3.4.4 and does not appear in the format rule. *)
Definition translate_global (g : module_Global_t) : module_global :=
  {| modglob_type := translate_globaltype g.(module_Global_gtype);
     modglob_init := [translate_const_expr g.(module_Global_init)] |}.

Definition env_with_global (env : module_Env_t)
                           (gls : alloc_vec_Vec module_Global_t)
                           (gts : alloc_vec_Vec types_GlobalType_t)
  : module_Env_t :=
  {| module_Env_types := env.(module_Env_types);
     module_Env_imports := env.(module_Env_imports);
     module_Env_globals := gls;
     module_Env_exports := env.(module_Env_exports);
     module_Env_elements := env.(module_Env_elements);
     module_Env_start := env.(module_Env_start);
     module_Env_func_type_indices := env.(module_Env_func_type_indices);
     module_Env_func_types := env.(module_Env_func_types);
     module_Env_table_types := env.(module_Env_table_types);
     module_Env_mem_types := env.(module_Env_mem_types);
     module_Env_global_types := gts;
     module_Env_num_imported_funcs := env.(module_Env_num_imported_funcs);
     module_Env_num_imported_globals := env.(module_Env_num_imported_globals) |}.

Lemma env_with_global_refl : forall env,
  env = env_with_global env env.(module_Env_globals) env.(module_Env_global_types).
Proof. intros env. destruct env. reflexivity. Qed.

Lemma env_with_global_idem : forall env a b c d,
  env_with_global (env_with_global env a b) c d = env_with_global env c d.
Proof. intros. reflexivity. Qed.

(** Spec 3.4.4: a global's initialiser is a constant expression of the
    global's own type. The environment grows underneath the section -- each
    global goes into [global_types] as it is read -- so what is reported is
    the check against the environment the initialiser was decoded in, and
    [const_expr_ok] survives the later appends because the imported prefix it
    names does not move. *)
Definition global_ok (env : module_Env_t) (g : module_Global_t) : Prop :=
  const_expr_ok env g.(module_Global_gtype).(types_GlobalType_valtype)
                g.(module_Global_init).

Lemma const_expr_ok_grow : forall env env' t e more,
  vec_list env'.(module_Env_global_types)
    = vec_list env.(module_Env_global_types) ++ more ->
  to_Z env'.(module_Env_num_imported_globals)
    = to_Z env.(module_Env_num_imported_globals) ->
  const_expr_ok env t e -> const_expr_ok env' t e.
Proof.
  intros env env' t e more Hg Hn H. destruct e; try exact H.
  destruct H as [gt [Hnth [Hmut [Hty Hlt]]]].
  exists gt. rewrite Hg. rewrite Hn.
  split; [| split; [exact Hmut | split; [exact Hty | exact Hlt]]].
  rewrite List.nth_error_app1; [exact Hnth|].
  apply List.nth_error_Some. rewrite Hnth. discriminate.
Qed.

Lemma global_ok_grow : forall env env' g more,
  vec_list env'.(module_Env_global_types)
    = vec_list env.(module_Env_global_types) ++ more ->
  to_Z env'.(module_Env_num_imported_globals)
    = to_Z env.(module_Env_num_imported_globals) ->
  global_ok env g -> global_ok env' g.
Proof.
  intros env env' g more Hg Hn H.
  apply (const_expr_ok_grow env env' _ _ more Hg Hn H).
Qed.

Lemma decode_global_section_loop_sound : forall m data env count q i q' env',
  to_Z count - to_Z i <= Z.of_nat m ->
  module_decode_global_section_loop data env count q i
    = Ok (Core_result_Result_Ok q', env') ->
  exists gls,
    vec_list env'.(module_Env_globals) = vec_list env.(module_Env_globals) ++ gls
    /\ env' = env_with_global env env'.(module_Env_globals)
                                  env'.(module_Env_global_types)
    /\ repr_rep repr_global (Z.to_nat (to_Z count - to_Z i))
         (bytes_from data q) (List.map translate_global gls)
         (bytes_from data q')
    /\ vec_list env'.(module_Env_global_types)
         = vec_list env.(module_Env_global_types)
           ++ List.map (fun g => g.(module_Global_gtype)) gls
    /\ List.Forall (global_ok env') gls.
Proof.
  induction m as [|m IH]; intros data env count q i q' env' Hmeas H;
    unfold module_decode_global_section_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (i s>= count) eqn:Hge.
  1,3: injection H as <- <-; exists []; rewrite app_nil_r;
       split; [reflexivity|]; split; [apply env_with_global_refl|];
       split; [| split; [exact (eq_sym (app_nil_r _)) | apply List.Forall_nil]];
       apply scalar_geb_true_ge in Hge;
       rewrite to_nat_nonpos by lia; apply repr_rep_nil.
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (module_decode_global_type data q) as [r|] eqn:Hgt;
      cbn [bind] in H; [|discriminate].
    destruct r as [[gtype q1]|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (module_decode_const_expr data q1 env
                gtype.(types_GlobalType_valtype)) as [r1|] eqn:Hinit;
      cbn [bind] in H; [|discriminate].
    destruct r1 as [[init q2]|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (alloc_vec_Vec_push env.(module_Env_global_types) gtype)
      as [v|] eqn:Hpv; cbn [bind] in H; [|discriminate].
    destruct (alloc_vec_Vec_push env.(module_Env_globals)
                {| module_Global_gtype := gtype; module_Global_init := init |})
      as [v1|] eqn:Hpv1; cbn [bind] in H; [|discriminate].
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in H;
      [|discriminate].
    pose proof (scalar_add_val _ _ _ 1 Hadd eq_refl) as Hi2.
    destruct (IH data (env_with_global env v1 v) count q2 i2 q' env'
                (ltac:(cbn in Hmeas; lia)) H)
      as [gls [Hlist [Henv [Hrep [Hgts Hoks]]]]].
    assert (Hgtsout : vec_list env'.(module_Env_global_types)
                      = vec_list env.(module_Env_global_types)
                        ++ List.map (fun g => g.(module_Global_gtype))
                             ({| module_Global_gtype := gtype;
                                 module_Global_init := init |} :: gls)).
    { rewrite Hgts. cbn [env_with_global module_Env_global_types].
      rewrite (vec_push_spec _ _ _ Hpv). rewrite <- app_assoc.
      cbn [List.map List.app module_Global_gtype]. reflexivity. }
    assert (Hnigout : to_Z env'.(module_Env_num_imported_globals)
                      = to_Z env.(module_Env_num_imported_globals))
      by (rewrite Henv;
          cbn [env_with_global module_Env_num_imported_globals]; reflexivity).
    exists ({| module_Global_gtype := gtype; module_Global_init := init |} :: gls).
    split; [|split; [|split; [|split]]].
    + rewrite Hlist. cbn [env_with_global module_Env_globals].
      rewrite (vec_push_spec _ _ _ Hpv1). rewrite <- app_assoc. reflexivity.
    + rewrite Henv at 1. apply env_with_global_idem.
    + assert (Hcnt : to_Z count - to_Z i = (to_Z count - to_Z i2) + 1) by lia.
      rewrite Hcnt. rewrite Z_to_nat_add1 by lia.
      cbn [List.map]. eapply repr_rep_cons; [|exact Hrep].
      unfold translate_global. cbn [module_Global_gtype module_Global_init].
      apply repr_global_intro with (p1 := bytes_from data q1).
      * apply (decode_global_type_sound _ _ _ _ Hgt).
      * apply (decode_const_expr_sound _ _ _ _ _ _ Hinit).
    + exact Hgtsout.
    + apply List.Forall_cons; [| exact Hoks].
      apply (global_ok_grow env env' _ _ Hgtsout Hnigout).
      unfold global_ok. cbn [module_Global_gtype module_Global_init].
      exact (decode_const_expr_typed _ _ _ _ _ _ Hinit).
Qed.

Lemma decode_global_section_sound : forall data pos env q' env',
  module_decode_global_section data pos env
    = Ok (Core_result_Result_Ok q', env') ->
  exists gls,
    vec_list env'.(module_Env_globals) = vec_list env.(module_Env_globals) ++ gls
    /\ env' = env_with_global env env'.(module_Env_globals)
                                  env'.(module_Env_global_types)
    /\ repr_vec repr_global (bytes_from data pos)
         (List.map translate_global gls) (bytes_from data q')
    /\ vec_list env'.(module_Env_global_types)
         = vec_list env.(module_Env_global_types)
           ++ List.map (fun g => g.(module_Global_gtype)) gls
    /\ List.Forall (global_ok env') gls.
Proof.
  intros data pos env q' env' H. unfold module_decode_global_section in H.
  destruct (reader_read_u32_leb data pos) as [r|] eqn:Hn; cbn [bind] in H;
    [|discriminate].
  destruct r as [[count p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (decode_global_section_loop_sound (Z.to_nat (to_Z count)) data env
              count p 0%u32 q' env')
    as [gls [Hlist [Henv [Hrep [Hgts Hoks]]]]].
  - assert (H0 : to_Z 0%u32 = 0) by reflexivity.
    pose proof (u32_nonneg count). lia.
  - exact H.
  - exists gls. split; [exact Hlist|]. split; [exact Henv|].
    split; [| split; [exact Hgts | exact Hoks]].
    apply repr_vec_intro with (n := to_Z count) (mid := bytes_from data p).
    + apply (read_u32_leb_sound _ _ _ _ Hn).
    + assert (H0 : to_Z 0%u32 = 0) by reflexivity.
      rewrite H0 in Hrep. rewrite Z.sub_0_r in Hrep. exact Hrep.
Qed.

(** Spec 5.5.10: [exportsec ::= ex*:vec(export)]. That the index is in range
    and the name unused are spec 3.4.11, and do not appear in the format. *)
Definition translate_exportdesc (d : module_ExportDesc_t) : module_export_desc :=
  match d with
  | Module_ExportDesc_Func x => MED_func (translate_idx x)
  | Module_ExportDesc_Table x => MED_table (translate_idx x)
  | Module_ExportDesc_Memory x => MED_mem (translate_idx x)
  | Module_ExportDesc_Global x => MED_global (translate_idx x)
  end.

Definition translate_export (e : module_Export_t) : module_export :=
  {| modexp_name := translate_name e.(module_Export_name);
     modexp_desc := translate_exportdesc e.(module_Export_desc) |}.

Definition env_with_exports (env : module_Env_t)
                            (v : alloc_vec_Vec module_Export_t) : module_Env_t :=
  {| module_Env_types := env.(module_Env_types);
     module_Env_imports := env.(module_Env_imports);
     module_Env_globals := env.(module_Env_globals);
     module_Env_exports := v;
     module_Env_elements := env.(module_Env_elements);
     module_Env_start := env.(module_Env_start);
     module_Env_func_type_indices := env.(module_Env_func_type_indices);
     module_Env_func_types := env.(module_Env_func_types);
     module_Env_table_types := env.(module_Env_table_types);
     module_Env_mem_types := env.(module_Env_mem_types);
     module_Env_global_types := env.(module_Env_global_types);
     module_Env_num_imported_funcs := env.(module_Env_num_imported_funcs);
     module_Env_num_imported_globals := env.(module_Env_num_imported_globals) |}.

Lemma env_with_exports_refl : forall env,
  env = env_with_exports env env.(module_Env_exports).
Proof. intros env. destruct env. reflexivity. Qed.

Lemma env_with_exports_idem : forall env v w,
  env_with_exports (env_with_exports env v) w = env_with_exports env w.
Proof. intros env v w. reflexivity. Qed.

(** The kind byte and the descriptor it produces, which is the pairing
    [repr_exportdesc] states. The Rust function needs qualifying: WasmCert's
    [datatypes] has a *type* of the same name, and it is imported last. *)
Lemma export_desc_sound : forall env kind idx d bs rest,
  Itasca.Aeneas_Specs.module_export_desc env kind idx = Ok (Core_result_Result_Ok d) ->
  repr_u32 bs (to_Z idx) rest ->
  repr_exportdesc (to_Z kind :: bs) (translate_exportdesc d) rest.
Proof.
  intros env kind idx d bs rest H Hidx. unfold Itasca.Aeneas_Specs.module_export_desc in H.
  destruct (scalar_cast U32 Usize idx) as [i|]; cbn [bind] in H;
    [|discriminate].
  destruct (kind s= 0%u8) eqn:E0.
  { destruct (i s>= alloc_vec_Vec_len env.(module_Env_func_types));
      [discriminate|].
    injection H as <-. rewrite (scalar_eqb_val _ _ 0 E0 eq_refl).
    apply repr_exportdesc_func. apply repr_idx_intro. exact Hidx. }
  destruct (kind s= 1%u8) eqn:E1.
  { destruct (i s>= alloc_vec_Vec_len env.(module_Env_table_types));
      [discriminate|].
    injection H as <-. rewrite (scalar_eqb_val _ _ 1 E1 eq_refl).
    apply repr_exportdesc_table. apply repr_idx_intro. exact Hidx. }
  destruct (kind s= 2%u8) eqn:E2.
  { destruct (i s>= alloc_vec_Vec_len env.(module_Env_mem_types));
      [discriminate|].
    injection H as <-. rewrite (scalar_eqb_val _ _ 2 E2 eq_refl).
    apply repr_exportdesc_mem. apply repr_idx_intro. exact Hidx. }
  destruct (kind s= 3%u8) eqn:E3; [|discriminate].
  destruct (i s>= alloc_vec_Vec_len env.(module_Env_global_types));
    [discriminate|].
  injection H as <-. rewrite (scalar_eqb_val _ _ 3 E3 eq_refl).
  apply repr_exportdesc_global. apply repr_idx_intro. exact Hidx.
Qed.

(** Spec 3.4.14 and the one uniqueness rule the format does not carry: an
    export's index is in the space its kind names, and no two exports share a
    name. [export_name_taken] is a linear scan, so what an accepting run gives
    is that the new name differs from every name already there, which is
    exactly the step of [NoDup]. *)
Definition export_name (e : module_Export_t) : list Z :=
  byte_list e.(module_Export_name).

Definition exports_distinct (env : module_Env_t) : Prop :=
  List.NoDup (List.map export_name (vec_list env.(module_Env_exports))).

Definition export_desc_ok (env : module_Env_t) (e : module_Export_t) : Prop :=
  match e.(module_Export_desc) with
  | Module_ExportDesc_Func x =>
      to_Z x < Z.of_nat (List.length (vec_list env.(module_Env_func_types)))
  | Module_ExportDesc_Table x =>
      to_Z x < Z.of_nat (List.length (vec_list env.(module_Env_table_types)))
  | Module_ExportDesc_Memory x =>
      to_Z x < Z.of_nat (List.length (vec_list env.(module_Env_mem_types)))
  | Module_ExportDesc_Global x =>
      to_Z x < Z.of_nat (List.length (vec_list env.(module_Env_global_types)))
  end.

(** Equal byte strings compare equal, so a scan that reported "not taken"
    means every name already there is a different byte string. *)
Lemma nodup_app_one : forall A (l : list A) x,
  List.NoDup l -> ~ List.In x l -> List.NoDup (l ++ [x]).
Proof.
  intros A l x Hnd Hin. induction l as [|y l IH].
  - cbn [List.app]. apply List.NoDup_cons; [exact Hin | apply List.NoDup_nil].
  - inversion Hnd as [|y' l' Hy Hl]; subst.
    cbn [List.app]. apply List.NoDup_cons.
    + intros Hcon. apply List.in_app_or in Hcon.
      destruct Hcon as [Hcon|Hcon]; [exact (Hy Hcon)|].
      destruct Hcon as [Hcon|Hcon]; [|destruct Hcon].
      apply Hin. left. symmetry. exact Hcon.
    + apply IH; [exact Hl|]. intros Hcon. apply Hin. right. exact Hcon.
Qed.

Lemma export_desc_range : forall env kind idx d,
  Itasca.Aeneas_Specs.module_export_desc env kind idx
    = Ok (Core_result_Result_Ok d) ->
  match d with
  | Module_ExportDesc_Func x =>
      to_Z x < Z.of_nat (List.length (vec_list env.(module_Env_func_types)))
  | Module_ExportDesc_Table x =>
      to_Z x < Z.of_nat (List.length (vec_list env.(module_Env_table_types)))
  | Module_ExportDesc_Memory x =>
      to_Z x < Z.of_nat (List.length (vec_list env.(module_Env_mem_types)))
  | Module_ExportDesc_Global x =>
      to_Z x < Z.of_nat (List.length (vec_list env.(module_Env_global_types)))
  end.
Proof.
  intros env kind idx d H.
  unfold Itasca.Aeneas_Specs.module_export_desc in H.
  destruct (scalar_cast U32 Usize idx) as [i|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  assert (Hi : to_Z i = to_Z idx)
    by (unfold scalar_cast in Hcast; apply mk_scalar_ok_to_Z in Hcast;
        exact Hcast).
  destruct (kind s= 0%u8).
  { destruct (i s>= alloc_vec_Vec_len env.(module_Env_func_types)) eqn:Hr;
      [discriminate|].
    injection H as <-. apply scalar_geb_false_lt in Hr.
    rewrite vec_len_spec in Hr. lia. }
  destruct (kind s= 1%u8).
  { destruct (i s>= alloc_vec_Vec_len env.(module_Env_table_types)) eqn:Hr;
      [discriminate|].
    injection H as <-. apply scalar_geb_false_lt in Hr.
    rewrite vec_len_spec in Hr. lia. }
  destruct (kind s= 2%u8).
  { destruct (i s>= alloc_vec_Vec_len env.(module_Env_mem_types)) eqn:Hr;
      [discriminate|].
    injection H as <-. apply scalar_geb_false_lt in Hr.
    rewrite vec_len_spec in Hr. lia. }
  destruct (kind s= 3%u8); [|discriminate].
  destruct (i s>= alloc_vec_Vec_len env.(module_Env_global_types)) eqn:Hr;
    [discriminate|].
  injection H as <-. apply scalar_geb_false_lt in Hr.
  rewrite vec_len_spec in Hr. lia.
Qed.

Lemma names_equal_loop_true : forall m (a b : slice u8) i,
  Z.of_nat (List.length (vec_list a)) - to_Z i <= Z.of_nat m ->
  0 <= to_Z i ->
  byte_list a = byte_list b ->
  module_names_equal_loop a b i = Ok true.
Proof.
  induction m as [|m IH]; intros a b i Hmeas Hi Heq;
    unfold module_names_equal_loop; rewrite loop_unfold;
    cbn beta iota; destruct (i s>= slice_len a) eqn:Hgef;
    try reflexivity.
  1: { exfalso. pose proof (scalar_geb_false_lt _ _ Hgef) as Hge.
       rewrite slice_len_spec in Hge. lia. }
  pose proof (scalar_geb_false_lt _ _ Hgef) as Hge.
  rewrite slice_len_spec in Hge.
  assert (Hlen : List.length (vec_list a) = List.length (vec_list b)).
  { apply (f_equal (@List.length Z)) in Heq. unfold byte_list in Heq.
    rewrite List.map_length in Heq. rewrite List.map_length in Heq.
    exact Heq. }
  destruct (slice_index_usize a i) as [x|] eqn:Hx.
  2: { exfalso. rewrite slice_index_usize_spec in Hx.
       destruct (List.nth_error (vec_list a) (Z.to_nat (to_Z i))) eqn:Hn;
         [discriminate|].
       apply List.nth_error_None in Hn. lia. }
  cbn [bind].
  destruct (slice_index_usize b i) as [y|] eqn:Hy.
  2: { exfalso. rewrite slice_index_usize_spec in Hy.
       destruct (List.nth_error (vec_list b) (Z.to_nat (to_Z i))) eqn:Hn;
         [discriminate|].
       apply List.nth_error_None in Hn. lia. }
  cbn [bind].
  assert (Hxy : to_Z x = to_Z y).
  { rewrite slice_index_usize_spec in Hx. rewrite slice_index_usize_spec in Hy.
    destruct (List.nth_error (vec_list a) (Z.to_nat (to_Z i))) as [x0|] eqn:Hna;
      [|discriminate].
    destruct (List.nth_error (vec_list b) (Z.to_nat (to_Z i))) as [y0|] eqn:Hnb;
      [|discriminate].
    injection Hx as <-. injection Hy as <-.
    assert (Hma : List.nth_error (byte_list a) (Z.to_nat (to_Z i))
                  = Some (to_Z x0))
      by (unfold byte_list; rewrite (List.map_nth_error _ _ _ Hna); reflexivity).
    assert (Hmb : List.nth_error (byte_list b) (Z.to_nat (to_Z i))
                  = Some (to_Z y0))
      by (unfold byte_list; rewrite (List.map_nth_error _ _ _ Hnb); reflexivity).
    rewrite Heq in Hma. rewrite Hma in Hmb. injection Hmb as <-. reflexivity. }
  destruct (x s<> y) eqn:Hne.
  { exfalso. apply scalar_neqb_true in Hne. exact (Hne Hxy). }
  cbn [bind].
  destruct (usize_add_1_ok i (usize_add_1_lt_max i a Hgef))
    as [i2 [Hadd Hi2]].
  rewrite Hadd. cbn [bind].
  apply (IH a b i2); [lia | lia | exact Heq].
Qed.

Lemma names_equal_true : forall (a b : slice u8),
  byte_list a = byte_list b -> module_names_equal a b = Ok true.
Proof.
  intros a b Heq. unfold module_names_equal.
  assert (Hlen : List.length (vec_list a) = List.length (vec_list b)).
  { apply (f_equal (@List.length Z)) in Heq. unfold byte_list in Heq.
    rewrite List.map_length in Heq. rewrite List.map_length in Heq.
    exact Heq. }
  destruct (slice_len a s<> slice_len b) eqn:Hne.
  { exfalso. apply scalar_neqb_true in Hne. apply Hne.
    rewrite slice_len_spec. rewrite slice_len_spec. rewrite Hlen. reflexivity. }
  apply (names_equal_loop_true (List.length (vec_list a)) a b 0%usize);
    [ assert (H0 : to_Z 0%usize = 0) by reflexivity; lia
    | assert (H0 : to_Z 0%usize = 0) by reflexivity; lia
    | exact Heq ].
Qed.

Lemma export_name_taken_loop_false : forall m env nm i,
  Z.of_nat (List.length (vec_list env.(module_Env_exports))) - to_Z i
    <= Z.of_nat m ->
  0 <= to_Z i ->
  module_export_name_taken_loop env nm i = Ok false ->
  forall k e, (Z.to_nat (to_Z i) <= k)%nat ->
    List.nth_error (vec_list env.(module_Env_exports)) k = Some e ->
    byte_list e.(module_Export_name) <> byte_list nm.
Proof.
  induction m as [|m IH]; intros env nm i Hmeas Hi H k e Hk Hnth;
    unfold module_export_name_taken_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H;
    destruct (i s>= alloc_vec_Vec_len env.(module_Env_exports)) eqn:Hge.
  1,3: exfalso; apply scalar_geb_true_ge in Hge;
       rewrite vec_len_spec in Hge;
       assert (Hlen := proj1 (List.nth_error_Some
                                (vec_list env.(module_Env_exports)) k)
                         (ltac:(rewrite Hnth; discriminate)));
       lia.
  1: { exfalso. apply scalar_geb_false_lt in Hge.
       rewrite vec_len_spec in Hge. cbn in Hmeas. lia. }
  apply scalar_geb_false_lt in Hge. rewrite vec_len_spec in Hge.
  destruct (alloc_vec_Vec_index
              (core_slice_index_SliceIndexUsizeSliceInst module_Export_t)
              env.(module_Env_exports) i) as [e0|] eqn:He0; cbn [bind] in H;
    [|discriminate].
  rewrite vec_index_spec in He0.
  destruct (List.nth_error (vec_list env.(module_Env_exports))
              (Z.to_nat (to_Z i))) as [e1|] eqn:Hnth1; [|discriminate].
  injection He0 as <-.
  rewrite vec_deref_spec in H.
  destruct (module_names_equal e1.(module_Export_name) nm) as [taken|] eqn:Hnm;
    cbn [bind] in H; [|discriminate].
  destruct taken; [discriminate|].
  destruct (usize_add_1_ok i (ltac:(pose proof (usize_le_max
              (alloc_vec_Vec_len env.(module_Env_exports)));
              rewrite vec_len_spec in *; lia)))
    as [i2 [Hadd Hi2]].
  rewrite Hadd in H. cbn [bind] in H.
  destruct (Nat.eq_dec k (Z.to_nat (to_Z i))) as [->|Hne].
  - (* the entry the scan is looking at *)
    rewrite Hnth1 in Hnth. injection Hnth as <-.
    intros Heq. rewrite (names_equal_true _ _ Heq) in Hnm. discriminate.
  - apply (IH env nm i2 (ltac:(lia)) (ltac:(lia)) H k e (ltac:(lia)) Hnth).
Qed.

Lemma export_name_taken_false : forall env nm,
  module_export_name_taken env nm = Ok false ->
  forall e, List.In e (vec_list env.(module_Env_exports)) ->
    byte_list e.(module_Export_name) <> byte_list nm.
Proof.
  intros env nm H e Hin. unfold module_export_name_taken in H.
  apply List.In_nth_error in Hin. destruct Hin as [k Hnth].
  apply (export_name_taken_loop_false
           (List.length (vec_list env.(module_Env_exports))) env nm 0%usize
           (ltac:(assert (H0 : to_Z 0%usize = 0) by reflexivity; lia))
           (ltac:(assert (H0 : to_Z 0%usize = 0) by reflexivity; lia))
           H k e (ltac:(assert (H0 : to_Z 0%usize = 0) by reflexivity;
                        rewrite H0; cbn; lia)) Hnth).
Qed.

Lemma decode_export_section_loop_sound : forall m data env count q i q' env',
  to_Z count - to_Z i <= Z.of_nat m ->
  module_decode_export_section_loop data env count q i
    = Ok (Core_result_Result_Ok q', env') ->
  exists exs,
    vec_list env'.(module_Env_exports) = vec_list env.(module_Env_exports) ++ exs
    /\ env' = env_with_exports env env'.(module_Env_exports)
    /\ repr_rep repr_export (Z.to_nat (to_Z count - to_Z i))
         (bytes_from data q) (List.map translate_export exs)
         (bytes_from data q')
    /\ (exports_distinct env -> exports_distinct env')
    /\ List.Forall (export_desc_ok env) exs.
Proof.
  induction m as [|m IH]; intros data env count q i q' env' Hmeas H;
    unfold module_decode_export_section_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (i s>= count) eqn:Hge.
  1,3: injection H as <- <-; exists []; rewrite app_nil_r;
       split; [reflexivity|]; split; [apply env_with_exports_refl|];
       split; [| split; [exact (fun Hd => Hd) | apply List.Forall_nil]];
       apply scalar_geb_true_ge in Hge;
       rewrite to_nat_nonpos by lia; apply repr_rep_nil.
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (module_decode_name data q) as [r|] eqn:Hnm; cbn [bind] in H;
      [|discriminate].
    destruct r as [[name q1]|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    rewrite vec_deref_spec in H.
    destruct (module_export_name_taken env name) as [taken|] eqn:Htaken;
      cbn [bind] in H; [|discriminate].
    destruct taken; [discriminate|].
    destruct (reader_read_byte data q1) as [r1|] eqn:Hk; cbn [bind] in H;
      [|discriminate].
    destruct r1 as [[kind q2]|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (reader_read_u32_leb data q2) as [r2|] eqn:Hidx; cbn [bind] in H;
      [|discriminate].
    destruct r2 as [[idx q3]|e2]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (Itasca.Aeneas_Specs.module_export_desc env kind idx) as [r3|] eqn:Hd;
      cbn [bind] in H; [|discriminate].
    destruct r3 as [d|e3]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (alloc_vec_Vec_push env.(module_Env_exports)
                {| module_Export_name := name; module_Export_desc := d |})
      as [v|] eqn:Hpv; cbn [bind] in H; [|discriminate].
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in H;
      [|discriminate].
    pose proof (scalar_add_val _ _ _ 1 Hadd eq_refl) as Hi2.
    destruct (IH data (env_with_exports env v) count q3 i2 q' env'
                (ltac:(cbn in Hmeas; lia)) H)
      as [exs [Hlist [Henv [Hrep [Hdist Hall]]]]].
    exists ({| module_Export_name := name; module_Export_desc := d |} :: exs).
    split; [|split; [|split; [|split]]].
    + rewrite Hlist. cbn [env_with_exports module_Env_exports].
      rewrite (vec_push_spec _ _ _ Hpv). rewrite <- app_assoc. reflexivity.
    + rewrite Henv at 1. apply env_with_exports_idem.
    + assert (Hcnt : to_Z count - to_Z i = (to_Z count - to_Z i2) + 1) by lia.
      rewrite Hcnt. rewrite Z_to_nat_add1 by lia.
      cbn [List.map]. eapply repr_rep_cons; [|exact Hrep].
      unfold translate_export. cbn [module_Export_name module_Export_desc].
      apply repr_export_intro with (p1 := bytes_from data q1).
      * apply (decode_name_sound _ _ _ _ Hnm).
      * rewrite (proj1 (read_byte_ok _ _ _ _ Hk)).
        apply (export_desc_sound env kind idx); [exact Hd|].
        apply (read_u32_leb_sound _ _ _ _ Hidx).
    + (* the new name is not one of those already there *)
      intros Hd0. apply Hdist.
      unfold exports_distinct.
      cbn [env_with_exports module_Env_exports].
      rewrite (vec_push_spec _ _ _ Hpv). rewrite List.map_app.
      apply nodup_app_one; [exact Hd0|].
      intros Hin. apply List.in_map_iff in Hin.
      destruct Hin as [e [Hname Hine]].
      apply (export_name_taken_false env name Htaken e Hine).
      unfold export_name in Hname. cbn [module_Export_name] in Hname.
      exact Hname.
    + apply List.Forall_cons.
      * unfold export_desc_ok. cbn [module_Export_desc].
        exact (export_desc_range _ _ _ _ Hd).
      * cbn [env_with_exports module_Env_func_types module_Env_table_types
             module_Env_mem_types module_Env_global_types] in Hall.
        exact Hall.
Qed.

Lemma decode_export_section_sound : forall data pos env q' env',
  module_decode_export_section data pos env
    = Ok (Core_result_Result_Ok q', env') ->
  exists exs,
    vec_list env'.(module_Env_exports) = vec_list env.(module_Env_exports) ++ exs
    /\ env' = env_with_exports env env'.(module_Env_exports)
    /\ repr_vec repr_export (bytes_from data pos)
         (List.map translate_export exs) (bytes_from data q')
    /\ (exports_distinct env -> exports_distinct env')
    /\ List.Forall (export_desc_ok env) exs.
Proof.
  intros data pos env q' env' H. unfold module_decode_export_section in H.
  destruct (reader_read_u32_leb data pos) as [r|] eqn:Hn; cbn [bind] in H;
    [|discriminate].
  destruct r as [[count p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (decode_export_section_loop_sound (Z.to_nat (to_Z count)) data env
              count p 0%u32 q' env')
    as [exs [Hlist [Henv [Hrep [Hdist Hall]]]]].
  - assert (H0 : to_Z 0%u32 = 0) by reflexivity.
    pose proof (u32_nonneg count). lia.
  - exact H.
  - exists exs. split; [exact Hlist|]. split; [exact Henv|].
    split; [| split; [exact Hdist | exact Hall]].
    apply repr_vec_intro with (n := to_Z count) (mid := bytes_from data p).
    + apply (read_u32_leb_sound _ _ _ _ Hn).
    + assert (H0 : to_Z 0%u32 = 0) by reflexivity.
      rewrite H0 in Hrep. rewrite Z.sub_0_r in Hrep. exact Hrep.
Qed.

(** Spec 5.5.11: [startsec ::= section_8(start)], [start ::= x:funcidx]. That
    the function exists and takes and returns nothing is spec 3.4.13. *)
Definition env_with_start (env : module_Env_t)
                          (s : option (scalar U32)) : module_Env_t :=
  {| module_Env_types := env.(module_Env_types);
     module_Env_imports := env.(module_Env_imports);
     module_Env_globals := env.(module_Env_globals);
     module_Env_exports := env.(module_Env_exports);
     module_Env_elements := env.(module_Env_elements);
     module_Env_start := s;
     module_Env_func_type_indices := env.(module_Env_func_type_indices);
     module_Env_func_types := env.(module_Env_func_types);
     module_Env_table_types := env.(module_Env_table_types);
     module_Env_mem_types := env.(module_Env_mem_types);
     module_Env_global_types := env.(module_Env_global_types);
     module_Env_num_imported_funcs := env.(module_Env_num_imported_funcs);
     module_Env_num_imported_globals := env.(module_Env_num_imported_globals) |}.

Lemma env_with_start_refl : forall env,
  env = env_with_start env env.(module_Env_start).
Proof. intros env. destruct env. reflexivity. Qed.

Definition translate_start (s : option (scalar U32)) : option module_start :=
  option_map (fun x => {| modstart_func := translate_idx x |}) s.

(** Spec 3.4.13: the start function is in the function space and takes and
    returns nothing. *)
Definition start_ok (env : module_Env_t) : Prop :=
  match env.(module_Env_start) with
  | None => True
  | Some x =>
      exists ft,
        List.nth_error (vec_list env.(module_Env_func_types))
                       (Z.to_nat (to_Z x)) = Some ft
        /\ vec_list ft.(types_FuncType_params) = []
        /\ vec_list ft.(types_FuncType_results) = []
  end.

Lemma decode_start_section_sound : forall data pos env q' env',
  module_decode_start_section data pos env
    = Ok (Core_result_Result_Ok q', env') ->
  env' = env_with_start env env'.(module_Env_start)
  /\ repr_start (bytes_from data pos) (translate_start env'.(module_Env_start))
       (bytes_from data q')
  /\ start_ok env'.
Proof.
  intros data pos env q' env' H. unfold module_decode_start_section in H.
  destruct (reader_read_u32_leb data pos) as [r|] eqn:Hidx; cbn [bind] in H;
    [|discriminate].
  destruct r as [[idx p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (scalar_cast U32 Usize idx) as [i|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  assert (Hi : to_Z i = to_Z idx)
    by (unfold scalar_cast in Hcast; apply mk_scalar_ok_to_Z in Hcast;
        exact Hcast).
  destruct (i s>= alloc_vec_Vec_len env.(module_Env_func_types)); [discriminate|].
  destruct (alloc_vec_Vec_index
              (core_slice_index_SliceIndexUsizeSliceInst types_FuncType_t)
              env.(module_Env_func_types) i) as [ft|] eqn:Hft;
    cbn [bind] in H; [|discriminate].
  rewrite vec_index_spec in Hft.
  destruct (List.nth_error (vec_list env.(module_Env_func_types))
              (Z.to_nat (to_Z i))) as [ft0|] eqn:Hnth; [|discriminate].
  injection Hft as <-.
  rewrite vec_is_empty_spec in H. cbn [bind] in H.
  destruct (vec_list ft0.(types_FuncType_params)) eqn:Hps; [|discriminate].
  rewrite vec_is_empty_spec in H. cbn [bind] in H.
  destruct (vec_list ft0.(types_FuncType_results)) eqn:Hrs; [|discriminate].
  injection H as <- <-. cbn [env_with_start module_Env_start]. split.
  - destruct env. reflexivity.
  - split.
    + unfold repr_start, translate_start. cbn [option_map].
      exists (translate_idx idx). split; [|reflexivity].
      apply repr_idx_intro. apply (read_u32_leb_sound _ _ _ _ Hidx).
    + unfold start_ok. cbn [env_with_start module_Env_start module_Env_func_types].
      exists ft0. rewrite Hi in Hnth.
      split; [exact Hnth | split; [exact Hps | exact Hrs]].
Qed.

(** Spec 5.5.12: [elemsec ::= seg*:vec(elem)], and Wasm 1.0's single form
    [elem ::= x:tableidx e:expr y*:vec(funcidx)]. The header of
    [Spec_Module.v] describes how that lands in the 2.0 [module_element]. *)
Definition translate_element (el : module_Element_t) : module_element :=
  {| modelem_type := T_funcref;
     modelem_init :=
       List.map (fun y => [BI_ref_func (translate_idx y)])
         (vec_list el.(module_Element_init));
     modelem_mode :=
       ME_active (translate_idx el.(module_Element_table_idx))
         [translate_const_expr el.(module_Element_offset)] |}.

Definition env_with_elements (env : module_Env_t)
                             (v : alloc_vec_Vec module_Element_t) : module_Env_t :=
  {| module_Env_types := env.(module_Env_types);
     module_Env_imports := env.(module_Env_imports);
     module_Env_globals := env.(module_Env_globals);
     module_Env_exports := env.(module_Env_exports);
     module_Env_elements := v;
     module_Env_start := env.(module_Env_start);
     module_Env_func_type_indices := env.(module_Env_func_type_indices);
     module_Env_func_types := env.(module_Env_func_types);
     module_Env_table_types := env.(module_Env_table_types);
     module_Env_mem_types := env.(module_Env_mem_types);
     module_Env_global_types := env.(module_Env_global_types);
     module_Env_num_imported_funcs := env.(module_Env_num_imported_funcs);
     module_Env_num_imported_globals := env.(module_Env_num_imported_globals) |}.

Lemma env_with_elements_refl : forall env,
  env = env_with_elements env env.(module_Env_elements).
Proof. intros env. destruct env. reflexivity. Qed.

Lemma env_with_elements_idem : forall env v w,
  env_with_elements (env_with_elements env v) w = env_with_elements env w.
Proof. intros env v w. reflexivity. Qed.

(** [vec(funcidx)], the one vector a 1.0 element segment carries. *)
Lemma decode_func_indices_loop_sound :
  forall m data env count out q i out' q',
  to_Z count - to_Z i <= Z.of_nat m ->
  module_decode_func_indices_loop data env count out q i
    = Ok (Core_result_Result_Ok (out', q')) ->
  exists xs,
    vec_list out' = vec_list out ++ xs
    /\ repr_rep repr_idx (Z.to_nat (to_Z count - to_Z i))
         (bytes_from data q) (List.map translate_idx xs)
         (bytes_from data q')
    /\ List.Forall (fun x => to_Z x
           < Z.of_nat (List.length (vec_list env.(module_Env_func_types)))) xs.
Proof.
  induction m as [|m IH]; intros data env count out q i out' q' Hmeas H;
    unfold module_decode_func_indices_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (i s>= count) eqn:Hge.
  1,3: injection H as <- <-; exists []; rewrite app_nil_r;
       split; [reflexivity|]; split; [| apply List.Forall_nil];
       apply scalar_geb_true_ge in Hge;
       rewrite to_nat_nonpos by lia; apply repr_rep_nil.
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (reader_read_u32_leb data q) as [r|] eqn:Hidx; cbn [bind] in H;
      [|discriminate].
    destruct r as [[idx q1]|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (scalar_cast U32 Usize idx) as [j|] eqn:Hcast; cbn [bind] in H;
      [|discriminate].
    assert (Hj : to_Z j = to_Z idx)
      by (unfold scalar_cast in Hcast; apply mk_scalar_ok_to_Z in Hcast;
          exact Hcast).
    destruct (j s>= alloc_vec_Vec_len env.(module_Env_func_types)) eqn:Hrange;
      [discriminate|].
    apply scalar_geb_false_lt in Hrange. rewrite vec_len_spec in Hrange.
    destruct (alloc_vec_Vec_push out idx) as [out2|] eqn:Hpush;
      cbn [bind] in H; [|discriminate].
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in H;
      [|discriminate].
    pose proof (scalar_add_val _ _ _ 1 Hadd eq_refl) as Hi2.
    destruct (IH data env count out2 q1 i2 out' q'
                (ltac:(cbn in Hmeas; lia)) H) as [xs [Hlist [Hrep Hall]]].
    exists (idx :: xs). split; [|split].
    + rewrite Hlist. rewrite (vec_push_spec _ _ _ Hpush).
      rewrite <- app_assoc. reflexivity.
    + assert (Hcnt : to_Z count - to_Z i = (to_Z count - to_Z i2) + 1) by lia.
      rewrite Hcnt. rewrite Z_to_nat_add1 by lia.
      cbn [List.map]. eapply repr_rep_cons; [|exact Hrep].
      apply repr_idx_intro. apply (read_u32_leb_sound _ _ _ _ Hidx).
    + apply List.Forall_cons; [lia | exact Hall].
Qed.

Lemma decode_func_indices_sound : forall data pos env out q',
  module_decode_func_indices data pos env
    = Ok (Core_result_Result_Ok (out, q')) ->
  repr_vec repr_idx (bytes_from data pos)
    (List.map translate_idx (vec_list out)) (bytes_from data q')
  /\ List.Forall (fun x => to_Z x
         < Z.of_nat (List.length (vec_list env.(module_Env_func_types))))
       (vec_list out).
Proof.
  intros data pos env out q' H. unfold module_decode_func_indices in H.
  destruct (reader_read_u32_leb data pos) as [r|] eqn:Hn; cbn [bind] in H;
    [|discriminate].
  destruct r as [[count p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (decode_func_indices_loop_sound (Z.to_nat (to_Z count)) data env
              count (alloc_vec_Vec_new (scalar U32)) p 0%u32 out q')
    as [xs [Hlist [Hrep Hall]]].
  - assert (H0 : to_Z 0%u32 = 0) by reflexivity.
    pose proof (u32_nonneg count). lia.
  - exact H.
  - assert (Hxs : vec_list out = xs)
      by (rewrite Hlist;
          cbn [vec_list alloc_vec_Vec_new proj1_sig List.app]; reflexivity).
    split.
    + apply repr_vec_intro with (n := to_Z count) (mid := bytes_from data p).
      * apply (read_u32_leb_sound _ _ _ _ Hn).
      * rewrite Hxs.
        assert (H0 : to_Z 0%u32 = 0) by reflexivity.
        rewrite H0 in Hrep. rewrite Z.sub_0_r in Hrep. exact Hrep.
    + rewrite Hxs. exact Hall.
Qed.

(** What the element section checked of a segment: spec 3.4.5's rules that do
    not need the code section. The table index is in the table space, the
    offset is a constant expression of type [i32], and every function the
    segment writes is in the function space. *)
Definition element_ok (env : module_Env_t) (el : module_Element_t) : Prop :=
  to_Z el.(module_Element_table_idx)
    < Z.of_nat (List.length (vec_list env.(module_Env_table_types)))
  /\ const_expr_ok env Types_ValueType_I32 el.(module_Element_offset)
  /\ List.Forall (fun x => to_Z x
         < Z.of_nat (List.length (vec_list env.(module_Env_func_types))))
       (vec_list el.(module_Element_init)).

Lemma decode_element_section_loop_sound : forall m data env count q i q' env',
  to_Z count - to_Z i <= Z.of_nat m ->
  module_decode_element_section_loop data env count q i
    = Ok (Core_result_Result_Ok q', env') ->
  exists els,
    vec_list env'.(module_Env_elements) = vec_list env.(module_Env_elements) ++ els
    /\ env' = env_with_elements env env'.(module_Env_elements)
    /\ repr_rep repr_elem (Z.to_nat (to_Z count - to_Z i))
         (bytes_from data q) (List.map translate_element els)
         (bytes_from data q')
    /\ List.Forall (element_ok env) els.
Proof.
  induction m as [|m IH]; intros data env count q i q' env' Hmeas H;
    unfold module_decode_element_section_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (i s>= count) eqn:Hge.
  1,3: injection H as <- <-; exists []; rewrite app_nil_r;
       split; [reflexivity|]; split; [apply env_with_elements_refl|];
       split; [| apply List.Forall_nil];
       apply scalar_geb_true_ge in Hge;
       rewrite to_nat_nonpos by lia; apply repr_rep_nil.
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (reader_read_u32_leb data q) as [r|] eqn:Htidx; cbn [bind] in H;
      [|discriminate].
    destruct r as [[table_idx q1]|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (scalar_cast U32 Usize table_idx) as [j|] eqn:Hcast;
      cbn [bind] in H; [|discriminate].
    assert (Hj : to_Z j = to_Z table_idx)
      by (unfold scalar_cast in Hcast; apply mk_scalar_ok_to_Z in Hcast;
          exact Hcast).
    destruct (j s>= alloc_vec_Vec_len env.(module_Env_table_types)) eqn:Htr;
      [discriminate|].
    apply scalar_geb_false_lt in Htr. rewrite vec_len_spec in Htr.
    destruct (module_decode_const_expr data q1 env Types_ValueType_I32)
      as [r1|] eqn:Hoff; cbn [bind] in H; [|discriminate].
    destruct r1 as [[offset q2]|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (module_decode_func_indices data q2 env) as [r2|] eqn:Hinit;
      cbn [bind] in H; [|discriminate].
    destruct r2 as [[init q3]|e2]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (alloc_vec_Vec_push env.(module_Env_elements)
                {| module_Element_table_idx := table_idx;
                   module_Element_offset := offset;
                   module_Element_init := init |}) as [v|] eqn:Hpv;
      cbn [bind] in H; [|discriminate].
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in H;
      [|discriminate].
    pose proof (scalar_add_val _ _ _ 1 Hadd eq_refl) as Hi2.
    destruct (IH data (env_with_elements env v) count q3 i2 q' env'
                (ltac:(cbn in Hmeas; lia)) H) as [els [Hlist [Henv [Hrep Hall]]]].
    exists ({| module_Element_table_idx := table_idx;
               module_Element_offset := offset;
               module_Element_init := init |} :: els).
    split; [|split; [|split]].
    + rewrite Hlist. cbn [env_with_elements module_Env_elements].
      rewrite (vec_push_spec _ _ _ Hpv). rewrite <- app_assoc. reflexivity.
    + rewrite Henv at 1. apply env_with_elements_idem.
    + assert (Hcnt : to_Z count - to_Z i = (to_Z count - to_Z i2) + 1) by lia.
      rewrite Hcnt. rewrite Z_to_nat_add1 by lia.
      cbn [List.map]. eapply repr_rep_cons; [|exact Hrep].
      unfold translate_element.
      cbn [module_Element_table_idx module_Element_offset module_Element_init].
      (* [repr_elem] wraps each index the format read; the translation wraps
         each index the decoder kept, which is the same map composed *)
      rewrite <- (List.map_map translate_idx (fun y : funcidx => [BI_ref_func y])).
      apply repr_elem_intro with (p1 := bytes_from data q1)
                                 (p2 := bytes_from data q2).
      * apply repr_idx_intro. apply (read_u32_leb_sound _ _ _ _ Htidx).
      * apply (decode_const_expr_sound _ _ _ _ _ _ Hoff).
      * apply (proj1 (decode_func_indices_sound _ _ _ _ _ Hinit)).
    + apply List.Forall_cons.
      * split; [cbn [module_Element_table_idx]; lia|].
        split; [cbn [module_Element_offset];
                  exact (decode_const_expr_typed _ _ _ _ _ _ Hoff)|].
        cbn [module_Element_init].
        exact (proj2 (decode_func_indices_sound _ _ _ _ _ Hinit)).
      * (* the loop only appended to [elements] *)
        cbn [env_with_elements module_Env_table_types module_Env_func_types
             module_Env_global_types module_Env_num_imported_globals] in Hall.
        exact Hall.
Qed.

Lemma decode_element_section_sound : forall data pos env q' env',
  module_decode_element_section data pos env
    = Ok (Core_result_Result_Ok q', env') ->
  exists els,
    vec_list env'.(module_Env_elements) = vec_list env.(module_Env_elements) ++ els
    /\ env' = env_with_elements env env'.(module_Env_elements)
    /\ repr_vec repr_elem (bytes_from data pos)
         (List.map translate_element els) (bytes_from data q')
    /\ List.Forall (element_ok env) els.
Proof.
  intros data pos env q' env' H. unfold module_decode_element_section in H.
  destruct (reader_read_u32_leb data pos) as [r|] eqn:Hn; cbn [bind] in H;
    [|discriminate].
  destruct r as [[count p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (decode_element_section_loop_sound (Z.to_nat (to_Z count)) data env
              count p 0%u32 q' env') as [els [Hlist [Henv [Hrep Hall]]]].
  - assert (H0 : to_Z 0%u32 = 0) by reflexivity.
    pose proof (u32_nonneg count). lia.
  - exact H.
  - exists els. split; [exact Hlist|]. split; [exact Henv|].
    split; [| exact Hall].
    apply repr_vec_intro with (n := to_Z count) (mid := bytes_from data p).
    + apply (read_u32_leb_sound _ _ _ _ Hn).
    + assert (H0 : to_Z 0%u32 = 0) by reflexivity.
      rewrite H0 in Hrep. rewrite Z.sub_0_r in Hrep. exact Hrep.
Qed.

(** Spec 5.5.5: [importsec ::= im*:vec(import)],
    [import ::= mod:name nm:name d:importdesc]. This is the one section that
    writes more than two fields: an import goes on the import list and into
    whichever index space its descriptor names, and the two counters that
    record where the imported entries end move with it. *)
Definition translate_importdesc (d : module_ImportDesc_t) : module_import_desc :=
  match d with
  | Module_ImportDesc_Func x => MID_func (translate_idx x)
  | Module_ImportDesc_Table t => MID_table (translate_tabletype t)
  | Module_ImportDesc_Memory m => MID_mem (translate_memtype m)
  | Module_ImportDesc_Global g => MID_global (translate_globaltype g)
  end.

Definition translate_import (im : module_Import_t) : module_import :=
  {| imp_module := translate_name im.(module_Import_module);
     imp_name := translate_name im.(module_Import_name);
     imp_desc := translate_importdesc im.(module_Import_desc) |}.

Definition env_with_import (env : module_Env_t)
                           (imps : alloc_vec_Vec module_Import_t)
                           (fts : alloc_vec_Vec types_FuncType_t)
                           (tts : alloc_vec_Vec types_TableType_t)
                           (mts : alloc_vec_Vec types_MemType_t)
                           (gts : alloc_vec_Vec types_GlobalType_t)
                           (nif nig : usize) : module_Env_t :=
  {| module_Env_types := env.(module_Env_types);
     module_Env_imports := imps;
     module_Env_globals := env.(module_Env_globals);
     module_Env_exports := env.(module_Env_exports);
     module_Env_elements := env.(module_Env_elements);
     module_Env_start := env.(module_Env_start);
     module_Env_func_type_indices := env.(module_Env_func_type_indices);
     module_Env_func_types := fts;
     module_Env_table_types := tts;
     module_Env_mem_types := mts;
     module_Env_global_types := gts;
     module_Env_num_imported_funcs := nif;
     module_Env_num_imported_globals := nig |}.

(** The shape of an environment an import section produced, said once so that
    the loop and the section share it. *)
Definition env_imported (env env' : module_Env_t) : Prop :=
  env' = env_with_import env
           env'.(module_Env_imports) env'.(module_Env_func_types)
           env'.(module_Env_table_types) env'.(module_Env_mem_types)
           env'.(module_Env_global_types) env'.(module_Env_num_imported_funcs)
           env'.(module_Env_num_imported_globals).

Lemma env_imported_refl : forall env, env_imported env env.
Proof. intros env. unfold env_imported. destruct env. reflexivity. Qed.

(** What the import section put into each index space. Spec 3.1.1 puts the
    imported entries first, and [decode_import] pushes each descriptor into
    the matching vector as it reads it, so the imported prefix of an index
    space is a function of the import list alone. That is the same function
    WasmCert applies on its side: [module_imports_typer] turns an [MID_table]
    into an [ET_table] and [ext_t_tables] filters them back out.

    The function index space is not here. An imported function's descriptor
    carries a type *index*, so its entry is the resolved type rather than
    something read off the descriptor, and saying what was appended means
    saying what [lookup_type] returned. *)
Definition imported_tables (imps : list module_Import_t)
                           : list types_TableType_t :=
  List.flat_map (fun im => match im.(module_Import_desc) with
                           | Module_ImportDesc_Table t => [t]
                           | _ => [] end) imps.

Definition imported_mems (imps : list module_Import_t) : list types_MemType_t :=
  List.flat_map (fun im => match im.(module_Import_desc) with
                           | Module_ImportDesc_Memory m => [m]
                           | _ => [] end) imps.

Definition imported_globals (imps : list module_Import_t)
                            : list types_GlobalType_t :=
  List.flat_map (fun im => match im.(module_Import_desc) with
                           | Module_ImportDesc_Global g => [g]
                           | _ => [] end) imps.

Definition imported_func_idxs (imps : list module_Import_t)
                              : list (scalar U32) :=
  List.flat_map (fun im => match im.(module_Import_desc) with
                           | Module_ImportDesc_Func idx => [idx]
                           | _ => [] end) imps.

Definition import_spaces (env env' : module_Env_t)
                         (imps : list module_Import_t) : Prop :=
  vec_list env'.(module_Env_table_types)
    = vec_list env.(module_Env_table_types) ++ imported_tables imps
  /\ vec_list env'.(module_Env_mem_types)
    = vec_list env.(module_Env_mem_types) ++ imported_mems imps
  /\ vec_list env'.(module_Env_global_types)
    = vec_list env.(module_Env_global_types) ++ imported_globals imps
  /\ vec_list env'.(module_Env_types) = vec_list env.(module_Env_types)
  /\ func_space env env' (imported_func_idxs imps)
  /\ to_Z env'.(module_Env_num_imported_globals)
       = to_Z env.(module_Env_num_imported_globals)
         + Z.of_nat (List.length (imported_globals imps)).

Lemma import_spaces_refl : forall env, import_spaces env env [].
Proof.
  intros env. split; [|split; [|split; [|split; [|split]]]];
    solve [ exact (eq_sym (app_nil_r _)) | reflexivity
          | apply func_space_refl | (cbn; lia) ].
Qed.

Lemma imported_tables_app : forall xs ys,
  imported_tables (xs ++ ys) = imported_tables xs ++ imported_tables ys.
Proof. intros xs ys. apply List.flat_map_app. Qed.

Lemma imported_mems_app : forall xs ys,
  imported_mems (xs ++ ys) = imported_mems xs ++ imported_mems ys.
Proof. intros xs ys. apply List.flat_map_app. Qed.

Lemma imported_globals_app : forall xs ys,
  imported_globals (xs ++ ys) = imported_globals xs ++ imported_globals ys.
Proof. intros xs ys. apply List.flat_map_app. Qed.

Lemma imported_func_idxs_app : forall xs ys,
  imported_func_idxs (xs ++ ys)
    = imported_func_idxs xs ++ imported_func_idxs ys.
Proof. intros xs ys. apply List.flat_map_app. Qed.

Lemma import_spaces_trans : forall env mid env' xs ys,
  import_spaces env mid xs -> import_spaces mid env' ys ->
  import_spaces env env' (xs ++ ys).
Proof.
  intros env mid env' xs ys [Ht [Hm [Hg [Hty [Hf Hn]]]]]
                            [Ht' [Hm' [Hg' [Hty' [Hf' Hn']]]]].
  split; [|split; [|split; [|split; [|split]]]].
  - rewrite Ht'. rewrite Ht. rewrite imported_tables_app.
    symmetry. apply app_assoc.
  - rewrite Hm'. rewrite Hm. rewrite imported_mems_app.
    symmetry. apply app_assoc.
  - rewrite Hg'. rewrite Hg. rewrite imported_globals_app.
    symmetry. apply app_assoc.
  - rewrite Hty'. exact Hty.
  - rewrite imported_func_idxs_app.
    apply (func_space_trans env mid env'); assumption.
  - rewrite Hn'. rewrite Hn. rewrite imported_globals_app.
    rewrite List.app_length. lia.
Qed.

Lemma env_imported_trans : forall env mid env',
  env_imported env mid -> env_imported mid env' -> env_imported env env'.
Proof.
  intros env mid env' H1 H2. unfold env_imported in *.
  rewrite H2 at 1. rewrite H1. reflexivity.
Qed.

Lemma decode_import_sound : forall data pos env p' env',
  module_decode_import data pos env = Ok (Core_result_Result_Ok p', env') ->
  exists im,
    vec_list env'.(module_Env_imports) = vec_list env.(module_Env_imports) ++ [im]
    /\ env_imported env env'
    /\ repr_import (bytes_from data pos) (translate_import im)
         (bytes_from data p')
    /\ (env_limits_valid env -> env_limits_valid env')
    /\ import_spaces env env' [im].
Proof.
  intros data pos env p' env' H. unfold module_decode_import in H.
  destruct (module_decode_name data pos) as [r|] eqn:Hmd; cbn [bind] in H;
    [|discriminate].
  destruct r as [[md p1]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (module_decode_name data p1) as [r1|] eqn:Hnm; cbn [bind] in H;
    [|discriminate].
  destruct r1 as [[nm p2]|e1]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_byte data p2) as [r2|] eqn:Hk; cbn [bind] in H;
    [|discriminate].
  destruct r2 as [[kind p3]|e2]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  (* every arm ends the same way, so the two names and the descriptor are
     assembled once *)
  assert (Hnames : forall d rest,
            repr_importdesc (to_Z kind :: bytes_from data p3) d rest ->
            repr_import (bytes_from data pos)
              {| imp_module := translate_name md;
                 imp_name := translate_name nm;
                 imp_desc := d |} rest).
  { intros d rest Hd. apply repr_import_intro with (p1 := bytes_from data p1)
                                                   (p2 := bytes_from data p2).
    - apply (decode_name_sound _ _ _ _ Hmd).
    - apply (decode_name_sound _ _ _ _ Hnm).
    - rewrite (proj1 (read_byte_ok _ _ _ _ Hk)). exact Hd. }
  destruct (kind s= 0%u8) eqn:K0.
  { destruct (reader_read_u32_leb data p3) as [r3|] eqn:Hidx;
      cbn [bind] in H; [|discriminate].
    destruct r3 as [[idx p4]|e3]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (module_lookup_type env idx) as [r4|] eqn:Hlk; cbn [bind] in H;
      [|discriminate].
    destruct r4 as [ft|e4]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (lookup_type_sound _ _ _ Hlk) as [Hrange Hres].
    destruct (alloc_vec_Vec_push env.(module_Env_func_types) ft) as [v|] eqn:Hpv;
      cbn [bind] in H; [|discriminate].
    destruct (usize_add env.(module_Env_num_imported_funcs) 1%usize) as [i|];
      cbn [bind] in H; [|discriminate].
    destruct (alloc_vec_Vec_push env.(module_Env_imports)
                {| module_Import_module := md; module_Import_name := nm;
                   module_Import_desc := Module_ImportDesc_Func idx |})
      as [v1|] eqn:Hpv1; cbn [bind] in H; [|discriminate].
    injection H as <- <-.
    exists {| module_Import_module := md; module_Import_name := nm;
              module_Import_desc := Module_ImportDesc_Func idx |}.
    split; [exact (vec_push_spec _ _ _ Hpv1)|].
    split; [unfold env_imported; destruct env; reflexivity|].
    split; [| split].
    2: { intros [Hvi [Hvt Hvm]].
         split; [apply (forall_push _ _ _ _ _ Hpv1 Hvi); exact I
               | split; [exact Hvt | exact Hvm]]. }
    2: { split; [|split; [|split; [|split; [|split]]]];
           try exact (eq_sym (app_nil_r _)); [reflexivity| |cbn; lia].
         split; [| apply List.Forall_cons;
                     [exact Hrange | apply List.Forall_nil]].
         cbn [module_Env_func_types module_Env_types].
         rewrite (vec_push_spec _ _ _ Hpv). rewrite List.map_app.
         cbn [List.map imported_func_idxs List.flat_map module_Import_desc app].
         rewrite Hres. reflexivity. }
    unfold translate_import, translate_importdesc.
    cbn [module_Import_module module_Import_name module_Import_desc].
    apply Hnames. rewrite (scalar_eqb_val _ _ 0 K0 eq_refl).
    apply repr_importdesc_func. apply repr_idx_intro.
    apply (read_u32_leb_sound _ _ _ _ Hidx). }
  destruct (kind s= 1%u8) eqn:K1.
  { destruct (module_decode_table_type data p3) as [r3|] eqn:Htt;
      cbn [bind] in H; [|discriminate].
    destruct r3 as [[tt1 p4]|e3]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (alloc_vec_Vec_push env.(module_Env_table_types) tt1) as [v|] eqn:Hpv;
      cbn [bind] in H; [|discriminate].
    destruct (alloc_vec_Vec_len v s> limits_max_tables); [discriminate|].
    destruct (alloc_vec_Vec_push env.(module_Env_imports)
                {| module_Import_module := md; module_Import_name := nm;
                   module_Import_desc := Module_ImportDesc_Table tt1 |})
      as [v1|] eqn:Hpv1; cbn [bind] in H; [|discriminate].
    injection H as <- <-.
    exists {| module_Import_module := md; module_Import_name := nm;
              module_Import_desc := Module_ImportDesc_Table tt1 |}.
    split; [exact (vec_push_spec _ _ _ Hpv1)|].
    split; [unfold env_imported; destruct env; reflexivity|].
    split; [| split].
    2: { intros [Hvi [Hvt Hvm]].
         split; [apply (forall_push _ _ _ _ _ Hpv1 Hvi)
               | split; [apply (forall_push _ _ _ _ _ Hpv Hvt) | exact Hvm]];
         exact (decode_table_type_valid _ _ _ _ Htt). }
    2: { split; [exact (vec_push_spec _ _ _ Hpv)|].
         split; [exact (eq_sym (app_nil_r _))|].
         split; [exact (eq_sym (app_nil_r _))|].
         split; [reflexivity|].
         split; [apply func_space_keep; reflexivity | cbn; lia]. }
    unfold translate_import, translate_importdesc.
    cbn [module_Import_module module_Import_name module_Import_desc].
    apply Hnames. rewrite (scalar_eqb_val _ _ 1 K1 eq_refl).
    apply repr_importdesc_table. apply (decode_table_type_sound _ _ _ _ Htt). }
  destruct (kind s= 2%u8) eqn:K2.
  { destruct (module_decode_mem_type data p3) as [r3|] eqn:Hmt;
      cbn [bind] in H; [|discriminate].
    destruct r3 as [[mt p4]|e3]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (alloc_vec_Vec_push env.(module_Env_mem_types) mt) as [v|] eqn:Hpv;
      cbn [bind] in H; [|discriminate].
    destruct (alloc_vec_Vec_len v s> limits_max_memories); [discriminate|].
    destruct (alloc_vec_Vec_push env.(module_Env_imports)
                {| module_Import_module := md; module_Import_name := nm;
                   module_Import_desc := Module_ImportDesc_Memory mt |})
      as [v1|] eqn:Hpv1; cbn [bind] in H; [|discriminate].
    injection H as <- <-.
    exists {| module_Import_module := md; module_Import_name := nm;
              module_Import_desc := Module_ImportDesc_Memory mt |}.
    split; [exact (vec_push_spec _ _ _ Hpv1)|].
    split; [unfold env_imported; destruct env; reflexivity|].
    split; [| split].
    2: { intros [Hvi [Hvt Hvm]].
         split; [apply (forall_push _ _ _ _ _ Hpv1 Hvi)
               | split; [exact Hvt | apply (forall_push _ _ _ _ _ Hpv Hvm)]];
         exact (decode_mem_type_valid _ _ _ _ Hmt). }
    2: { split; [exact (eq_sym (app_nil_r _))|].
         split; [exact (vec_push_spec _ _ _ Hpv)|].
         split; [exact (eq_sym (app_nil_r _))|].
         split; [reflexivity|].
         split; [apply func_space_keep; reflexivity | cbn; lia]. }
    unfold translate_import, translate_importdesc.
    cbn [module_Import_module module_Import_name module_Import_desc].
    apply Hnames. rewrite (scalar_eqb_val _ _ 2 K2 eq_refl).
    apply repr_importdesc_mem. apply (decode_mem_type_sound _ _ _ _ Hmt). }
  destruct (kind s= 3%u8) eqn:K3; [|discriminate].
  destruct (module_decode_global_type data p3) as [r3|] eqn:Hgt;
    cbn [bind] in H; [|discriminate].
  destruct r3 as [[gt p4]|e3]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (alloc_vec_Vec_push env.(module_Env_global_types) gt) as [v|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  destruct (usize_add env.(module_Env_num_imported_globals) 1%usize) as [i|]
    eqn:Hnig; cbn [bind] in H; [|discriminate].
  destruct (alloc_vec_Vec_push env.(module_Env_imports)
              {| module_Import_module := md; module_Import_name := nm;
                 module_Import_desc := Module_ImportDesc_Global gt |})
    as [v1|] eqn:Hpv1; cbn [bind] in H; [|discriminate].
  injection H as <- <-.
  exists {| module_Import_module := md; module_Import_name := nm;
            module_Import_desc := Module_ImportDesc_Global gt |}.
  split; [exact (vec_push_spec _ _ _ Hpv1)|].
  split; [unfold env_imported; destruct env; reflexivity|].
  split; [| split].
  2: { intros [Hvi [Hvt Hvm]].
       split; [apply (forall_push _ _ _ _ _ Hpv1 Hvi); exact I
             | split; [exact Hvt | exact Hvm]]. }
  2: { split; [exact (eq_sym (app_nil_r _))|].
       split; [exact (eq_sym (app_nil_r _))|].
       split; [exact (vec_push_spec _ _ _ Hpv)|].
       split; [reflexivity|].
       split; [apply func_space_keep; reflexivity|].
       cbn [module_Env_num_imported_globals imported_globals List.flat_map
            module_Import_desc List.length].
       rewrite (scalar_add_val _ _ _ 1 Hnig eq_refl).
       cbn [List.app List.length Z.of_nat]. lia. }
  unfold translate_import, translate_importdesc.
  cbn [module_Import_module module_Import_name module_Import_desc].
  apply Hnames. rewrite (scalar_eqb_val _ _ 3 K3 eq_refl).
  apply repr_importdesc_global. apply (decode_global_type_sound _ _ _ _ Hgt).
Qed.

Lemma decode_import_section_loop_sound : forall m data env count q i q' env',
  to_Z count - to_Z i <= Z.of_nat m ->
  module_decode_import_section_loop data env count q i
    = Ok (Core_result_Result_Ok q', env') ->
  exists imps,
    vec_list env'.(module_Env_imports) = vec_list env.(module_Env_imports) ++ imps
    /\ env_imported env env'
    /\ repr_rep repr_import (Z.to_nat (to_Z count - to_Z i))
         (bytes_from data q) (List.map translate_import imps)
         (bytes_from data q')
    /\ (env_limits_valid env -> env_limits_valid env')
    /\ import_spaces env env' imps.
Proof.
  induction m as [|m IH]; intros data env count q i q' env' Hmeas H;
    unfold module_decode_import_section_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (i s>= count) eqn:Hge.
  1,3: injection H as <- <-; exists []; rewrite app_nil_r;
       split; [reflexivity|]; split; [apply env_imported_refl|];
       split; [| split; [exact (fun Hv => Hv) | apply import_spaces_refl]];
       apply scalar_geb_true_ge in Hge;
       rewrite to_nat_nonpos by lia; apply repr_rep_nil.
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (module_decode_import data q env) as [[r env1]|] eqn:Him;
      cbn [bind] in H; [|discriminate].
    destruct r as [q1|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in H;
      [|discriminate].
    pose proof (scalar_add_val _ _ _ 1 Hadd eq_refl) as Hi2.
    destruct (decode_import_sound _ _ _ _ _ Him)
      as [im [Hone [Henv1 [Hrepr [Hval1 Hsp1]]]]].
    destruct (IH data env1 count q1 i2 q' env' (ltac:(cbn in Hmeas; lia)) H)
      as [imps [Hlist [Henv [Hrep [Hval Hsp]]]]].
    exists (im :: imps). split; [|split; [|split; [|split]]].
    + rewrite Hlist. rewrite Hone. rewrite <- app_assoc. reflexivity.
    + apply (env_imported_trans _ env1); assumption.
    + assert (Hcnt : to_Z count - to_Z i = (to_Z count - to_Z i2) + 1) by lia.
      rewrite Hcnt. rewrite Z_to_nat_add1 by lia.
      cbn [List.map]. eapply repr_rep_cons; [exact Hrepr | exact Hrep].
    + intros Hv. apply Hval. apply Hval1. exact Hv.
    + exact (import_spaces_trans _ _ _ _ _ Hsp1 Hsp).
Qed.

Lemma decode_import_section_sound : forall data pos env q' env',
  module_decode_import_section data pos env
    = Ok (Core_result_Result_Ok q', env') ->
  exists imps,
    vec_list env'.(module_Env_imports) = vec_list env.(module_Env_imports) ++ imps
    /\ env_imported env env'
    /\ repr_vec repr_import (bytes_from data pos)
         (List.map translate_import imps) (bytes_from data q')
    /\ (env_limits_valid env -> env_limits_valid env')
    /\ import_spaces env env' imps.
Proof.
  intros data pos env q' env' H. unfold module_decode_import_section in H.
  destruct (reader_read_u32_leb data pos) as [r|] eqn:Hn; cbn [bind] in H;
    [|discriminate].
  destruct r as [[count p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (decode_import_section_loop_sound (Z.to_nat (to_Z count)) data env
              count p 0%u32 q' env') as [imps [Hlist [Henv [Hrep [Hval Hsp]]]]].
  - assert (H0 : to_Z 0%u32 = 0) by reflexivity.
    pose proof (u32_nonneg count). lia.
  - exact H.
  - exists imps. split; [exact Hlist|]. split; [exact Henv|].
    split; [| split; [exact Hval | exact Hsp]].
    apply repr_vec_intro with (n := to_Z count) (mid := bytes_from data p).
    + apply (read_u32_leb_sound _ _ _ _ Hn).
    + assert (H0 : to_Z 0%u32 = 0) by reflexivity.
      rewrite H0 in Hrep. rewrite Z.sub_0_r in Hrep. exact Hrep.
Qed.

(* ================================================================== *)
(** ** From a run over the module to a section's contents             *)
(* ================================================================== *)

(** [repr_section] states its contents relation over the section's bytes
    alone, while the decoder runs over the whole module, so every section
    lemma has to move from one to the other. [Spec_Binary.reads_prefix] is
    what makes that possible, and these three do the move. *)
Lemma firstn_split : forall {A} a b (l : list A),
  List.firstn a l ++ List.firstn b (List.skipn a l) = List.firstn (a + b) l.
Proof.
  intros A a b l. rewrite List.firstn_skipn_comm.
  replace (List.firstn a l) with (List.firstn a (List.firstn (a + b) l))
    by (rewrite List.firstn_firstn; f_equal; lia).
  apply List.firstn_skipn.
Qed.

Lemma section_content_split : forall data start p fin,
  to_Z start <= to_Z p -> to_Z p <= to_Z fin ->
  section_content data start fin
    = List.firstn (Z.to_nat (to_Z p - to_Z start)) (bytes_from data start)
      ++ section_content data p fin.
Proof.
  intros data start p fin H1 H2. unfold section_content.
  rewrite (bytes_from_skipn data start p (Z.to_nat (to_Z p - to_Z start)))
    by (rewrite Z2Nat.id; lia).
  rewrite firstn_split. f_equal.
  rewrite <- Z2Nat.inj_add by lia. f_equal. lia.
Qed.

(** A run that stopped inside the section, read as a run over the section. *)
Lemma section_contents_within :
  forall A (R : list Z -> A -> list Z -> Prop) data start p fin x,
  reads_prefix R ->
  R (bytes_from data start) x (bytes_from data p) ->
  to_Z start <= to_Z p -> to_Z p <= to_Z fin ->
  R (section_content data start fin) x (section_content data p fin).
Proof.
  intros A R data start p fin x HR Hrun H1 H2.
  destruct (HR _ _ _ Hrun) as [pre [Heq Hall]].
  assert (Htail : bytes_from data p
                  = List.skipn (Z.to_nat (to_Z p - to_Z start))
                      (bytes_from data start))
    by (apply bytes_from_skipn; rewrite Z2Nat.id; lia).
  assert (Hpre : pre = List.firstn (Z.to_nat (to_Z p - to_Z start))
                         (bytes_from data start)).
  { apply (app_inv_tail (bytes_from data p)).
    rewrite <- Heq. rewrite Htail. symmetry. apply List.firstn_skipn. }
  rewrite (section_content_split data start p fin H1 H2).
  rewrite <- Hpre. apply Hall.
Qed.

(** And one that stopped exactly at the section's end, which is what
    [repr_section] asks for. *)
Lemma section_contents : forall A (R : list Z -> A -> list Z -> Prop)
                                data start fin x,
  reads_prefix R ->
  R (bytes_from data start) x (bytes_from data fin) ->
  to_Z start <= to_Z fin ->
  R (section_content data start fin) x [].
Proof.
  intros A R data start fin x HR Hrun H1.
  pose proof (section_contents_within A R data start fin fin x HR Hrun H1
                (Z.le_refl _)) as Hc.
  replace (section_content data fin fin) with (@nil Z) in Hc; [exact Hc|].
  unfold section_content. rewrite Z.sub_diag. reflexivity.
Qed.

Lemma section_sound : forall A (R : list Z -> A -> list Z -> Prop)
                             data pos id start fin x,
  reads_prefix R ->
  module_read_section_header data pos
    = Ok (Core_result_Result_Ok (id, start, fin)) ->
  R (bytes_from data start) x (bytes_from data fin) ->
  repr_section (to_Z id) R (bytes_from data pos) x (bytes_from data fin).
Proof.
  intros A R data pos id start fin x HR Hhdr Hrun.
  destruct (read_section_header_step _ _ _ _ _ Hhdr) as [_ [Hle _]].
  apply (read_section_header_sound _ _ _ _ _ _ _ _ Hhdr).
  apply (section_contents _ R data start fin x HR Hrun Hle).
Qed.

(** Spec 5.5.3: [custom ::= nm:name b*:byte*]. The trailing bytes are
    unconstrained, so all the rule asks is that a name starts the section and
    fits inside it, which is what the decoder checks. *)
Lemma decode_custom_section_sound : forall data pos fin c,
  module_decode_custom_section data pos fin
    = Ok (Core_result_Result_Ok c) ->
  to_Z pos <= to_Z fin ->
  to_Z fin <= Z.of_nat (List.length (vec_list data)) ->
  repr_custom (section_content data pos fin) tt [].
Proof.
  intros data pos fin c H Hle Hfin. unfold module_decode_custom_section in H.
  destruct (module_decode_name data pos) as [r|] eqn:Hnm; cbn [bind] in H;
    [|discriminate].
  destruct r as [[v p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (p s> fin) eqn:Hgt; [discriminate|].
  apply scalar_gtb_false in Hgt.
  destruct (decode_name_step _ _ _ _ Hnm (ltac:(rewrite slice_len_spec; lia)))
    as [Hlt _].
  unfold repr_custom.
  exists (translate_name v). exists (section_content data p fin).
  split; [|reflexivity].
  apply (section_contents_within _ repr_name data pos p fin);
    [ apply repr_name_prefix
    | apply (decode_name_sound _ _ _ _ Hnm)
    | lia | lia ].
Qed.

(** The dispatch. One lemma per id rather than one disjunction, because the
    chain that consumes them reads the id first and then knows which it is.
    The walk peels the [if] chain a guard at a time: the matching guard's
    [then] branch *is* the goal, and every other branch contradicts the id. *)
Ltac env_dispatch H :=
  repeat (match type of H with
          | context [if (?i s= ?c) then _ else _] =>
              let E := fresh "E" in
              destruct (i s= c) eqn:E;
              [ first [ exact H
                      | exfalso; apply scalar_eqb_true in E; cbn in E; lia ]
              | apply scalar_eqb_false in E; cbn in E ]
          end); discriminate.

Lemma env_section_is_type : forall data pos id env q env',
  to_Z id = 1 ->
  module_decode_env_section data pos id env
    = Ok (Core_result_Result_Ok q, env') ->
  module_decode_type_section data pos env
    = Ok (Core_result_Result_Ok q, env').
Proof.
  intros data pos id env q env' Hid H. unfold module_decode_env_section in H.
  env_dispatch H.
Qed.

Lemma env_section_is_import : forall data pos id env q env',
  to_Z id = 2 ->
  module_decode_env_section data pos id env
    = Ok (Core_result_Result_Ok q, env') ->
  module_decode_import_section data pos env
    = Ok (Core_result_Result_Ok q, env').
Proof.
  intros data pos id env q env' Hid H. unfold module_decode_env_section in H.
  env_dispatch H.
Qed.

Lemma env_section_is_function : forall data pos id env q env',
  to_Z id = 3 ->
  module_decode_env_section data pos id env
    = Ok (Core_result_Result_Ok q, env') ->
  module_decode_function_section data pos env
    = Ok (Core_result_Result_Ok q, env').
Proof.
  intros data pos id env q env' Hid H. unfold module_decode_env_section in H.
  env_dispatch H.
Qed.

Lemma env_section_is_table : forall data pos id env q env',
  to_Z id = 4 ->
  module_decode_env_section data pos id env
    = Ok (Core_result_Result_Ok q, env') ->
  module_decode_table_section data pos env
    = Ok (Core_result_Result_Ok q, env').
Proof.
  intros data pos id env q env' Hid H. unfold module_decode_env_section in H.
  env_dispatch H.
Qed.

Lemma env_section_is_memory : forall data pos id env q env',
  to_Z id = 5 ->
  module_decode_env_section data pos id env
    = Ok (Core_result_Result_Ok q, env') ->
  module_decode_memory_section data pos env
    = Ok (Core_result_Result_Ok q, env').
Proof.
  intros data pos id env q env' Hid H. unfold module_decode_env_section in H.
  env_dispatch H.
Qed.

Lemma env_section_is_global : forall data pos id env q env',
  to_Z id = 6 ->
  module_decode_env_section data pos id env
    = Ok (Core_result_Result_Ok q, env') ->
  module_decode_global_section data pos env
    = Ok (Core_result_Result_Ok q, env').
Proof.
  intros data pos id env q env' Hid H. unfold module_decode_env_section in H.
  env_dispatch H.
Qed.

Lemma env_section_is_export : forall data pos id env q env',
  to_Z id = 7 ->
  module_decode_env_section data pos id env
    = Ok (Core_result_Result_Ok q, env') ->
  module_decode_export_section data pos env
    = Ok (Core_result_Result_Ok q, env').
Proof.
  intros data pos id env q env' Hid H. unfold module_decode_env_section in H.
  env_dispatch H.
Qed.

Lemma env_section_is_start : forall data pos id env q env',
  to_Z id = 8 ->
  module_decode_env_section data pos id env
    = Ok (Core_result_Result_Ok q, env') ->
  module_decode_start_section data pos env
    = Ok (Core_result_Result_Ok q, env').
Proof.
  intros data pos id env q env' Hid H. unfold module_decode_env_section in H.
  env_dispatch H.
Qed.

Lemma env_section_is_element : forall data pos id env q env',
  to_Z id = 9 ->
  module_decode_env_section data pos id env
    = Ok (Core_result_Result_Ok q, env') ->
  module_decode_element_section data pos env
    = Ok (Core_result_Result_Ok q, env').
Proof.
  intros data pos id env q env' Hid H. unfold module_decode_env_section in H.
  env_dispatch H.
Qed.

(* ================================================================== *)
(** ** The environment's section chain                                 *)
(* ================================================================== *)

(** Spec 5.5.16 is a fixed chain of [customs* Xsec] lines, one per section id.
    [validate_env] is one loop with a [last_id] ordering check. Relating the two
    is the one part of this file that is not a per-decoder argument, and the
    argument is:

    - a run of custom sections the loop consumes belongs to the [repr_customs]
      of the first absent line after the last present one; every absent line
      after that gets an empty run, which holds because the next byte is a
      non-zero id;
    - an absent line [j] needs [~ begins_with j] where it sits, and the byte
      there is either nothing at all or the id [k > j] the loop is about to
      read;
    - so the loop's invariant is: from cursor [q] with [last_id = L], an
      accepting run produces the chain for lines [L+1 .. 9].

    The nine lines have nine different element types, so there is no uniform
    inductive; they are nine definitions, each in terms of the next, with
    [chain_from] dispatching on [L] so that the loop needs one induction.

    The chain ends with the run of custom sections before the code section
    rather than at the element section, because that is where [validate_env]
    stops: [validate_code] supplies the [repr_optsec 10] those customs pad. *)

Definition chain_tail (data : slice u8) (p : usize) (env : module_Env_t)
                      (q : usize) (envf : module_Env_t) : Prop :=
  repr_customs (bytes_from data p) (bytes_from data q) /\ env = envf.

Definition env_chain_9 (data : slice u8) (p : usize) (env : module_Env_t)
                          (q : usize) (envf : module_Env_t) : Prop :=
  exists p' env' (vs : list module_Element_t),
    repr_padded 9 (repr_vec repr_elem) (@nil module_element) (bytes_from data p)
      (List.map translate_element vs) (bytes_from data p')
    /\ vec_list env'.(module_Env_elements) = vec_list env.(module_Env_elements) ++ vs
    /\ env' = env_with_elements env env'.(module_Env_elements)
    /\ List.Forall (element_ok env) vs
    /\ chain_tail data p' env' q envf.

Definition env_chain_8 (data : slice u8) (p : usize) (env : module_Env_t)
                          (q : usize) (envf : module_Env_t) : Prop :=
  exists p' env',
    repr_padded 8 repr_start None (bytes_from data p)
      (translate_start env'.(module_Env_start)) (bytes_from data p')
    /\ env' = env_with_start env env'.(module_Env_start)
    /\ start_ok env'
    /\ env_chain_9 data p' env' q envf.

Definition env_chain_7 (data : slice u8) (p : usize) (env : module_Env_t)
                          (q : usize) (envf : module_Env_t) : Prop :=
  exists p' env' (vs : list module_Export_t),
    repr_padded 7 (repr_vec repr_export) (@nil module_export) (bytes_from data p)
      (List.map translate_export vs) (bytes_from data p')
    /\ vec_list env'.(module_Env_exports) = vec_list env.(module_Env_exports) ++ vs
    /\ env' = env_with_exports env env'.(module_Env_exports)
    /\ (exports_distinct env -> exports_distinct env')
    /\ List.Forall (export_desc_ok env) vs
    /\ env_chain_8 data p' env' q envf.

Definition env_chain_6 (data : slice u8) (p : usize) (env : module_Env_t)
                          (q : usize) (envf : module_Env_t) : Prop :=
  exists p' env' (vs : list module_Global_t),
    repr_padded 6 (repr_vec repr_global) (@nil module_global) (bytes_from data p)
      (List.map translate_global vs) (bytes_from data p')
    /\ vec_list env'.(module_Env_globals) = vec_list env.(module_Env_globals) ++ vs
    /\ env' = env_with_global env env'.(module_Env_globals)
                           env'.(module_Env_global_types)
    /\ vec_list env'.(module_Env_global_types)
         = vec_list env.(module_Env_global_types)
           ++ List.map (fun g => g.(module_Global_gtype)) vs
    /\ List.Forall (global_ok env') vs
    /\ env_chain_7 data p' env' q envf.

Definition env_chain_5 (data : slice u8) (p : usize) (env : module_Env_t)
                          (q : usize) (envf : module_Env_t) : Prop :=
  exists p' env' (vs : list types_MemType_t),
    repr_padded 5 (repr_vec repr_mem) (@nil module_mem) (bytes_from data p)
      (List.map translate_mem vs) (bytes_from data p')
    /\ vec_list env'.(module_Env_mem_types)
         = vec_list env.(module_Env_mem_types) ++ vs
    /\ env' = env_with_mem env env'.(module_Env_mem_types)
    /\ env_chain_6 data p' env' q envf.

Definition env_chain_4 (data : slice u8) (p : usize) (env : module_Env_t)
                          (q : usize) (envf : module_Env_t) : Prop :=
  exists p' env' (vs : list types_TableType_t),
    repr_padded 4 (repr_vec repr_table) (@nil module_table) (bytes_from data p)
      (List.map translate_table vs) (bytes_from data p')
    /\ vec_list env'.(module_Env_table_types)
         = vec_list env.(module_Env_table_types) ++ vs
    /\ env' = env_with_table env env'.(module_Env_table_types)
    /\ env_chain_5 data p' env' q envf.

Definition env_chain_3 (data : slice u8) (p : usize) (env : module_Env_t)
                          (q : usize) (envf : module_Env_t) : Prop :=
  exists p' env' (vs : list (scalar U32)),
    repr_padded 3 (repr_vec repr_idx) (@nil funcidx) (bytes_from data p)
      (List.map translate_idx vs) (bytes_from data p')
    /\ vec_list env'.(module_Env_func_type_indices)
         = vec_list env.(module_Env_func_type_indices) ++ vs
    /\ env' = env_with_func env env'.(module_Env_func_types)
                         env'.(module_Env_func_type_indices)
    /\ func_space env env' vs
    /\ env_chain_4 data p' env' q envf.

Definition env_chain_2 (data : slice u8) (p : usize) (env : module_Env_t)
                          (q : usize) (envf : module_Env_t) : Prop :=
  exists p' env' (vs : list module_Import_t),
    repr_padded 2 (repr_vec repr_import) (@nil module_import) (bytes_from data p)
      (List.map translate_import vs) (bytes_from data p')
    /\ vec_list env'.(module_Env_imports) = vec_list env.(module_Env_imports) ++ vs
    /\ env_imported env env'
    /\ import_spaces env env' vs
    /\ env_chain_3 data p' env' q envf.

Definition env_chain_1 (data : slice u8) (p : usize) (env : module_Env_t)
                          (q : usize) (envf : module_Env_t) : Prop :=
  exists p' env' (vs : list types_FuncType_t),
    repr_padded 1 (repr_vec repr_functype) (@nil function_type) (bytes_from data p)
      (List.map translate_functype vs) (bytes_from data p')
    /\ vec_list env'.(module_Env_types) = vec_list env.(module_Env_types) ++ vs
    /\ env' = env_with_types env env'.(module_Env_types)
    /\ env_chain_2 data p' env' q envf.

(** The chain that remains once sections up to [L] have been read. *)
Definition chain_from (L : Z) (data : slice u8) (p : usize) (env : module_Env_t)
                      (q : usize) (envf : module_Env_t) : Prop :=
  if Z.eqb L 0 then env_chain_1 data p env q envf
  else if Z.eqb L 1 then env_chain_2 data p env q envf
  else if Z.eqb L 2 then env_chain_3 data p env q envf
  else if Z.eqb L 3 then env_chain_4 data p env q envf
  else if Z.eqb L 4 then env_chain_5 data p env q envf
  else if Z.eqb L 5 then env_chain_6 data p env q envf
  else if Z.eqb L 6 then env_chain_7 data p env q envf
  else if Z.eqb L 7 then env_chain_8 data p env q envf
  else if Z.eqb L 8 then env_chain_9 data p env q envf
  else chain_tail data p env q envf.

(* ================================================================== *)
(** ** What the rest of the chain leaves alone                         *)
(* ================================================================== *)

(** Each line writes its own field and rebuilds the record around it, so a
    reading [g] of any other field is the same at the end of the chain as at
    the line it starts from. Stating it for an arbitrary [g] rather than field
    by field is what keeps the assembly to one line per field: [keeps_k] lists
    the writers from line [k] on, and every one of its clauses is closed by
    [reflexivity] because the writer is a record literal. *)
Definition keeps_9 {A} (g : module_Env_t -> A) : Prop :=
  forall e v, g (env_with_elements e v) = g e.

Definition keeps_8 {A} (g : module_Env_t -> A) : Prop :=
  (forall e s, g (env_with_start e s) = g e) /\ keeps_9 g.

Definition keeps_7 {A} (g : module_Env_t -> A) : Prop :=
  (forall e v, g (env_with_exports e v) = g e) /\ keeps_8 g.

Definition keeps_6 {A} (g : module_Env_t -> A) : Prop :=
  (forall e v w, g (env_with_global e v w) = g e) /\ keeps_7 g.

Definition keeps_5 {A} (g : module_Env_t -> A) : Prop :=
  (forall e v, g (env_with_mem e v) = g e) /\ keeps_6 g.

Definition keeps_4 {A} (g : module_Env_t -> A) : Prop :=
  (forall e v, g (env_with_table e v) = g e) /\ keeps_5 g.

Definition keeps_3 {A} (g : module_Env_t -> A) : Prop :=
  (forall e v w, g (env_with_func e v w) = g e) /\ keeps_4 g.

Definition keeps_2 {A} (g : module_Env_t -> A) : Prop :=
  (forall e a b c d f x y, g (env_with_import e a b c d f x y) = g e)
  /\ keeps_3 g.

(** Every clause is a projection of a record literal. *)
Ltac keeps_refl := repeat (first [ solve [intros; reflexivity] | split ]).

(** Reduce a projection of one of those record rebuilds, so that the field
    underneath is there for the next rewrite to find. *)
Ltac env_proj :=
  cbn [env_with_types env_with_import env_with_func env_with_table env_with_mem
       env_with_global env_with_exports env_with_start env_with_elements
       module_Env_types module_Env_imports module_Env_globals module_Env_exports
       module_Env_elements module_Env_start module_Env_func_type_indices
       module_Env_func_types module_Env_table_types module_Env_mem_types
       module_Env_global_types module_Env_num_imported_funcs
       module_Env_num_imported_globals].

Lemma chain_tail_keeps : forall A (g : module_Env_t -> A) data p env q envf,
  chain_tail data p env q envf -> g envf = g env.
Proof. intros A g data p env q envf [_ <-]. reflexivity. Qed.

Lemma env_chain_9_keeps : forall A (g : module_Env_t -> A) data p env q envf,
  keeps_9 g -> env_chain_9 data p env q envf -> g envf = g env.
Proof.
  intros A g data p env q envf Hk
    [p' [env' [vs [Hr [Hl [Heq [_ Hrest]]]]]]].
  rewrite (chain_tail_keeps _ g _ _ _ _ _ Hrest).
  rewrite Heq at 1. apply Hk.
Qed.

Lemma env_chain_8_keeps : forall A (g : module_Env_t -> A) data p env q envf,
  keeps_8 g -> env_chain_8 data p env q envf -> g envf = g env.
Proof.
  intros A g data p env q envf [Hk Hk9] [p' [env' [Hr [Heq [_ Hrest]]]]].
  rewrite (env_chain_9_keeps _ g _ _ _ _ _ Hk9 Hrest).
  rewrite Heq at 1. apply Hk.
Qed.

Lemma env_chain_7_keeps : forall A (g : module_Env_t -> A) data p env q envf,
  keeps_7 g -> env_chain_7 data p env q envf -> g envf = g env.
Proof.
  intros A g data p env q envf [Hk Hk8]
    [p' [env' [vs [Hr [Hl [Heq [_ [_ Hrest]]]]]]]].
  rewrite (env_chain_8_keeps _ g _ _ _ _ _ Hk8 Hrest).
  rewrite Heq at 1. apply Hk.
Qed.

Lemma env_chain_6_keeps : forall A (g : module_Env_t -> A) data p env q envf,
  keeps_6 g -> env_chain_6 data p env q envf -> g envf = g env.
Proof.
  intros A g data p env q envf [Hk Hk7]
    [p' [env' [vs [Hr [Hl [Heq [_ [_ Hrest]]]]]]]].
  rewrite (env_chain_7_keeps _ g _ _ _ _ _ Hk7 Hrest).
  rewrite Heq at 1. apply Hk.
Qed.

Lemma env_chain_5_keeps : forall A (g : module_Env_t -> A) data p env q envf,
  keeps_5 g -> env_chain_5 data p env q envf -> g envf = g env.
Proof.
  intros A g data p env q envf [Hk Hk6] [p' [env' [vs [Hr [Hl [Heq Hrest]]]]]].
  rewrite (env_chain_6_keeps _ g _ _ _ _ _ Hk6 Hrest).
  rewrite Heq at 1. apply Hk.
Qed.

Lemma env_chain_4_keeps : forall A (g : module_Env_t -> A) data p env q envf,
  keeps_4 g -> env_chain_4 data p env q envf -> g envf = g env.
Proof.
  intros A g data p env q envf [Hk Hk5] [p' [env' [vs [Hr [Hl [Heq Hrest]]]]]].
  rewrite (env_chain_5_keeps _ g _ _ _ _ _ Hk5 Hrest).
  rewrite Heq at 1. apply Hk.
Qed.

Lemma env_chain_3_keeps : forall A (g : module_Env_t -> A) data p env q envf,
  keeps_3 g -> env_chain_3 data p env q envf -> g envf = g env.
Proof.
  intros A g data p env q envf [Hk Hk4]
    [p' [env' [vs [Hr [Hl [Heq [_ Hrest]]]]]]].
  rewrite (env_chain_4_keeps _ g _ _ _ _ _ Hk4 Hrest).
  rewrite Heq at 1. apply Hk.
Qed.

Lemma env_chain_2_keeps : forall A (g : module_Env_t -> A) data p env q envf,
  keeps_2 g -> env_chain_2 data p env q envf -> g envf = g env.
Proof.
  intros A g data p env q envf [Hk Hk3]
    [p' [env' [vs [Hr [Hl [Heq [_ Hrest]]]]]]].
  rewrite (env_chain_3_keeps _ g _ _ _ _ _ Hk3 Hrest).
  unfold env_imported in Heq. rewrite Heq at 1. apply Hk.
Qed.

(** Nothing an environment section could start with is here. *)
Definition no_env_id (bs : list Z) : Prop :=
  forall j, 0 <= j <= 9 -> ~ begins_with j bs.

(** Split [chain_from] into its ten cases. *)
Ltac chain_split L :=
  unfold chain_from;
  repeat (match goal with
          | [ |- context [Z.eqb L ?k] ] =>
              let E := fresh "E" in
              destruct (Z.eqb L k) eqn:E;
              [ apply Z.eqb_eq in E | apply Z.eqb_neq in E ]
          end).

(** The same when a hypothesis is at the same level, which is every step that
    turns one chain into another. Both sides have to be split by the same
    [destruct], or the second split doubles the cases. *)
Ltac chain_split2 L H :=
  unfold chain_from in H |- *;
  repeat (match goal with
          | [ |- context [Z.eqb L ?k] ] =>
              let E := fresh "E" in
              destruct (Z.eqb L k) eqn:E; cbn beta iota in H |- *
          end).

(** *** Every remaining line absent

    What the loop produces when it runs out of sections: either the input is
    over or the next id is the code section's, and both say the same thing
    about the bytes at the cursor. *)
Lemma chain_tail_absent : forall data q env,
  no_env_id (bytes_from data q) -> chain_tail data q env q env.
Proof.
  intros data q env Hno. split; [|reflexivity].
  apply repr_customs_done. apply Hno. lia.
Qed.

(** Section 9 does not need "start is still unset": its absent value is the
    empty vector, and only line 8 says anything about the start function. *)
Lemma env_chain_9_absent : forall data q env,
  no_env_id (bytes_from data q) -> env_chain_9 data q env q env.
Proof.
  intros data q env Hno. exists q. exists env. exists [].
  split; [|split; [|split; [|split]]].
  - exists (bytes_from data q). split.
    + apply repr_customs_done. apply Hno. lia.
    + apply repr_optsec_absent. apply Hno. lia.
  - rewrite app_nil_r. reflexivity.
  - apply env_with_elements_refl.
  - apply List.Forall_nil.
  - apply chain_tail_absent. exact Hno.
Qed.

(** The start section is the one line whose absent value is not the empty
    vector: it says there is no start function, and the environment has to
    agree. That is why the loop carries "start is still unset". *)
Lemma env_chain_8_absent : forall data q env,
  env.(module_Env_start) = None ->
  no_env_id (bytes_from data q) -> env_chain_8 data q env q env.
Proof.
  intros data q env Hst Hno. exists q. exists env.
  split; [|split; [|split]].
  - exists (bytes_from data q). split.
    + apply repr_customs_done. apply Hno. lia.
    + unfold translate_start. rewrite Hst. cbn [option_map].
      apply repr_optsec_absent. apply Hno. lia.
  - apply env_with_start_refl.
  - unfold start_ok. rewrite Hst. exact I.
  - apply env_chain_9_absent. exact Hno.
Qed.

Lemma env_chain_7_absent : forall data q env,
  env.(module_Env_start) = None ->
  no_env_id (bytes_from data q) -> env_chain_7 data q env q env.
Proof.
  intros data q env Hst Hno. exists q. exists env. exists [].
  split; [|split; [|split; [|split; [|split]]]].
  - exists (bytes_from data q). split.
    + apply repr_customs_done. apply Hno. lia.
    + apply repr_optsec_absent. apply Hno. lia.
  - rewrite app_nil_r. reflexivity.
  - apply env_with_exports_refl.
  - exact (fun Hd => Hd).
  - apply List.Forall_nil.
  - apply env_chain_8_absent; assumption.
Qed.

Lemma env_chain_6_absent : forall data q env,
  env.(module_Env_start) = None ->
  no_env_id (bytes_from data q) -> env_chain_6 data q env q env.
Proof.
  intros data q env Hst Hno. exists q. exists env. exists [].
  split; [|split; [|split; [|split; [|split]]]].
  - exists (bytes_from data q). split.
    + apply repr_customs_done. apply Hno. lia.
    + apply repr_optsec_absent. apply Hno. lia.
  - rewrite app_nil_r. reflexivity.
  - apply env_with_global_refl.
  - exact (eq_sym (app_nil_r _)).
  - apply List.Forall_nil.
  - apply env_chain_7_absent; assumption.
Qed.

Lemma env_chain_5_absent : forall data q env,
  env.(module_Env_start) = None ->
  no_env_id (bytes_from data q) -> env_chain_5 data q env q env.
Proof.
  intros data q env Hst Hno. exists q. exists env. exists [].
  split; [|split; [|split]].
  - exists (bytes_from data q). split.
    + apply repr_customs_done. apply Hno. lia.
    + apply repr_optsec_absent. apply Hno. lia.
  - rewrite app_nil_r. reflexivity.
  - apply env_with_mem_refl.
  - apply env_chain_6_absent; assumption.
Qed.

Lemma env_chain_4_absent : forall data q env,
  env.(module_Env_start) = None ->
  no_env_id (bytes_from data q) -> env_chain_4 data q env q env.
Proof.
  intros data q env Hst Hno. exists q. exists env. exists [].
  split; [|split; [|split]].
  - exists (bytes_from data q). split.
    + apply repr_customs_done. apply Hno. lia.
    + apply repr_optsec_absent. apply Hno. lia.
  - rewrite app_nil_r. reflexivity.
  - apply env_with_table_refl.
  - apply env_chain_5_absent; assumption.
Qed.

Lemma env_chain_3_absent : forall data q env,
  env.(module_Env_start) = None ->
  no_env_id (bytes_from data q) -> env_chain_3 data q env q env.
Proof.
  intros data q env Hst Hno. exists q. exists env. exists [].
  split; [|split; [|split; [|split]]].
  - exists (bytes_from data q). split.
    + apply repr_customs_done. apply Hno. lia.
    + apply repr_optsec_absent. apply Hno. lia.
  - rewrite app_nil_r. reflexivity.
  - apply env_with_func_refl.
  - apply func_space_refl.
  - apply env_chain_4_absent; assumption.
Qed.

Lemma env_chain_2_absent : forall data q env,
  env.(module_Env_start) = None ->
  no_env_id (bytes_from data q) -> env_chain_2 data q env q env.
Proof.
  intros data q env Hst Hno. exists q. exists env. exists [].
  split; [|split; [|split; [|split]]].
  - exists (bytes_from data q). split.
    + apply repr_customs_done. apply Hno. lia.
    + apply repr_optsec_absent. apply Hno. lia.
  - rewrite app_nil_r. reflexivity.
  - apply env_imported_refl.
  - apply import_spaces_refl.
  - apply env_chain_3_absent; assumption.
Qed.

Lemma env_chain_1_absent : forall data q env,
  env.(module_Env_start) = None ->
  no_env_id (bytes_from data q) -> env_chain_1 data q env q env.
Proof.
  intros data q env Hst Hno. exists q. exists env. exists [].
  split; [|split; [|split]].
  - exists (bytes_from data q). split.
    + apply repr_customs_done. apply Hno. lia.
    + apply repr_optsec_absent. apply Hno. lia.
  - rewrite app_nil_r. reflexivity.
  - apply env_with_types_refl.
  - apply env_chain_2_absent; assumption.
Qed.

Lemma chain_done : forall L data q env,
  (L < 8 -> env.(module_Env_start) = None) ->
  no_env_id (bytes_from data q) ->
  chain_from L data q env q env.
Proof.
  intros L data q env Hst Hno. chain_split L.
  all: try subst L.
  all: first [ apply env_chain_1_absent | apply env_chain_2_absent
             | apply env_chain_3_absent | apply env_chain_4_absent
             | apply env_chain_5_absent | apply env_chain_6_absent
             | apply env_chain_7_absent | apply env_chain_8_absent
             | apply env_chain_9_absent | apply chain_tail_absent ];
       solve [ exact Hno | apply Hst; lia ].
Qed.

(** *** Prepending a custom section

    A custom section the loop consumes joins the [repr_customs] run at the
    head of whatever line of the chain comes next. *)
Lemma chain_tail_custom : forall data p fin env q envf,
  repr_section 0 repr_custom (bytes_from data p) tt (bytes_from data fin) ->
  chain_tail data fin env q envf -> chain_tail data p env q envf.
Proof.
  intros data p fin env q envf Hs [Hc Henv]. split; [|exact Henv].
  apply repr_customs_more with (mid := bytes_from data fin); assumption.
Qed.

Lemma env_chain_9_custom : forall data p fin env q envf,
  repr_section 0 repr_custom (bytes_from data p) tt (bytes_from data fin) ->
  env_chain_9 data fin env q envf -> env_chain_9 data p env q envf.
Proof.
  intros data p fin env q envf Hs [p' [env' [vs [[mid [Hc Ho]] Hrest]]]].
  exists p'. exists env'. exists vs. split; [|exact Hrest].
  exists mid. split; [|exact Ho].
  apply repr_customs_more with (mid := bytes_from data fin); assumption.
Qed.

Lemma env_chain_7_custom : forall data p fin env q envf,
  repr_section 0 repr_custom (bytes_from data p) tt (bytes_from data fin) ->
  env_chain_7 data fin env q envf -> env_chain_7 data p env q envf.
Proof.
  intros data p fin env q envf Hs [p' [env' [vs [[mid [Hc Ho]] Hrest]]]].
  exists p'. exists env'. exists vs. split; [|exact Hrest].
  exists mid. split; [|exact Ho].
  apply repr_customs_more with (mid := bytes_from data fin); assumption.
Qed.

Lemma env_chain_6_custom : forall data p fin env q envf,
  repr_section 0 repr_custom (bytes_from data p) tt (bytes_from data fin) ->
  env_chain_6 data fin env q envf -> env_chain_6 data p env q envf.
Proof.
  intros data p fin env q envf Hs [p' [env' [vs [[mid [Hc Ho]] Hrest]]]].
  exists p'. exists env'. exists vs. split; [|exact Hrest].
  exists mid. split; [|exact Ho].
  apply repr_customs_more with (mid := bytes_from data fin); assumption.
Qed.

Lemma env_chain_5_custom : forall data p fin env q envf,
  repr_section 0 repr_custom (bytes_from data p) tt (bytes_from data fin) ->
  env_chain_5 data fin env q envf -> env_chain_5 data p env q envf.
Proof.
  intros data p fin env q envf Hs [p' [env' [vs [[mid [Hc Ho]] Hrest]]]].
  exists p'. exists env'. exists vs. split; [|exact Hrest].
  exists mid. split; [|exact Ho].
  apply repr_customs_more with (mid := bytes_from data fin); assumption.
Qed.

Lemma env_chain_4_custom : forall data p fin env q envf,
  repr_section 0 repr_custom (bytes_from data p) tt (bytes_from data fin) ->
  env_chain_4 data fin env q envf -> env_chain_4 data p env q envf.
Proof.
  intros data p fin env q envf Hs [p' [env' [vs [[mid [Hc Ho]] Hrest]]]].
  exists p'. exists env'. exists vs. split; [|exact Hrest].
  exists mid. split; [|exact Ho].
  apply repr_customs_more with (mid := bytes_from data fin); assumption.
Qed.

Lemma env_chain_3_custom : forall data p fin env q envf,
  repr_section 0 repr_custom (bytes_from data p) tt (bytes_from data fin) ->
  env_chain_3 data fin env q envf -> env_chain_3 data p env q envf.
Proof.
  intros data p fin env q envf Hs [p' [env' [vs [[mid [Hc Ho]] Hrest]]]].
  exists p'. exists env'. exists vs. split; [|exact Hrest].
  exists mid. split; [|exact Ho].
  apply repr_customs_more with (mid := bytes_from data fin); assumption.
Qed.

Lemma env_chain_2_custom : forall data p fin env q envf,
  repr_section 0 repr_custom (bytes_from data p) tt (bytes_from data fin) ->
  env_chain_2 data fin env q envf -> env_chain_2 data p env q envf.
Proof.
  intros data p fin env q envf Hs [p' [env' [vs [[mid [Hc Ho]] Hrest]]]].
  exists p'. exists env'. exists vs. split; [|exact Hrest].
  exists mid. split; [|exact Ho].
  apply repr_customs_more with (mid := bytes_from data fin); assumption.
Qed.

Lemma env_chain_1_custom : forall data p fin env q envf,
  repr_section 0 repr_custom (bytes_from data p) tt (bytes_from data fin) ->
  env_chain_1 data fin env q envf -> env_chain_1 data p env q envf.
Proof.
  intros data p fin env q envf Hs [p' [env' [vs [[mid [Hc Ho]] Hrest]]]].
  exists p'. exists env'. exists vs. split; [|exact Hrest].
  exists mid. split; [|exact Ho].
  apply repr_customs_more with (mid := bytes_from data fin); assumption.
Qed.

Lemma env_chain_8_custom : forall data p fin env q envf,
  repr_section 0 repr_custom (bytes_from data p) tt (bytes_from data fin) ->
  env_chain_8 data fin env q envf -> env_chain_8 data p env q envf.
Proof.
  intros data p fin env q envf Hs [p' [env' [[mid [Hc Ho]] Hrest]]].
  exists p'. exists env'. split; [|exact Hrest].
  exists mid. split; [|exact Ho].
  apply repr_customs_more with (mid := bytes_from data fin); assumption.
Qed.

Lemma chain_custom : forall L data p fin env q envf,
  repr_section 0 repr_custom (bytes_from data p) tt (bytes_from data fin) ->
  chain_from L data fin env q envf ->
  chain_from L data p env q envf.
Proof.
  intros L data p fin env q envf Hs H. chain_split2 L H.
  all: first [ apply (env_chain_1_custom _ _ fin) | apply (env_chain_2_custom _ _ fin)
             | apply (env_chain_3_custom _ _ fin) | apply (env_chain_4_custom _ _ fin)
             | apply (env_chain_5_custom _ _ fin) | apply (env_chain_6_custom _ _ fin)
             | apply (env_chain_7_custom _ _ fin) | apply (env_chain_8_custom _ _ fin)
             | apply (env_chain_9_custom _ _ fin) | apply (chain_tail_custom _ _ fin) ];
       solve [ exact Hs | exact H ].
Qed.

(** *** Skipping a line the module does not have

    An absent section contributes nothing and moves the cursor nowhere; all it
    asks is that no section of its id, and no custom section, starts here. *)

Lemma env_chain_1_skip : forall data p env q envf,
  ~ begins_with 0 (bytes_from data p) ->
  ~ begins_with 1 (bytes_from data p) ->
  env_chain_2 data p env q envf ->
  env_chain_1 data p env q envf.
Proof.
  intros data p env q envf H0 Hj Hnext. exists p. exists env. exists [].
  split; [|split; [|split]].
  - exists (bytes_from data p). split.
    + apply repr_customs_done. exact H0.
    + apply repr_optsec_absent. exact Hj.
  - rewrite app_nil_r. reflexivity.
  - apply env_with_types_refl.
  - exact Hnext.
Qed.

Lemma env_chain_2_skip : forall data p env q envf,
  ~ begins_with 0 (bytes_from data p) ->
  ~ begins_with 2 (bytes_from data p) ->
  env_chain_3 data p env q envf ->
  env_chain_2 data p env q envf.
Proof.
  intros data p env q envf H0 Hj Hnext. exists p. exists env. exists [].
  split; [|split; [|split; [|split]]].
  - exists (bytes_from data p). split.
    + apply repr_customs_done. exact H0.
    + apply repr_optsec_absent. exact Hj.
  - rewrite app_nil_r. reflexivity.
  - apply env_imported_refl.
  - apply import_spaces_refl.
  - exact Hnext.
Qed.

Lemma env_chain_3_skip : forall data p env q envf,
  ~ begins_with 0 (bytes_from data p) ->
  ~ begins_with 3 (bytes_from data p) ->
  env_chain_4 data p env q envf ->
  env_chain_3 data p env q envf.
Proof.
  intros data p env q envf H0 Hj Hnext. exists p. exists env. exists [].
  split; [|split; [|split; [|split]]].
  - exists (bytes_from data p). split.
    + apply repr_customs_done. exact H0.
    + apply repr_optsec_absent. exact Hj.
  - rewrite app_nil_r. reflexivity.
  - apply env_with_func_refl.
  - apply func_space_refl.
  - exact Hnext.
Qed.

Lemma env_chain_4_skip : forall data p env q envf,
  ~ begins_with 0 (bytes_from data p) ->
  ~ begins_with 4 (bytes_from data p) ->
  env_chain_5 data p env q envf ->
  env_chain_4 data p env q envf.
Proof.
  intros data p env q envf H0 Hj Hnext. exists p. exists env. exists [].
  split; [|split; [|split]].
  - exists (bytes_from data p). split.
    + apply repr_customs_done. exact H0.
    + apply repr_optsec_absent. exact Hj.
  - rewrite app_nil_r. reflexivity.
  - apply env_with_table_refl.
  - exact Hnext.
Qed.

Lemma env_chain_5_skip : forall data p env q envf,
  ~ begins_with 0 (bytes_from data p) ->
  ~ begins_with 5 (bytes_from data p) ->
  env_chain_6 data p env q envf ->
  env_chain_5 data p env q envf.
Proof.
  intros data p env q envf H0 Hj Hnext. exists p. exists env. exists [].
  split; [|split; [|split]].
  - exists (bytes_from data p). split.
    + apply repr_customs_done. exact H0.
    + apply repr_optsec_absent. exact Hj.
  - rewrite app_nil_r. reflexivity.
  - apply env_with_mem_refl.
  - exact Hnext.
Qed.

Lemma env_chain_6_skip : forall data p env q envf,
  ~ begins_with 0 (bytes_from data p) ->
  ~ begins_with 6 (bytes_from data p) ->
  env_chain_7 data p env q envf ->
  env_chain_6 data p env q envf.
Proof.
  intros data p env q envf H0 Hj Hnext. exists p. exists env. exists [].
  split; [|split; [|split; [|split; [|split]]]].
  - exists (bytes_from data p). split.
    + apply repr_customs_done. exact H0.
    + apply repr_optsec_absent. exact Hj.
  - rewrite app_nil_r. reflexivity.
  - apply env_with_global_refl.
  - exact (eq_sym (app_nil_r _)).
  - apply List.Forall_nil.
  - exact Hnext.
Qed.

Lemma env_chain_7_skip : forall data p env q envf,
  ~ begins_with 0 (bytes_from data p) ->
  ~ begins_with 7 (bytes_from data p) ->
  env_chain_8 data p env q envf ->
  env_chain_7 data p env q envf.
Proof.
  intros data p env q envf H0 Hj Hnext. exists p. exists env. exists [].
  split; [|split; [|split; [|split; [|split]]]].
  - exists (bytes_from data p). split.
    + apply repr_customs_done. exact H0.
    + apply repr_optsec_absent. exact Hj.
  - rewrite app_nil_r. reflexivity.
  - apply env_with_exports_refl.
  - exact (fun Hd => Hd).
  - apply List.Forall_nil.
  - exact Hnext.
Qed.

Lemma env_chain_8_skip : forall data p env q envf,
  env.(module_Env_start) = None ->
  ~ begins_with 0 (bytes_from data p) ->
  ~ begins_with 8 (bytes_from data p) ->
  env_chain_9 data p env q envf ->
  env_chain_8 data p env q envf.
Proof.
  intros data p env q envf Hst H0 Hj Hnext. exists p. exists env.
  split; [|split; [|split]].
  - exists (bytes_from data p). split.
    + apply repr_customs_done. exact H0.
    + unfold translate_start. rewrite Hst. cbn [option_map].
      apply repr_optsec_absent. exact Hj.
  - apply env_with_start_refl.
  - unfold start_ok. rewrite Hst. exact I.
  - exact Hnext.
Qed.

Lemma env_chain_9_skip : forall data p env q envf,
  ~ begins_with 0 (bytes_from data p) ->
  ~ begins_with 9 (bytes_from data p) ->
  chain_tail data p env q envf ->
  env_chain_9 data p env q envf.
Proof.
  intros data p env q envf H0 Hj Hnext. exists p. exists env. exists [].
  split; [|split; [|split; [|split]]].
  - exists (bytes_from data p). split.
    + apply repr_customs_done. exact H0.
    + apply repr_optsec_absent. exact Hj.
  - rewrite app_nil_r. reflexivity.
  - apply env_with_elements_refl.
  - apply List.Forall_nil.
  - exact Hnext.
Qed.

Lemma chain_skip : forall L data p env q envf,
  0 <= L -> L < 9 ->
  (L + 1 = 8 -> env.(module_Env_start) = None) ->
  ~ begins_with 0 (bytes_from data p) ->
  ~ begins_with (L + 1) (bytes_from data p) ->
  chain_from (L + 1) data p env q envf ->
  chain_from L data p env q envf.
Proof.
  intros L data p env q envf HL0 HL9 Hst H0 Hj H.
  unfold chain_from in H |- *.
  repeat (match goal with
          | [ |- context [Z.eqb L ?k] ] =>
              let E := fresh "E" in
              destruct (Z.eqb L k) eqn:E;
              [ apply Z.eqb_eq in E | apply Z.eqb_neq in E ]
          end).
  all: try (exfalso; lia).
  all: subst L; cbn beta iota in H |- *.
  all: first [ apply env_chain_1_skip | apply env_chain_2_skip
             | apply env_chain_3_skip | apply env_chain_4_skip
             | apply env_chain_5_skip | apply env_chain_6_skip
             | apply env_chain_7_skip | apply env_chain_8_skip
             | apply env_chain_9_skip ];
       solve [ exact H0 | exact Hj | exact H | apply Hst; lia ].
Qed.

(** [n] lines at once, which is what the loop needs: reading section [k] with
    [last_id = L] declares the [k - 1 - L] lines between them absent. *)
Lemma chain_skip_many : forall n L data p env q envf,
  0 <= L -> L + Z.of_nat n <= 9 ->
  (L < 8 -> env.(module_Env_start) = None) ->
  ~ begins_with 0 (bytes_from data p) ->
  (forall j, L < j <= L + Z.of_nat n -> ~ begins_with j (bytes_from data p)) ->
  chain_from (L + Z.of_nat n) data p env q envf ->
  chain_from L data p env q envf.
Proof.
  induction n as [|n IH]; intros L data p env q envf HL0 Hn Hst H0 Hj H.
  - cbn in H. rewrite Z.add_0_r in H. exact H.
  - apply chain_skip; try lia.
    + intros Heq. apply Hst. lia.
    + exact H0.
    + apply Hj. rewrite Nat2Z.inj_succ. lia.
    + apply (IH (L + 1) data p env q envf); try lia.
      * intros Hlt. apply Hst. lia.
      * exact H0.
      * intros j Hjr. apply Hj. rewrite Nat2Z.inj_succ in *. lia.
      * rewrite Nat2Z.inj_succ in H.
        replace (L + 1 + Z.of_nat n) with (L + Z.succ (Z.of_nat n)) by lia.
        exact H.
Qed.

(** *** A line the module does have *)

Lemma env_chain_1_present : forall data p fin env env' q envf (vs : list types_FuncType_t),
  ~ begins_with 0 (bytes_from data p) ->
  repr_section 1 (repr_vec repr_functype) (bytes_from data p)
    (List.map translate_functype vs) (bytes_from data fin) ->
  vec_list env'.(module_Env_types) = vec_list env.(module_Env_types) ++ vs ->
  env' = env_with_types env env'.(module_Env_types) ->
  env_chain_2 data fin env' q envf ->
  env_chain_1 data p env q envf.
Proof.
  intros data p fin env env' q envf vs H0 Hs Hl He Hnext.
  exists fin. exists env'. exists vs. split; [|split; [|split]].
  - exists (bytes_from data p). split.
    + apply repr_customs_done. exact H0.
    + apply repr_optsec_present. exact Hs.
  - exact Hl.
  - exact He.
  - exact Hnext.
Qed.

Lemma env_chain_2_present : forall data p fin env env' q envf (vs : list module_Import_t),
  ~ begins_with 0 (bytes_from data p) ->
  repr_section 2 (repr_vec repr_import) (bytes_from data p)
    (List.map translate_import vs) (bytes_from data fin) ->
  vec_list env'.(module_Env_imports) = vec_list env.(module_Env_imports) ++ vs ->
  env_imported env env' ->
  import_spaces env env' vs ->
  env_chain_3 data fin env' q envf ->
  env_chain_2 data p env q envf.
Proof.
  intros data p fin env env' q envf vs H0 Hs Hl He Hsp Hnext.
  exists fin. exists env'. exists vs. split; [|split; [|split; [|split]]].
  - exists (bytes_from data p). split.
    + apply repr_customs_done. exact H0.
    + apply repr_optsec_present. exact Hs.
  - exact Hl.
  - exact He.
  - exact Hsp.
  - exact Hnext.
Qed.

Lemma env_chain_3_present : forall data p fin env env' q envf (vs : list (scalar U32)),
  ~ begins_with 0 (bytes_from data p) ->
  repr_section 3 (repr_vec repr_idx) (bytes_from data p)
    (List.map translate_idx vs) (bytes_from data fin) ->
  vec_list env'.(module_Env_func_type_indices)
    = vec_list env.(module_Env_func_type_indices) ++ vs ->
  env' = env_with_func env env'.(module_Env_func_types)
                       env'.(module_Env_func_type_indices) ->
  func_space env env' vs ->
  env_chain_4 data fin env' q envf ->
  env_chain_3 data p env q envf.
Proof.
  intros data p fin env env' q envf vs H0 Hs Hl He Hfs Hnext.
  exists fin. exists env'. exists vs. split; [|split; [|split; [|split]]].
  - exists (bytes_from data p). split.
    + apply repr_customs_done. exact H0.
    + apply repr_optsec_present. exact Hs.
  - exact Hl.
  - exact He.
  - exact Hfs.
  - exact Hnext.
Qed.

Lemma env_chain_4_present : forall data p fin env env' q envf (vs : list types_TableType_t),
  ~ begins_with 0 (bytes_from data p) ->
  repr_section 4 (repr_vec repr_table) (bytes_from data p)
    (List.map translate_table vs) (bytes_from data fin) ->
  vec_list env'.(module_Env_table_types)
    = vec_list env.(module_Env_table_types) ++ vs ->
  env' = env_with_table env env'.(module_Env_table_types) ->
  env_chain_5 data fin env' q envf ->
  env_chain_4 data p env q envf.
Proof.
  intros data p fin env env' q envf vs H0 Hs Hl He Hnext.
  exists fin. exists env'. exists vs. split; [|split; [|split]].
  - exists (bytes_from data p). split.
    + apply repr_customs_done. exact H0.
    + apply repr_optsec_present. exact Hs.
  - exact Hl.
  - exact He.
  - exact Hnext.
Qed.

Lemma env_chain_5_present : forall data p fin env env' q envf (vs : list types_MemType_t),
  ~ begins_with 0 (bytes_from data p) ->
  repr_section 5 (repr_vec repr_mem) (bytes_from data p)
    (List.map translate_mem vs) (bytes_from data fin) ->
  vec_list env'.(module_Env_mem_types)
    = vec_list env.(module_Env_mem_types) ++ vs ->
  env' = env_with_mem env env'.(module_Env_mem_types) ->
  env_chain_6 data fin env' q envf ->
  env_chain_5 data p env q envf.
Proof.
  intros data p fin env env' q envf vs H0 Hs Hl He Hnext.
  exists fin. exists env'. exists vs. split; [|split; [|split]].
  - exists (bytes_from data p). split.
    + apply repr_customs_done. exact H0.
    + apply repr_optsec_present. exact Hs.
  - exact Hl.
  - exact He.
  - exact Hnext.
Qed.

Lemma env_chain_6_present : forall data p fin env env' q envf (vs : list module_Global_t),
  ~ begins_with 0 (bytes_from data p) ->
  repr_section 6 (repr_vec repr_global) (bytes_from data p)
    (List.map translate_global vs) (bytes_from data fin) ->
  vec_list env'.(module_Env_globals) = vec_list env.(module_Env_globals) ++ vs ->
  env' = env_with_global env env'.(module_Env_globals)
                         env'.(module_Env_global_types) ->
  vec_list env'.(module_Env_global_types)
    = vec_list env.(module_Env_global_types)
      ++ List.map (fun g => g.(module_Global_gtype)) vs ->
  List.Forall (global_ok env') vs ->
  env_chain_7 data fin env' q envf ->
  env_chain_6 data p env q envf.
Proof.
  intros data p fin env env' q envf vs H0 Hs Hl He Hgts Hoks Hnext.
  exists fin. exists env'. exists vs.
  split; [|split; [|split; [|split; [|split]]]].
  - exists (bytes_from data p). split.
    + apply repr_customs_done. exact H0.
    + apply repr_optsec_present. exact Hs.
  - exact Hl.
  - exact He.
  - exact Hgts.
  - exact Hoks.
  - exact Hnext.
Qed.

Lemma env_chain_7_present : forall data p fin env env' q envf (vs : list module_Export_t),
  ~ begins_with 0 (bytes_from data p) ->
  repr_section 7 (repr_vec repr_export) (bytes_from data p)
    (List.map translate_export vs) (bytes_from data fin) ->
  vec_list env'.(module_Env_exports) = vec_list env.(module_Env_exports) ++ vs ->
  env' = env_with_exports env env'.(module_Env_exports) ->
  (exports_distinct env -> exports_distinct env') ->
  List.Forall (export_desc_ok env) vs ->
  env_chain_8 data fin env' q envf ->
  env_chain_7 data p env q envf.
Proof.
  intros data p fin env env' q envf vs H0 Hs Hl He Hdist Hdesc Hnext.
  exists fin. exists env'. exists vs.
  split; [|split; [|split; [|split; [|split]]]].
  - exists (bytes_from data p). split.
    + apply repr_customs_done. exact H0.
    + apply repr_optsec_present. exact Hs.
  - exact Hl.
  - exact He.
  - exact Hdist.
  - exact Hdesc.
  - exact Hnext.
Qed.

Lemma env_chain_9_present : forall data p fin env env' q envf (vs : list module_Element_t),
  ~ begins_with 0 (bytes_from data p) ->
  repr_section 9 (repr_vec repr_elem) (bytes_from data p)
    (List.map translate_element vs) (bytes_from data fin) ->
  vec_list env'.(module_Env_elements) = vec_list env.(module_Env_elements) ++ vs ->
  env' = env_with_elements env env'.(module_Env_elements) ->
  List.Forall (element_ok env) vs ->
  chain_tail data fin env' q envf ->
  env_chain_9 data p env q envf.
Proof.
  intros data p fin env env' q envf vs H0 Hs Hl He Hels Hnext.
  exists fin. exists env'. exists vs. split; [|split; [|split; [|split]]].
  - exists (bytes_from data p). split.
    + apply repr_customs_done. exact H0.
    + apply repr_optsec_present. exact Hs.
  - exact Hl.
  - exact He.
  - exact Hels.
  - exact Hnext.
Qed.

Lemma env_chain_8_present : forall data p fin env env' q envf,
  ~ begins_with 0 (bytes_from data p) ->
  repr_section 8 repr_start (bytes_from data p)
    (translate_start env'.(module_Env_start)) (bytes_from data fin) ->
  env' = env_with_start env env'.(module_Env_start) ->
  start_ok env' ->
  env_chain_9 data fin env' q envf ->
  env_chain_8 data p env q envf.
Proof.
  intros data p fin env env' q envf H0 Hs He Hstart Hnext.
  exists fin. exists env'. split; [|split; [|split]].
  - exists (bytes_from data p). split.
    + apply repr_customs_done. exact H0.
    + apply repr_optsec_present. exact Hs.
  - exact He.
  - exact Hstart.
  - exact Hnext.
Qed.

(** The [k - 1 - L] lines between the last id read and this one. *)
Lemma chain_skip_to : forall L k data p env q envf,
  0 <= L -> L < k -> k <= 9 ->
  (L < 8 -> env.(module_Env_start) = None) ->
  (forall j, 0 <= j < k -> ~ begins_with j (bytes_from data p)) ->
  chain_from (k - 1) data p env q envf ->
  chain_from L data p env q envf.
Proof.
  intros L k data p env q envf HL0 HLk Hk9 Hst Hno H.
  apply (chain_skip_many (Z.to_nat (k - 1 - L)) L);
    [ lia | rewrite Z2Nat.id; lia | exact Hst | apply Hno; lia | | ].
  - intros j Hj. rewrite Z2Nat.id in Hj by lia. apply Hno. lia.
  - rewrite Z2Nat.id by lia.
    replace (L + (k - 1 - L)) with (k - 1) by lia. exact H.
Qed.

(** *** The loop

    The id a section header read is the byte at the cursor, which is what
    every absence in the chain is discharged from. *)
Lemma read_section_header_head : forall data pos id start fin,
  module_read_section_header data pos
    = Ok (Core_result_Result_Ok (id, start, fin)) ->
  exists rest, bytes_from data pos = to_Z id :: rest.
Proof.
  intros data pos id start fin H. unfold module_read_section_header in H.
  destruct (reader_read_byte data pos) as [r|] eqn:Hb; cbn [bind] in H;
    [|discriminate].
  destruct r as [[b p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_u32_leb data p) as [r1|]; cbn [bind] in H;
    [|discriminate].
  destruct r1 as [[size q]|e1]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (scalar_cast U32 Usize size) as [n|]; cbn [bind] in H;
    [|discriminate].
  destruct (module_have_bytes data q n) as [r2|]; cbn [bind] in H;
    [|discriminate].
  destruct r2 as [[]|e2]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (usize_add q n) as [q2|]; cbn [bind] in H; [|discriminate].
  injection H as -> -> ->.
  exists (bytes_from data p). apply (proj1 (read_byte_ok _ _ _ _ Hb)).
Qed.

Lemma not_begins_of_head : forall data q (id : u8) rest j,
  bytes_from data q = to_Z id :: rest ->
  j <> to_Z id ->
  ~ begins_with j (bytes_from data q).
Proof.
  intros data q id rest j Heq Hne [more Hm].
  rewrite Heq in Hm. injection Hm as Hj _. lia.
Qed.

Lemma no_env_id_nil : forall bs, bs = [] -> no_env_id bs.
Proof. intros bs -> j Hj [more Hm]. discriminate. Qed.

Lemma no_env_id_of_head : forall data q (id : u8) rest,
  bytes_from data q = to_Z id :: rest ->
  10 <= to_Z id ->
  no_env_id (bytes_from data q).
Proof.
  intros data q id rest Heq Hge j Hj.
  apply (not_begins_of_head data q id rest j Heq). lia.
Qed.

(** No [module_hooks_total] here, and none needed: this is about a run that
    happened, so whatever the consumer did it returned, and soundness of the
    bytes it accepted does not depend on what it did with them. Same reason
    [validate_code_entry_with_sound] carries no hypothesis. *)
Lemma validate_env_with_loop_sound :
  forall V (inst : module_ModuleVisitor_t V) m data vis vis' env q last_id envf qf,
  Z.of_nat (List.length (vec_list data)) - to_Z q <= Z.of_nat m ->
  0 <= to_Z last_id <= 9 ->
  (to_Z last_id < 8 -> env.(module_Env_start) = None) ->
  module_validate_env_with_loop inst data vis env q last_id
    = Ok (Core_result_Result_Ok (envf, qf), vis') ->
  chain_from (to_Z last_id) data q env qf envf.
Proof.
  intros V inst m. induction m as [|m IH];
    intros data vis vis' env q last_id envf qf Hmeas Hlid Hst H;
    unfold module_validate_env_with_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (q s>= slice_len data) eqn:Hge.
  1,3: injection H as <- <- <-; apply chain_done; [exact Hst|];
       apply no_env_id_nil; rewrite bytes_from_at; apply bytes_at_end;
       apply scalar_geb_true_ge in Hge; rewrite slice_len_spec in Hge; lia.
  - exfalso. apply scalar_geb_false_lt in Hge.
    rewrite slice_len_spec in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge. rewrite slice_len_spec in Hge.
    destruct (module_read_section_header data q) as [r|] eqn:Hhdr;
      cbn [bind] in H; [|discriminate].
    destruct r as [[[id start] fin]|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (read_section_header_step _ _ _ _ _ Hhdr) as [Hqs [Hsf Hfd]].
    rewrite slice_len_spec in Hfd.
    destruct (read_section_header_head _ _ _ _ _ Hhdr) as [rest Hhead].
    pose proof (u8_bounds id) as Hidb.
    destruct (id s= module_section_custom) eqn:Hcust.
    { pose proof (scalar_eqb_val _ _ 0 Hcust eq_refl) as Hid0.
      destruct (module_decode_custom_section data start fin) as [r1|] eqn:Hcs;
        cbn [bind] in H; [|discriminate].
      destruct r1 as [c|e1]; [|try_err_rw_in H; discriminate].
      rewrite branch_ok in H. cbn [bind] in H.
      (* the consumer was shown the section; whatever it did, it returned *)
      destruct (inst.(module_ModuleVisitor_t_on_custom_section) vis c)
        as [[rh vis1]|] eqn:Hh; cbn [bind] in H; [|discriminate].
      destruct rh as [u|ev]; [|cbn beta iota in H; discriminate].
      cbn beta iota in H.
      apply (chain_custom _ data q fin).
      - rewrite <- Hid0.
        apply (read_section_header_sound _ _ _ _ _ _ _ _ Hhdr).
        apply (decode_custom_section_sound data start fin c);
          [exact Hcs | lia | lia].
      - apply (IH data vis1 vis' env fin last_id envf qf);
          [lia | exact Hlid | exact Hst | exact H]. }
    apply scalar_eqb_false in Hcust. cbn in Hcust.
    destruct (id s>= module_section_code) eqn:Hcode.
    { pose proof (scalar_geb_val _ _ 10 Hcode eq_refl) as Hid10.
      injection H as <- <-. apply chain_done; [exact Hst|].
      apply (no_env_id_of_head data q id rest Hhead Hid10). }
    apply scalar_geb_false_lt in Hcode. cbn in Hcode.
    destruct (id s<= last_id) eqn:Hord; [discriminate|].
    apply scalar_leb_false in Hord.
    destruct (module_decode_env_section data start id env) as [[r1 env2]|]
      eqn:Hsec; cbn [bind] in H; [|discriminate].
    destruct r1 as [p|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (p s<> fin) eqn:Hne; [discriminate|].
    apply scalar_neqb_false in Hne.
    (* the cursor and the header pin the id between one and nine *)
    assert (Hnob : forall j, 0 <= j < to_Z id ->
                     ~ begins_with j (bytes_from data q))
      by (intros j Hj; apply (not_begins_of_head data q id rest j Hhead); lia).
    assert (Hstep : to_Z q < to_Z fin) by lia.
    assert (Hmeas' : Z.of_nat (List.length (vec_list data)) - to_Z fin
                     <= Z.of_nat m) by (cbn in Hmeas; lia).
    (* [p = fin] is the section-size check, so the section ends where the
       header said it would *)
    assert (Hpf : bytes_from data p = bytes_from data fin)
      by (apply bytes_at_congr; exact Hne).
    assert (Hcases : to_Z id = 1 \/ to_Z id = 2 \/ to_Z id = 3
                     \/ to_Z id = 4 \/ to_Z id = 5 \/ to_Z id = 6
                     \/ to_Z id = 7 \/ to_Z id = 8 \/ to_Z id = 9) by lia.
    destruct Hcases as [Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|Hk]]]]]]]].
    { destruct (decode_type_section_sound _ _ _ _ _
                  (env_section_is_type _ _ _ _ _ _ Hk Hsec))
        as [vs [Hlist [Henv [_ Hrep]]]].
      apply (chain_skip_to (to_Z last_id) (to_Z id) data q env qf envf);
        [ lia | lia | lia | exact Hst | exact Hnob | ].
      replace (to_Z id - 1) with 0 by lia. unfold chain_from. cbn beta iota.
      apply (env_chain_1_present data q fin env env2 qf envf vs).
      - apply Hnob. lia.
      - rewrite <- Hk.
        apply (section_sound _ _ data q id start fin _ (repr_vec_prefix _ _ repr_functype_prefix) Hhdr).
        rewrite <- Hpf. exact Hrep.
      - exact Hlist.
      - exact Henv.
      - assert (Hb : 0 <= to_Z id <= 9) by lia.
        assert (Hs : to_Z id < 8 -> env2.(module_Env_start) = None)
          by (intros _; rewrite Henv; cbn [env_with_types module_Env_start];
                apply Hst; lia).
        pose proof (IH data vis vis' env2 fin id envf qf Hmeas' Hb Hs H) as Hrec.
        rewrite Hk in Hrec. exact Hrec. }
    { destruct (decode_import_section_sound _ _ _ _ _
                  (env_section_is_import _ _ _ _ _ _ Hk Hsec))
        as [vs [Hlist [Henv [Hrep [_ Hsp]]]]].
      unfold env_imported in Henv. apply (chain_skip_to (to_Z last_id) (to_Z id) data q env qf envf);
        [ lia | lia | lia | exact Hst | exact Hnob | ].
      replace (to_Z id - 1) with 1 by lia. unfold chain_from. cbn beta iota.
      apply (env_chain_2_present data q fin env env2 qf envf vs).
      - apply Hnob. lia.
      - rewrite <- Hk.
        apply (section_sound _ _ data q id start fin _ (repr_vec_prefix _ _ repr_import_prefix) Hhdr).
        rewrite <- Hpf. exact Hrep.
      - exact Hlist.
      - exact Henv.
      - exact Hsp.
      - assert (Hb : 0 <= to_Z id <= 9) by lia.
        assert (Hs : to_Z id < 8 -> env2.(module_Env_start) = None)
          by (intros _; rewrite Henv; cbn [env_with_import module_Env_start];
                apply Hst; lia).
        pose proof (IH data vis vis' env2 fin id envf qf Hmeas' Hb Hs H) as Hrec.
        rewrite Hk in Hrec. exact Hrec. }
    { destruct (decode_function_section_sound _ _ _ _ _
                  (env_section_is_function _ _ _ _ _ _ Hk Hsec))
        as [vs [Hlist [Henv [Hrep Hfs]]]].
      apply (chain_skip_to (to_Z last_id) (to_Z id) data q env qf envf);
        [ lia | lia | lia | exact Hst | exact Hnob | ].
      replace (to_Z id - 1) with 2 by lia. unfold chain_from. cbn beta iota.
      apply (env_chain_3_present data q fin env env2 qf envf vs).
      - apply Hnob. lia.
      - rewrite <- Hk.
        apply (section_sound _ _ data q id start fin _ (repr_vec_prefix _ _ repr_idx_prefix) Hhdr).
        rewrite <- Hpf. exact Hrep.
      - exact Hlist.
      - exact Henv.
      - exact Hfs.
      - assert (Hb : 0 <= to_Z id <= 9) by lia.
        assert (Hs : to_Z id < 8 -> env2.(module_Env_start) = None)
          by (intros _; rewrite Henv; cbn [env_with_func module_Env_start];
                apply Hst; lia).
        pose proof (IH data vis vis' env2 fin id envf qf Hmeas' Hb Hs H) as Hrec.
        rewrite Hk in Hrec. exact Hrec. }
    { destruct (decode_table_section_sound _ _ _ _ _
                  (env_section_is_table _ _ _ _ _ _ Hk Hsec))
        as [vs [Hlist [Henv [Hrep _]]]].
      apply (chain_skip_to (to_Z last_id) (to_Z id) data q env qf envf);
        [ lia | lia | lia | exact Hst | exact Hnob | ].
      replace (to_Z id - 1) with 3 by lia. unfold chain_from. cbn beta iota.
      apply (env_chain_4_present data q fin env env2 qf envf vs).
      - apply Hnob. lia.
      - rewrite <- Hk.
        apply (section_sound _ _ data q id start fin _ (repr_vec_prefix _ _ repr_table_prefix) Hhdr).
        rewrite <- Hpf. exact Hrep.
      - exact Hlist.
      - exact Henv.
      - assert (Hb : 0 <= to_Z id <= 9) by lia.
        assert (Hs : to_Z id < 8 -> env2.(module_Env_start) = None)
          by (intros _; rewrite Henv; cbn [env_with_table module_Env_start];
                apply Hst; lia).
        pose proof (IH data vis vis' env2 fin id envf qf Hmeas' Hb Hs H) as Hrec.
        rewrite Hk in Hrec. exact Hrec. }
    { destruct (decode_memory_section_sound _ _ _ _ _
                  (env_section_is_memory _ _ _ _ _ _ Hk Hsec))
        as [vs [Hlist [Henv [Hrep _]]]].
      apply (chain_skip_to (to_Z last_id) (to_Z id) data q env qf envf);
        [ lia | lia | lia | exact Hst | exact Hnob | ].
      replace (to_Z id - 1) with 4 by lia. unfold chain_from. cbn beta iota.
      apply (env_chain_5_present data q fin env env2 qf envf vs).
      - apply Hnob. lia.
      - rewrite <- Hk.
        apply (section_sound _ _ data q id start fin _ (repr_vec_prefix _ _ repr_mem_prefix) Hhdr).
        rewrite <- Hpf. exact Hrep.
      - exact Hlist.
      - exact Henv.
      - assert (Hb : 0 <= to_Z id <= 9) by lia.
        assert (Hs : to_Z id < 8 -> env2.(module_Env_start) = None)
          by (intros _; rewrite Henv; cbn [env_with_mem module_Env_start];
                apply Hst; lia).
        pose proof (IH data vis vis' env2 fin id envf qf Hmeas' Hb Hs H) as Hrec.
        rewrite Hk in Hrec. exact Hrec. }
    { destruct (decode_global_section_sound _ _ _ _ _
                  (env_section_is_global _ _ _ _ _ _ Hk Hsec))
        as [vs [Hlist [Henv [Hrep [Hgts Hoks]]]]].
      apply (chain_skip_to (to_Z last_id) (to_Z id) data q env qf envf);
        [ lia | lia | lia | exact Hst | exact Hnob | ].
      replace (to_Z id - 1) with 5 by lia. unfold chain_from. cbn beta iota.
      apply (env_chain_6_present data q fin env env2 qf envf vs).
      - apply Hnob. lia.
      - rewrite <- Hk.
        apply (section_sound _ _ data q id start fin _ (repr_vec_prefix _ _ repr_global_prefix) Hhdr).
        rewrite <- Hpf. exact Hrep.
      - exact Hlist.
      - exact Henv.
      - exact Hgts.
      - exact Hoks.
      - assert (Hb : 0 <= to_Z id <= 9) by lia.
        assert (Hs : to_Z id < 8 -> env2.(module_Env_start) = None)
          by (intros _; rewrite Henv; cbn [env_with_global module_Env_start];
                apply Hst; lia).
        pose proof (IH data vis vis' env2 fin id envf qf Hmeas' Hb Hs H) as Hrec.
        rewrite Hk in Hrec. exact Hrec. }
    { destruct (decode_export_section_sound _ _ _ _ _
                  (env_section_is_export _ _ _ _ _ _ Hk Hsec))
        as [vs [Hlist [Henv [Hrep [Hdist Hdesc]]]]].
      apply (chain_skip_to (to_Z last_id) (to_Z id) data q env qf envf);
        [ lia | lia | lia | exact Hst | exact Hnob | ].
      replace (to_Z id - 1) with 6 by lia. unfold chain_from. cbn beta iota.
      apply (env_chain_7_present data q fin env env2 qf envf vs).
      - apply Hnob. lia.
      - rewrite <- Hk.
        apply (section_sound _ _ data q id start fin _ (repr_vec_prefix _ _ repr_export_prefix) Hhdr).
        rewrite <- Hpf. exact Hrep.
      - exact Hlist.
      - exact Henv.
      - exact Hdist.
      - exact Hdesc.
      - assert (Hb : 0 <= to_Z id <= 9) by lia.
        assert (Hs : to_Z id < 8 -> env2.(module_Env_start) = None)
          by (intros _; rewrite Henv; cbn [env_with_exports module_Env_start];
                apply Hst; lia).
        pose proof (IH data vis vis' env2 fin id envf qf Hmeas' Hb Hs H) as Hrec.
        rewrite Hk in Hrec. exact Hrec. }
    { destruct (decode_start_section_sound _ _ _ _ _
                  (env_section_is_start _ _ _ _ _ _ Hk Hsec))
        as [Henv [Hrep Hstart]].
      apply (chain_skip_to (to_Z last_id) (to_Z id) data q env qf envf);
        [ lia | lia | lia | exact Hst | exact Hnob | ].
      replace (to_Z id - 1) with 7 by lia. unfold chain_from. cbn beta iota.
      apply (env_chain_8_present data q fin env env2 qf envf).
      - apply Hnob. lia.
      - rewrite <- Hk.
        apply (section_sound _ _ data q id start fin _ repr_start_prefix Hhdr).
        rewrite <- Hpf. exact Hrep.
      - exact Henv.
      - exact Hstart.
      - assert (Hb : 0 <= to_Z id <= 9) by lia.
        assert (Hs : to_Z id < 8 -> env2.(module_Env_start) = None)
          by (intros Hlt; exfalso; lia).
        pose proof (IH data vis vis' env2 fin id envf qf Hmeas' Hb Hs H) as Hrec.
        rewrite Hk in Hrec. exact Hrec. }
    { destruct (decode_element_section_sound _ _ _ _ _
                  (env_section_is_element _ _ _ _ _ _ Hk Hsec))
        as [vs [Hlist [Henv [Hrep Hels]]]].
      apply (chain_skip_to (to_Z last_id) (to_Z id) data q env qf envf);
        [ lia | lia | lia | exact Hst | exact Hnob | ].
      replace (to_Z id - 1) with 8 by lia. unfold chain_from. cbn beta iota.
      apply (env_chain_9_present data q fin env env2 qf envf vs).
      - apply Hnob. lia.
      - rewrite <- Hk.
        apply (section_sound _ _ data q id start fin _ (repr_vec_prefix _ _ repr_elem_prefix) Hhdr).
        rewrite <- Hpf. exact Hrep.
      - exact Hlist.
      - exact Henv.
      - exact Hels.
      - assert (Hb : 0 <= to_Z id <= 9) by lia.
        assert (Hs : to_Z id < 8 -> env2.(module_Env_start) = None)
          by (intros Hlt; exfalso; lia).
        pose proof (IH data vis vis' env2 fin id envf qf Hmeas' Hb Hs H) as Hrec.
        rewrite Hk in Hrec. exact Hrec. }
Qed.

(** Spec 5.5.16's magic number and version, then the nine lines of the section
    chain. [validate_env] hands back the cursor it stopped at, which is where
    the run of custom sections before the code section ended. *)
(** The nop consumer's one hook, as an equation. *)
Lemma nop_custom_section : forall c,
  module_EmptyModuleVisitor_Insts_ItascaModuleModuleVisitor.(module_ModuleVisitor_t_on_custom_section)
    tt c = Ok (Core_result_Result_Ok tt, tt).
Proof. intros c. reflexivity. Qed.

(** An accepting driven decode is an accepting plain one, with the same
    environment and the same cursor.

    No hypothesis about the consumer: reporting a custom section cannot change
    what the walk reads next, so a run that got to the end got there by the
    same path the nop consumer takes. The only thing a hook can do is stop the
    walk, and this is about a walk that did not stop. *)
Lemma validate_env_with_loop_driven :
  forall V (inst : module_ModuleVisitor_t V) m data vis vis' env q last_id envf qf,
  Z.of_nat (List.length (vec_list data)) - to_Z q <= Z.of_nat m ->
  module_validate_env_with_loop inst data vis env q last_id
    = Ok (Core_result_Result_Ok (envf, qf), vis') ->
  module_validate_env_with_loop
    module_EmptyModuleVisitor_Insts_ItascaModuleModuleVisitor data tt env q
    last_id = Ok (Core_result_Result_Ok (envf, qf), tt).
Proof.
  intros V inst m. induction m as [|m IH];
    intros data vis vis' env q last_id envf qf Hmeas H;
    unfold module_validate_env_with_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H;
    unfold module_validate_env_with_loop; rewrite loop_unfold; cbn beta iota;
    destruct (q s>= slice_len data) eqn:Hge.
  1,3: injection H as <- <- <-; reflexivity.
  - exfalso. apply scalar_geb_false_lt in Hge.
    rewrite slice_len_spec in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge. rewrite slice_len_spec in Hge.
    destruct (module_read_section_header data q) as [r|] eqn:Hhdr;
      cbn [bind] in H |- *; [|discriminate].
    destruct r as [[[id start] fin]|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H |- *. cbn [bind] in H |- *.
    destruct (read_section_header_step _ _ _ _ _ Hhdr) as [Hqs [Hsf Hfd]].
    rewrite slice_len_spec in Hfd.
    destruct (id s= module_section_custom).
    { destruct (module_decode_custom_section data start fin) as [r1|] eqn:Hcs;
        cbn [bind] in H |- *; [|discriminate].
      destruct r1 as [c|e1]; [|try_err_rw_in H; discriminate].
      rewrite branch_ok in H |- *. cbn [bind] in H |- *.
      destruct (inst.(module_ModuleVisitor_t_on_custom_section) vis c)
        as [[rh vis1]|] eqn:Hh; cbn [bind] in H; [|discriminate].
      destruct rh as [u|ev]; [|cbn beta iota in H; discriminate].
      cbn beta iota in H.
      rewrite nop_custom_section. cbn [bind]. cbn beta iota.
      exact (IH data vis1 vis' env fin last_id envf qf (ltac:(lia)) H). }
    destruct (id s>= module_section_code).
    { injection H as <- <- <-. reflexivity. }
    destruct (id s<= last_id); [discriminate|].
    destruct (module_decode_env_section data start id env) as [[r1 env2]|]
      eqn:Hsec; cbn [bind] in H |- *; [|discriminate].
    destruct r1 as [p|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H |- *. cbn [bind] in H |- *.
    destruct (p s<> fin); [discriminate|].
    cbn beta iota in H |- *.
    exact (IH data vis vis' env2 fin id envf qf (ltac:(lia)) H).
Qed.

Lemma validate_env_driven :
  forall V (inst : module_ModuleVisitor_t V) data vis vis' env qf,
  module_validate_env_with inst data vis
    = Ok (Core_result_Result_Ok (env, qf), vis') ->
  module_validate_env data = Ok (Core_result_Result_Ok (env, qf)).
Proof.
  intros V inst data vis vis' env qf H.
  apply validate_env_nop.
  unfold module_validate_env_with in H |- *.
  destruct module_Env_new as [env0|] eqn:Hnew; cbn [bind] in H |- *;
    [|discriminate].
  destruct (module_read_header data) as [r|] eqn:Hhdr;
    cbn [bind] in H |- *; [|discriminate].
  destruct r as [p0|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H |- *. cbn [bind] in H |- *.
  exact (validate_env_with_loop_driven V inst (List.length (vec_list data)) data
           vis vis' env0 p0 0%u8 env qf
           (ltac:(pose proof (usize_nonneg p0); lia)) H).
Qed.

(** [validate_env] is [validate_env_with] at the do-nothing consumer with the
    visitor state projected away, so an accepting run of the one is an
    accepting run of the other. The mirror of [code_entry_nop_inv]. *)
Lemma validate_env_nop_inv : forall data r,
  module_validate_env data = Ok r ->
  module_validate_env_with module_EmptyModuleVisitor_Insts_ItascaModuleModuleVisitor
    data tt = Ok (r, tt).
Proof.
  intros data r H. unfold module_validate_env in H.
  destruct (module_validate_env_with
              module_EmptyModuleVisitor_Insts_ItascaModuleModuleVisitor data tt)
    as [[r0 v0]|] eqn:Hw; cbn [bind] in H; [|discriminate].
  injection H as <-. destruct v0. reflexivity.
Qed.

(** The same for the tail, and for the same reason. *)
Lemma validate_tail_with_loop_driven :
  forall V (inst : module_ModuleVisitor_t V) m data env vis vis' segments q seen tail,
  Z.of_nat (List.length (vec_list data)) - to_Z q <= Z.of_nat m ->
  module_validate_tail_with_loop inst data env vis segments q seen
    = Ok (Core_result_Result_Ok tail, vis') ->
  module_validate_tail_with_loop
    module_EmptyModuleVisitor_Insts_ItascaModuleModuleVisitor data env tt
    segments q seen = Ok (Core_result_Result_Ok tail, tt).
Proof.
  intros V inst m. induction m as [|m IH];
    intros data env vis vis' segments q seen tail Hmeas H;
    unfold module_validate_tail_with_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H;
    unfold module_validate_tail_with_loop; rewrite loop_unfold; cbn beta iota;
    destruct (q s>= slice_len data) eqn:Hge.
  1,3: injection H as <- <-; reflexivity.
  - exfalso. apply scalar_geb_false_lt in Hge.
    rewrite slice_len_spec in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge. rewrite slice_len_spec in Hge.
    destruct (module_read_section_header data q) as [r|] eqn:Hhdr;
      cbn [bind] in H |- *; [|discriminate].
    destruct r as [[[id start] fin]|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H |- *. cbn [bind] in H |- *.
    destruct (read_section_header_step _ _ _ _ _ Hhdr) as [Hqs [Hsf Hfd]].
    rewrite slice_len_spec in Hfd.
    destruct (id s= module_section_custom).
    { destruct (module_decode_custom_section data start fin) as [r1|] eqn:Hcs;
        cbn [bind] in H |- *; [|discriminate].
      destruct r1 as [c|e1]; [|try_err_rw_in H; discriminate].
      rewrite branch_ok in H |- *. cbn [bind] in H |- *.
      destruct (inst.(module_ModuleVisitor_t_on_custom_section) vis c)
        as [[rh vis1]|] eqn:Hh; cbn [bind] in H; [|discriminate].
      destruct rh as [u|ev]; [|cbn beta iota in H; discriminate].
      cbn beta iota in H.
      rewrite nop_custom_section. cbn [bind]. cbn beta iota.
      exact (IH data env vis1 vis' segments fin seen tail (ltac:(lia)) H). }
    destruct (id s<> module_section_data); [discriminate|].
    destruct seen; [discriminate|].
    destruct (module_decode_data_section data start env) as [r1|] eqn:Hds;
      cbn [bind] in H |- *; [|discriminate].
    destruct r1 as [[decoded p]|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H |- *. cbn [bind] in H |- *.
    destruct (p s<> fin); [discriminate|].
    cbn beta iota in H |- *.
    exact (IH data env vis vis' decoded fin true tail (ltac:(lia)) H).
Qed.

Lemma validate_tail_driven :
  forall V (inst : module_ModuleVisitor_t V) data pos env vis vis' tail,
  module_validate_tail_with inst data pos env vis
    = Ok (Core_result_Result_Ok tail, vis') ->
  module_validate_tail data pos env = Ok (Core_result_Result_Ok tail).
Proof.
  intros V inst data pos env vis vis' tail H.
  apply validate_tail_nop.
  unfold module_validate_tail_with in H |- *.
  exact (validate_tail_with_loop_driven V inst (List.length (vec_list data)) data
           env vis vis' (alloc_vec_Vec_new module_Data_t) pos false tail
           (ltac:(pose proof (usize_nonneg pos); lia)) H).
Qed.

Lemma validate_tail_nop_inv : forall data pos env r,
  module_validate_tail data pos env = Ok r ->
  module_validate_tail_with module_EmptyModuleVisitor_Insts_ItascaModuleModuleVisitor
    data pos env tt = Ok (r, tt).
Proof.
  intros data pos env r H. unfold module_validate_tail in H.
  destruct (module_validate_tail_with
              module_EmptyModuleVisitor_Insts_ItascaModuleModuleVisitor data pos
              env tt) as [[r0 v0]|] eqn:Hw; cbn [bind] in H; [|discriminate].
  injection H as <-. destruct v0. reflexivity.
Qed.

Lemma validate_env_sound : forall data env qf,
  module_validate_env data = Ok (Core_result_Result_Ok (env, qf)) ->
  exists p0 env0,
    repr_magic_version (byte_list data) (bytes_from data p0)
    /\ module_Env_new = Ok env0
    /\ chain_from 0 data p0 env0 qf env.
Proof.
  intros data env qf H0. pose proof (validate_env_nop_inv _ _ H0) as H.
  clear H0. unfold module_validate_env_with in H.
  destruct module_Env_new as [env0|] eqn:Hnew; cbn [bind] in H; [|discriminate].
  destruct (module_read_header data) as [r|] eqn:Hhdr; cbn [bind] in H;
    [|discriminate].
  destruct r as [p0|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  exists p0. exists env0.
  split; [apply (read_header_sound _ _ Hhdr)|].
  (* [destruct] rewrote the goal's occurrence too *)
  split; [reflexivity|].
  assert (Hz : to_Z 0%u8 = 0) by reflexivity.
  rewrite <- Hz.
  apply (validate_env_with_loop_sound _
           module_EmptyModuleVisitor_Insts_ItascaModuleModuleVisitor
           (List.length (vec_list data)) data tt tt env0 p0 0%u8 env qf);
    [ pose proof (usize_nonneg p0); lia
    | rewrite Hz; lia
    | intros _; unfold module_Env_new in Hnew; injection Hnew as <-; reflexivity
    | exact H ].
Qed.

(* ================================================================== *)
(** ** 5.5.14 Data segments, and the tail                              *)
(* ================================================================== *)

Definition translate_data (d : module_Data_t) : module_data :=
  {| moddata_init := translate_data_bytes d.(module_Data_init);
     moddata_mode :=
       MD_active (translate_idx d.(module_Data_memory_idx))
         [translate_const_expr d.(module_Data_offset)] |}.

Lemma data_byte_is_translate : forall b : u8,
  data_byte_is (to_Z b) (translate_data_byte b).
Proof.
  intros b. pose proof (u8_bounds b) as Hb.
  unfold data_byte_is, translate_data_byte.
  apply Integers.Byte.unsigned_repr.
  change Integers.Byte.max_unsigned with 255. lia.
Qed.

Lemma forall2_data_bytes : forall v : alloc_vec_Vec u8,
  Forall2 data_byte_is (List.map to_Z (vec_list v)) (translate_data_bytes v).
Proof.
  intros v. unfold translate_data_bytes.
  induction (vec_list v) as [|b l IH]; cbn [List.map].
  - apply Forall2_nil.
  - apply Forall2_cons; [apply data_byte_is_translate | exact IH].
Qed.

(** Spec 3.4.6: the memory index is in the memory space and the offset is a
    constant expression of type [i32]. The tail decodes against the finished
    environment, so this is already about the environment the module's type
    checker will use. *)
Definition data_ok (env : module_Env_t) (d : module_Data_t) : Prop :=
  to_Z d.(module_Data_memory_idx)
    < Z.of_nat (List.length (vec_list env.(module_Env_mem_types)))
  /\ const_expr_ok env Types_ValueType_I32 d.(module_Data_offset).

Lemma decode_data_segment_sound : forall data pos env d p',
  module_decode_data_segment data pos env
    = Ok (Core_result_Result_Ok (d, p')) ->
  repr_data (bytes_from data pos) (translate_data d) (bytes_from data p')
  /\ data_ok env d.
Proof.
  intros data pos env d p' H. unfold module_decode_data_segment in H.
  destruct (reader_read_u32_leb data pos) as [r|] eqn:Hidx; cbn [bind] in H;
    [|discriminate].
  destruct r as [[memory_idx p1]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (scalar_cast U32 Usize memory_idx) as [i|] eqn:Hcast0;
    cbn [bind] in H; [|discriminate].
  assert (Hi : to_Z i = to_Z memory_idx)
    by (unfold scalar_cast in Hcast0; apply mk_scalar_ok_to_Z in Hcast0;
        exact Hcast0).
  destruct (i s>= alloc_vec_Vec_len env.(module_Env_mem_types)) eqn:Hmr;
    [discriminate|].
  apply scalar_geb_false_lt in Hmr. rewrite vec_len_spec in Hmr.
  destruct (module_decode_const_expr data p1 env Types_ValueType_I32)
    as [r1|] eqn:Hoff; cbn [bind] in H; [|discriminate].
  destruct r1 as [[offset p2]|e1]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (reader_read_u32_leb data p2) as [r2|] eqn:Hlen; cbn [bind] in H;
    [|discriminate].
  destruct r2 as [[len p3]|e2]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (scalar_cast U32 Usize len) as [n|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  destruct (module_have_bytes data p3 n) as [r3|]; cbn [bind] in H;
    [|discriminate].
  destruct r3 as [[]|e3]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (usize_add p3 n) as [p4|] eqn:Hadd; cbn [bind] in H;
    [|discriminate].
  destruct (module_copy_bytes data p3 p4) as [init|] eqn:Hcopy;
    cbn [bind] in H; [|discriminate].
  injection H as <- <-.
  assert (Hn : to_Z n = to_Z len)
    by (unfold scalar_cast in Hcast; apply mk_scalar_ok_to_Z in Hcast;
        exact Hcast).
  pose proof (scalar_add_val _ _ _ (to_Z n) Hadd eq_refl) as Hp4.
  split.
  - unfold translate_data.
    cbn [module_Data_memory_idx module_Data_offset module_Data_init].
    apply repr_data_intro with (p1 := bytes_from data p1)
                               (p2 := bytes_from data p2).
    + apply repr_idx_intro. apply (read_u32_leb_sound _ _ _ _ Hidx).
    + apply (decode_const_expr_sound _ _ _ _ _ _ Hoff).
    + apply repr_bytevec_intro with (zs := List.map to_Z (vec_list init)).
      * apply (decode_bytevec_sound data p2 p3 p4 len init);
          [ apply (read_u32_leb_sound _ _ _ _ Hlen) | exact Hcopy | lia ].
      * apply forall2_data_bytes.
  - split;
      [ cbn [module_Data_memory_idx]; lia
      | cbn [module_Data_offset];
        exact (decode_const_expr_typed _ _ _ _ _ _ Hoff) ].
Qed.

Lemma decode_data_section_loop_sound :
  forall m data env count out q i out' q',
  to_Z count - to_Z i <= Z.of_nat m ->
  module_decode_data_section_loop data env count out q i
    = Ok (Core_result_Result_Ok (out', q')) ->
  exists ds,
    vec_list out' = vec_list out ++ ds
    /\ repr_rep repr_data (Z.to_nat (to_Z count - to_Z i))
         (bytes_from data q) (List.map translate_data ds)
         (bytes_from data q')
    /\ List.Forall (data_ok env) ds.
Proof.
  induction m as [|m IH]; intros data env count out q i out' q' Hmeas H;
    unfold module_decode_data_section_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (i s>= count) eqn:Hge.
  1,3: injection H as <- <-; exists []; rewrite app_nil_r;
       split; [reflexivity|]; split; [| apply List.Forall_nil];
       apply scalar_geb_true_ge in Hge;
       rewrite to_nat_nonpos by lia; apply repr_rep_nil.
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (module_decode_data_segment data q env) as [r|] eqn:Hseg;
      cbn [bind] in H; [|discriminate].
    destruct r as [[seg q1]|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (alloc_vec_Vec_push out seg) as [out2|] eqn:Hpush;
      cbn [bind] in H; [|discriminate].
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in H;
      [|discriminate].
    pose proof (scalar_add_val _ _ _ 1 Hadd eq_refl) as Hi2.
    destruct (IH data env count out2 q1 i2 out' q'
                (ltac:(cbn in Hmeas; lia)) H) as [ds [Hlist [Hrep Hall]]].
    exists (seg :: ds). split; [|split].
    + rewrite Hlist. rewrite (vec_push_spec _ _ _ Hpush).
      rewrite <- app_assoc. reflexivity.
    + assert (Hcnt : to_Z count - to_Z i = (to_Z count - to_Z i2) + 1) by lia.
      rewrite Hcnt. rewrite Z_to_nat_add1 by lia.
      cbn [List.map]. eapply repr_rep_cons; [|exact Hrep].
      apply (proj1 (decode_data_segment_sound _ _ _ _ _ Hseg)).
    + apply List.Forall_cons;
        [exact (proj2 (decode_data_segment_sound _ _ _ _ _ Hseg)) | exact Hall].
Qed.

Lemma decode_data_section_sound : forall data pos env out q',
  module_decode_data_section data pos env
    = Ok (Core_result_Result_Ok (out, q')) ->
  repr_vec repr_data (bytes_from data pos)
    (List.map translate_data (vec_list out)) (bytes_from data q')
  /\ List.Forall (data_ok env) (vec_list out).
Proof.
  intros data pos env out q' H. unfold module_decode_data_section in H.
  destruct (reader_read_u32_leb data pos) as [r|] eqn:Hn; cbn [bind] in H;
    [|discriminate].
  destruct r as [[count p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (decode_data_section_loop_sound (Z.to_nat (to_Z count)) data env
              count (alloc_vec_Vec_new module_Data_t) p 0%u32 out q')
    as [ds [Hlist [Hrep Hall]]].
  - assert (H0 : to_Z 0%u32 = 0) by reflexivity.
    pose proof (u32_nonneg count). lia.
  - exact H.
  - assert (Hds : vec_list out = ds)
      by (rewrite Hlist;
          cbn [vec_list alloc_vec_Vec_new proj1_sig List.app]; reflexivity).
    split.
    + apply repr_vec_intro with (n := to_Z count) (mid := bytes_from data p).
      * apply (read_u32_leb_sound _ _ _ _ Hn).
      * rewrite Hds.
        assert (H0 : to_Z 0%u32 = 0) by reflexivity.
        rewrite H0 in Hrep. rewrite Z.sub_0_r in Hrep. exact Hrep.
    + rewrite Hds. exact Hall.
Qed.

(** Spec 5.5.16's last two lines: the data section with its run of custom
    sections, and the run of custom sections that closes the module. Before
    the data section the loop is inside the first; after it, the second. *)
Definition tail_chain (data : slice u8) (p : usize)
                      (segs : list module_data) : Prop :=
  exists mid,
    repr_padded 11 (repr_vec repr_data) [] (bytes_from data p) segs mid
    /\ repr_customs mid [].

Definition tail_after (data : slice u8) (p : usize) : Prop :=
  repr_customs (bytes_from data p) [].

Lemma tail_chain_custom : forall data p fin segs,
  repr_section 0 repr_custom (bytes_from data p) tt (bytes_from data fin) ->
  tail_chain data fin segs -> tail_chain data p segs.
Proof.
  intros data p fin segs Hs [mid [[m [Hc Ho]] Hend]].
  exists mid. split; [|exact Hend]. exists m. split; [|exact Ho].
  apply repr_customs_more with (mid := bytes_from data fin); assumption.
Qed.

Lemma tail_after_custom : forall data p fin,
  repr_section 0 repr_custom (bytes_from data p) tt (bytes_from data fin) ->
  tail_after data fin -> tail_after data p.
Proof.
  intros data p fin Hs Hc. unfold tail_after in *.
  apply repr_customs_more with (mid := bytes_from data fin); assumption.
Qed.

Lemma validate_tail_with_loop_sound :
  forall V (inst : module_ModuleVisitor_t V) m data env vis vis' segments q seen tail,
  Z.of_nat (List.length (vec_list data)) - to_Z q <= Z.of_nat m ->
  (seen = false -> vec_list segments = []) ->
  module_validate_tail_with_loop inst data env vis segments q seen
    = Ok (Core_result_Result_Ok tail, vis') ->
  (seen = false ->
     tail_chain data q (List.map translate_data
                          (vec_list tail.(module_Tail_data))))
  /\ (seen = true ->
        tail_after data q /\ tail.(module_Tail_data) = segments)
  /\ (List.Forall (data_ok env) (vec_list segments) ->
      List.Forall (data_ok env) (vec_list tail.(module_Tail_data))).
Proof.
  intros V inst m. induction m as [|m IH];
    intros data env vis vis' segments q seen tail Hmeas Hseg H;
    unfold module_validate_tail_with_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (q s>= slice_len data) eqn:Hge.
  1,3: injection H as <-;
       apply scalar_geb_true_ge in Hge; rewrite slice_len_spec in Hge;
       assert (Hnil : bytes_from data q = [])
         by (rewrite bytes_from_at; apply bytes_at_end; lia);
       split;
       [ intros Hs; cbn [module_Tail_data]; rewrite (Hseg Hs);
         cbn [List.map]; exists (bytes_from data q); split;
         [ exists (bytes_from data q); split;
           [ apply repr_customs_done; rewrite Hnil; intros [more Hm];
             discriminate
           | apply repr_optsec_absent; rewrite Hnil; intros [more Hm];
             discriminate ]
         | rewrite Hnil; apply repr_customs_done; intros [more Hm];
           discriminate ]
       | split;
         [ intros _; split; [|reflexivity]; unfold tail_after; rewrite Hnil;
           apply repr_customs_done; intros [more Hm]; discriminate
         | exact (fun Hd => Hd) ] ].
  - exfalso. apply scalar_geb_false_lt in Hge.
    rewrite slice_len_spec in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge. rewrite slice_len_spec in Hge.
    destruct (module_read_section_header data q) as [r|] eqn:Hhdr;
      cbn [bind] in H; [|discriminate].
    destruct r as [[[id start] fin]|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (read_section_header_step _ _ _ _ _ Hhdr) as [Hqs [Hsf Hfd]].
    rewrite slice_len_spec in Hfd.
    destruct (read_section_header_head _ _ _ _ _ Hhdr) as [rest Hhead].
    assert (Hmeas' : Z.of_nat (List.length (vec_list data)) - to_Z fin
                     <= Z.of_nat m) by (cbn in Hmeas; lia).
    destruct (id s= module_section_custom) eqn:Hcust.
    { pose proof (scalar_eqb_val _ _ 0 Hcust eq_refl) as Hid0.
      destruct (module_decode_custom_section data start fin) as [r1|] eqn:Hcs;
        cbn [bind] in H; [|discriminate].
      destruct r1 as [c|e1]; [|try_err_rw_in H; discriminate].
      rewrite branch_ok in H. cbn [bind] in H.
      destruct (inst.(module_ModuleVisitor_t_on_custom_section) vis c)
        as [[rh vis1]|] eqn:Hh; cbn [bind] in H; [|discriminate].
      destruct rh as [u|ev]; [|cbn beta iota in H; discriminate].
      cbn beta iota in H.
      assert (Hsec : repr_section 0 repr_custom (bytes_from data q) tt
                       (bytes_from data fin)).
      { rewrite <- Hid0.
        apply (read_section_header_sound _ _ _ _ _ _ _ _ Hhdr).
        apply (decode_custom_section_sound data start fin c);
          [exact Hcs | lia | lia]. }
      destruct (IH data env vis1 vis' segments fin seen tail Hmeas' Hseg H)
        as [Hf [Ht Hok]].
      split; [|split].
      - intros Hs. apply (tail_chain_custom _ _ fin); [exact Hsec|].
        apply Hf. exact Hs.
      - intros Hs. destruct (Ht Hs) as [Ha He]. split; [|exact He].
        apply (tail_after_custom _ _ fin); assumption.
      - exact Hok. }
    apply scalar_eqb_false in Hcust. cbn in Hcust.
    destruct (id s<> module_section_data) eqn:Hdat; [discriminate|].
    apply scalar_neqb_false in Hdat. cbn in Hdat.
    destruct seen; [discriminate|].
    destruct (module_decode_data_section data start env) as [r1|] eqn:Hds;
      cbn [bind] in H; [|discriminate].
    destruct r1 as [[decoded p]|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (p s<> fin) eqn:Hne; [discriminate|].
    apply scalar_neqb_false in Hne.
    destruct (IH data env vis vis' decoded fin true tail Hmeas'
                (ltac:(discriminate)) H) as [_ [Ht Hok]].
    destruct (Ht eq_refl) as [Ha He].
    split; [|split; [discriminate|]].
    2: { intros _. apply Hok.
         exact (proj2 (decode_data_section_sound _ _ _ _ _ Hds)). }
    intros _. exists (bytes_from data fin). split; [|exact Ha].
    exists (bytes_from data q). split.
    + apply repr_customs_done.
      apply (not_begins_of_head data q id rest 0 Hhead). lia.
    + rewrite He. rewrite <- Hdat.
      apply repr_optsec_present.
      apply (section_sound _ _ data q id start fin _
               (repr_vec_prefix _ _ repr_data_prefix) Hhdr).
      assert (Hpf : bytes_from data p = bytes_from data fin)
        by (apply bytes_at_congr; exact Hne).
      rewrite <- Hpf.
      apply (proj1 (decode_data_section_sound _ _ _ _ _ Hds)).
Qed.

Lemma validate_tail_sound : forall data pos env tail,
  module_validate_tail data pos env = Ok (Core_result_Result_Ok tail) ->
  tail_chain data pos
    (List.map translate_data (vec_list tail.(module_Tail_data)))
  /\ List.Forall (data_ok env) (vec_list tail.(module_Tail_data)).
Proof.
  intros data pos env tail H0. pose proof (validate_tail_nop_inv _ _ _ _ H0) as H.
  clear H0. unfold module_validate_tail_with in H.
  destruct (validate_tail_with_loop_sound _
              module_EmptyModuleVisitor_Insts_ItascaModuleModuleVisitor
              (List.length (vec_list data)) data env tt tt
              (alloc_vec_Vec_new module_Data_t) pos false tail)
    as [Hf [_ Hok]]; [ pose proof (usize_nonneg pos); lia
                     | intros _; reflexivity | exact H | ].
  split; [apply Hf; reflexivity|].
  apply Hok. cbn [vec_list alloc_vec_Vec_new proj1_sig]. apply List.Forall_nil.
Qed.

(* ================================================================== *)
(** ** 5.5.13 Code                                                     *)
(* ================================================================== *)

(** [locals ::= n:u32 t:valtype => t^n]: a group is a count and a type, and
    the decoder flattens it as it goes, so what it appends is the repeat. *)
Lemma map_repeat_vt : forall vt n,
  List.map translate_vt_v (List.repeat vt n)
    = List.repeat (translate_vt_v vt) n.
Proof.
  intros vt n. induction n as [|n IH]; cbn [List.repeat List.map];
    [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma push_locals_loop_sound : forall m out count vt i out',
  to_Z count - to_Z i <= Z.of_nat m ->
  0 <= to_Z i ->
  module_push_locals_loop out count vt i = Ok out' ->
  vec_list out' = vec_list out
                  ++ List.repeat vt (Z.to_nat (to_Z count - to_Z i)).
Proof.
  induction m as [|m IH]; intros out count vt i out' Hmeas Hi H;
    unfold module_push_locals_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (i s>= count) eqn:Hge.
  1,3: injection H as <-; apply scalar_geb_true_ge in Hge;
       rewrite to_nat_nonpos by lia; cbn [List.repeat];
       rewrite app_nil_r; reflexivity.
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (alloc_vec_Vec_push out vt) as [out2|] eqn:Hpush;
      cbn [bind] in H; [|discriminate].
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in H;
      [|discriminate].
    pose proof (scalar_add_val _ _ _ 1 Hadd eq_refl) as Hi2.
    rewrite (IH out2 count vt i2 out' (ltac:(cbn in Hmeas; lia))
               (ltac:(lia)) H).
    rewrite (vec_push_spec _ _ _ Hpush). rewrite <- app_assoc.
    assert (Hcnt : to_Z count - to_Z i = 1 + (to_Z count - to_Z i2)) by lia.
    rewrite Hcnt. rewrite Z2Nat.inj_add by lia. reflexivity.
Qed.

Lemma push_locals_sound : forall out count vt out',
  module_push_locals out count vt = Ok out' ->
  vec_list out' = vec_list out ++ List.repeat vt (Z.to_nat (to_Z count)).
Proof.
  intros out count vt out' H. unfold module_push_locals in H.
  assert (H0 : to_Z 0%u32 = 0) by reflexivity.
  pose proof (push_locals_loop_sound (Z.to_nat (to_Z count)) out count vt
                0%u32 out'
                (ltac:(rewrite Z2Nat.id by apply u32_nonneg; lia))
                (ltac:(lia)) H) as Hr.
  rewrite H0 in Hr. rewrite Z.sub_0_r in Hr. exact Hr.
Qed.

Lemma decode_locals_loop_sound : forall m data groups out q i out' q',
  to_Z groups - to_Z i <= Z.of_nat m ->
  module_decode_locals_loop data groups out q i
    = Ok (Core_result_Result_Ok (out', q')) ->
  exists gs,
    vec_list out' = vec_list out ++ List.concat gs
    /\ repr_rep repr_locals (Z.to_nat (to_Z groups - to_Z i))
         (bytes_from data q) (List.map (List.map translate_vt_v) gs)
         (bytes_from data q').
Proof.
  induction m as [|m IH]; intros data groups out q i out' q' Hmeas H;
    unfold module_decode_locals_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (i s>= groups) eqn:Hge.
  1,3: injection H as <- <-; exists []; cbn [List.concat List.map];
       rewrite app_nil_r; split; [reflexivity|];
       apply scalar_geb_true_ge in Hge;
       rewrite to_nat_nonpos by lia; apply repr_rep_nil.
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (reader_read_u32_leb data q) as [r|] eqn:Hcount;
      cbn [bind] in H; [|discriminate].
    destruct r as [[count q1]|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (module_decode_value_type data q1) as [r1|] eqn:Hvt;
      cbn [bind] in H; [|discriminate].
    destruct r1 as [[vt q2]|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (scalar_cast U32 Usize count) as [n|]; cbn [bind] in H;
      [|discriminate].
    destruct (usize_sub limits_max_locals (alloc_vec_Vec_len out)) as [room|];
      cbn [bind] in H; [|discriminate].
    destruct (n s> room); [discriminate|].
    destruct (module_push_locals out count vt) as [out2|] eqn:Hpush;
      cbn [bind] in H; [|discriminate].
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in H;
      [|discriminate].
    pose proof (scalar_add_val _ _ _ 1 Hadd eq_refl) as Hi2.
    destruct (IH data groups out2 q2 i2 out' q'
                (ltac:(cbn in Hmeas; lia)) H) as [gs [Hlist Hrep]].
    exists (List.repeat vt (Z.to_nat (to_Z count)) :: gs). split.
    + rewrite Hlist. rewrite (push_locals_sound _ _ _ _ Hpush).
      cbn [List.concat]. rewrite <- app_assoc. reflexivity.
    + assert (Hcnt : to_Z groups - to_Z i = (to_Z groups - to_Z i2) + 1)
        by lia.
      rewrite Hcnt. rewrite Z_to_nat_add1 by lia.
      cbn [List.map]. eapply repr_rep_cons; [|exact Hrep].
      rewrite map_repeat_vt.
      apply repr_locals_intro with (n := to_Z count)
                                   (p1 := bytes_from data q1).
      * apply (read_u32_leb_sound _ _ _ _ Hcount).
      * apply (decode_value_type_sound _ _ _ _ Hvt).
Qed.

Lemma decode_locals_sound : forall data pos out q',
  module_decode_locals data pos = Ok (Core_result_Result_Ok (out, q')) ->
  exists gs,
    List.map translate_vt_v (vec_list out) = List.concat gs
    /\ repr_vec repr_locals (bytes_from data pos) gs (bytes_from data q').
Proof.
  intros data pos out q' H. unfold module_decode_locals in H.
  destruct (reader_read_u32_leb data pos) as [r|] eqn:Hn; cbn [bind] in H;
    [|discriminate].
  destruct r as [[groups p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (decode_locals_loop_sound (Z.to_nat (to_Z groups)) data groups
              (alloc_vec_Vec_new types_ValueType_t) p 0%u32 out q')
    as [gs [Hlist Hrep]].
  - assert (H0 : to_Z 0%u32 = 0) by reflexivity.
    pose proof (u32_nonneg groups). lia.
  - exact H.
  - exists (List.map (List.map translate_vt_v) gs). split.
    + rewrite Hlist.
      cbn [vec_list alloc_vec_Vec_new proj1_sig List.app].
      apply List.concat_map.
    + apply repr_vec_intro with (n := to_Z groups) (mid := bytes_from data p).
      * apply (read_u32_leb_sound _ _ _ _ Hn).
      * assert (H0 : to_Z 0%u32 = 0) by reflexivity.
        rewrite H0 in Hrep. rewrite Z.sub_0_r in Hrep. exact Hrep.
Qed.

(** The context [validate_body] is proven against, built from the environment
    and the entry's own signature. The four fields the agreement clauses say
    nothing about are the ones the body validator never reads: Wasm 1.0 has no
    instruction that consults [tc_elems], [tc_datas] or [tc_refs], and
    [tc_labels] is what [validate_body_sound] adds for itself. They are
    parameters here so that the module's own context can supply them when the
    two are matched up. *)
Definition body_context (elems : list reference_type) (datas : list ok)
                        (refs : list funcidx)
                        (env : module_Env_t) (ctx : code_Context_t)
  : t_context :=
  {| tc_types := List.map translate_ft (vec_list env.(module_Env_types));
     tc_funcs := List.map translate_ft (vec_list env.(module_Env_func_types));
     tc_tables :=
       List.map translate_tabletype (vec_list env.(module_Env_table_types));
     tc_mems := List.map translate_memtype (vec_list env.(module_Env_mem_types));
     tc_globals :=
       List.map translate_globaltype (vec_list env.(module_Env_global_types));
     tc_elems := elems;
     tc_datas := datas;
     tc_locals :=
       List.map translate_vt_v (vec_list ctx.(code_Context_locals));
     tc_labels := [];
     tc_return :=
       Some (translate_typelist (vec_list ctx.(code_Context_results)));
     tc_refs := refs |}.

(** All seven agreement clauses, by construction. This is the join between the
    module proof and the body proof: [validate_body_sound] takes them as
    hypotheses, and the module validator is what makes them true. *)
Lemma body_context_agrees : forall elems datas refs env ctx,
  let C0 := body_context elems datas refs env ctx in
  mems_agree env C0 /\ locals_agree ctx C0 /\ globals_agree env C0
  /\ return_agree ctx C0 /\ funcs_agree env C0 /\ types_agree env C0
  /\ tables_agree env C0.
Proof.
  intros elems datas refs env ctx C0. unfold C0, body_context.
  unfold mems_agree, locals_agree, globals_agree, return_agree,
         funcs_agree, types_agree, tables_agree.
  cbn [tc_mems tc_locals tc_globals tc_return tc_funcs tc_types tc_tables].
  repeat split.
Qed.


(** The body's own bytes, as the format sees them. This is the one place the
    decoder takes a sub-slice, and it is where [validate_body]'s conclusion
    becomes an expression inside the code entry. *)
Lemma byte_list_sub : forall data (p q : usize) sub,
  to_Z p <= to_Z q ->
  to_Z q <= Z.of_nat (List.length (vec_list data)) ->
  core_slice_index_Slice_index
    (core_slice_index_SliceIndexRangeUsizeSliceInst u8) data
    {| core_ops_range_Range_start := p; core_ops_range_Range_end_ := q |}
    = Ok sub ->
  byte_list sub = section_content data p q.
Proof.
  intros data p q sub Hpq Hq H.
  destruct (slice_range_ok data p q Hpq Hq) as [sub' [Hcall Hlist]].
  rewrite Hcall in H. injection H as <-.
  unfold byte_list, section_content, bytes_from, byte_list.
  rewrite Hlist. rewrite List.skipn_map. rewrite List.firstn_map. reflexivity.
Qed.

(** Spec 5.5.13: [code ::= size:u32 code:func]. The size prefix is framed the
    way a section's is, so a code entry cannot be read past its own end
    either, and the body's sub-slice is exactly what is left of the frame once
    the locals have been read.

    The hypothesis is the Wasm 1.0 restriction to at most one result, which
    [validate_body_sound] needs and [decode_func_type] enforces. It is a
    property of the environment rather than of this entry, so it is carried in
    from the type section. *)
(** [build_func_locals] copies the signature's parameters and then appends the
    body's declared locals, which is the [tn ++ t_locs] the type system puts
    in front of a function's locals. *)
Lemma build_func_locals_loop_sound : forall m declared locals i out,
  Z.of_nat (List.length (vec_list declared)) - to_Z i <= Z.of_nat m ->
  0 <= to_Z i ->
  module_build_func_locals_loop declared locals i = Ok out ->
  vec_list out
    = vec_list locals ++ List.skipn (Z.to_nat (to_Z i)) (vec_list declared).
Proof.
  induction m as [|m IH]; intros declared locals i out Hmeas Hi H;
    unfold module_build_func_locals_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (i s>= slice_len declared) eqn:Hge.
  1,3: injection H as <-; apply scalar_geb_true_ge in Hge;
       rewrite slice_len_spec in Hge;
       rewrite List.skipn_all2 by (apply Nat2Z.inj_le;
         rewrite Z2Nat.id by lia; lia);
       rewrite app_nil_r; reflexivity.
  1: { exfalso. apply scalar_geb_false_lt in Hge.
       rewrite slice_len_spec in Hge. lia. }
  apply scalar_geb_false_lt in Hge. rewrite slice_len_spec in Hge.
  destruct (slice_index_usize declared i) as [vt|] eqn:Hvt; cbn [bind] in H;
    [|discriminate].
  destruct (alloc_vec_Vec_push locals vt) as [locals2|] eqn:Hpush;
    cbn [bind] in H; [|discriminate].
  destruct (usize_add_1_ok i (usize_add_1_lt_max i declared
              (ltac:(destruct (i s>= slice_len declared) eqn:E;
                     [apply scalar_geb_true_ge in E;
                      rewrite slice_len_spec in E; lia | reflexivity]))))
    as [i2 [Hadd Hi2]].
  rewrite Hadd in H. cbn [bind] in H.
  rewrite (IH declared locals2 i2 out (ltac:(lia)) (ltac:(lia)) H).
  rewrite (vec_push_spec _ _ _ Hpush). rewrite <- app_assoc.
  rewrite slice_index_usize_spec in Hvt.
  destruct (List.nth_error (vec_list declared) (Z.to_nat (to_Z i)))
    as [x|] eqn:Hnth; [|discriminate].
  injection Hvt as <-.
  rewrite (skipn_nth_error _ _ _ Hnth).
  rewrite Hi2. rewrite Z_to_nat_add1 by lia. reflexivity.
Qed.

Lemma build_func_locals_sound : forall params declared out,
  module_build_func_locals params declared = Ok out ->
  vec_list out = vec_list params ++ vec_list declared.
Proof.
  intros params declared out H. unfold module_build_func_locals in H.
  destruct (module_copy_value_types params) as [locals|] eqn:Hc;
    cbn [bind] in H; [|discriminate].
  rewrite (build_func_locals_loop_sound
             (List.length (vec_list declared)) declared locals 0%usize out
             (ltac:(assert (H0 : to_Z 0%usize = 0) by reflexivity; lia))
             (ltac:(assert (H0 : to_Z 0%usize = 0) by reflexivity; lia)) H).
  rewrite (copy_value_types_sound _ _ Hc).
  assert (H0 : to_Z 0%usize = 0) by reflexivity. rewrite H0.
  cbn [Z.to_nat List.skipn]. reflexivity.
Qed.

(** The context a code entry's body is checked in, which is the module's own
    context with the signature's parameters in front of the declared locals,
    one label, and the result type as the return. This is
    [module_func_type_checker]'s [c'] written out. *)
Definition func_body_context (elems : list reference_type) (datas : list ok)
                             (refs : list funcidx) (env : module_Env_t)
                             (ft : types_FuncType_t)
                             (t_locs : list value_type) : t_context :=
  {| tc_types := List.map translate_functype (vec_list env.(module_Env_types));
     tc_funcs :=
       List.map translate_functype (vec_list env.(module_Env_func_types));
     tc_tables :=
       List.map translate_tabletype (vec_list env.(module_Env_table_types));
     tc_mems := List.map translate_memtype (vec_list env.(module_Env_mem_types));
     tc_globals :=
       List.map translate_globaltype (vec_list env.(module_Env_global_types));
     tc_elems := elems;
     tc_datas := datas;
     tc_locals :=
       List.map translate_vt_v (vec_list ft.(types_FuncType_params)) ++ t_locs;
     tc_labels :=
       [List.map translate_vt_v (vec_list ft.(types_FuncType_results))];
     tc_return :=
       Some (List.map translate_vt_v (vec_list ft.(types_FuncType_results)));
     tc_refs := refs |}.

Lemma rev_tf_translate_ft : forall ft,
  rev_tf (translate_ft ft) = translate_functype ft.
Proof.
  intros ft. unfold rev_tf, translate_ft, translate_functype,
                    translate_typelist.
  rewrite seq.revK. rewrite seq.revK. reflexivity.
Qed.

(** A code entry is well typed when the type its index names is the one its
    body checks against. This is [module_func_type_checker]'s content, in the
    extraction's terms. *)
Definition code_typed (env : module_Env_t) (tidx : scalar U32)
                      (c : list value_type * expr) : Prop :=
  exists ft,
    List.nth_error (vec_list env.(module_Env_types))
                   (Z.to_nat (to_Z tidx)) = Some ft
    /\ (exists ds, fst c = List.map translate_vt_v ds)
    /\ forall elems datas refs,
         b_e_type_checker (func_body_context elems datas refs env ft (fst c))
           (snd c)
           (Tf [] (List.map translate_vt_v
                     (vec_list ft.(types_FuncType_results)))) = true.

Lemma validate_code_entry_with_sound : forall V (inst : code_OpVisitor_t V)
                                             vis vis' data pos env index end',
  (forall ft, List.In ft (vec_list env.(module_Env_types)) ->
     (List.length (vec_list ft.(types_FuncType_results)) <= 1)%nat) ->
  module_validate_code_entry_with inst data pos env index vis
    = Ok (Core_result_Result_Ok end', vis') ->
  exists c ops,
    repr_code (bytes_from data pos) c (bytes_from data end')
    (* and the consumer was shown exactly the body's operators: the frame hook
       is not one, and the body's loop is the one the trace theorem is about *)
    /\ else_sugar (flat_of (snd c) ++ [FO_end]) ops
    /\ traced inst vis vis' ops
    /\ exists tidx,
         List.nth_error (vec_list env.(module_Env_func_type_indices))
                        (Z.to_nat (to_Z index)) = Some tidx
         /\ code_typed env tidx c.
Proof.
  intros V inst vis vis' data pos env index end' Hres H.
  unfold module_validate_code_entry_with in H.
  destruct (index s>= alloc_vec_Vec_len env.(module_Env_func_type_indices));
    [discriminate|].
  destruct (reader_read_u32_leb data pos) as [r|] eqn:Hsz; cbn [bind] in H;
    [|discriminate].
  destruct r as [[size p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (scalar_cast U32 Usize size) as [n|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  destruct (module_have_bytes data p n) as [r1|] eqn:Hh; cbn [bind] in H;
    [|discriminate].
  destruct r1 as [[]|e1]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (usize_add p n) as [end1|] eqn:Hadd; cbn [bind] in H;
    [|discriminate].
  destruct (module_decode_locals data p) as [r2|] eqn:Hdl; cbn [bind] in H;
    [|discriminate].
  destruct r2 as [[declared p1]|e2]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (p1 s> end1) eqn:Hgt; [discriminate|].
  apply scalar_gtb_false in Hgt.
  assert (Hn : to_Z n = to_Z size)
    by (unfold scalar_cast in Hcast; apply mk_scalar_ok_to_Z in Hcast;
        exact Hcast).
  pose proof (scalar_add_val _ _ _ (to_Z n) Hadd eq_refl) as Hend1.
  pose proof (have_bytes_room _ _ _ Hh) as Hroom.
  rewrite slice_len_spec in Hroom.
  pose proof (usize_nonneg n).
  (* the locals were read inside the frame *)
  destruct (decode_locals_ok data p (ltac:(rewrite slice_len_spec; lia)))
    as [r0 [Hr0 Hpost]].
  rewrite Hdl in Hr0. injection Hr0 as <-.
  destruct (Hpost declared p1 eq_refl) as [Hpp1 _].
  destruct (decode_locals_sound _ _ _ _ Hdl) as [gs [Hflat Hlocals]].
  (* the entry's signature *)
  destruct (alloc_vec_Vec_index
              (core_slice_index_SliceIndexUsizeSliceInst Primitives.u32)
              env.(module_Env_func_type_indices) index) as [type_idx|] eqn:Htyi;
    cbn [bind] in H; [|discriminate].
  rewrite vec_index_spec in Htyi.
  destruct (List.nth_error (vec_list env.(module_Env_func_type_indices))
              (Z.to_nat (to_Z index))) as [tidx|] eqn:Hnthi; [|discriminate].
  injection Htyi as <-.
  destruct (scalar_cast U32 Usize tidx) as [t|] eqn:Hcast2;
    cbn [bind] in H; [|discriminate].
  assert (Ht : to_Z t = to_Z tidx)
    by (unfold scalar_cast in Hcast2; apply mk_scalar_ok_to_Z in Hcast2;
        exact Hcast2).
  destruct (t s>= alloc_vec_Vec_len env.(module_Env_types)); [discriminate|].
  destruct (alloc_vec_Vec_index
              (core_slice_index_SliceIndexUsizeSliceInst types_FuncType_t)
              env.(module_Env_types) t) as [ft|] eqn:Hft; cbn [bind] in H;
    [|discriminate].
  rewrite vec_deref_spec in H. rewrite vec_deref_spec in H.
  destruct (module_build_func_locals ft.(types_FuncType_params) declared)
    as [locals|] eqn:Hbl; cbn [bind] in H; [|discriminate].
  rewrite vec_deref_spec in H.
  destruct (module_copy_value_types ft.(types_FuncType_results))
    as [results|] eqn:Hcopy; cbn [bind] in H; [|discriminate].
  (* the frame hook comes first, and the run got past it, so the consumer
     accepted the frame *)
  destruct (inst.(code_OpVisitor_t_on_function_start) vis
              {| code_Context_locals := locals;
                 code_Context_results := results |} tidx)
    as [[rh vh]|] eqn:Hhk; cbn [bind] in H; [|discriminate].
  destruct rh as [uh|eh]; cbn beta iota in H; [|discriminate].
  destruct uh.
  destruct (core_slice_index_Slice_index
              (core_slice_index_SliceIndexRangeUsizeSliceInst u8) data
              {| core_ops_range_Range_start := p1;
                 core_ops_range_Range_end_ := end1 |}) as [sub|] eqn:Hsub;
    cbn [bind] in H; [|discriminate].
  destruct (code_validate_body_with inst sub env
              {| code_Context_locals := locals;
                 code_Context_results := results |} vh) as [[r3 v3]|] eqn:Hvb;
    cbn [bind] in H; [|discriminate].
  destruct r3 as [u|e3]; [|discriminate]. destruct u.
  injection H as <- <-.
  (* the body's expression *)
  assert (Hlen1 : (List.length (vec_list results) <= 1)%nat).
  { rewrite (copy_value_types_sound _ _ Hcopy). apply Hres.
    rewrite vec_index_spec in Hft.
    destruct (List.nth_error (vec_list env.(module_Env_types))
                (Z.to_nat (to_Z t))) as [x|] eqn:Hnth; [|discriminate].
    injection Hft as <-. apply (List.nth_error_In _ _ Hnth). }
  destruct (body_context_agrees [] [] [] env
              {| code_Context_locals := locals;
                 code_Context_results := results |})
    as [Hm [Hl [Hg [Hr [Hf [Htt Htb]]]]]].
  destruct (validate_body_with_checker V inst vh v3
              _ env _ sub Hm Hl Hg Hr Hf Htt Htb Hlen1 Hvb)
    as [es [Hexpr _]].
  (* the same run, read for its trace: the operator list is the body's *)
  destruct (validate_body_with_trace V inst vh v3
              _ env _ sub Hm Hl Hg Hr Hf Htt Htb Hlen1 Hvb)
    as [es0 [ops [Hexpr0 [Hsug0 [_ Htr0]]]]].
  rewrite (repr_expr_det _ _ _ Hexpr0 Hexpr) in Hsug0.
  pose proof (traced_trans V inst vis vh v3 [] ops
                (traced_frame V inst vis vh _ tidx _ _ Hhk) Htr0) as Htrall.
  cbn [List.app] in Htrall.
  rewrite (byte_list_sub data p1 end1 sub (ltac:(lia)) (ltac:(lia)) Hsub)
    in Hexpr.
  (* and the frame the size prefix declared *)
  assert (Hsplit : bytes_from data p
                   = section_content data p end1 ++ bytes_from data end1).
  { unfold section_content.
    rewrite (bytes_from_skipn data p end1 (Z.to_nat (to_Z end1 - to_Z p)))
      by (rewrite Z2Nat.id; lia).
    symmetry. apply List.firstn_skipn. }
  assert (Hfits : (Z.to_nat (to_Z end1 - to_Z p)
                     <= List.length (bytes_from data p))%nat)
    by (apply bytes_from_length_ge; lia).
  exists (List.concat gs, es), ops. split.
  - apply repr_code_intro with (size := to_Z size)
                               (content := section_content data p end1).
    + rewrite <- Hsplit. apply (read_u32_leb_sound _ _ _ _ Hsz).
    + unfold section_content. rewrite List.firstn_length_le by exact Hfits.
      rewrite Z2Nat.id; lia.
    + apply repr_func_intro with (p1 := section_content data p1 end1).
      * apply (section_contents_within _ (repr_vec repr_locals) data p p1 end1);
          [ apply repr_vec_prefix; apply repr_locals_prefix
          | exact Hlocals | lia | lia ].
      * exact Hexpr.
  - split; [cbn [snd]; exact Hsug0|]. split; [exact Htrall|].
    (* the entry's signature, and the body checked against it *)
    rewrite vec_index_spec in Hft.
    destruct (List.nth_error (vec_list env.(module_Env_types))
                (Z.to_nat (to_Z t))) as [ft0|] eqn:Hnthf; [|discriminate].
    injection Hft as <-.
    exists tidx. split; [reflexivity|]. exists ft0.
    split; [rewrite <- Ht; exact Hnthf|].
    split; [cbn [fst]; exists (vec_list declared); symmetry; exact Hflat|].
    intros elems datas refs.
    destruct (body_context_agrees elems datas refs env
                {| code_Context_locals := locals;
                   code_Context_results := results |})
      as [Hm' [Hl' [Hg' [Hr' [Hf' [Htt' Htb']]]]]].
    destruct (validate_body_with_checker V inst vh v3
                _ env _ sub Hm' Hl' Hg' Hr' Hf' Htt' Htb'
                Hlen1 Hvb) as [es' [Hexpr' Hchk]].
    rewrite (byte_list_sub data p1 end1 sub (ltac:(lia)) (ltac:(lia)) Hsub)
      in Hexpr'.
    rewrite <- (repr_expr_det _ _ _ Hexpr' Hexpr).
    cbn [fst snd].
    (* the two contexts are the same record *)
    assert (Hres' : List.map translate_vt_v (vec_list results)
                    = List.map translate_vt_v
                        (vec_list ft0.(types_FuncType_results)))
      by (rewrite (copy_value_types_sound _ _ Hcopy); reflexivity).
    assert (Hctx : func_body_context elems datas refs env ft0
                     (List.concat gs)
                   = context_reverse
                       (upd_label
                          (body_context elems datas refs env
                             {| code_Context_locals := locals;
                                code_Context_results := results |})
                          [translate_typelist (vec_list results)])).
    { unfold func_body_context, context_reverse, upd_label,
             upd_local_label_return, body_context.
      cbn [tc_types tc_funcs tc_tables tc_mems tc_globals tc_elems tc_datas
           tc_locals tc_labels tc_return tc_refs
           code_Context_locals code_Context_results].
      assert (Hrv : forall l, seq.map rev_tf (List.map translate_ft l)
                              = List.map translate_functype l).
      { intros l. induction l as [|x l IH]; [reflexivity|].
        cbn [List.map seq.map]. rewrite IH. rewrite rev_tf_translate_ft.
        reflexivity. }
      rewrite Hrv. rewrite Hrv.
      rewrite (build_func_locals_sound _ _ _ Hbl).
      rewrite List.map_app. rewrite <- Hflat.
      unfold translate_typelist. cbn [List.map seq.map option_map].
      rewrite seq.revK.
      rewrite (copy_value_types_sound _ _ Hcopy).
      reflexivity. }
    rewrite Hctx. rewrite <- Hres'. exact Hchk.
Qed.

(** The same for the validating-only consumer, which is what [validate_code]
    drives. *)
Corollary validate_code_entry_sound : forall data pos env index end',
  (forall ft, List.In ft (vec_list env.(module_Env_types)) ->
     (List.length (vec_list ft.(types_FuncType_results)) <= 1)%nat) ->
  module_validate_code_entry data pos env index
    = Ok (Core_result_Result_Ok end') ->
  exists c,
    repr_code (bytes_from data pos) c (bytes_from data end')
    /\ exists tidx,
         List.nth_error (vec_list env.(module_Env_func_type_indices))
                        (Z.to_nat (to_Z index)) = Some tidx
         /\ code_typed env tidx c.
Proof.
  intros data pos env index end' Hres H.
  destruct (validate_code_entry_with_sound _
              code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor tt tt data pos env
              index end' Hres (ltac:(apply code_entry_nop_inv; exact H)))
    as [c [ops [Hc [_ [_ Hty]]]]].
  exists c. split; [exact Hc | exact Hty].
Qed.

Lemma repr_rep_length : forall A (R : list Z -> A -> list Z -> Prop) n bs xs rest,
  repr_rep R n bs xs rest -> List.length xs = n.
Proof.
  intros A R n bs xs rest H. induction H as [|n bs x mid xs rest Hx Hrec IH];
    [reflexivity | cbn [List.length]; rewrite IH; reflexivity].
Qed.

(** Spec 5.5.16 pairs the function section's type indices with the code
    section's entries, which is a pairing rather than a check: the two have
    the same length, and [funcs_of] walks them together. *)
Lemma funcs_of_exists : forall xs cs,
  List.length xs = List.length cs -> exists fs, funcs_of xs cs fs.
Proof.
  induction xs as [|x xs IH]; intros cs Hlen.
  - destruct cs; [exists []; apply funcs_of_nil | discriminate].
  - destruct cs as [|[lcls e] cs]; [discriminate|].
    cbn [List.length] in Hlen. injection Hlen as Hlen.
    destruct (IH cs Hlen) as [fs Hfs].
    eexists. apply funcs_of_cons. exact Hfs.
Qed.

(** The framing step and the validator agree on where an entry ends.
    Both read the same size prefix at the same position and add the same length
    to it, so this is one equality and not an argument: the two functions share
    their first four steps and [usize_add] is a function.

    This is what makes a driven walk sound. The walk moves its cursor by the
    extent, before anything has validated the entry; the entry is validated
    later, possibly on another thread, and reports its own end. Without this
    the two could be different positions and the chain of entries would not be
    the chain [validate_code] walks. *)
Lemma code_entry_extent_frames : forall data pos env index contents fin q',
  module_code_entry_extent data pos
    = Ok (Core_result_Result_Ok (contents, fin)) ->
  module_validate_code_entry data pos env index
    = Ok (Core_result_Result_Ok q') ->
  to_Z q' = to_Z fin.
Proof.
  intros data pos env index contents fin q' Hx Hv.
  apply code_entry_nop_inv in Hv.
  unfold module_code_entry_extent in Hx.
  unfold module_validate_code_entry_with in Hv.
  destruct (index s>= alloc_vec_Vec_len env.(module_Env_func_type_indices));
    [discriminate|].
  destruct (reader_read_u32_leb data pos) as [r|] eqn:Hr;
    cbn [bind] in Hx, Hv; [|discriminate].
  destruct r as [[size p]|e]; [|try_err_rw_in Hx; discriminate].
  rewrite branch_ok in Hx, Hv. cbn [bind] in Hx, Hv.
  destruct (scalar_cast U32 Usize size) as [n|] eqn:Hcast;
    cbn [bind] in Hx, Hv; [|discriminate].
  destruct (module_have_bytes data p n) as [rh|] eqn:Hh;
    cbn [bind] in Hx, Hv; [|discriminate].
  destruct rh as [u|eh]; [|try_err_rw_in Hx; discriminate].
  rewrite branch_ok in Hx, Hv. cbn [bind] in Hx, Hv.
  destruct (usize_add p n) as [e1|] eqn:Hadd; cbn [bind] in Hx, Hv;
    [|discriminate].
  (* the extent is that [e1]; so is the only answer the validator can accept
     with, whatever it does in between *)
  injection Hx as _ <-.
  repeat (match type of Hv with
          (* a [?]: split the Result before the branch, so the error arm is a
             literal [Err] and rewrites away *)
          | bind (core_result_Result_Insts_CoreOpsTry_traitTryTResultInfallibleE_branch ?r) _ = _ =>
              destruct r as [?|?];
              [ rewrite branch_ok in Hv; cbn [bind] in Hv
              | try_err_rw_in Hv; discriminate ]
          | bind ?x _ = _ =>
              destruct x eqn:?; cbn [bind] in Hv; try discriminate
          | (match ?x with _ => _ end) = _ =>
              destruct x eqn:?; cbn [bind] in Hv; try discriminate
          | (if ?b then _ else _) = _ =>
              destruct b eqn:?; cbn [bind] in Hv; try discriminate
          end).
  all: injection Hv; intros; subst; reflexivity.
Qed.

(** The converse framing fact: an entry the validator accepted is one the
    framing step frames, ending where the validator said. Same shared prefix,
    read the other way round, and what completeness needs to know the walk
    gets as far as the hook. *)
Lemma code_entry_extent_of_valid : forall data pos env index q',
  module_validate_code_entry data pos env index
    = Ok (Core_result_Result_Ok q') ->
  exists contents,
    module_code_entry_extent data pos
      = Ok (Core_result_Result_Ok (contents, q')).
Proof.
  intros data pos env index q' Hv.
  apply code_entry_nop_inv in Hv.
  unfold module_validate_code_entry_with in Hv.
  unfold module_code_entry_extent.
  destruct (index s>= alloc_vec_Vec_len env.(module_Env_func_type_indices));
    [discriminate|].
  destruct (reader_read_u32_leb data pos) as [r|] eqn:Hr;
    cbn [bind] in Hv |- *; [|discriminate].
  destruct r as [[size p]|e]; [|try_err_rw_in Hv; discriminate].
  rewrite branch_ok in Hv |- *. cbn [bind] in Hv |- *.
  destruct (scalar_cast U32 Usize size) as [n|] eqn:Hcast;
    cbn [bind] in Hv |- *; [|discriminate].
  destruct (module_have_bytes data p n) as [rh|] eqn:Hh;
    cbn [bind] in Hv |- *; [|discriminate].
  destruct rh as [u|eh]; [|try_err_rw_in Hv; discriminate].
  rewrite branch_ok in Hv |- *. cbn [bind] in Hv |- *.
  destruct (usize_add p n) as [e1|] eqn:Hadd; cbn [bind] in Hv |- *;
    [|discriminate].
  exists p. f_equal. f_equal. f_equal.
  repeat (match type of Hv with
          | bind (core_result_Result_Insts_CoreOpsTry_traitTryTResultInfallibleE_branch ?r) _ = _ =>
              destruct r as [?|?];
              [ rewrite branch_ok in Hv; cbn [bind] in Hv
              | try_err_rw_in Hv; discriminate ]
          | bind ?x _ = _ =>
              destruct x eqn:?; cbn [bind] in Hv; try discriminate
          | (match ?x with _ => _ end) = _ =>
              destruct x eqn:?; cbn [bind] in Hv; try discriminate
          | (if ?b then _ else _) = _ =>
              destruct b eqn:?; cbn [bind] in Hv; try discriminate
          end).
  all: injection Hv; intros; subst; reflexivity.
Qed.

(** What a consumer that takes [on_code_entry] owes: the entry it accepted is
    one [validate_code_entry] accepts, at the position and index it was handed.
    That function is pure in those, so this says nothing about when or on which
    thread the consumer did it. *)
Definition code_hooks_validate {V : Type} (inst : module_CodeVisitor_t V)
                               (data : slice u8) (env : module_Env_t) : Prop :=
  forall v v' index pos contents fin,
    inst.(module_CodeVisitor_t_on_code_entry) v data env index pos contents fin
      = Ok (Core_result_Result_Ok tt, v') ->
    exists q', module_validate_code_entry data pos env index
                 = Ok (Core_result_Result_Ok q').

Lemma validating_code_hooks_validate : forall data env,
  code_hooks_validate
    module_ValidatingCodeVisitor_Insts_ItascaModuleCodeVisitor data env.
Proof.
  intros data env v v' index pos contents fin H.
  unfold module_ValidatingCodeVisitor_Insts_ItascaModuleCodeVisitor in H.
  cbn [module_CodeVisitor_t_on_code_entry] in H.
  unfold module_ValidatingCodeVisitor_Insts_ItascaModuleCodeVisitor_on_code_entry
    in H.
  destruct (module_validate_code_entry data pos env index) as [r|] eqn:Hr;
    cbn [bind] in H; [|discriminate].
  destruct r as [q'|e]; [|try_err_rw_in H; discriminate].
  exists q'. reflexivity.
Qed.

(** [bytes_from] reads its position only through [to_Z], so two positions that
    agree there leave the same stream. What turns [code_entry_extent_frames]
    into a fact about the bytes the walk goes on to read. *)
Lemma bytes_from_to_Z : forall data (p q : usize),
  to_Z p = to_Z q -> bytes_from data p = bytes_from data q.
Proof. intros data p q H. unfold bytes_from. rewrite H. reflexivity. Qed.

Lemma validate_code_entries_with_loop_sound :
  forall V (inst : module_CodeVisitor_t V) m data env vis vis' q i q',
  code_hooks_validate inst data env ->
  Z.of_nat (List.length (vec_list env.(module_Env_func_type_indices)))
    - to_Z i <= Z.of_nat m ->
  0 <= to_Z i ->
  (forall ft, List.In ft (vec_list env.(module_Env_types)) ->
     (List.length (vec_list ft.(types_FuncType_results)) <= 1)%nat) ->
  module_validate_code_entries_with_loop inst data env vis q i
    = Ok (Core_result_Result_Ok q', vis') ->
  exists codes,
    repr_rep repr_code
      (List.length (vec_list env.(module_Env_func_type_indices))
         - Z.to_nat (to_Z i))%nat
      (bytes_from data q) codes (bytes_from data q')
    /\ List.Forall2 (code_typed env)
         (List.skipn (Z.to_nat (to_Z i))
            (vec_list env.(module_Env_func_type_indices))) codes.
Proof.
  intros V inst m. induction m as [|m IH];
    intros data env vis vis' q i q' Hvalid Hmeas Hi Hres H;
    unfold module_validate_code_entries_with_loop in H;
    rewrite loop_unfold in H; cbn beta iota in H;
    destruct (i s>= alloc_vec_Vec_len env.(module_Env_func_type_indices)) eqn:Hge.
  1,3: injection H as <- <-; exists [];
       apply scalar_geb_true_ge in Hge; rewrite vec_len_spec in Hge;
       assert (Hoff : (List.length (vec_list env.(module_Env_func_type_indices))
                       <= Z.to_nat (to_Z i))%nat)
         by (apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; lia);
       split;
       [ replace (List.length (vec_list env.(module_Env_func_type_indices))
                    - Z.to_nat (to_Z i))%nat with 0%nat
           by (symmetry; apply Nat.sub_0_le; exact Hoff);
         apply repr_rep_nil
       | rewrite List.skipn_all2 by exact Hoff; apply List.Forall2_nil ].
  - exfalso. apply scalar_geb_false_lt in Hge.
    rewrite vec_len_spec in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge. rewrite vec_len_spec in Hge.
    (* the framing read's wait *)
    destruct (usize_add q limits_max_leb_bytes) as [qw|] eqn:Hqw;
      cbn [bind] in H; [|discriminate].
    destruct (inst.(module_CodeVisitor_t_on_need_bytes) vis qw) as [[rn v1]|]
      eqn:Hn; cbn [bind] in H; [|discriminate].
    destruct rn as [un|en]; [|try_err_rw_in H; cbn beta iota in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    (* the entry is framed, and then handed over *)
    destruct (module_code_entry_extent data q) as [rx|] eqn:Hx;
      cbn [bind] in H; [|discriminate].
    destruct rx as [[contents fin]|ex];
      [|try_err_rw_in H; cbn beta iota in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (inst.(module_CodeVisitor_t_on_need_bytes) v1 fin) as [[rn2 v2]|]
      eqn:Hn2; cbn [bind] in H; [|discriminate].
    destruct rn2 as [un2|en2];
      [|try_err_rw_in H; cbn beta iota in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (inst.(module_CodeVisitor_t_on_code_entry) v2 data env i q contents
                fin) as [[re v3]|] eqn:He; cbn [bind] in H; [|discriminate].
    destruct re as [ue|ee]; [|try_err_rw_in H; cbn beta iota in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    (* what taking the hook owed: the entry is one the validator accepts, and
       it ends where the framing said it would *)
    destruct ue.
    destruct (Hvalid _ _ _ _ _ _ He) as [q1 Hent].
    pose proof (code_entry_extent_frames _ _ env i _ _ _ Hx Hent) as Hsame.
    destruct (usize_add i 1%usize) as [i2|] eqn:Hadd; cbn [bind] in H;
      [|discriminate].
    pose proof (scalar_add_val _ _ _ 1 Hadd eq_refl) as Hi2.
    destruct (validate_code_entry_sound _ _ _ _ _ Hres Hent)
      as [c [Hc [tidx [Hnth Hty]]]].
    rewrite (bytes_from_to_Z data _ _ Hsame) in Hc.
    destruct (IH data env v3 vis' fin i2 q' Hvalid (ltac:(cbn in Hmeas; lia))
                (ltac:(lia)) Hres H) as [codes [Hrep Hall]].
    assert (Hlt : (Z.to_nat (to_Z i)
                   < List.length (vec_list env.(module_Env_func_type_indices)))%nat)
      by (apply Nat2Z.inj_lt; rewrite Z2Nat.id by lia; lia).
    assert (Hstep : (List.length (vec_list env.(module_Env_func_type_indices))
                       - Z.to_nat (to_Z i))%nat
                    = S (List.length (vec_list env.(module_Env_func_type_indices))
                           - Z.to_nat (to_Z i2)))
      by (rewrite Hi2; rewrite Z_to_nat_add1 by lia; lia).
    exists (c :: codes). split.
    + rewrite Hstep. eapply repr_rep_cons; [exact Hc | exact Hrep].
    + rewrite (skipn_nth_error _ _ _ Hnth).
      apply List.Forall2_cons; [exact Hty|].
      rewrite Hi2 in Hall. rewrite Z_to_nat_add1 in Hall by lia.
      exact Hall.
Qed.

Lemma validate_code_entries_with_sound :
  forall V (inst : module_CodeVisitor_t V) data env vis vis' pos q',
  code_hooks_validate inst data env ->
  (forall ft, List.In ft (vec_list env.(module_Env_types)) ->
     (List.length (vec_list ft.(types_FuncType_results)) <= 1)%nat) ->
  module_validate_code_entries_with inst data pos env vis
    = Ok (Core_result_Result_Ok q', vis') ->
  exists codes,
    repr_rep repr_code
      (List.length (vec_list env.(module_Env_func_type_indices)))
      (bytes_from data pos) codes (bytes_from data q')
    /\ List.Forall2 (code_typed env)
         (vec_list env.(module_Env_func_type_indices)) codes.
Proof.
  intros V inst data env vis vis' pos q' Hvalid Hres H.
  unfold module_validate_code_entries_with in H.
  assert (H0 : to_Z 0%usize = 0) by reflexivity.
  destruct (validate_code_entries_with_loop_sound V inst
              (List.length (vec_list env.(module_Env_func_type_indices)))
              data env vis vis' pos 0%usize q' Hvalid (ltac:(lia))
              (ltac:(lia)) Hres H)
    as [codes [Hrep Hall]].
  rewrite H0 in Hrep. cbn [Z.to_nat] in Hrep.
  rewrite Nat.sub_0_r in Hrep.
  rewrite H0 in Hall. cbn [Z.to_nat List.skipn] in Hall.
  exists codes. split; [exact Hrep | exact Hall].
Qed.

(** Spec 5.5.16's code line. A missing code section is the absent case, and
    the function section is what makes it legal: [no_code_section] accepts
    only when the module declared no functions, which is the same condition
    as [funcs_of] pairing the two empty vectors. *)
Lemma no_code_section_sound : forall env oc,
  module_no_code_section env = Ok (Core_result_Result_Ok oc) ->
  oc = None /\ vec_list env.(module_Env_func_type_indices) = [].
Proof.
  intros env oc H. unfold module_no_code_section in H.
  rewrite vec_is_empty_spec in H. cbn [bind] in H.
  destruct (vec_list env.(module_Env_func_type_indices)) eqn:Hl;
    [|discriminate].
  injection H as <-. split; reflexivity.
Qed.

(** What the header reader established, packaged so that [validate_code] and a
    consumer driving the entries itself both get it from one place. Present is
    the interesting case: the section is at [pos], it is the code section, its
    count is the function section's, and its entries begin just past that count.
    Absent is the format fact that nothing here is a code section, which is what
    [repr_optsec]'s absent case needs. *)
Lemma code_section_sound : forall data pos env oc,
  module_code_section data pos env = Ok (Core_result_Result_Ok oc) ->
  match oc with
  | None => ~ begins_with 10 (bytes_from data pos)
            /\ vec_list env.(module_Env_func_type_indices) = []
  | Some cs =>
      exists id start,
        to_Z id = 10
        /\ module_read_section_header data pos
           = Ok (Core_result_Result_Ok
                   (id, start, cs.(module_CodeSection_end)))
        /\ reader_read_u32_leb data start
           = Ok (Core_result_Result_Ok
                   (cs.(module_CodeSection_count),
                    cs.(module_CodeSection_entries)))
        /\ Z.of_nat (List.length (vec_list env.(module_Env_func_type_indices)))
           = to_Z cs.(module_CodeSection_count)
  end.
Proof.
  intros data pos env oc H. unfold module_code_section in H.
  (* absent, twice over: no bytes left, or the next id is not the code
     section's *)
  assert (Habsent : forall oc',
            module_no_code_section env = Ok (Core_result_Result_Ok oc') ->
            ~ begins_with 10 (bytes_from data pos) ->
            match oc' with
            | None => ~ begins_with 10 (bytes_from data pos)
                      /\ vec_list env.(module_Env_func_type_indices) = []
            | Some _ => True
            end).
  { intros oc' Hno Hnb. destruct (no_code_section_sound _ _ Hno) as [-> Hnil].
    split; [exact Hnb | exact Hnil]. }
  destruct (pos s>= slice_len data) eqn:Hge.
  { assert (Hnb : ~ begins_with 10 (bytes_from data pos)).
    { apply scalar_geb_true_ge in Hge. rewrite slice_len_spec in Hge.
      assert (Hnil : bytes_from data pos = [])
        by (rewrite bytes_from_at; apply bytes_at_end; lia).
      rewrite Hnil. intros [more Hm]. discriminate. }
    destruct (no_code_section_sound _ _ H) as [-> Hnil].
    split; [exact Hnb | exact Hnil]. }
  apply scalar_geb_false_lt in Hge. rewrite slice_len_spec in Hge.
  destruct (module_read_section_header data pos) as [r|] eqn:Hhdr;
    cbn [bind] in H; [|discriminate].
  destruct r as [[[id start] fin]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (read_section_header_head _ _ _ _ _ Hhdr) as [rest Hhead].
  destruct (id s<> module_section_code) eqn:Hcode.
  { assert (Hnb : ~ begins_with 10 (bytes_from data pos)).
    { apply scalar_neqb_true in Hcode. cbn in Hcode.
      apply (not_begins_of_head data pos id rest 10 Hhead). lia. }
    destruct (no_code_section_sound _ _ H) as [-> Hnil].
    split; [exact Hnb | exact Hnil]. }
  apply scalar_neqb_false in Hcode. cbn in Hcode.
  destruct (reader_read_u32_leb data start) as [r1|] eqn:Hcnt;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [[count p]|e1]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (scalar_cast U32 Usize count) as [n|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  destruct (n s<> alloc_vec_Vec_len env.(module_Env_func_type_indices)) eqn:Hlen;
    [discriminate|].
  apply scalar_neqb_false in Hlen. rewrite vec_len_spec in Hlen.
  injection H as <-. cbn.
  (* The header's equation is the one just destructed, and its subject mentions
     no existential, so `destruct ... eqn:` rewrote the goal along with the
     hypothesis and it is closed by reflexivity. The count's subject mentions
     `start`, which was still under a binder then, so that one is not. *)
  exists id, start. split; [exact Hcode|]. split; [reflexivity|].
  split; [exact Hcnt|].
  assert (Hn : to_Z n = to_Z count)
    by (unfold scalar_cast in Hcast; apply mk_scalar_ok_to_Z in Hcast;
        exact Hcast).
  lia.
Qed.

Lemma validate_code_with_sound :
  forall V (inst : module_CodeVisitor_t V) data pos env vis vis' q',
  code_hooks_validate inst data env ->
  (forall ft, List.In ft (vec_list env.(module_Env_types)) ->
     (List.length (vec_list ft.(types_FuncType_results)) <= 1)%nat) ->
  module_validate_code_with inst data pos env vis
    = Ok (Core_result_Result_Ok q', vis') ->
  exists codes,
    repr_optsec 10 (repr_vec repr_code) [] (bytes_from data pos) codes
      (bytes_from data q')
    /\ List.length codes
       = List.length (vec_list env.(module_Env_func_type_indices))
    /\ List.Forall2 (code_typed env)
         (vec_list env.(module_Env_func_type_indices)) codes.
Proof.
  intros V inst data pos env vis vis' q' Hvalid Hres H.
  unfold module_validate_code_with in H.
  (* the header's wait, before anything is read *)
  destruct (usize_add pos limits_max_code_header_bytes) as [pw|] eqn:Hpw;
    cbn [bind] in H; [|discriminate].
  destruct (inst.(module_CodeVisitor_t_on_need_bytes) vis pw) as [[rn v1]|]
    eqn:Hn; cbn [bind] in H; [|discriminate].
  destruct rn as [un|en]; [|try_err_rw_in H; cbn beta iota in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (module_code_section data pos env) as [r|] eqn:Hcs;
    cbn [bind] in H; [|discriminate].
  destruct r as [oc|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (code_section_sound _ _ _ _ Hcs) as Hsnd.
  destruct oc as [cs|].
  - (* the section is here: its entries are the codes, and they fill it *)
    destruct Hsnd as [id [start [Hid [Hhdr [Hcnt Hcount]]]]].
    destruct (module_validate_code_entries_with inst data
                cs.(module_CodeSection_entries) env v1) as [[r2 v2]|] eqn:Hents;
      cbn [bind] in H; [|discriminate].
    destruct r2 as [q|e2];
      [|try_err_rw_in H; cbn beta iota in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (q s<> cs.(module_CodeSection_end)) eqn:Hne; [discriminate|].
    apply scalar_neqb_false in Hne.
    (* The section's end is what was returned, so name that and carry it into
       the two facts that mention it. It is a projection rather than a variable,
       so it cannot simply be substituted. *)
    injection H as Hq' _.
    rewrite Hq' in Hne, Hhdr.
    destruct (validate_code_entries_with_sound _ _ _ _ _ _ _ _ Hvalid Hres Hents)
      as [codes [Hrep Hall]].
    assert (Hqf : bytes_from data q = bytes_from data q')
      by (apply bytes_at_congr; exact Hne).
    exists codes. split; [| split; [| exact Hall]].
    + rewrite <- Hid. apply repr_optsec_present.
      apply (section_sound _ _ data pos id start q' _
               (repr_vec_prefix _ _ repr_code_prefix) Hhdr).
      apply repr_vec_intro
        with (n := to_Z cs.(module_CodeSection_count))
             (mid := bytes_from data cs.(module_CodeSection_entries)).
      * apply (read_u32_leb_sound _ _ _ _ Hcnt).
      * rewrite <- Hqf.
        replace (Z.to_nat (to_Z cs.(module_CodeSection_count)))
          with (List.length (vec_list env.(module_Env_func_type_indices)))
          by (apply Nat2Z.inj; rewrite Z2Nat.id by
                (pose proof (u32_nonneg cs.(module_CodeSection_count)); lia);
              lia).
        exact Hrep.
    + apply (repr_rep_length _ _ _ _ _ _ Hrep).
  - (* no section, so no codes *)
    destruct Hsnd as [Hnb Hnil].
    injection H as <-.
    exists []. rewrite Hnil. split; [|split; [reflexivity|]].
    + apply repr_optsec_absent. exact Hnb.
    + apply List.Forall2_nil.
Qed.

(* ================================================================== *)
(** ** Driving the entries yourself is the run the theorems are about   *)
(* ================================================================== *)

(** A compiler does not call [validate_code]. It reads the header, then
    validates one entry at a time, on whatever thread suits, so that it can
    generate code as each body goes by. These two say that doing so is not a
    second way of validating the section: an accepting drive is an accepting
    [validate_code] and an accepting [validate_code] is an accepting drive, on
    the same bytes and landing on the same position. So everything
    [validate_code_sound] says about the section holds of the drive, including
    that the codes it saw are the ones spec 5.5.16 says are there.

    This is what makes the position a consumer starts its loop from a position
    the theorems cover. Without it, [validate_code_entry_with_sound] would say
    the operators shown are the body of the entry at whatever offset the
    consumer supplied, and nothing would say that offset was the module's. *)

(** [scalar_neqb_false] read the other way. Positions are compared as numbers
    throughout, which is why the two theorems below relate them with [to_Z]
    rather than as scalars: two scalars with the same value are the same
    position, but showing they are the same *term* would need more than the
    numbers. *)
Lemma scalar_neqb_of_to_Z : forall {ty} (x y : scalar ty),
  to_Z x = to_Z y -> (x s<> y) = false.
Proof.
  intros ty x y H. unfold scalar_neqb, scalar_eqb.
  apply Bool.negb_false_iff. apply Z.eqb_eq. exact H.
Qed.

Lemma validate_code_nop_inv : forall data pos env r,
  module_validate_code data pos env = Ok r ->
  module_validate_code_with
    module_ValidatingCodeVisitor_Insts_ItascaModuleCodeVisitor data pos env tt
    = Ok (r, tt).
Proof.
  intros data pos env r H. unfold module_validate_code in H.
  destruct (module_validate_code_with
              module_ValidatingCodeVisitor_Insts_ItascaModuleCodeVisitor data
              pos env tt) as [[r0 v0]|] eqn:Hw; cbn [bind] in H; [|discriminate].
  injection H as <-. destruct v0. reflexivity.
Qed.

Corollary validate_code_sound : forall data pos env q',
  (forall ft, List.In ft (vec_list env.(module_Env_types)) ->
     (List.length (vec_list ft.(types_FuncType_results)) <= 1)%nat) ->
  module_validate_code data pos env = Ok (Core_result_Result_Ok q') ->
  exists codes,
    repr_optsec 10 (repr_vec repr_code) [] (bytes_from data pos) codes
      (bytes_from data q')
    /\ List.length codes
       = List.length (vec_list env.(module_Env_func_type_indices))
    /\ List.Forall2 (code_typed env)
         (vec_list env.(module_Env_func_type_indices)) codes.
Proof.
  intros data pos env q' Hres H.
  apply validate_code_nop_inv in H.
  exact (validate_code_with_sound _ _ _ _ _ _ _ _
           (validating_code_hooks_validate data env) Hres H).
Qed.

(** The validating consumer's two hooks, as equations. Rewriting with these is
    steadier than unfolding the instance in place, and says what they are:
    it waits for nothing, and its answer on an entry is the validator's. *)
Lemma validating_need_bytes : forall e,
  module_ValidatingCodeVisitor_Insts_ItascaModuleCodeVisitor.(module_CodeVisitor_t_on_need_bytes)
    tt e = Ok (Core_result_Result_Ok tt, tt).
Proof. intros e. reflexivity. Qed.

Lemma validating_entry_ok : forall data env index pos contents fin q',
  module_validate_code_entry data pos env index
    = Ok (Core_result_Result_Ok q') ->
  module_ValidatingCodeVisitor_Insts_ItascaModuleCodeVisitor.(module_CodeVisitor_t_on_code_entry)
    tt data env index pos contents fin = Ok (Core_result_Result_Ok tt, tt).
Proof.
  intros data env index pos contents fin q' H.
  cbn [module_CodeVisitor_t_on_code_entry
       module_ValidatingCodeVisitor_Insts_ItascaModuleCodeVisitor].
  unfold module_ValidatingCodeVisitor_Insts_ItascaModuleCodeVisitor_on_code_entry.
  rewrite H. cbn [bind]. rewrite branch_ok. cbn [bind]. reflexivity.
Qed.

(** An accepting driven walk is an accepting [validate_code].
    Both walks read the same header and frame each entry by its own size
    prefix, so they take the same path; the only place they can differ is the
    entry itself, and [code_hooks_validate] says the consumer's answer there
    was the validator's. That is what lets a consumer that drove the section
    itself use [validate_module_parts]: the position it landed on is the one
    [validate_code] would have.

    Stated over the loop by induction rather than assembled from the two
    walks' results, because the cursor has to agree at every step and not only
    at the end. *)
Lemma validate_code_entries_driven :
  forall V (inst : module_CodeVisitor_t V) m data env vis vis' q i q',
  code_hooks_validate inst data env ->
  Z.of_nat (List.length (vec_list env.(module_Env_func_type_indices)))
    - to_Z i <= Z.of_nat m ->
  module_validate_code_entries_with_loop inst data env vis q i
    = Ok (Core_result_Result_Ok q', vis') ->
  module_validate_code_entries_with_loop
    module_ValidatingCodeVisitor_Insts_ItascaModuleCodeVisitor data env tt q i
    = Ok (Core_result_Result_Ok q', tt).
Proof.
  intros V inst m. induction m as [|m IH];
    intros data env vis vis' q i q' Hvalid Hmeas H;
    unfold module_validate_code_entries_with_loop in H;
    rewrite loop_unfold in H; cbn beta iota in H;
    unfold module_validate_code_entries_with_loop;
    rewrite loop_unfold; cbn beta iota;
    destruct (i s>= alloc_vec_Vec_len env.(module_Env_func_type_indices)) eqn:Hge.
  1,3: injection H as <- <-; reflexivity.
  - exfalso. apply scalar_geb_false_lt in Hge. rewrite vec_len_spec in Hge.
    cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge. rewrite vec_len_spec in Hge.
    destruct (usize_add q limits_max_leb_bytes) as [qw|] eqn:Hqw;
      cbn [bind] in H |- *; [|discriminate].
    destruct (inst.(module_CodeVisitor_t_on_need_bytes) vis qw) as [[rn v1]|]
      eqn:Hn; cbn [bind] in H; [|discriminate].
    destruct rn as [un|en]; [|try_err_rw_in H; cbn beta iota in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    (* the validating consumer waits for nothing, so its step is immediate *)
    rewrite validating_need_bytes. cbn [bind]. rewrite branch_ok. cbn [bind].
    destruct (module_code_entry_extent data q) as [rx|] eqn:Hx;
      cbn [bind] in H |- *; [|discriminate].
    destruct rx as [[contents fin]|ex];
      [|try_err_rw_in H; cbn beta iota in H; discriminate].
    rewrite branch_ok in H |- *. cbn [bind] in H |- *.
    destruct (inst.(module_CodeVisitor_t_on_need_bytes) v1 fin) as [[rn2 v2]|]
      eqn:Hn2; cbn [bind] in H; [|discriminate].
    destruct rn2 as [un2|en2];
      [|try_err_rw_in H; cbn beta iota in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    rewrite validating_need_bytes. cbn [bind]. rewrite branch_ok. cbn [bind].
    destruct (inst.(module_CodeVisitor_t_on_code_entry) v2 data env i q contents
                fin) as [[re v3]|] eqn:He; cbn [bind] in H; [|discriminate].
    destruct re as [ue|ee]; [|try_err_rw_in H; cbn beta iota in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    (* what the consumer owed: the same entry, accepted, ending where the
       framing said *)
    destruct ue.
    destruct (Hvalid _ _ _ _ _ _ He) as [q1 Hent].
    rewrite (validating_entry_ok _ _ _ _ contents fin _ Hent). cbn [bind].
    rewrite branch_ok. cbn [bind].
    destruct (usize_add i 1%usize) as [i2|] eqn:Hadd;
      cbn [bind] in H |- *; [|discriminate].
    apply (IH data env v3 vis' fin i2 q' Hvalid
             (ltac:(pose proof (scalar_add_val _ _ _ 1 Hadd eq_refl);
                    cbn in Hmeas; lia)) H).
Qed.

Theorem validate_code_driven :
  forall V (inst : module_CodeVisitor_t V) data pos env vis vis' q',
  code_hooks_validate inst data env ->
  module_validate_code_with inst data pos env vis
    = Ok (Core_result_Result_Ok q', vis') ->
  module_validate_code data pos env = Ok (Core_result_Result_Ok q').
Proof.
  intros V inst data pos env vis vis' q' Hvalid H.
  unfold module_validate_code. apply validate_code_nop.
  unfold module_validate_code_with in H |- *.
  destruct (usize_add pos limits_max_code_header_bytes) as [pw|] eqn:Hpw;
    cbn [bind] in H |- *; [|discriminate].
  destruct (inst.(module_CodeVisitor_t_on_need_bytes) vis pw) as [[rn v1]|]
    eqn:Hn; cbn [bind] in H; [|discriminate].
  destruct rn as [un|en]; [|try_err_rw_in H; cbn beta iota in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  rewrite validating_need_bytes. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (module_code_section data pos env) as [r|] eqn:Hcs;
    cbn [bind] in H |- *; [|discriminate].
  destruct r as [oc|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H |- *. cbn [bind] in H |- *.
  destruct oc as [cs|].
  - unfold module_validate_code_entries_with in H |- *.
    destruct (module_validate_code_entries_with_loop inst data env v1
                cs.(module_CodeSection_entries) 0%usize) as [[r2 v2]|] eqn:Hents;
      cbn [bind] in H; [|discriminate].
    destruct r2 as [q|e2];
      [|try_err_rw_in H; cbn beta iota in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    rewrite (validate_code_entries_driven V inst
               (List.length (vec_list env.(module_Env_func_type_indices)))
               data env v1 v2 cs.(module_CodeSection_entries) 0%usize q
               Hvalid (ltac:(assert (to_Z 0%usize = 0) by reflexivity; lia))
               Hents).
    cbn [bind]. rewrite branch_ok. cbn [bind].
    destruct (q s<> cs.(module_CodeSection_end)); [discriminate|].
    injection H as <- _. reflexivity.
  - injection H as <- _. reflexivity.
Qed.

(* ================================================================== *)
(** ** At most one result, carried to the code section                 *)
(* ================================================================== *)

(** The one thing the code section needs of the environment that no format
    rule says. It is an invariant of the loop rather than a line of the chain:
    only the type section writes [types], and everything it writes was checked
    as it was decoded. *)
Definition types_wasm10 (env : module_Env_t) : Prop :=
  forall ft, List.In ft (vec_list env.(module_Env_types)) -> ft_wasm10 ft.

Lemma decode_env_section_wasm10 : forall data start id env q env2,
  module_decode_env_section data start id env
    = Ok (Core_result_Result_Ok q, env2) ->
  types_wasm10 env -> types_wasm10 env2.
Proof.
  intros data start id env q env2 H Hw.
  unfold module_decode_env_section in H.
  (* the same walk the dispatch lemmas take, but every arm has the same
     shape: either [types] grew and each entry was checked, or it did not
     move at all *)
  assert (Hkeep : forall envB,
            vec_list envB.(module_Env_types) = vec_list env.(module_Env_types) ->
            types_wasm10 envB)
    by (intros envB Ht ft Hin; apply Hw; rewrite <- Ht; exact Hin).
  repeat (match type of H with
          | context [if (id s= ?c) then _ else _] =>
              let E := fresh "E" in destruct (id s= c) eqn:E
          end).
  all: try discriminate.
  (* the type section: the entries it appended were each checked *)
  1: { destruct (decode_type_section_sound _ _ _ _ _ H)
         as [tfs [Hlist [_ [Hall _]]]].
       intros ft Hin. rewrite Hlist in Hin.
       apply List.in_app_or in Hin. destruct Hin as [Hin|Hin];
         [apply Hw; exact Hin|].
       rewrite List.Forall_forall in Hall. apply Hall. exact Hin. }
  (* every other section leaves [types] where it found it *)
  1: { destruct (decode_import_section_sound _ _ _ _ _ H) as [_ [_ [He _]]].
       unfold env_imported in He. apply Hkeep. rewrite He. reflexivity. }
  1: { destruct (decode_function_section_sound _ _ _ _ _ H) as [_ [_ [He _]]].
       apply Hkeep. rewrite He. reflexivity. }
  1: { destruct (decode_table_section_sound _ _ _ _ _ H) as [_ [_ [He _]]].
       apply Hkeep. rewrite He. reflexivity. }
  1: { destruct (decode_memory_section_sound _ _ _ _ _ H) as [_ [_ [He _]]].
       apply Hkeep. rewrite He. reflexivity. }
  1: { destruct (decode_global_section_sound _ _ _ _ _ H) as [_ [_ [He _]]].
       apply Hkeep. rewrite He. reflexivity. }
  1: { destruct (decode_export_section_sound _ _ _ _ _ H) as [_ [_ [He _]]].
       apply Hkeep. rewrite He. reflexivity. }
  1: { destruct (decode_start_section_sound _ _ _ _ _ H) as [He _].
       apply Hkeep. rewrite He. reflexivity. }
  1: { destruct (decode_element_section_sound _ _ _ _ _ H) as [_ [_ [He _]]].
       apply Hkeep. rewrite He. reflexivity. }
Qed.

(** Every invariant the typing half will need of the environment is preserved
    the same way: the loop itself does not touch it, and each section either
    leaves the field alone or appends something it checked as it decoded.
    Abstracting the loop over the property means a new one costs only its nine
    section cases. *)
Lemma validate_env_with_loop_preserves : forall (P : module_Env_t -> Prop),
  (forall data start id env q env2,
     module_decode_env_section data start id env
       = Ok (Core_result_Result_Ok q, env2) -> P env -> P env2) ->
  forall V (inst : module_ModuleVisitor_t V) m data vis vis' env q last_id envf qf,
  Z.of_nat (List.length (vec_list data)) - to_Z q <= Z.of_nat m ->
  P env ->
  module_validate_env_with_loop inst data vis env q last_id
    = Ok (Core_result_Result_Ok (envf, qf), vis') ->
  P envf.
Proof.
  intros P Hstep V inst m. induction m as [|m IH];
    intros data vis vis' env q last_id envf qf Hmeas Hw H;
    unfold module_validate_env_with_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H; destruct (q s>= slice_len data) eqn:Hge.
  1,3: injection H as <- <- <-; exact Hw.
  - exfalso. apply scalar_geb_false_lt in Hge.
    rewrite slice_len_spec in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge. rewrite slice_len_spec in Hge.
    destruct (module_read_section_header data q) as [r|] eqn:Hhdr;
      cbn [bind] in H; [|discriminate].
    destruct r as [[[id start] fin]|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (read_section_header_step _ _ _ _ _ Hhdr) as [Hqs [Hsf Hfd]].
    rewrite slice_len_spec in Hfd.
    assert (Hmeas' : Z.of_nat (List.length (vec_list data)) - to_Z fin
                     <= Z.of_nat m) by (cbn in Hmeas; lia).
    destruct (id s= module_section_custom).
    { destruct (module_decode_custom_section data start fin) as [r1|];
        cbn [bind] in H; [|discriminate].
      destruct r1 as [c|e1]; [|try_err_rw_in H; discriminate].
      rewrite branch_ok in H. cbn [bind] in H.
      destruct (inst.(module_ModuleVisitor_t_on_custom_section) vis c)
        as [[rh vis1]|]; cbn [bind] in H; [|discriminate].
      destruct rh as [u|ev]; [|cbn beta iota in H; discriminate].
      cbn beta iota in H.
      apply (IH data vis1 vis' env fin last_id envf qf Hmeas' Hw H). }
    destruct (id s>= module_section_code); [injection H as <- <- <-; exact Hw|].
    destruct (id s<= last_id); [discriminate|].
    destruct (module_decode_env_section data start id env) as [[r1 env2]|]
      eqn:Hsec; cbn [bind] in H; [|discriminate].
    destruct r1 as [p|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (p s<> fin); [discriminate|].
    apply (IH data vis vis' env2 fin id envf qf Hmeas'
             (Hstep _ _ _ _ _ _ Hsec Hw) H).
Qed.

Lemma validate_env_preserves : forall (P : module_Env_t -> Prop),
  (forall data start id env q env2,
     module_decode_env_section data start id env
       = Ok (Core_result_Result_Ok q, env2) -> P env -> P env2) ->
  (forall env0, module_Env_new = Ok env0 -> P env0) ->
  forall data env qf,
  module_validate_env data = Ok (Core_result_Result_Ok (env, qf)) ->
  P env.
Proof.
  intros P Hstep Hinit data env qf H0.
  pose proof (validate_env_nop_inv _ _ H0) as H. clear H0.
  unfold module_validate_env_with in H.
  destruct module_Env_new as [env0|] eqn:Hnew; cbn [bind] in H; [|discriminate].
  destruct (module_read_header data) as [r|]; cbn [bind] in H;
    [|discriminate].
  destruct r as [p0|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  apply (validate_env_with_loop_preserves P Hstep _
           module_EmptyModuleVisitor_Insts_ItascaModuleModuleVisitor
           (List.length (vec_list data)) data tt tt env0 p0 0%u8 env qf);
    [ pose proof (usize_nonneg p0); lia
    | apply Hinit; reflexivity
    | exact H ].
Qed.

Lemma validate_env_wasm10 : forall data env qf,
  module_validate_env data = Ok (Core_result_Result_Ok (env, qf)) ->
  types_wasm10 env.
Proof.
  apply (validate_env_preserves types_wasm10 decode_env_section_wasm10).
  intros env0 Hnew. unfold module_Env_new in Hnew. injection Hnew as <-.
  intros ft Hin. cbn [vec_list alloc_vec_Vec_new proj1_sig] in Hin.
  destruct Hin.
Qed.

(** The limits invariant across the whole environment. Three sections hand it
    on and the other six leave all three fields alone, which is the same one
    record equation each of them already carries. *)
Lemma decode_env_section_limits_valid : forall data start id env q env2,
  module_decode_env_section data start id env
    = Ok (Core_result_Result_Ok q, env2) ->
  env_limits_valid env -> env_limits_valid env2.
Proof.
  intros data start id env q env2 H Hv.
  unfold module_decode_env_section in H.
  repeat (match type of H with
          | context [if (id s= ?c) then _ else _] =>
              let E := fresh "E" in destruct (id s= c) eqn:E
          end).
  all: try discriminate.
  (* six sections leave all three fields alone; three hand the invariant on *)
  1: { destruct (decode_type_section_sound _ _ _ _ _ H) as [_ [_ [He _]]].
       rewrite He. apply (env_limits_valid_keep env);
         try reflexivity; exact Hv. }
  1: { destruct (decode_import_section_sound _ _ _ _ _ H)
         as [_ [_ [_ [_ [Hk _]]]]].
       exact (Hk Hv). }
  1: { destruct (decode_function_section_sound _ _ _ _ _ H) as [_ [_ [He _]]].
       rewrite He. apply (env_limits_valid_keep env);
         try reflexivity; exact Hv. }
  1: { destruct (decode_table_section_sound _ _ _ _ _ H) as [_ [_ [_ [_ Hk]]]].
       exact (Hk Hv). }
  1: { destruct (decode_memory_section_sound _ _ _ _ _ H) as [_ [_ [_ [_ Hk]]]].
       exact (Hk Hv). }
  1: { destruct (decode_global_section_sound _ _ _ _ _ H) as [_ [_ [He _]]].
       rewrite He. apply (env_limits_valid_keep env);
         try reflexivity; exact Hv. }
  1: { destruct (decode_export_section_sound _ _ _ _ _ H) as [_ [_ [He _]]].
       rewrite He. apply (env_limits_valid_keep env);
         try reflexivity; exact Hv. }
  1: { destruct (decode_start_section_sound _ _ _ _ _ H) as [He _].
       rewrite He. apply (env_limits_valid_keep env);
         try reflexivity; exact Hv. }
  1: { destruct (decode_element_section_sound _ _ _ _ _ H) as [_ [_ [He _]]].
       rewrite He. apply (env_limits_valid_keep env);
         try reflexivity; exact Hv. }
Qed.

Lemma validate_env_limits_valid : forall data env qf,
  module_validate_env data = Ok (Core_result_Result_Ok (env, qf)) ->
  env_limits_valid env.
Proof.
  apply (validate_env_preserves env_limits_valid decode_env_section_limits_valid).
  intros env0 Hnew. unfold module_Env_new in Hnew. injection Hnew as <-.
  cbn [vec_list alloc_vec_Vec_new proj1_sig].
  split; [apply List.Forall_nil|].
  split; apply List.Forall_nil.
Qed.

(* ================================================================== *)
(** ** The module                                                      *)
(* ================================================================== *)

(** The four checked-what-it-said predicates are functions of the index spaces
    and nothing else, so they move from the environment a section ran against
    to the one the run ended with, which is what the chain's [_keeps] lemmas
    supply. *)
Lemma const_expr_ok_congr : forall env env' t e,
  vec_list env'.(module_Env_global_types) = vec_list env.(module_Env_global_types) ->
  to_Z env'.(module_Env_num_imported_globals)
    = to_Z env.(module_Env_num_imported_globals) ->
  const_expr_ok env t e -> const_expr_ok env' t e.
Proof.
  intros env env' t e Hg Hn H. destruct e; try exact H.
  destruct H as [gt [Hnth [Hmut [Hty Hlt]]]].
  exists gt. rewrite Hg. rewrite Hn.
  split; [exact Hnth | split; [exact Hmut | split; [exact Hty | exact Hlt]]].
Qed.

Lemma element_ok_congr : forall env env' el,
  vec_list env'.(module_Env_table_types) = vec_list env.(module_Env_table_types) ->
  vec_list env'.(module_Env_func_types) = vec_list env.(module_Env_func_types) ->
  vec_list env'.(module_Env_global_types) = vec_list env.(module_Env_global_types) ->
  to_Z env'.(module_Env_num_imported_globals)
    = to_Z env.(module_Env_num_imported_globals) ->
  element_ok env el -> element_ok env' el.
Proof.
  intros env env' el Ht Hf Hg Hn [H1 [H2 H3]].
  split; [rewrite Ht; exact H1|].
  split; [apply (const_expr_ok_congr env env'); assumption
        | rewrite Hf; exact H3].
Qed.

Lemma export_desc_ok_congr : forall env env' e,
  vec_list env'.(module_Env_func_types) = vec_list env.(module_Env_func_types) ->
  vec_list env'.(module_Env_table_types) = vec_list env.(module_Env_table_types) ->
  vec_list env'.(module_Env_mem_types) = vec_list env.(module_Env_mem_types) ->
  vec_list env'.(module_Env_global_types) = vec_list env.(module_Env_global_types) ->
  export_desc_ok env e -> export_desc_ok env' e.
Proof.
  intros env env' e Hf Ht Hm Hg H. unfold export_desc_ok in *.
  destruct e.(module_Export_desc);
    [rewrite Hf | rewrite Ht | rewrite Hm | rewrite Hg]; exact H.
Qed.

Lemma start_ok_congr : forall env env',
  env'.(module_Env_start) = env.(module_Env_start) ->
  vec_list env'.(module_Env_func_types) = vec_list env.(module_Env_func_types) ->
  start_ok env -> start_ok env'.
Proof.
  intros env env' Hs Hf H. unfold start_ok in *. rewrite Hs. rewrite Hf.
  exact H.
Qed.

(** The module an accepting run decoded, as a function of the environment it
    built. Eight of the ten fields are a field of [Env] translated; the two
    that are not are the tables and memories the module *defines*, which are
    the suffix of the index space the import section did not write, and the
    functions, which pair the function section's type indices with the code
    section's bodies and so are not recoverable from [Env] at all -- the
    validator does not keep function bodies. *)
Definition module_of (env : module_Env_t) (fs : list module_func)
                     (tabs : list types_TableType_t)
                     (mems : list types_MemType_t)
                     (datas : list module_data) : module :=
  {| mod_types   := List.map translate_functype (vec_list env.(module_Env_types));
     mod_funcs   := fs;
     mod_tables  := List.map translate_table tabs;
     mod_mems    := List.map translate_mem mems;
     mod_globals := List.map translate_global (vec_list env.(module_Env_globals));
     mod_elems   := List.map translate_element (vec_list env.(module_Env_elements));
     mod_datas   := datas;
     mod_start   := translate_start env.(module_Env_start);
     mod_imports := List.map translate_import (vec_list env.(module_Env_imports));
     mod_exports := List.map translate_export (vec_list env.(module_Env_exports)) |}.

(** An accepting run means the input is a Wasm 1.0 module binary: spec
    5.5.16's production holds of it, from the magic number to the last custom
    section, and the module it decoded to is the one the environment says.

    The three parts meet here. [validate_env] supplies the magic number, the
    nine environment lines and the run of custom sections that pads the code
    line; [validate_code] supplies that line's section, and the count check is
    what pairs the function section's type indices with the code entries;
    [validate_tail] supplies the data line and the run that closes the module.

    Each of the module's fields is read off the final environment in one line:
    the chain's [_keeps] lemmas carry the field forward from the section that
    wrote it, and that section's own equation says what it appended to what
    was there before. For the two index spaces that is not an empty prefix --
    it is what the import section put there, which is [import_spaces].

    [Spec_Module.repr_module_det] makes the module unique, so this is the
    module the bytes encode, not merely one of them. *)
(** A whole module driven through the hooks is the module [validate_module]
    validates: the same verdict, and the same [Module].
    
    This is what makes the interface worth having. Every result about
    [validate_module] -- [validate_module_repr], [validate_module_typed],
    [validate_module_parts] and the rest -- applies to a consumer that drove
    the module itself, because the run it drove is that run. Nothing about the
    module theorems had to be restated for a driven consumer.
    
    The obligation is the code section's alone. Reporting a custom section
    cannot change what is read next, so the two decoders need nothing of their
    consumer; the entries do, because the walk frames them and hands them over
    rather than validating them, and [code_hooks_validate] is where that is
    written down. Quantified over the environment because the walk computes it:
    the hook is handed one, and this says the consumer validates against
    whichever it is handed. *)
Theorem validate_module_driven :
  forall V (minst : module_ModuleVisitor_t V) (cinst : module_CodeVisitor_t V)
         data vis vis' vm,
  (forall env, code_hooks_validate cinst data env) ->
  module_validate_module_with minst cinst data vis
    = Ok (Core_result_Result_Ok vm, vis') ->
  module_validate_module data = Ok (Core_result_Result_Ok vm).
Proof.
  intros V minst cinst data vis vis' vm Hvalid H.
  unfold module_validate_module_with in H. unfold module_validate_module.
  destruct (slice_len data s> limits_max_module_bytes); [discriminate|].
  destruct (module_validate_env_with minst data vis) as [[re v1]|] eqn:He;
    cbn [bind] in H; [|discriminate].
  destruct re as [[env code_pos]|e];
    [|try_err_rw_in H; cbn beta iota in H; discriminate].
  rewrite (validate_env_driven V minst data vis v1 env code_pos He).
  cbn [bind]. rewrite branch_ok. cbn [bind].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (module_validate_code_with cinst data code_pos env v1) as [[rc v2]|]
    eqn:Hc; cbn [bind] in H; [|discriminate].
  destruct rc as [tail_pos|e];
    [|try_err_rw_in H; cbn beta iota in H; discriminate].
  rewrite (validate_code_driven V cinst data code_pos env v1 v2 tail_pos
             (Hvalid env) Hc).
  cbn [bind]. rewrite branch_ok. cbn [bind].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (module_validate_tail_with minst data tail_pos env v2) as [[rt v3]|]
    eqn:Ht; cbn [bind] in H; [|discriminate].
  destruct rt as [tail|e];
    [|try_err_rw_in H; cbn beta iota in H; discriminate].
  rewrite (validate_tail_driven V minst data tail_pos env v2 v3 tail Ht).
  cbn [bind]. rewrite branch_ok. cbn [bind].
  rewrite branch_ok in H. cbn [bind] in H.
  injection H as <- _. reflexivity.
Qed.

Theorem validate_module_parts : forall data vm,
  module_validate_module data = Ok (Core_result_Result_Ok vm) ->
  exists env code_pos tail_pos tl fs tabs mems,
    vm = {| module_Module_env := env;
            module_Module_tail := tl |}
    /\ module_validate_env data = Ok (Core_result_Result_Ok (env, code_pos))
    /\ module_validate_code data code_pos env
         = Ok (Core_result_Result_Ok tail_pos)
    /\ module_validate_tail data tail_pos env = Ok (Core_result_Result_Ok tl)
    /\ vec_list env.(module_Env_table_types)
         = imported_tables (vec_list env.(module_Env_imports)) ++ tabs
    /\ vec_list env.(module_Env_mem_types)
         = imported_mems (vec_list env.(module_Env_imports)) ++ mems
    /\ env_func_space env
         (imported_func_idxs (vec_list env.(module_Env_imports))
          ++ vec_list env.(module_Env_func_type_indices))
    /\ vec_list env.(module_Env_global_types)
         = imported_globals (vec_list env.(module_Env_imports))
           ++ List.map (fun g => g.(module_Global_gtype))
                (vec_list env.(module_Env_globals))
    /\ to_Z env.(module_Env_num_imported_globals)
         = Z.of_nat (List.length
             (imported_globals (vec_list env.(module_Env_imports))))
    /\ List.Forall (element_ok env) (vec_list env.(module_Env_elements))
    /\ start_ok env
    /\ exports_distinct env
    /\ List.Forall (export_desc_ok env) (vec_list env.(module_Env_exports))
    /\ List.Forall (data_ok env) (vec_list tl.(module_Tail_data))
    /\ List.Forall (global_ok env) (vec_list env.(module_Env_globals))
    /\ (exists codes,
          List.Forall2 (code_typed env)
            (vec_list env.(module_Env_func_type_indices)) codes
          /\ funcs_of (List.map translate_idx
                        (vec_list env.(module_Env_func_type_indices))) codes fs)
    /\ repr_module (byte_list data)
         (module_of env fs tabs mems
            (List.map translate_data (vec_list tl.(module_Tail_data)))).
Proof.
  intros data vm H. unfold module_validate_module in H.
  destruct (slice_len data s> limits_max_module_bytes); [discriminate|].
  destruct (module_validate_env data) as [r|] eqn:Henv; cbn [bind] in H;
    [|discriminate].
  destruct r as [[env code_pos]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (module_validate_code data code_pos env) as [r1|] eqn:Hcode;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [tail_pos|e1]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (module_validate_tail data tail_pos env) as [r2|] eqn:Htail;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [tl|e2]; [|try_err_rw_in H; discriminate].
  (* the value the run returned is built from these two parts, which is what
     lets the theorems downstream talk about [vm] rather than about [env] *)
  assert (Hvm : vm = {| module_Module_env := env;
                        module_Module_tail := tl |}).
  { rewrite branch_ok in H. cbn [bind] in H. injection H as H.
    symmetry. exact H. }
  clear H.
  destruct (validate_env_sound _ _ _ Henv) as [p0 [env0 [Hmagic [Hnew Hchain]]]].
  destruct (validate_code_sound _ _ _ _ (validate_env_wasm10 _ _ _ Henv) Hcode)
    as [codes [Hcodesec [Hcodelen Hcodety]]].
  destruct (validate_tail_sound _ _ _ _ Htail) as [Htailchain Hdataok].
  unfold module_Env_new in Hnew. injection Hnew as <-.
  (* peel the nine environment lines and the run of customs that follows,
     keeping the tail of the chain at each line: that is what carries a field
     the line wrote through to the environment the run ends with *)
  destruct Hchain as [p1 [e1' [tfs  [Hp1 [Hl1 [Hv1 Hchain2]]]]]].
  pose proof Hchain2 as C2.
  destruct C2 as [p2 [e2' [imps [Hp2 [Hl2 [Hv2 [Hsp2 Hchain3]]]]]]].
  pose proof Hchain3 as C3.
  destruct C3 as [p3 [e3' [tidxs [Hp3 [Hl3 [Hv3 [Hfs3 Hchain4]]]]]]].
  pose proof Hchain4 as C4.
  destruct C4 as [p4 [e4' [tabs [Hp4 [Hl4 [Hv4 Hchain5]]]]]].
  pose proof Hchain5 as C5.
  destruct C5 as [p5 [e5' [mems [Hp5 [Hl5 [Hv5 Hchain6]]]]]].
  pose proof Hchain6 as C6.
  destruct C6 as [p6 [e6' [globs [Hp6 [Hl6 [Hv6 [Hgts6 [Hoks6 Hchain7]]]]]]]].
  pose proof Hchain7 as C7.
  destruct C7 as [p7 [e7' [exps [Hp7 [Hl7 [Hv7 [Hdist7 [Hdesc7 Hchain8]]]]]]]].
  pose proof Hchain8 as C8.
  destruct C8 as [p8 [e8' [Hp8 [Hv8 [Hstart8 Hchain9]]]]].
  pose proof Hchain9 as C9.
  destruct C9 as [p9 [e9' [els [Hp9 [Hl9 [Hv9 [Hels9 Hchaint]]]]]]].
  destruct Hchaint as [Hcustoms Henvf].
  destruct Htailchain as [mid11 [Hp11 Hend]].
  unfold env_imported in Hv2.
  destruct Hsp2 as [Hsp2t [Hsp2m [Hsp2g [Hsp2ty [Hfs2 Hnig2]]]]].
  (* the code section's line, padded by the run [validate_env] stopped in *)
  assert (Hp10 : repr_padded 10 (repr_vec repr_code) [] (bytes_from data p9)
                   codes (bytes_from data tail_pos))
    by (exists (bytes_from data code_pos); split;
        [exact Hcustoms | exact Hcodesec]).
  (* the ten fields, each carried from the line that wrote it *)
  assert (Ktypes1 : vec_list env.(module_Env_types) = vec_list e1'.(module_Env_types))
    by (apply (env_chain_2_keeps _ (fun e => vec_list e.(module_Env_types))
                 _ _ _ _ _ ltac:(keeps_refl) Hchain2)).
  assert (Ktypes : vec_list env.(module_Env_types) = tfs)
    by (rewrite Ktypes1; rewrite Hl1; reflexivity).
  assert (Kimports : vec_list env.(module_Env_imports) = imps).
  { rewrite (env_chain_3_keeps _ (fun e => vec_list e.(module_Env_imports))
               _ _ _ _ _ ltac:(keeps_refl) Hchain3).
    rewrite Hl2. rewrite Hv1. reflexivity. }
  assert (Kfti : vec_list env.(module_Env_func_type_indices) = tidxs).
  { rewrite (env_chain_4_keeps _
               (fun e => vec_list e.(module_Env_func_type_indices))
               _ _ _ _ _ ltac:(keeps_refl) Hchain4).
    rewrite Hl3. rewrite Hv2. rewrite Hv1. reflexivity. }
  assert (Ktables : vec_list env.(module_Env_table_types)
                    = imported_tables imps ++ tabs).
  { rewrite (env_chain_5_keeps _ (fun e => vec_list e.(module_Env_table_types))
               _ _ _ _ _ ltac:(keeps_refl) Hchain5).
    rewrite Hl4. rewrite Hv3. env_proj. rewrite Hsp2t. rewrite Hv1.
    reflexivity. }
  assert (Kmems : vec_list env.(module_Env_mem_types)
                  = imported_mems imps ++ mems).
  { rewrite (env_chain_6_keeps _ (fun e => vec_list e.(module_Env_mem_types))
               _ _ _ _ _ ltac:(keeps_refl) Hchain6).
    rewrite Hl5. rewrite Hv4. rewrite Hv3. env_proj. rewrite Hsp2m.
    rewrite Hv1. reflexivity. }
  assert (Kglobals : vec_list env.(module_Env_globals) = globs).
  { rewrite (env_chain_7_keeps _ (fun e => vec_list e.(module_Env_globals))
               _ _ _ _ _ ltac:(keeps_refl) Hchain7).
    rewrite Hl6. rewrite Hv5. rewrite Hv4. rewrite Hv3. rewrite Hv2.
    rewrite Hv1. reflexivity. }
  assert (Kexports : vec_list env.(module_Env_exports) = exps).
  { rewrite (env_chain_8_keeps _ (fun e => vec_list e.(module_Env_exports))
               _ _ _ _ _ ltac:(keeps_refl) Hchain8).
    rewrite Hl7. rewrite Hv6. rewrite Hv5. rewrite Hv4. rewrite Hv3.
    rewrite Hv2. rewrite Hv1. reflexivity. }
  assert (Kstart : env.(module_Env_start) = e8'.(module_Env_start))
    by (apply (env_chain_9_keeps _ (fun e => e.(module_Env_start))
                 _ _ _ _ _ ltac:(keeps_refl) Hchain9)).
  assert (Kelems : vec_list env.(module_Env_elements) = els).
  { rewrite (chain_tail_keeps _ (fun e => vec_list e.(module_Env_elements))
               _ _ _ _ _ (conj Hcustoms Henvf)).
    rewrite Hl9. rewrite Hv8. rewrite Hv7. rewrite Hv6. rewrite Hv5.
    rewrite Hv4. rewrite Hv3. rewrite Hv2. rewrite Hv1. reflexivity. }
  assert (Kgts : vec_list env.(module_Env_global_types)
                 = imported_globals (vec_list env.(module_Env_imports))
                   ++ List.map (fun g => g.(module_Global_gtype))
                        (vec_list env.(module_Env_globals))).
  { rewrite Kimports. rewrite Kglobals.
    rewrite (env_chain_7_keeps _
               (fun e => vec_list e.(module_Env_global_types))
               _ _ _ _ _ ltac:(keeps_refl) Hchain7).
    rewrite Hgts6. rewrite Hv5. rewrite Hv4. rewrite Hv3. env_proj.
    rewrite Hsp2g. rewrite Hv1. reflexivity. }
  assert (Knig : to_Z env.(module_Env_num_imported_globals)
                 = Z.of_nat (List.length
                     (imported_globals (vec_list env.(module_Env_imports))))).
  { rewrite Kimports.
    rewrite (env_chain_3_keeps _
               (fun e => to_Z e.(module_Env_num_imported_globals))
               _ _ _ _ _ ltac:(keeps_refl) Hchain3).
    rewrite Hnig2. rewrite Hv1. env_proj. cbn. lia. }
  assert (Kfuncs : env_func_space env
                     (imported_func_idxs (vec_list env.(module_Env_imports))
                      ++ vec_list env.(module_Env_func_type_indices))).
  { rewrite Kimports. rewrite Kfti.
    destruct (func_space_trans e1' e2' e3' _ _ Hsp2ty Hfs2 Hfs3)
      as [Hmap Hall].
    split; [| rewrite Ktypes1; exact Hall].
    rewrite (env_chain_4_keeps _
               (fun e => List.map translate_functype
                           (vec_list e.(module_Env_func_types)))
               _ _ _ _ _ ltac:(keeps_refl) Hchain4).
    rewrite Hmap. rewrite Ktypes1. rewrite Hv1. env_proj.
    cbn [vec_list alloc_vec_Vec_new proj1_sig List.map List.app].
    reflexivity. }
  (* the four spaces are the same at line 7, 8 and 9 as they are at the end *)
  assert (K9t : vec_list env.(module_Env_table_types)
                = vec_list e8'.(module_Env_table_types))
    by (apply (env_chain_9_keeps _ (fun e => vec_list e.(module_Env_table_types))
                 _ _ _ _ _ ltac:(keeps_refl) Hchain9)).
  assert (K9f : vec_list env.(module_Env_func_types)
                = vec_list e8'.(module_Env_func_types))
    by (apply (env_chain_9_keeps _ (fun e => vec_list e.(module_Env_func_types))
                 _ _ _ _ _ ltac:(keeps_refl) Hchain9)).
  assert (K9g : vec_list env.(module_Env_global_types)
                = vec_list e8'.(module_Env_global_types))
    by (apply (env_chain_9_keeps _ (fun e => vec_list e.(module_Env_global_types))
                 _ _ _ _ _ ltac:(keeps_refl) Hchain9)).
  assert (K9n : to_Z env.(module_Env_num_imported_globals)
                = to_Z e8'.(module_Env_num_imported_globals))
    by (apply (env_chain_9_keeps _
                 (fun e => to_Z e.(module_Env_num_imported_globals))
                 _ _ _ _ _ ltac:(keeps_refl) Hchain9)).
  assert (Kelems_ok : List.Forall (element_ok env)
                        (vec_list env.(module_Env_elements))).
  { rewrite Kelems. rewrite List.Forall_forall in Hels9.
    apply List.Forall_forall. intros el Hin.
    apply (element_ok_congr e8' env el K9t K9f K9g K9n).
    apply Hels9. exact Hin. }
  assert (Kstart_ok : start_ok env)
    by (apply (start_ok_congr e8' env Kstart K9f); exact Hstart8).
  (* the export section's env is [e6'], and lines 7 to 9 leave the spaces *)
  assert (K7e : vec_list env.(module_Env_exports)
                = vec_list e7'.(module_Env_exports))
    by (apply (env_chain_8_keeps _ (fun e => vec_list e.(module_Env_exports))
                 _ _ _ _ _ ltac:(keeps_refl) Hchain8)).
  assert (K7f : vec_list env.(module_Env_func_types)
                = vec_list e6'.(module_Env_func_types))
    by (rewrite K9f; rewrite Hv8; env_proj; rewrite Hv7; env_proj;
        reflexivity).
  assert (K7t : vec_list env.(module_Env_table_types)
                = vec_list e6'.(module_Env_table_types))
    by (rewrite K9t; rewrite Hv8; env_proj; rewrite Hv7; env_proj;
        reflexivity).
  assert (K7m : vec_list env.(module_Env_mem_types)
                = vec_list e6'.(module_Env_mem_types))
    by (rewrite (env_chain_9_keeps _ (fun e => vec_list e.(module_Env_mem_types))
                   _ _ _ _ _ ltac:(keeps_refl) Hchain9);
        rewrite Hv8; env_proj; rewrite Hv7; env_proj; reflexivity).
  assert (K7g : vec_list env.(module_Env_global_types)
                = vec_list e6'.(module_Env_global_types))
    by (rewrite K9g; rewrite Hv8; env_proj; rewrite Hv7; env_proj;
        reflexivity).
  assert (Kglob_ok : List.Forall (global_ok env)
                       (vec_list env.(module_Env_globals))).
  { rewrite Kglobals. rewrite List.Forall_forall in Hoks6.
    apply List.Forall_forall. intros g Hin.
    apply (global_ok_grow e6' env g []
             (ltac:(rewrite K7g; rewrite app_nil_r; reflexivity))
             (ltac:(rewrite K9n; rewrite Hv8; env_proj; rewrite Hv7; env_proj;
                    reflexivity))).
    apply Hoks6. exact Hin. }
  assert (Kdesc_ok : List.Forall (export_desc_ok env)
                       (vec_list env.(module_Env_exports))).
  { rewrite K7e. rewrite Hl7. rewrite List.Forall_forall in Hdesc7.
    apply List.Forall_app. split.
    - (* nothing was there before the export section *)
      rewrite Hv6. env_proj. rewrite Hv5. env_proj. rewrite Hv4. env_proj.
      rewrite Hv3. env_proj. rewrite Hv2. env_proj. rewrite Hv1. env_proj.
      cbn [vec_list alloc_vec_Vec_new proj1_sig]. apply List.Forall_nil.
    - apply List.Forall_forall. intros e Hin.
      apply (export_desc_ok_congr e6' env e K7f K7t K7m K7g).
      apply Hdesc7. exact Hin. }
  assert (Kdist_ok : exports_distinct env).
  { unfold exports_distinct. rewrite K7e.
    apply Hdist7. unfold exports_distinct.
    rewrite Hv6. env_proj. rewrite Hv5. env_proj. rewrite Hv4. env_proj.
    rewrite Hv3. env_proj. rewrite Hv2. env_proj. rewrite Hv1. env_proj.
    cbn [vec_list alloc_vec_Vec_new proj1_sig List.map]. apply List.NoDup_nil. }
  destruct (funcs_of_exists (List.map translate_idx tidxs) codes
              (ltac:(rewrite List.map_length; rewrite Hcodelen;
                     rewrite Kfti; reflexivity))) as [fs Hfs].
  exists env, code_pos, tail_pos, tl, fs, tabs, mems.
  split; [exact Hvm|].
  (* [destruct ... eqn:] rewrote the first of the three in the goal already *)
  split; [reflexivity|]. split; [exact Hcode|]. split; [exact Htail|].
  split; [rewrite Kimports; exact Ktables|].
  split; [rewrite Kimports; exact Kmems|].
  split; [exact Kfuncs|]. split; [exact Kgts|]. split; [exact Knig|].
  split; [exact Kelems_ok|]. split; [exact Kstart_ok|].
  split; [exact Kdist_ok|]. split; [exact Kdesc_ok|].
  split; [exact Hdataok|].
  split; [exact Kglob_ok|].
  split; [exists codes; split; [exact Hcodety|];
          rewrite Kfti; exact Hfs|].
  unfold module_of.
  rewrite Ktypes, Kglobals, Kelems, Kstart, Kimports, Kexports.
  eapply repr_module_intro.
  - exact Hmagic.
  - exact Hp1.
  - exact Hp2.
  - exact Hp3.
  - exact Hp4.
  - exact Hp5.
  - exact Hp6.
  - exact Hp7.
  - exact Hp8.
  - exact Hp9.
  - exact Hp10.
  - exact Hp11.
  - exact Hend.
  - exact Hfs.
Qed.

Theorem validate_module_repr : forall data vm,
  module_validate_module data = Ok (Core_result_Result_Ok vm) ->
  exists m, repr_module (byte_list data) m.
Proof.
  intros data vm H.
  destruct (validate_module_parts _ _ H)
    as [env [cp [tp [tl [fs [tabs [mems Hrest]]]]]]].
  exists (module_of env fs tabs mems
            (List.map translate_data (vec_list tl.(module_Tail_data)))).
  repeat match goal with
         | [ Hc : _ /\ _ |- _ ] => destruct Hc as [_ Hc]
         end.
  exact Hrest.
Qed.
