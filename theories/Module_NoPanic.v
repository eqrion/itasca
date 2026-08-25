(** * The module decoder cannot panic

    [validate_module] always returns a verdict. Never [Fail_], which is what the
    Aeneas extraction turns a Rust panic into, and never a non-terminating loop.
    [OpIter_NoPanic.v] says the same of one function body; this file says it of
    everything around the bodies, and finishes by calling that theorem.

    Where [validate_body] leans on [MAX_FUNCTION_BYTES], this leans on
    [MAX_MODULE_BYTES], and in the same way. Every position the decoder computes
    is between zero and the input length, so no cursor arithmetic overflows; and
    every vector it builds costs at least one input byte per element, so no
    [Vec::push] can reach [usize_max]. Two exceptions, each with its own bound:
    a function's locals are capped by [MAX_LOCALS] because a local declaration
    is a count rather than a list, and the table and memory vectors are capped
    at one entry by Wasm 1.0 itself.

    The proof is therefore two facts per decoder, stated bottom up:

    - totality: given a cursor inside the input, it returns something;
    - progress: an accepting run leaves the cursor further along than it found
      it, and still inside the input.

    Progress is what pays for the pushes, so the two are not separable. *)

Require Import Primitives.
Import Primitives.
Require Import Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Import Itasca.Aeneas_Specs.
Require Import Itasca.OpIter_State.
Require Import Itasca.OpIter_Decode.
Require Import Itasca.OpIter_Visit.
Require Import Itasca.OpIter_NoPanic.

Open Scope Z_scope.

(* ================================================================== *)
(** ** The one bound everything rests on                               *)
(* ================================================================== *)

(** The input length, which is the bound on every cursor and every vector. *)
Notation dlen data := (to_Z (slice_len data)).

Notation module_bytes := 1073741824.

Lemma max_module_bytes_val : to_Z limits_max_module_bytes = module_bytes.
Proof. reflexivity. Qed.

Lemma max_locals_val : to_Z limits_max_locals = 50000.
Proof. reflexivity. Qed.

(** Room to spare, and the slack is what lets every lemma below say
    [<= module_bytes] and never think about [usize_max] again. *)
Lemma module_bytes_fits : module_bytes + 65536 <= usize_max.
Proof.
  pose proof usize_max_bound as H. rewrite u32_max_val in H. lia.
Qed.

Ltac fits := pose proof module_bytes_fits; lia.

(* ================================================================== *)
(** ** Reading a run of bytes                                          *)
(* ================================================================== *)

(** [have_bytes] subtracts the cursor from the length, so it is the first place
    a cursor past the end would panic rather than reject. *)
Lemma have_bytes_ok : forall data pos n,
  to_Z pos <= dlen data ->
  exists r, module_have_bytes data pos n = Ok r
            /\ (r = Core_result_Result_Ok tt \/
                r = Core_result_Result_Err Error_Error_UnexpectedEof).
Proof.
  intros data pos n Hpos. unfold module_have_bytes.
  destruct (usize_sub_ok (slice_len data) pos (ltac:(lia))) as [d [Hsub Hd]].
  rewrite Hsub. cbn [bind].
  destruct (n s> d); eexists; split; try reflexivity; auto.
Qed.

(** And what it establishes when it accepts. No precondition: a cursor past
    the end makes the subtraction fail, and an accepting run rules that out. *)
Lemma have_bytes_room : forall data pos n,
  module_have_bytes data pos n = Ok (Core_result_Result_Ok tt) ->
  to_Z pos + to_Z n <= dlen data.
Proof.
  intros data pos n H. unfold module_have_bytes in H.
  destruct (usize_sub (slice_len data) pos) as [d|] eqn:Hsub; cbn [bind] in H;
    [|discriminate].
  unfold usize_sub, scalar_sub in Hsub. apply mk_scalar_ok_to_Z in Hsub.
  destruct (n s> d) eqn:Hgt; [discriminate|].
  apply scalar_gtb_false in Hgt. lia.
Qed.

(** [copy_bytes] is the only allocation the decoder makes that is not one
    element per decoded item: it copies a byte range out. The range is inside
    the input, so its length is, and the vector cannot outgrow it. *)
Lemma copy_bytes_loop_ok : forall m data to out i,
  to_Z to <= dlen data ->
  dlen data <= module_bytes ->
  Z.of_nat (List.length (vec_list out)) + (to_Z to - to_Z i) <= module_bytes ->
  to_Z to - to_Z i <= Z.of_nat m ->
  exists v, module_copy_bytes_loop data to out i = Ok v.
Proof.
  induction m as [|m IH]; intros data to out i Hto Hlen Hroom Hmeas;
    unfold module_copy_bytes_loop; rewrite loop_unfold; cbn beta iota;
    destruct (i s>= to) eqn:Hge; [eexists; reflexivity| |eexists; reflexivity|].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    pose proof (usize_nonneg i).
    destruct (slice_index_usize_ok data i) as [b Hidx];
      [rewrite slice_len_spec in Hto; lia|].
    rewrite Hidx. cbn [bind].
    destruct (vec_push_ok out b (ltac:(fits))) as [out' Hpush].
    rewrite Hpush. cbn [bind].
    destruct (usize_add_1_ok i (ltac:(fits))) as [i' [Hadd Hi']].
    rewrite Hadd. cbn [bind].
    apply (IH data to out' i').
    + exact Hto.
    + exact Hlen.
    + rewrite (vec_push_spec _ _ _ Hpush). rewrite List.app_length.
      cbn [List.length]. lia.
    + rewrite Nat2Z.inj_succ in Hmeas. lia.
Qed.

Lemma copy_bytes_ok : forall data from to,
  to_Z from <= to_Z to ->
  to_Z to <= dlen data ->
  dlen data <= module_bytes ->
  exists v, module_copy_bytes data from to = Ok v.
Proof.
  intros data from to Hfrom Hto Hlen. unfold module_copy_bytes.
  destruct (usize_sub_ok to from (ltac:(lia)))
    as [capacity [Hsub Hcapacity]].
  rewrite Hsub. cbn [bind].
  apply (copy_bytes_loop_ok (Z.to_nat (Z.max 0 (to_Z to - to_Z from))) data to
           (alloc_vec_Vec_with_capacity u8 capacity) from).
  - exact Hto.
  - exact Hlen.
  - cbn [alloc_vec_Vec_with_capacity vec_list alloc_vec_Vec_new proj1_sig
         List.length].
    pose proof (usize_nonneg from). lia.
  - rewrite Z2Nat.id by lia. lia.
Qed.

(** The copied range's length, which the caller needs when it turns round and
    validates the bytes. *)
Lemma copy_bytes_length : forall data from to v,
  module_copy_bytes data from to = Ok v ->
  Z.of_nat (List.length (vec_list v)) <= Z.max 0 (to_Z to - to_Z from).
Proof.
  intros data from to v H.
  assert (Hgen : forall m out i,
            to_Z to - to_Z i <= Z.of_nat m ->
            forall v', module_copy_bytes_loop data to out i = Ok v' ->
            Z.of_nat (List.length (vec_list v'))
              <= Z.of_nat (List.length (vec_list out)) + Z.max 0 (to_Z to - to_Z i)).
  { induction m as [|m IH]; intros out i Hmeas v' H';
      unfold module_copy_bytes_loop in H'; rewrite loop_unfold in H';
      cbn beta iota in H'; destruct (i s>= to) eqn:Hge;
      [injection H' as <-; lia | | injection H' as <-; lia |].
    - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
    - apply scalar_geb_false_lt in Hge.
      destruct (slice_index_usize data i) as [b|] eqn:Hidx; cbn [bind] in H';
        [|discriminate].
      destruct (alloc_vec_Vec_push out b) as [out2|] eqn:Hpush;
        cbn [bind] in H'; [|discriminate].
      destruct (usize_add i 1%usize) as [i2|] eqn:Hadd; cbn [bind] in H';
        [|discriminate].
      assert (Hi2 : to_Z i2 = to_Z i + 1).
      { unfold usize_add, scalar_add in Hadd. apply mk_scalar_ok_to_Z in Hadd.
        assert (H1 : to_Z 1%usize = 1) by reflexivity. lia. }
      pose proof (IH out2 i2 (ltac:(cbn in Hmeas; lia)) v' H') as Hle.
      rewrite (vec_push_spec _ _ _ Hpush) in Hle. rewrite List.app_length in Hle.
      cbn [List.length] in Hle. lia. }
  unfold module_copy_bytes in H.
  destruct (usize_sub to from) as [capacity|] eqn:Hsub;
    cbn [bind] in H; [|discriminate].
  pose proof (Hgen (Z.to_nat (Z.max 0 (to_Z to - to_Z from)))
                (alloc_vec_Vec_with_capacity u8 capacity) from
                (ltac:(lia)) v H) as Hle.
  cbn [alloc_vec_Vec_with_capacity vec_list alloc_vec_Vec_new proj1_sig
       List.length] in Hle. lia.
Qed.

(* ================================================================== *)
(** ** Names, and the UTF-8 table                                      *)
(* ================================================================== *)

(** A continuation byte. Total with no precondition at all: it checks the index
    itself before reading. *)
Lemma utf8_cont_ok : forall bytes i lo hi,
  exists r, module_utf8_cont bytes i lo hi = Ok r.
Proof.
  intros bytes i lo hi. unfold module_utf8_cont.
  destruct (i s>= slice_len bytes) eqn:Hge; [eexists; reflexivity|].
  apply scalar_geb_false_lt in Hge. rewrite slice_len_spec in Hge.
  destruct (slice_index_usize_ok bytes i Hge) as [b Hidx].
  rewrite Hidx. cbn [bind].
  destruct (b s< lo); [eexists; reflexivity|].
  destruct (b s> hi); eexists; reflexivity.
Qed.

(** And when it accepts, the byte it read was inside the input. That is where
    the length of a multi-byte sequence comes from: the run of accepted
    continuation bytes is what says the sequence fits. *)
Lemma utf8_cont_inb : forall bytes i lo hi,
  module_utf8_cont bytes i lo hi = Ok (Core_result_Result_Ok tt) ->
  to_Z i < dlen bytes.
Proof.
  intros bytes i lo hi H. unfold module_utf8_cont in H.
  destruct (i s>= slice_len bytes) eqn:Hge; [discriminate|].
  apply scalar_geb_false_lt in Hge. exact Hge.
Qed.

(** [utf8_sequence_len] is one [if] chain with ten arms, differing only in which
    continuation ranges they demand. Both proofs below walk it with one tactic
    rather than naming the arms: the shape of an arm is a cursor step, a
    continuation check, and a literal length. *)
Ltac utf8_goal_step :=
  first
  [ solve [eexists; reflexivity]
  | match goal with
    | [ |- context [usize_add ?a ?b] ] =>
        let q := fresh "q" in let E := fresh "Eadd" in let Q := fresh "Hq" in
        destruct (usize_add_ok a b ltac:(fits)) as [q [E Q]];
        rewrite E; cbn [bind]
    end
  | match goal with
    | [ |- context [module_utf8_cont ?a ?b ?c ?d] ] =>
        let r := fresh "r" in let E := fresh "Econt" in
        let u := fresh "u" in
        destruct (utf8_cont_ok a b c d) as [r E]; rewrite E; cbn [bind];
        destruct r as [u|];
        [ rewrite branch_ok; cbn [bind]
        | rewrite branch_err; cbn [bind]; rewrite from_residual_err;
          cbn [bind] ]
    end
  | match goal with
    | [ |- context [if ?c then _ else _] ] => destruct c
    end ].

Lemma utf8_sequence_len_ok : forall bytes i,
  to_Z i < dlen bytes ->
  dlen bytes <= module_bytes ->
  exists r, module_utf8_sequence_len bytes i = Ok r.
Proof.
  intros bytes i Hi Hlen.
  assert (Hc1 : to_Z 1%usize = 1) by reflexivity.
  assert (Hc2 : to_Z 2%usize = 2) by reflexivity.
  assert (Hc3 : to_Z 3%usize = 3) by reflexivity.
  unfold module_utf8_sequence_len.
  rewrite slice_len_spec in Hi.
  destruct (slice_index_usize_ok bytes i Hi) as [b Hidx].
  rewrite Hidx. cbn [bind].
  rewrite <- slice_len_spec in Hi.
  repeat utf8_goal_step.
Qed.

Ltac utf8_hyp_step H :=
  first
  [ match type of H with
    | context [slice_index_usize ?s ?j] =>
        let b := fresh "b" in let E := fresh "Eidx" in
        destruct (slice_index_usize s j) as [b|] eqn:E; cbn [bind] in H;
          [|discriminate];
        pose proof (slice_index_usize_lt s j b E)
    end
  | match type of H with
    | context [usize_add ?a ?c] =>
        let q := fresh "q" in let E := fresh "Eadd" in
        destruct (usize_add a c) as [q|] eqn:E; cbn [bind] in H;
          [|discriminate];
        unfold usize_add, scalar_add in E; apply mk_scalar_ok_to_Z in E
    end
  | match type of H with
    | context [module_utf8_cont ?a ?b ?c ?d] =>
        let r := fresh "r" in let E := fresh "Econt" in
        let u := fresh "u" in
        destruct (module_utf8_cont a b c d) as [r|] eqn:E; cbn [bind] in H;
          [|discriminate];
        destruct r as [u|];
        [ rewrite branch_ok in H; cbn [bind] in H; destruct u;
          pose proof (utf8_cont_inb _ _ _ _ E)
        | rewrite branch_err in H; cbn [bind] in H;
          rewrite from_residual_err in H; cbn [bind] in H; discriminate ]
    end
  | match type of H with
    | context [if ?c then _ else _] => destruct c
    end ].

(** An accepted sequence is at least one byte long and stops at or before the
    end. That is exactly what [validate_utf8]'s loop needs: the first half is
    its termination measure and the second keeps its cursor in range. *)
Lemma utf8_sequence_len_step : forall bytes i n,
  module_utf8_sequence_len bytes i = Ok (Core_result_Result_Ok n) ->
  1 <= to_Z n /\ to_Z i + to_Z n <= dlen bytes.
Proof.
  intros bytes i n H.
  assert (Hc1 : to_Z 1%usize = 1) by reflexivity.
  assert (Hc2 : to_Z 2%usize = 2) by reflexivity.
  assert (Hc3 : to_Z 3%usize = 3) by reflexivity.
  assert (Hc4 : to_Z 4%usize = 4) by reflexivity.
  unfold module_utf8_sequence_len in H.
  repeat utf8_hyp_step H.
  all: try discriminate.
  all: injection H as Hn; rewrite <- Hn;
       unfold to_Z in *; cbn [proj1_sig] in *; split; lia.
Qed.

(** The [?] operator's error arm, which every decoder in this file has one of
    per read: hand the error back unchanged. *)
Ltac try_err :=
  rewrite branch_err; cbn [bind];
  first [rewrite from_residual_err | rewrite from_residual_op_err];
  cbn [bind]; solve [eexists; reflexivity].

(** The same arm read backwards: a run that accepted did not take it. *)
Ltac err_absurd H :=
  rewrite branch_err in H; cbn [bind] in H;
  first [rewrite from_residual_err in H | rewrite from_residual_op_err in H];
  cbn [bind] in H; discriminate.

(** The loop over a name's bytes. Its measure is the bytes left, which each
    accepted sequence shortens by at least one. *)
Lemma validate_utf8_loop_ok : forall m bytes i,
  dlen bytes - to_Z i <= Z.of_nat m ->
  dlen bytes <= module_bytes ->
  exists r, module_validate_utf8_loop bytes i = Ok r.
Proof.
  induction m as [|m IH]; intros bytes i Hmeas Hlen;
    unfold module_validate_utf8_loop; rewrite loop_unfold; cbn beta iota;
    destruct (i s>= slice_len bytes) eqn:Hge;
    [eexists; reflexivity| |eexists; reflexivity|].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (utf8_sequence_len_ok bytes i Hge Hlen) as [r Hr].
    rewrite Hr. cbn [bind]. destruct r as [n|e]; [|try_err].
    rewrite branch_ok. cbn [bind].
    destruct (utf8_sequence_len_step bytes i n Hr) as [Hn1 Hn2].
    destruct (usize_add_ok i n (ltac:(fits))) as [j [Hadd Hj]].
    rewrite Hadd. cbn [bind].
    apply (IH bytes j); [|exact Hlen].
    rewrite Nat2Z.inj_succ in Hmeas. lia.
Qed.

Lemma validate_utf8_ok : forall bytes,
  dlen bytes <= module_bytes ->
  exists r, module_validate_utf8 bytes = Ok r.
Proof.
  intros bytes Hlen. unfold module_validate_utf8.
  apply (validate_utf8_loop_ok (Z.to_nat (dlen bytes)) bytes 0%usize);
    [|exact Hlen].
  assert (H0 : to_Z 0%usize = 0) by reflexivity.
  rewrite Z2Nat.id by (pose proof (usize_nonneg (slice_len bytes)); lia). lia.
Qed.

(* ================================================================== *)
(** ** Names and section headers                                      *)
(* ================================================================== *)

Lemma decode_name_ok : forall data pos,
  to_Z pos <= dlen data ->
  dlen data <= module_bytes ->
  exists r, module_decode_name data pos = Ok r.
Proof.
  intros data pos Hpos Hlen. unfold module_decode_name.
  destruct (read_u32_leb_ok data pos) as [r Hr]. rewrite Hr. cbn [bind].
  destruct r as [[len p]|e]; [|try_err].
  rewrite branch_ok. cbn [bind].
  pose proof (read_u32_leb_le_len _ _ _ _ Hr) as Hp.
  destruct (scalar_cast_u32_usize len) as [n [Hcast Hn]].
  rewrite Hcast. cbn [bind].
  destruct (have_bytes_ok data p n Hp) as [rh [Hh Hcase]].
  rewrite Hh. cbn [bind].
  destruct Hcase as [-> | ->]; [|try_err].
  rewrite branch_ok. cbn [bind].
  pose proof (have_bytes_room data p n Hh) as Hroom.
  pose proof (usize_nonneg n).
  destruct (usize_add_ok p n (ltac:(fits))) as [q [Hadd Hq]].
  rewrite Hadd. cbn [bind].
  destruct (copy_bytes_ok data p q (ltac:(lia)) (ltac:(lia)) Hlen)
    as [bs Hcopy].
  rewrite Hcopy. cbn [bind].
  pose proof (copy_bytes_length _ _ _ _ Hcopy) as Hbl.
  rewrite vec_deref_spec.
  destruct (validate_utf8_ok bs) as [ru Hu].
  { rewrite slice_len_spec. rewrite Z.max_r in Hbl by lia.
    pose proof (usize_nonneg p). lia. }
  rewrite Hu. cbn [bind]. destruct ru as [u|e]; [|try_err].
  rewrite branch_ok. cbn [bind]. eexists. reflexivity.
Qed.

(** A name is at least its own length prefix long, and stops inside the input.
    Every vector the decoder builds one-per-name inherits its bound from the
    first half. *)
Lemma decode_name_step : forall data pos bs p',
  module_decode_name data pos = Ok (Core_result_Result_Ok (bs, p')) ->
  to_Z pos <= dlen data ->
  to_Z pos < to_Z p' /\ to_Z p' <= dlen data.
Proof.
  intros data pos bs p' H Hpos. unfold module_decode_name in H.
  destruct (reader_read_u32_leb data pos) as [r|] eqn:Hr; cbn [bind] in H;
    [|discriminate].
  destruct r as [[len p]|e].
  2: err_absurd H.
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_u32_leb_lt _ _ _ _ Hr) as Hlt.
  pose proof (read_u32_leb_le_len _ _ _ _ Hr) as Hple.
  destruct (scalar_cast U32 Usize len) as [n|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  destruct (module_have_bytes data p n) as [rh|] eqn:Hh; cbn [bind] in H;
    [|discriminate].
  destruct rh as [u|e].
  2: err_absurd H.
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (have_bytes_room data p n Hh) as Hroom.
  destruct (usize_add p n) as [q|] eqn:Hadd; cbn [bind] in H; [|discriminate].
  unfold usize_add, scalar_add in Hadd. apply mk_scalar_ok_to_Z in Hadd.
  pose proof (usize_nonneg n).
  destruct (module_copy_bytes data p q) as [bs2|] eqn:Hcopy; cbn [bind] in H;
    [|discriminate].
  destruct (module_validate_utf8 (alloc_vec_Vec_deref bs2)) as [ru|] eqn:Hu;
    cbn [bind] in H; [|discriminate].
  destruct ru as [u|e].
  2: err_absurd H.
  rewrite branch_ok in H. cbn [bind] in H.
  injection H as _ <-. lia.
Qed.

Lemma decode_custom_section_ok : forall data pos end_,
  to_Z pos <= dlen data ->
  dlen data <= module_bytes ->
  exists r, module_decode_custom_section data pos end_ = Ok r.
Proof.
  intros data pos end_ Hpos Hlen. unfold module_decode_custom_section.
  destruct (decode_name_ok data pos Hpos Hlen) as [r Hr]. rewrite Hr. cbn [bind].
  destruct r as [[bs p]|e]; [|try_err].
  rewrite branch_ok. cbn [bind].
  destruct (p s> end_); eexists; reflexivity.
Qed.

(** Spec 5.5.2's framing. What the caller gets is the pair of positions
    delimiting the contents, and both are inside the input: [have_bytes] is
    what makes the second one so. *)
Lemma read_section_header_ok : forall data pos,
  to_Z pos <= dlen data ->
  exists r, module_read_section_header data pos = Ok r.
Proof.
  intros data pos Hpos. unfold module_read_section_header.
  destruct (read_byte_total data pos) as [r Hr]. rewrite Hr. cbn [bind].
  destruct r as [[id p]|e]; [|try_err].
  rewrite branch_ok. cbn [bind].
  destruct (read_u32_leb_ok data p) as [r1 Hr1]. rewrite Hr1. cbn [bind].
  destruct r1 as [[size q]|e]; [|try_err].
  rewrite branch_ok. cbn [bind].
  pose proof (read_u32_leb_le_len _ _ _ _ Hr1) as Hq.
  destruct (scalar_cast_u32_usize size) as [n [Hcast Hn]].
  rewrite Hcast. cbn [bind].
  destruct (have_bytes_ok data q n Hq) as [rh [Hh Hcase]].
  rewrite Hh. cbn [bind].
  destruct Hcase as [-> | ->]; [|try_err].
  rewrite branch_ok. cbn [bind].
  pose proof (have_bytes_room data q n Hh) as Hroom.
  pose proof (usize_le_max (slice_len data)).
  destruct (usize_add_ok q n (ltac:(lia))) as [e2 [Hadd He2]].
  rewrite Hadd. cbn [bind]. eexists. reflexivity.
Qed.

Lemma read_section_header_step : forall data pos id start end_,
  module_read_section_header data pos = Ok (Core_result_Result_Ok (id, start, end_)) ->
  to_Z pos < to_Z start /\ to_Z start <= to_Z end_ /\ to_Z end_ <= dlen data.
Proof.
  intros data pos id start end_ H. unfold module_read_section_header in H.
  destruct (reader_read_byte data pos) as [r|] eqn:Hr; cbn [bind] in H;
    [|discriminate].
  destruct r as [[id0 p]|e]; [|err_absurd H].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (read_byte_ok _ _ _ _ Hr) as [_ Hp].
  pose proof (read_byte_le_len _ _ _ _ Hr) as Hple.
  destruct (reader_read_u32_leb data p) as [r1|] eqn:Hr1; cbn [bind] in H;
    [|discriminate].
  destruct r1 as [[size q]|e]; [|err_absurd H].
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_u32_leb_lt _ _ _ _ Hr1) as Hqlt.
  pose proof (read_u32_leb_le_len _ _ _ _ Hr1) as Hqle.
  destruct (scalar_cast U32 Usize size) as [n|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  destruct (module_have_bytes data q n) as [rh|] eqn:Hh; cbn [bind] in H;
    [|discriminate].
  destruct rh as [u|e]; [|err_absurd H]. destruct u.
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (have_bytes_room data q n Hh) as Hroom.
  destruct (usize_add q n) as [e2|] eqn:Hadd; cbn [bind] in H; [|discriminate].
  unfold usize_add, scalar_add in Hadd. apply mk_scalar_ok_to_Z in Hadd.
  pose proof (usize_nonneg n).
  injection H as _ <- <-. lia.
Qed.

(** The header's own extent, which is what a streaming consumer waits for
    before reading it: an id byte and a size, so the contents start at most six
    bytes along. [read_section_header_step] bounds the header by the input;
    this bounds it by its own start. *)
Lemma read_section_header_span : forall data pos id start end_,
  module_read_section_header data pos
    = Ok (Core_result_Result_Ok (id, start, end_)) ->
  to_Z start <= to_Z pos + 1 + to_Z limits_max_leb_bytes.
Proof.
  intros data pos id start end_ H. unfold module_read_section_header in H.
  destruct (reader_read_byte data pos) as [r|] eqn:Hr; cbn [bind] in H;
    [|discriminate].
  destruct r as [[id0 p]|e]; [|err_absurd H].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (read_byte_ok _ _ _ _ Hr) as [_ Hp].
  destruct (reader_read_u32_leb data p) as [r1|] eqn:Hr1; cbn [bind] in H;
    [|discriminate].
  destruct r1 as [[size q]|e]; [|err_absurd H].
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_u32_leb_span _ _ _ _ Hr1) as Hq.
  destruct (scalar_cast U32 Usize size) as [n|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  destruct (module_have_bytes data q n) as [rh|] eqn:Hh; cbn [bind] in H;
    [|discriminate].
  destruct rh as [u|e]; [|err_absurd H]. destruct u.
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (usize_add q n) as [e2|] eqn:Hadd; cbn [bind] in H; [|discriminate].
  injection H as _ <- _. lia.
Qed.

(** The magic number and the version. Eight [read_byte]s and two comparisons,
    with nothing to say about them beyond that each read is total. *)
Lemma read_header_ok : forall data,
  exists r, module_read_header data = Ok r.
Proof.
  intros data. unfold module_read_header.
  repeat first
    [ match goal with
      | [ |- context [if ?c then _ else _] ] => destruct c
      end
    | match goal with
      | [ |- context [reader_read_byte data ?p] ] =>
          let r := fresh "r" in let E := fresh "Er" in
          let b := fresh "b" in let q := fresh "q" in
          destruct (read_byte_total data p) as [r E]; rewrite E; cbn [bind];
          destruct r as [[b q]|];
          [ rewrite branch_ok; cbn [bind] | try_err_rw ]
      end ].
  all: eexists; reflexivity.
Qed.

Lemma read_header_step : forall data p,
  module_read_header data = Ok (Core_result_Result_Ok p) ->
  to_Z p <= dlen data.
Proof.
  intros data p H. unfold module_read_header in H.
  repeat first
    [ match type of H with
      | context [if ?c then _ else _] => destruct c
      end
    | match type of H with
      | context [reader_read_byte data ?q] =>
          let r := fresh "r" in let E := fresh "Er" in
          let b := fresh "b" in let q1 := fresh "q" in
          destruct (reader_read_byte data q) as [r|] eqn:E;
            cbn [bind] in H; [|discriminate];
          destruct r as [[b q1]|];
          [ rewrite branch_ok in H; cbn [bind] in H;
            pose proof (read_byte_le_len _ _ _ _ E)
          | try_err_rw_in H ]
      end ].
  all: try discriminate.
  all: injection H as <-; assumption.
Qed.

(* ================================================================== *)
(** ** The type decoders                                              *)
(* ================================================================== *)

(** Spec 3.2.1's range check. Comparisons only, so it cannot fail. *)
Lemma validate_limits_ok : forall lim range,
  exists r, limits_validate_limits lim range = Ok r.
Proof.
  intros lim range. unfold limits_validate_limits.
  destruct (types_Limits_min lim s> range); [eexists; reflexivity|].
  destruct (types_Limits_max lim) as [mx|]; [|eexists; reflexivity].
  destruct (mx s> range); [eexists; reflexivity|].
  destruct (types_Limits_min lim s> mx); eexists; reflexivity.
Qed.

(** Below this point a decoder is a chain of reads and comparisons, and both
    directions of the proof are a walk over that chain. [read_step] takes one
    step of it forwards, [read_step_in] one step backwards while collecting
    what the step says about the cursor. *)
Ltac if_step :=
  match goal with [ |- context [if ?c then _ else _] ] => destruct c end.

Ltac opt_step :=
  match goal with
  | [ |- context [match ?x with | Some _ => _ | None => _ end] ] =>
      match type of x with option _ => destruct x end
  end.

Ltac pair_of L :=
  let r := fresh "r" in let E := fresh "E" in
  let a := fresh "a" in let q := fresh "q" in
  destruct L as [r E]; rewrite E; cbn [bind];
  destruct r as [[a q]|]; [rewrite branch_ok; cbn [bind] | try_err_rw].

Ltac unit_of L :=
  let r := fresh "r" in let E := fresh "E" in let u := fresh "u" in
  destruct L as [r E]; rewrite E; cbn [bind];
  destruct r as [u|]; [rewrite branch_ok; cbn [bind]; destruct u | try_err_rw].

Ltac read_step :=
  first
  [ if_step
  | opt_step
  | match goal with
    | [ |- context [reader_read_byte ?d ?p] ] => pair_of (read_byte_total d p)
    | [ |- context [reader_read_u32_leb ?d ?p] ] => pair_of (read_u32_leb_ok d p)
    | [ |- context [reader_read_s32_leb ?d ?p] ] => pair_of (read_s32_leb_ok d p)
    | [ |- context [reader_read_s64_leb ?d ?p] ] => pair_of (read_s64_leb_ok d p)
    | [ |- context [reader_read_f32_bits ?d ?p] ] =>
        pair_of (read_f32_bits_ok d p)
    | [ |- context [reader_read_f64_bits ?d ?p] ] =>
        pair_of (read_f64_bits_ok d p)
    | [ |- context [limits_validate_limits ?l ?rg] ] =>
        unit_of (validate_limits_ok l rg)
    end ].

Ltac reads := repeat read_step; try solve [eexists; reflexivity].

Ltac if_step_in H :=
  match type of H with context [if ?c then _ else _] => destruct c end.

Ltac opt_step_in H :=
  match type of H with
  | context [match ?x with | Some _ => _ | None => _ end] =>
      match type of x with option _ => destruct x end
  end.

Ltac read_step_in H :=
  first
  [ if_step_in H
  | opt_step_in H
  | match type of H with
    | context [reader_read_byte ?d ?p] =>
        let r := fresh "r" in let E := fresh "E" in
        let a := fresh "a" in let q := fresh "q" in
        destruct (reader_read_byte d p) as [r|] eqn:E; cbn [bind] in H;
          [|discriminate];
        destruct r as [[a q]|];
        [ rewrite branch_ok in H; cbn [bind] in H;
          pose proof (read_byte_le_len _ _ _ _ E);
          pose proof (proj2 (read_byte_ok _ _ _ _ E))
        | try_err_rw_in H ]
    | context [reader_read_u32_leb ?d ?p] =>
        let r := fresh "r" in let E := fresh "E" in
        let a := fresh "a" in let q := fresh "q" in
        destruct (reader_read_u32_leb d p) as [r|] eqn:E; cbn [bind] in H;
          [|discriminate];
        destruct r as [[a q]|];
        [ rewrite branch_ok in H; cbn [bind] in H;
          pose proof (read_u32_leb_le_len _ _ _ _ E);
          pose proof (read_u32_leb_lt _ _ _ _ E)
        | try_err_rw_in H ]
    | context [reader_read_s32_leb ?d ?p] =>
        let r := fresh "r" in let E := fresh "E" in
        let a := fresh "a" in let q := fresh "q" in
        destruct (reader_read_s32_leb d p) as [r|] eqn:E; cbn [bind] in H;
          [|discriminate];
        destruct r as [[a q]|];
        [ rewrite branch_ok in H; cbn [bind] in H;
          pose proof (read_s32_leb_le_len _ _ _ _ E);
          pose proof (read_s32_leb_mono _ _ _ _ E)
        | try_err_rw_in H ]
    | context [reader_read_s64_leb ?d ?p] =>
        let r := fresh "r" in let E := fresh "E" in
        let a := fresh "a" in let q := fresh "q" in
        destruct (reader_read_s64_leb d p) as [r|] eqn:E; cbn [bind] in H;
          [|discriminate];
        destruct r as [[a q]|];
        [ rewrite branch_ok in H; cbn [bind] in H;
          pose proof (read_s64_leb_le_len _ _ _ _ E);
          pose proof (read_s64_leb_mono _ _ _ _ E)
        | try_err_rw_in H ]
    | context [reader_read_f32_bits ?d ?p] =>
        let r := fresh "r" in let E := fresh "E" in
        let a := fresh "a" in let q := fresh "q" in
        destruct (reader_read_f32_bits d p) as [r|] eqn:E; cbn [bind] in H;
          [|discriminate];
        destruct r as [[a q]|];
        [ rewrite branch_ok in H; cbn [bind] in H;
          pose proof (read_f32_bits_le_len _ _ _ _ E);
          pose proof (read_f32_bits_mono _ _ _ _ E)
        | try_err_rw_in H ]
    | context [reader_read_f64_bits ?d ?p] =>
        let r := fresh "r" in let E := fresh "E" in
        let a := fresh "a" in let q := fresh "q" in
        destruct (reader_read_f64_bits d p) as [r|] eqn:E; cbn [bind] in H;
          [|discriminate];
        destruct r as [[a q]|];
        [ rewrite branch_ok in H; cbn [bind] in H;
          pose proof (read_f64_bits_le_len _ _ _ _ E);
          pose proof (read_f64_bits_mono _ _ _ _ E)
        | try_err_rw_in H ]
    | context [limits_validate_limits ?l ?rg] =>
        let r := fresh "r" in let E := fresh "E" in let u := fresh "u" in
        destruct (limits_validate_limits l rg) as [r|] eqn:E; cbn [bind] in H;
          [|discriminate];
        destruct r as [u|];
        [ rewrite branch_ok in H; cbn [bind] in H; destruct u
        | try_err_rw_in H ]
    end ].

Ltac reads_in H := repeat read_step_in H; try discriminate.

Lemma decode_value_type_ok : forall data pos,
  exists r, module_decode_value_type data pos = Ok r.
Proof. intros data pos. unfold module_decode_value_type. reads. Qed.

Lemma decode_value_type_step : forall data pos vt p',
  module_decode_value_type data pos = Ok (Core_result_Result_Ok (vt, p')) ->
  to_Z pos < to_Z p' /\ to_Z p' <= dlen data.
Proof.
  intros data pos vt p' H. unfold module_decode_value_type in H.
  reads_in H. all: injection H as _ <-; lia.
Qed.

Lemma decode_limits_ok : forall data pos,
  exists r, module_decode_limits data pos = Ok r.
Proof. intros data pos. unfold module_decode_limits. reads. Qed.

Lemma decode_limits_step : forall data pos lim p',
  module_decode_limits data pos = Ok (Core_result_Result_Ok (lim, p')) ->
  to_Z pos < to_Z p' /\ to_Z p' <= dlen data.
Proof.
  intros data pos lim p' H. unfold module_decode_limits in H.
  reads_in H. all: injection H as _ <-; lia.
Qed.

(** One layer up: the same walk, now able to step through a type decoder as
    well as a reader. *)
Ltac type_step :=
  first
  [ match goal with
    | [ |- context [module_decode_limits ?d ?p] ] =>
        pair_of (decode_limits_ok d p)
    | [ |- context [module_decode_value_type ?d ?p] ] =>
        pair_of (decode_value_type_ok d p)
    end
  | read_step ].

Ltac type_reads := repeat type_step; try solve [eexists; reflexivity].

Ltac type_step_in H :=
  first
  [ match type of H with
    | context [module_decode_limits ?d ?p] =>
        let r := fresh "r" in let E := fresh "E" in
        let a := fresh "a" in let q := fresh "q" in
        destruct (module_decode_limits d p) as [r|] eqn:E; cbn [bind] in H;
          [|discriminate];
        destruct r as [[a q]|];
        [ rewrite branch_ok in H; cbn [bind] in H;
          pose proof (decode_limits_step _ _ _ _ E)
        | try_err_rw_in H ]
    | context [module_decode_value_type ?d ?p] =>
        let r := fresh "r" in let E := fresh "E" in
        let a := fresh "a" in let q := fresh "q" in
        destruct (module_decode_value_type d p) as [r|] eqn:E; cbn [bind] in H;
          [|discriminate];
        destruct r as [[a q]|];
        [ rewrite branch_ok in H; cbn [bind] in H;
          pose proof (decode_value_type_step _ _ _ _ E)
        | try_err_rw_in H ]
    end
  | read_step_in H ].

Ltac type_reads_in H := repeat type_step_in H; try discriminate.

Lemma decode_mem_type_ok : forall data pos,
  exists r, module_decode_mem_type data pos = Ok r.
Proof. intros data pos. unfold module_decode_mem_type. type_reads. Qed.

Lemma decode_mem_type_step : forall data pos mt p',
  module_decode_mem_type data pos = Ok (Core_result_Result_Ok (mt, p')) ->
  to_Z pos < to_Z p' /\ to_Z p' <= dlen data.
Proof.
  intros data pos mt p' H. unfold module_decode_mem_type in H.
  type_reads_in H. all: injection H as _ <-; lia.
Qed.

Lemma decode_table_type_ok : forall data pos,
  exists r, module_decode_table_type data pos = Ok r.
Proof. intros data pos. unfold module_decode_table_type. type_reads. Qed.

Lemma decode_table_type_step : forall data pos tt p',
  module_decode_table_type data pos = Ok (Core_result_Result_Ok (tt, p')) ->
  to_Z pos < to_Z p' /\ to_Z p' <= dlen data.
Proof.
  intros data pos tt p' H. unfold module_decode_table_type in H.
  type_reads_in H. all: injection H as _ <-; lia.
Qed.

Lemma decode_global_type_ok : forall data pos,
  exists r, module_decode_global_type data pos = Ok r.
Proof. intros data pos. unfold module_decode_global_type. type_reads. Qed.

Lemma decode_global_type_step : forall data pos gt p',
  module_decode_global_type data pos = Ok (Core_result_Result_Ok (gt, p')) ->
  to_Z pos < to_Z p' /\ to_Z p' <= dlen data.
Proof.
  intros data pos gt p' H. unfold module_decode_global_type in H.
  type_reads_in H. all: injection H as _ <-; lia.
Qed.

(* ================================================================== *)
(** ** Vectors                                                        *)
(* ================================================================== *)

(** Every loop from here down builds a vector, and each of them needs both
    facts at once: that it returns, and that what it returned keeps the cursor
    and the vector in step. Proving them together is one induction rather than
    two, and the second is stated as a property of the result so the [Err] arms
    discharge it by [discriminate].

    The invariant is [length out <= to_Z q]: an element costs a byte, and the
    cursor counts the bytes. With the cursor bounded by [module_bytes] that is
    what keeps [Vec::push] away from [usize_max]. *)
(** The visitor-carrying functions report a pair, so an exit has one existential
    more than the rest of the file's do. *)
Ltac finish_post :=
  solve [ eexists; split; [reflexivity | intros; discriminate]
        | eexists; eexists; split; [reflexivity | intros; discriminate] ].

Ltac try_err_post := try_err_rw; finish_post.

Lemma decode_value_types_loop_ok : forall m data count out q i,
  to_Z count - to_Z i <= Z.of_nat m ->
  Z.of_nat (List.length (vec_list out)) <= to_Z q ->
  to_Z q <= dlen data ->
  dlen data <= module_bytes ->
  exists r, module_decode_value_types_loop data count out q i = Ok r
            /\ forall out' q', r = Core_result_Result_Ok (out', q') ->
                 to_Z q <= to_Z q' /\ to_Z q' <= dlen data
                 /\ Z.of_nat (List.length (vec_list out')) <= to_Z q'.
Proof.
  induction m as [|m IH]; intros data count out q i Hmeas Hacc Hq Hlen;
    unfold module_decode_value_types_loop; rewrite loop_unfold; cbn beta iota;
    destruct (i s>= count) eqn:Hge;
    [ eexists; split; [reflexivity|]; intros ? ? Hc; injection Hc as <- <-;
      repeat split; lia
    | | eexists; split; [reflexivity|]; intros ? ? Hc; injection Hc as <- <-;
        repeat split; lia
    | ].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (decode_value_type_ok data q) as [r Hr]. rewrite Hr. cbn [bind].
    destruct r as [[vt q1]|e]; [|try_err_post].
    rewrite branch_ok. cbn [bind].
    destruct (decode_value_type_step _ _ _ _ Hr) as [Hlt Hq1].
    destruct (vec_push_ok out vt (ltac:(fits))) as [out2 Hpush].
    rewrite Hpush. cbn [bind].
    pose proof (u32_bounds count).
    assert (Hu1 : to_Z 1%u32 = 1) by reflexivity.
    destruct (u32_add_ok i 1%u32 (ltac:(lia))) as [i2 [Hadd Hi2]].
    rewrite Hadd. cbn [bind].
    destruct (IH data count out2 q1 i2) as [r2 [Hr2 Hpost]].
    + rewrite Nat2Z.inj_succ in Hmeas. lia.
    + rewrite (vec_push_spec _ _ _ Hpush). rewrite List.app_length.
      cbn [List.length]. lia.
    + exact Hq1.
    + exact Hlen.
    + exists r2. split; [exact Hr2|].
      intros out' q' Hc. destruct (Hpost _ _ Hc) as [A [B C]].
      repeat split; lia.
Qed.

Lemma decode_value_types_ok : forall data pos,
  to_Z pos <= dlen data ->
  dlen data <= module_bytes ->
  exists r, module_decode_value_types data pos = Ok r
            /\ forall out q', r = Core_result_Result_Ok (out, q') ->
                 to_Z pos < to_Z q' /\ to_Z q' <= dlen data
                 /\ Z.of_nat (List.length (vec_list out)) <= to_Z q'.
Proof.
  intros data pos Hpos Hlen. unfold module_decode_value_types.
  destruct (read_u32_leb_ok data pos) as [r Hr]. rewrite Hr. cbn [bind].
  destruct r as [[count p]|e]; [|try_err_post].
  rewrite branch_ok. cbn [bind].
  pose proof (read_u32_leb_lt _ _ _ _ Hr) as Hlt.
  pose proof (read_u32_leb_le_len _ _ _ _ Hr) as Hple.
  destruct (decode_value_types_loop_ok (Z.to_nat (to_Z count)) data count
              (alloc_vec_Vec_new types_ValueType_t) p 0%u32) as [r2 [Hr2 Hpost]].
  - assert (H0 : to_Z 0%u32 = 0) by reflexivity.
    pose proof (u32_bounds count). rewrite Z2Nat.id by lia. lia.
  - cbn [vec_list alloc_vec_Vec_new proj1_sig List.length].
    pose proof (usize_nonneg p). lia.
  - exact Hple.
  - exact Hlen.
  - exists r2. split; [exact Hr2|].
    intros out q' Hc. destruct (Hpost _ _ Hc) as [A [B C]]. repeat split; lia.
Qed.

(** The three copying loops. None of them reads input, so each is bounded by
    the length of what it is copying rather than by the cursor, and each
    reports the length it produced because the next one needs it. *)
Lemma copy_value_types_loop_ok : forall m src out i,
  to_Z (slice_len src) - to_Z i <= Z.of_nat m ->
  to_Z i <= to_Z (slice_len src) ->
  Z.of_nat (List.length (vec_list out))
    + (to_Z (slice_len src) - to_Z i) <= usize_max ->
  exists v, module_copy_value_types_loop src out i = Ok v
            /\ Z.of_nat (List.length (vec_list v))
               = Z.of_nat (List.length (vec_list out))
                 + (to_Z (slice_len src) - to_Z i).
Proof.
  induction m as [|m IH]; intros src out i Hmeas Hi Hroom;
    unfold module_copy_value_types_loop; rewrite loop_unfold; cbn beta iota;
    destruct (i s>= slice_len src) eqn:Hge;
    [ apply scalar_geb_true_ge in Hge; eexists; split; [reflexivity | lia]
    | | apply scalar_geb_true_ge in Hge; eexists; split; [reflexivity | lia]
    | ].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (slice_index_usize_ok src i) as [vt Hidx];
      [rewrite slice_len_spec in Hge; lia|].
    rewrite Hidx. cbn [bind].
    destruct (vec_push_ok out vt (ltac:(lia))) as [out2 Hpush].
    rewrite Hpush. cbn [bind].
    pose proof (usize_le_max (slice_len src)).
    destruct (usize_add_1_ok i (ltac:(lia))) as [i2 [Hadd Hi2]].
    rewrite Hadd. cbn [bind].
    destruct (IH src out2 i2) as [v [Hv Hlv]].
    + rewrite Nat2Z.inj_succ in Hmeas. lia.
    + lia.
    + rewrite (vec_push_spec _ _ _ Hpush). rewrite List.app_length.
      cbn [List.length]. lia.
    + exists v. split; [exact Hv|].
      rewrite Hlv. rewrite (vec_push_spec _ _ _ Hpush).
      rewrite List.app_length. cbn [List.length]. lia.
Qed.

Lemma copy_value_types_ok : forall src,
  exists v, module_copy_value_types src = Ok v
            /\ Z.of_nat (List.length (vec_list v)) = to_Z (slice_len src).
Proof.
  intros src. unfold module_copy_value_types.
  pose proof (usize_nonneg (slice_len src)).
  pose proof (usize_le_max (slice_len src)).
  assert (Hz : to_Z 0%usize = 0) by reflexivity.
  destruct (copy_value_types_loop_ok (Z.to_nat (to_Z (slice_len src))) src
              (alloc_vec_Vec_new types_ValueType_t) 0%usize) as [v [Hv Hlv]].
  - rewrite Z2Nat.id by lia. lia.
  - lia.
  - cbn [vec_list alloc_vec_Vec_new proj1_sig List.length]. lia.
  - exists v. split; [exact Hv|].
    rewrite Hlv. cbn [vec_list alloc_vec_Vec_new proj1_sig List.length]. lia.
Qed.

Lemma single_result_ok : forall results,
  exists r, module_single_result results = Ok r.
Proof.
  intros results. unfold module_single_result.
  destruct (slice_len results s= 0%usize) eqn:Hz; [eexists; reflexivity|].
  apply scalar_eqb_false in Hz.
  destruct (slice_index_usize_ok results 0%usize) as [vt Hidx].
  { rewrite slice_len_spec in Hz.
    assert (H0 : to_Z 0%usize = 0) by reflexivity. lia. }
  rewrite Hidx. cbn [bind]. eexists. reflexivity.
Qed.

Lemma copy_params_loop_ok : forall m params locals i,
  to_Z (slice_len params) - to_Z i <= Z.of_nat m ->
  to_Z i <= to_Z (slice_len params) ->
  Z.of_nat (List.length (locals_list locals))
    + (to_Z (slice_len params) - to_Z i) <= usize_max ->
  exists v, module_decode_and_build_locals_loop0 params locals i = Ok v
    /\ Z.of_nat (List.length (locals_list v))
       = Z.of_nat (List.length (locals_list locals))
         + (to_Z (slice_len params) - to_Z i).
Proof.
  induction m as [|m IH]; intros params locals i Hmeas Hi Hroom;
    unfold module_decode_and_build_locals_loop0; rewrite loop_unfold;
    cbn beta iota; destruct (i s>= slice_len params) eqn:Hge;
    [ apply scalar_geb_true_ge in Hge; eexists; split; [reflexivity|lia]
    | | apply scalar_geb_true_ge in Hge; eexists; split; [reflexivity|lia]
    | ].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (slice_index_usize_ok params i) as [vt Hidx];
      [rewrite slice_len_spec in Hge; lia|].
    rewrite Hidx. cbn [bind].
    destruct (locals_stack_push_total locals vt ltac:(lia))
      as [locals2 Hpush].
    rewrite Hpush. cbn [bind].
    pose proof (usize_le_max (slice_len params)).
    destruct (usize_add_1_ok i (ltac:(lia))) as [i2 [Hadd Hi2]].
    rewrite Hadd. cbn [bind].
    destruct (IH params locals2 i2) as [v [Hv Hlv]].
    + rewrite Nat2Z.inj_succ in Hmeas. lia.
    + lia.
    + rewrite (locals_stack_push_spec _ _ _ Hpush).
      rewrite List.app_length. cbn [List.length]. lia.
    + exists v. split; [exact Hv|].
      rewrite Hlv, (locals_stack_push_spec _ _ _ Hpush).
      rewrite List.app_length. cbn [List.length]. lia.
Qed.


Lemma push_locals_loop_ok : forall m out count vt i,
  to_Z count - to_Z i <= Z.of_nat m ->
  to_Z i <= to_Z count ->
  Z.of_nat (List.length (locals_list out)) + (to_Z count - to_Z i)
    <= usize_max ->
  exists v, module_push_locals_loop out count vt i = Ok v
    /\ Z.of_nat (List.length (locals_list v))
       = Z.of_nat (List.length (locals_list out)) + (to_Z count - to_Z i).
Proof.
  induction m as [|m IH]; intros out count vt i Hmeas Hi Hroom;
    unfold module_push_locals_loop; rewrite loop_unfold; cbn beta iota;
    destruct (i s>= count) eqn:Hge;
    [ apply scalar_geb_true_ge in Hge; eexists; split; [reflexivity|lia]
    | | apply scalar_geb_true_ge in Hge; eexists; split; [reflexivity|lia]
    | ].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (locals_stack_push_total out vt ltac:(lia)) as [out2 Hpush].
    rewrite Hpush. cbn [bind].
    assert (Hu1 : to_Z 1%u32 = 1) by reflexivity.
    pose proof (u32_bounds count).
    destruct (u32_add_ok i 1%u32 (ltac:(lia))) as [i2 [Hadd Hi2]].
    rewrite Hadd. cbn [bind].
    destruct (IH out2 count vt i2) as [v [Hv Hlv]].
    + rewrite Nat2Z.inj_succ in Hmeas. lia.
    + lia.
    + rewrite (locals_stack_push_spec _ _ _ Hpush).
      rewrite List.app_length. cbn [List.length]. lia.
    + exists v. split; [exact Hv|].
      rewrite Hlv, (locals_stack_push_spec _ _ _ Hpush).
      rewrite List.app_length. cbn [List.length]. lia.
Qed.

Lemma push_locals_ok : forall out count vt,
  Z.of_nat (List.length (locals_list out)) + to_Z count <= usize_max ->
  exists v, module_push_locals out count vt = Ok v
    /\ Z.of_nat (List.length (locals_list v))
       = Z.of_nat (List.length (locals_list out)) + to_Z count.
Proof.
  intros out count vt Hroom. unfold module_push_locals.
  assert (H0 : to_Z 0%u32 = 0) by reflexivity.
  pose proof (u32_bounds count).
  destruct (push_locals_loop_ok (Z.to_nat (to_Z count))
    out count vt 0%u32) as [v [Hv Hlv]].
  - rewrite Z2Nat.id by lia. lia.
  - lia.
  - lia.
  - exists v. split; [exact Hv|lia].
Qed.

Lemma decode_and_build_locals_loop_ok :
  forall m data groups locals declared_len q g,
  to_Z groups - to_Z g <= Z.of_nat m ->
  to_Z declared_len <= 50000 ->
  Z.of_nat (List.length (locals_list locals))
    + (50000 - to_Z declared_len) <= module_bytes + 50000 ->
  to_Z q <= dlen data ->
  exists r, module_decode_and_build_locals_loop1
      data groups locals declared_len q g = Ok r
    /\ forall out q', r = Core_result_Result_Ok (out, q') ->
         to_Z q <= to_Z q' /\ to_Z q' <= dlen data
         /\ Z.of_nat (List.length (locals_list out))
              <= module_bytes + 50000.
Proof.
  induction m as [|m IH];
    intros data groups locals declared_len q g Hmeas Hdecl Hacc Hq;
    unfold module_decode_and_build_locals_loop1; rewrite loop_unfold;
    cbn beta iota; destruct (g s>= groups) eqn:Hge;
    [ eexists; split; [reflexivity|]; intros ? ? Hc; injection Hc as <- <-;
      repeat split; lia
    | | eexists; split; [reflexivity|]; intros ? ? Hc; injection Hc as <- <-;
        repeat split; lia
    | ].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (read_u32_leb_ok data q) as [r Hr]. rewrite Hr. cbn [bind].
    destruct r as [[count q1]|e]; [|try_err_post].
    rewrite branch_ok. cbn [bind].
    pose proof (read_u32_leb_lt _ _ _ _ Hr) as Hlt1.
    pose proof (read_u32_leb_le_len _ _ _ _ Hr) as Hle1.
    destruct (decode_value_type_ok data q1) as [r1 Hr1].
    rewrite Hr1. cbn [bind].
    destruct r1 as [[vt q2]|e]; [|try_err_post].
    rewrite branch_ok. cbn [bind].
    destruct (decode_value_type_step _ _ _ _ Hr1) as [Hlt2 Hle2].
    destruct (scalar_cast_u32_usize count) as [n [Hcast Hn]].
    rewrite Hcast. cbn [bind].
    pose proof max_locals_val as Hml.
    destruct (usize_sub_ok limits_max_locals declared_len
      (ltac:(lia))) as [room [Hsub Hroom]].
    rewrite Hsub. cbn [bind].
    destruct (n s> room) eqn:Hbig.
    + eexists. split; [reflexivity|]. intros ? ? Hc. discriminate.
    + apply scalar_gtb_false in Hbig.
      assert (Hpushroom :
        Z.of_nat (List.length (locals_list locals)) + to_Z count
          <= usize_max).
      { pose proof module_bytes_fits. rewrite <- Hn. lia. }
      destruct (push_locals_ok locals count vt Hpushroom)
        as [locals2 [Hpush Hlen]].
      rewrite Hpush. cbn [bind].
      destruct (usize_add_ok declared_len n ltac:(
        pose proof usize_max_bound; rewrite u32_max_val in *; lia))
        as [declared_len2 [Hadd Hdecl2]].
      rewrite Hadd. cbn [bind].
      assert (Hu1 : to_Z 1%u32 = 1) by reflexivity.
      pose proof (u32_bounds groups).
      destruct (u32_add_ok g 1%u32 (ltac:(lia))) as [g2 [Hgadd Hg2]].
      rewrite Hgadd. cbn [bind].
      destruct (IH data groups locals2 declared_len2 q2 g2)
        as [r2 [Hr2 Hpost]].
      * rewrite Nat2Z.inj_succ in Hmeas. lia.
      * lia.
      * rewrite Hlen, <- Hn. lia.
      * exact Hle2.
      * exists r2. split; [exact Hr2|].
        intros out q' Hc. destruct (Hpost _ _ Hc) as [A [B C]].
        repeat split; lia.
Qed.

Lemma decode_and_build_locals_ok : forall data pos params,
  to_Z pos <= dlen data ->
  to_Z (slice_len params) <= module_bytes ->
  exists r, module_decode_and_build_locals data pos params = Ok r
    /\ forall out q', r = Core_result_Result_Ok (out, q') ->
         to_Z pos < to_Z q' /\ to_Z q' <= dlen data
         /\ Z.of_nat (List.length (locals_list out))
              <= module_bytes + 50000.
Proof.
  intros data pos params Hpos Hparams.
  unfold module_decode_and_build_locals.
  destruct (read_u32_leb_ok data pos) as [r Hr]. rewrite Hr. cbn [bind].
  destruct r as [[groups p]|e]; [|try_err_post].
  rewrite branch_ok. cbn [bind].
  pose proof (read_u32_leb_lt _ _ _ _ Hr) as Hlt.
  pose proof (read_u32_leb_le_len _ _ _ _ Hr) as Hple.
  destruct code_LocalsStack_new as [locals|e] eqn:Hnew.
  2: { unfold code_LocalsStack_new in Hnew. inversion Hnew. }
  pose proof (locals_stack_new_spec locals Hnew) as Hnil.
  assert (Hz : to_Z 0%usize = 0) by reflexivity.
  pose proof (usize_nonneg (slice_len params)).
  destruct (copy_params_loop_ok (Z.to_nat (to_Z (slice_len params)))
    params locals 0%usize) as [locals1 [Hcopy Hcopylen]].
  - rewrite Z2Nat.id by apply usize_nonneg. lia.
  - lia.
  - rewrite Hnil. cbn. pose proof usize_max_bound.
    pose proof module_bytes_fits. lia.
  - cbn [bind]. rewrite Hcopy. cbn [bind].
    assert (Hg0 : to_Z 0%u32 = 0) by reflexivity.
    pose proof (u32_bounds groups).
    destruct (decode_and_build_locals_loop_ok
      (Z.to_nat (to_Z groups)) data groups locals1 0%usize p 0%u32)
      as [r2 [Hr2 Hpost]].
    + rewrite Z2Nat.id by lia. lia.
    + lia.
    + rewrite Hcopylen, Hnil. cbn. lia.
    + exact Hple.
    + exists r2. split; [exact Hr2|].
      intros out q' Hc. destruct (Hpost _ _ Hc) as [A [B C]].
      repeat split; lia.
Qed.

Lemma decode_and_build_locals_loop_progress :
  forall m data groups locals declared_len q g out q',
  to_Z groups - to_Z g <= Z.of_nat m ->
  to_Z q <= dlen data ->
  module_decode_and_build_locals_loop1 data groups locals declared_len q g
    = Ok (Core_result_Result_Ok (out, q')) ->
  to_Z q <= to_Z q' /\ to_Z q' <= dlen data.
Proof.
  induction m as [|m IH];
    intros data groups locals declared_len q g out q' Hmeas Hq H;
    unfold module_decode_and_build_locals_loop1 in H;
    rewrite loop_unfold in H; cbn beta iota in H;
    destruct (g s>= groups) eqn:Hge.
  1,3: injection H as <- <-; lia.
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (reader_read_u32_leb data q) as [r|] eqn:Hr;
      cbn [bind] in H; [|discriminate].
    destruct r as [[count q1]|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    pose proof (read_u32_leb_mono _ _ _ _ Hr) as Hqq1.
    pose proof (read_u32_leb_le_len _ _ _ _ Hr) as Hq1.
    destruct (module_decode_value_type data q1) as [r1|] eqn:Hvt;
      cbn [bind] in H; [|discriminate].
    destruct r1 as [[vt q2]|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    pose proof (decode_value_type_step _ _ _ _ Hvt) as [Hstep Hq2].
    destruct (scalar_cast U32 Usize count) as [n|]; cbn [bind] in H;
      [|discriminate].
    destruct (usize_sub limits_max_locals declared_len) as [room|];
      cbn [bind] in H; [|discriminate].
    destruct (n s> room); [discriminate|].
    destruct (module_push_locals locals count vt) as [locals2|];
      cbn [bind] in H; [|discriminate].
    destruct (usize_add declared_len n) as [declared_len2|];
      cbn [bind] in H; [|discriminate].
    destruct (u32_add g 1%u32) as [g2|] eqn:Hgadd;
      cbn [bind] in H; [|discriminate].
    pose proof (scalar_add_val _ _ _ 1 Hgadd eq_refl) as Hg2.
    assert (Hnext : to_Z groups - to_Z g2 <= Z.of_nat m).
    { pose proof Hmeas as Hmeasure. rewrite Nat2Z.inj_succ in Hmeasure.
      rewrite Hg2. lia. }
    destruct (IH data groups locals2 declared_len2 q2 g2 out q'
      Hnext Hq2 H) as [A B]. lia.
Qed.

Lemma decode_and_build_locals_progress : forall data pos params out q',
  to_Z pos <= dlen data ->
  module_decode_and_build_locals data pos params
    = Ok (Core_result_Result_Ok (out, q')) ->
  to_Z pos < to_Z q' /\ to_Z q' <= dlen data.
Proof.
  intros data pos params out q' Hpos H.
  unfold module_decode_and_build_locals in H.
  destruct (reader_read_u32_leb data pos) as [r|] eqn:Hr;
    cbn [bind] in H; [|discriminate].
  destruct r as [[groups p]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_u32_leb_lt _ _ _ _ Hr) as Hlt.
  pose proof (read_u32_leb_le_len _ _ _ _ Hr) as Hp.
  destruct code_LocalsStack_new as [locals|]; cbn [bind] in H;
    [|discriminate].
  destruct (module_decode_and_build_locals_loop0 params locals 0%usize)
    as [locals1|]; cbn [bind] in H; [|discriminate].
  assert (Hg0 : to_Z 0%u32 = 0) by reflexivity.
  pose proof (u32_bounds groups).
  destruct (decode_and_build_locals_loop_progress
    (Z.to_nat (to_Z groups)) data groups locals1 0%usize p 0%u32 out q'
    (ltac:(rewrite Z2Nat.id by lia; lia)) Hp H) as [A B]. lia.
Qed.

Lemma decode_func_type_ok : forall data pos,
  to_Z pos <= dlen data ->
  dlen data <= module_bytes ->
  exists r, module_decode_func_type data pos = Ok r
            /\ forall ft q', r = Core_result_Result_Ok (ft, q') ->
                 to_Z pos < to_Z q' /\ to_Z q' <= dlen data
                 /\ Z.of_nat (List.length
                       (vec_list ft.(types_FuncType_params))) <= module_bytes.
Proof.
  intros data pos Hpos Hlen. unfold module_decode_func_type.
  destruct (read_byte_total data pos) as [r Hr]. rewrite Hr. cbn [bind].
  destruct r as [[tag p]|e]; [|try_err_post].
  rewrite branch_ok. cbn [bind].
  pose proof (read_byte_le_len _ _ _ _ Hr) as Hple.
  pose proof (proj2 (read_byte_ok _ _ _ _ Hr)) as Hplt.
  destruct (tag s<> 96%u8);
    [eexists; split; [reflexivity|]; intros ? ? Hc; discriminate|].
  destruct (decode_value_types_ok data p Hple Hlen) as [r1 [Hr1 Hpost1]].
  rewrite Hr1. cbn [bind].
  destruct r1 as [[params p1]|e]; [|try_err_post].
  rewrite branch_ok. cbn [bind].
  destruct (Hpost1 _ _ (ltac:(reflexivity))) as [A1 [B1 C1]].
  destruct (decode_value_types_ok data p1 B1 Hlen) as [r2 [Hr2 Hpost2]].
  rewrite Hr2. cbn [bind].
  destruct r2 as [[results p2]|e]; [|try_err_post].
  rewrite branch_ok. cbn [bind].
  destruct (Hpost2 _ _ (ltac:(reflexivity))) as [A2 [B2 C2]].
  destruct (alloc_vec_Vec_len results s> limits_max_results);
    [eexists; split; [reflexivity|]; intros ? ? Hc; discriminate|].
  eexists. split; [reflexivity|]. intros ft q' Hc.
  injection Hc as <- <-. cbn [types_FuncType_params]. repeat split; lia.
Qed.

(* ================================================================== *)
(** ** The environment                                                *)
(* ================================================================== *)

(** What [validate_env] maintains about the environment it is building.

    Every vector in it holds at most one element per input byte read so far,
    which is the same accounting the local vectors use, carried across sections
    instead of within one. Two counters are bounded the same way. The last
    clause is different in kind: it says every function type's parameter list
    is short, which is what [validate_code_entry] needs when it appends a
    type's parameters to a body's declared locals, the one place two
    separately bounded lengths are added. *)
Definition ft_small (ft : types_FuncType_t) : Prop :=
  Z.of_nat (List.length (vec_list ft.(types_FuncType_params))) <= module_bytes.

Record env_small (env : module_Env_t) (q : usize) : Prop := {
  es_types :
    Z.of_nat (List.length (vec_list env.(module_Env_types))) <= to_Z q;
  es_imports :
    Z.of_nat (List.length (vec_list env.(module_Env_imports))) <= to_Z q;
  es_globals :
    Z.of_nat (List.length (vec_list env.(module_Env_globals))) <= to_Z q;
  es_exports :
    Z.of_nat (List.length (vec_list env.(module_Env_exports))) <= to_Z q;
  es_elements :
    Z.of_nat (List.length (vec_list env.(module_Env_elements))) <= to_Z q;
  es_findices :
    Z.of_nat (List.length (vec_list env.(module_Env_func_type_indices))) <= to_Z q;
  es_ftypes :
    Z.of_nat (List.length (vec_list env.(module_Env_func_types))) <= to_Z q;
  es_tables :
    Z.of_nat (List.length (vec_list env.(module_Env_table_types))) <= to_Z q;
  es_mems :
    Z.of_nat (List.length (vec_list env.(module_Env_mem_types))) <= to_Z q;
  es_gtypes :
    Z.of_nat (List.length (vec_list env.(module_Env_global_types))) <= to_Z q;
  es_nfuncs : to_Z env.(module_Env_num_imported_funcs) <= to_Z q;
  es_nglobals : to_Z env.(module_Env_num_imported_globals) <= to_Z q;
  es_params : List.Forall ft_small (vec_list env.(module_Env_types));
}.

Arguments es_types {_ _}. Arguments es_imports {_ _}.
Arguments es_globals {_ _}. Arguments es_exports {_ _}.
Arguments es_elements {_ _}. Arguments es_findices {_ _}.
Arguments es_ftypes {_ _}. Arguments es_tables {_ _}.
Arguments es_mems {_ _}. Arguments es_gtypes {_ _}.
Arguments es_nfuncs {_ _}. Arguments es_nglobals {_ _}.
Arguments es_params {_ _}.

Lemma env_small_mono : forall env q q',
  env_small env q -> to_Z q <= to_Z q' -> env_small env q'.
Proof.
  intros env q q' H Hle. destruct H. constructor; try lia. assumption.
Qed.

Lemma env_small_new : forall q env,
  module_Env_new = Ok env -> env_small env q.
Proof.
  intros q env H. unfold module_Env_new in H. injection H as <-.
  pose proof (usize_nonneg q).
  constructor; cbn in *; try lia. apply List.Forall_nil.
Qed.

(** Spec 5.5.4. The first of the eight section decoders, and the pattern for
    the rest: one entry per iteration, each costing at least one input byte,
    each pushing one element onto one of the environment's vectors. *)
Lemma decode_type_section_loop_ok : forall m data env count q i,
  to_Z count - to_Z i <= Z.of_nat m ->
  env_small env q ->
  to_Z q <= dlen data ->
  dlen data <= module_bytes ->
  exists r e, module_decode_type_section_loop data env count q i = Ok (r, e)
              /\ forall q', r = Core_result_Result_Ok q' ->
                   to_Z q <= to_Z q' /\ to_Z q' <= dlen data /\ env_small e q'.
Proof.
  induction m as [|m IH]; intros data env count q i Hmeas Henv Hq Hlen;
    unfold module_decode_type_section_loop; rewrite loop_unfold; cbn beta iota;
    destruct (i s>= count) eqn:Hge;
    [ eexists; eexists; split; [reflexivity|]; intros ? Hc; injection Hc as <-;
      split; [lia|]; split; [lia | exact Henv]
    | | eexists; eexists; split; [reflexivity|]; intros ? Hc; injection Hc as <-;
        split; [lia|]; split; [lia | exact Henv]
    | ].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (decode_func_type_ok data q Hq Hlen) as [r [Hr Hpost]].
    rewrite Hr. cbn [bind].
    destruct r as [[ft q1]|e];
      [|rewrite branch_err; cbn [bind]; rewrite from_residual_err; cbn [bind];
        eexists; eexists; split; [reflexivity|]; intros ? Hc; discriminate].
    rewrite branch_ok. cbn [bind].
    destruct (Hpost _ _ (ltac:(reflexivity))) as [Hlt [Hq1 Hft]].
    pose proof (es_types Henv) as Het.
    destruct (vec_push_ok env.(module_Env_types) ft (ltac:(fits))) as [v Hpush].
    rewrite Hpush. cbn [bind].
    assert (Hu1 : to_Z 1%u32 = 1) by reflexivity.
    pose proof (u32_bounds count).
    destruct (u32_add_ok i 1%u32 (ltac:(lia))) as [i2 [Hadd Hi2]].
    rewrite Hadd. cbn [bind].
    destruct (IH data
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
                   module_Env_num_imported_globals := env.(module_Env_num_imported_globals) |}
                count q1 i2) as [r2 [e2 [Hr2 Hpost2]]].
    + rewrite Nat2Z.inj_succ in Hmeas. lia.
    + destruct Henv. constructor; cbn; try lia.
      * rewrite (vec_push_spec _ _ _ Hpush). rewrite List.app_length.
        cbn [List.length]. lia.
      * rewrite (vec_push_spec _ _ _ Hpush). apply List.Forall_app.
        split; [assumption|]. apply List.Forall_cons; [exact Hft|].
        apply List.Forall_nil.
    + exact Hq1.
    + exact Hlen.
    + exists r2, e2. split; [exact Hr2|].
      intros q' Hc. destruct (Hpost2 _ Hc) as [A [B C]].
      split; [lia|]. split; [lia | exact C].
Qed.

Lemma decode_type_section_ok : forall data pos env,
  env_small env pos ->
  to_Z pos <= dlen data ->
  dlen data <= module_bytes ->
  exists r e, module_decode_type_section data pos env = Ok (r, e)
              /\ forall q', r = Core_result_Result_Ok q' ->
                   to_Z pos <= to_Z q' /\ to_Z q' <= dlen data /\ env_small e q'.
Proof.
  intros data pos env Henv Hpos Hlen. unfold module_decode_type_section.
  destruct (read_u32_leb_ok data pos) as [r Hr]. rewrite Hr. cbn [bind].
  destruct r as [[count p]|e];
    [|rewrite branch_err; cbn [bind]; rewrite from_residual_op_err; cbn [bind];
      eexists; eexists; split; [reflexivity|]; intros ? Hc; discriminate].
  rewrite branch_ok. cbn [bind].
  pose proof (read_u32_leb_lt _ _ _ _ Hr) as Hlt.
  pose proof (read_u32_leb_le_len _ _ _ _ Hr) as Hple.
  assert (Hz : to_Z 0%u32 = 0) by reflexivity.
  pose proof (u32_bounds count).
  destruct (decode_type_section_loop_ok (Z.to_nat (to_Z count)) data env count
              p 0%u32) as [r2 [e2 [Hr2 Hpost]]].
  - rewrite Z2Nat.id by lia. lia.
  - apply (env_small_mono _ pos); [exact Henv | lia].
  - exact Hple.
  - exact Hlen.
  - exists r2, e2. split; [exact Hr2|].
    intros q' Hc. destruct (Hpost _ Hc) as [A [B C]].
    split; [lia|]. split; [lia | exact C].
Qed.

(** Looking a type up in the type section, and the copy it hands back. The
    copy keeps the parameter list the same length, so the environment's bound
    on it travels with the value. *)
Lemma copy_func_type_ok : forall ft,
  exists ft', module_copy_func_type ft = Ok ft'
              /\ Z.of_nat (List.length (vec_list ft'.(types_FuncType_params)))
                 = Z.of_nat (List.length (vec_list ft.(types_FuncType_params))).
Proof.
  intros ft. unfold module_copy_func_type.
  destruct (copy_value_types_ok (alloc_vec_Vec_deref ft.(types_FuncType_params)))
    as [v [Hv Hlv]].
  rewrite Hv. cbn [bind].
  destruct (copy_value_types_ok (alloc_vec_Vec_deref ft.(types_FuncType_results)))
    as [v1 [Hv1 _]].
  rewrite Hv1. cbn [bind]. eexists. split; [reflexivity|].
  cbn [types_FuncType_params]. rewrite Hlv.
  rewrite vec_deref_spec. rewrite slice_len_spec. reflexivity.
Qed.

Lemma lookup_type_ok : forall env idx,
  List.Forall ft_small (vec_list env.(module_Env_types)) ->
  exists r, module_lookup_type env idx = Ok r
            /\ forall ft, r = Core_result_Result_Ok ft -> ft_small ft.
Proof.
  intros env idx Hall. unfold module_lookup_type.
  destruct (scalar_cast_u32_usize idx) as [i [Hcast Hi]].
  rewrite Hcast. cbn [bind].
  destruct (i s>= alloc_vec_Vec_len env.(module_Env_types)) eqn:Hge;
    [eexists; split; [reflexivity|]; intros ? Hc; discriminate|].
  destruct (vec_index_ok env.(module_Env_types) i Hge) as [ft Hidx].
  rewrite Hidx. cbn [bind].
  assert (Hsmall : ft_small ft).
  { rewrite vec_index_spec in Hidx.
    destruct (List.nth_error (vec_list env.(module_Env_types))
                (Z.to_nat (to_Z i))) as [x|] eqn:Hnth; [|discriminate].
    injection Hidx as <-.
    rewrite List.Forall_forall in Hall. apply Hall.
    eapply List.nth_error_In. exact Hnth. }
  destruct (copy_func_type_ok ft) as [ft' [Hcopy Hlen]].
  rewrite Hcopy. cbn [bind]. eexists. split; [reflexivity|].
  intros ft2 Hc. injection Hc as <-. unfold ft_small in *. lia.
Qed.

(** Spec 5.5.11. No loop, and the only field of the environment it changes is
    the start index. *)
Lemma decode_start_section_ok : forall data pos env,
  env_small env pos ->
  to_Z pos <= dlen data ->
  exists r e, module_decode_start_section data pos env = Ok (r, e)
              /\ forall q', r = Core_result_Result_Ok q' ->
                   to_Z pos <= to_Z q' /\ to_Z q' <= dlen data /\ env_small e q'.
Proof.
  intros data pos env Henv Hpos. unfold module_decode_start_section.
  destruct (read_u32_leb_ok data pos) as [r Hr]. rewrite Hr. cbn [bind].
  destruct r as [[idx p]|e];
    [|rewrite branch_err; cbn [bind]; rewrite from_residual_op_err; cbn [bind];
      eexists; eexists; split; [reflexivity|]; intros ? Hc; discriminate].
  rewrite branch_ok. cbn [bind].
  pose proof (read_u32_leb_lt _ _ _ _ Hr) as Hlt.
  pose proof (read_u32_leb_le_len _ _ _ _ Hr) as Hple.
  destruct (scalar_cast_u32_usize idx) as [i [Hcast Hi]].
  rewrite Hcast. cbn [bind].
  destruct (i s>= alloc_vec_Vec_len env.(module_Env_func_types)) eqn:Hge;
    [eexists; eexists; split; [reflexivity|]; intros ? Hc; discriminate|].
  destruct (vec_index_ok env.(module_Env_func_types) i Hge) as [ft Hidx].
  rewrite Hidx. cbn [bind].
  rewrite vec_is_empty_spec. cbn [bind].
  destruct (match vec_list ft.(types_FuncType_params) with [] => true | _ => false end);
    [|eexists; eexists; split; [reflexivity|]; intros ? Hc; discriminate].
  rewrite vec_is_empty_spec. cbn [bind].
  destruct (match vec_list ft.(types_FuncType_results) with [] => true | _ => false end);
    [|eexists; eexists; split; [reflexivity|]; intros ? Hc; discriminate].
  eexists. eexists. split; [reflexivity|]. intros q' Hc. injection Hc as <-.
  split; [lia|]. split; [lia|].
  apply (env_small_mono _ pos); [|lia].
  destruct Henv. constructor; cbn; try lia. assumption.
Qed.

(** Comparing two names, and the linear scan over the exports so far that uses
    it. Neither reads input, and both are bounded by what they walk. *)
Lemma names_equal_loop_ok : forall m a b i,
  to_Z (slice_len a) - to_Z i <= Z.of_nat m ->
  to_Z (slice_len a) = to_Z (slice_len b) ->
  exists v, module_names_equal_loop a b i = Ok v.
Proof.
  induction m as [|m IH]; intros a b i Hmeas Hab;
    unfold module_names_equal_loop; rewrite loop_unfold; cbn beta iota;
    destruct (i s>= slice_len a) eqn:Hge;
    [eexists; reflexivity| |eexists; reflexivity|].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (slice_index_usize_ok a i) as [x Hx];
      [rewrite <- slice_len_spec; lia|].
    rewrite Hx. cbn [bind].
    destruct (slice_index_usize_ok b i) as [y Hy];
      [rewrite <- slice_len_spec; lia|].
    rewrite Hy. cbn [bind].
    destruct (x s<> y); [eexists; reflexivity|].
    pose proof (usize_le_max (slice_len a)).
    destruct (usize_add_1_ok i (ltac:(lia))) as [i2 [Hadd Hi2]].
    rewrite Hadd. cbn [bind].
    apply (IH a b i2); [rewrite Nat2Z.inj_succ in Hmeas; lia | exact Hab].
Qed.

Lemma names_equal_ok : forall a b, exists v, module_names_equal a b = Ok v.
Proof.
  intros a b. unfold module_names_equal.
  destruct (slice_len a s<> slice_len b) eqn:Hne; [eexists; reflexivity|].
  apply Bool.negb_false_iff in Hne. apply scalar_eqb_true in Hne.
  pose proof (usize_nonneg (slice_len a)).
  assert (Hz : to_Z 0%usize = 0) by reflexivity.
  apply (names_equal_loop_ok (Z.to_nat (to_Z (slice_len a))) a b 0%usize);
    [rewrite Z2Nat.id by lia; lia | exact Hne].
Qed.

Lemma export_name_taken_loop_ok : forall m env name i,
  Z.of_nat (List.length (vec_list env.(module_Env_exports))) - to_Z i
    <= Z.of_nat m ->
  exists v, module_export_name_taken_loop env name i = Ok v.
Proof.
  induction m as [|m IH]; intros env name i Hmeas;
    unfold module_export_name_taken_loop; rewrite loop_unfold; cbn beta iota;
    destruct (i s>= alloc_vec_Vec_len env.(module_Env_exports)) eqn:Hge;
    [eexists; reflexivity| |eexists; reflexivity|].
  - exfalso. apply scalar_geb_false_lt in Hge. rewrite vec_len_spec in Hge.
    cbn in Hmeas. lia.
  - destruct (vec_index_ok env.(module_Env_exports) i Hge) as [e He].
    rewrite He. cbn [bind].
    destruct (names_equal_ok (alloc_vec_Vec_deref e.(module_Export_name)) name)
      as [b Hb].
    rewrite Hb. cbn [bind].
    destruct b; [eexists; reflexivity|].
    apply scalar_geb_false_lt in Hge. rewrite vec_len_spec in Hge.
    pose proof (usize_le_max (alloc_vec_Vec_len env.(module_Env_exports))).
    rewrite vec_len_spec in *.
    destruct (usize_add_1_ok i (ltac:(lia))) as [i2 [Hadd Hi2]].
    rewrite Hadd. cbn [bind].
    apply (IH env name i2). rewrite Nat2Z.inj_succ in Hmeas. lia.
Qed.

Lemma export_name_taken_ok : forall env name,
  exists v, module_export_name_taken env name = Ok v.
Proof.
  intros env name. unfold module_export_name_taken.
  assert (Hz : to_Z 0%usize = 0) by reflexivity.
  apply (export_name_taken_loop_ok
           (List.length (vec_list env.(module_Env_exports))) env name 0%usize).
  lia.
Qed.

(* ================================================================== *)
(** ** Constant expressions                                           *)
(* ================================================================== *)

Lemma const_global_ok : forall env idx,
  exists r, module_const_global env idx = Ok r.
Proof.
  intros env idx. unfold module_const_global.
  destruct (scalar_cast_u32_usize idx) as [i [Hcast Hi]].
  rewrite Hcast. cbn [bind].
  destruct (i s>= alloc_vec_Vec_len env.(module_Env_global_types)) eqn:Hge;
    [eexists; reflexivity|].
  destruct (i s>= env.(module_Env_num_imported_globals)); [eexists; reflexivity|].
  destruct (vec_index_ok env.(module_Env_global_types) i Hge) as [gt Hidx].
  rewrite Hidx. cbn [bind]. rewrite mut_ne_spec. cbn [bind].
  destruct (negb _); eexists; reflexivity.
Qed.

Lemma read_expr_end_ok : forall data pos,
  exists r, module_read_expr_end data pos = Ok r
            /\ forall p', r = Core_result_Result_Ok p' ->
                 to_Z pos < to_Z p' /\ to_Z p' <= dlen data.
Proof.
  intros data pos. unfold module_read_expr_end.
  destruct (read_byte_total data pos) as [r Hr]. rewrite Hr. cbn [bind].
  destruct r as [[b p]|e]; [|try_err_post].
  rewrite branch_ok. cbn [bind].
  pose proof (read_byte_le_len _ _ _ _ Hr).
  pose proof (proj2 (read_byte_ok _ _ _ _ Hr)).
  destruct (b s<> code_op_end);
    [eexists; split; [reflexivity|]; intros ? Hc; discriminate|].
  eexists. split; [reflexivity|]. intros p' Hc. injection Hc as <-. lia.
Qed.

Lemma expect_const_type_ok : forall actual expected,
  exists r, module_expect_const_type actual expected = Ok r.
Proof.
  intros actual expected. unfold module_expect_const_type.
  rewrite vt_ne_spec. cbn [bind]. destruct (negb _); eexists; reflexivity.
Qed.

(** Spec 3.4.10 restricted to Wasm 1.0: five opcodes, each one immediate and a
    closing [end]. A dedicated reader rather than a mode of [code], because
    every constant instruction pushes exactly one value, so a sequence typed
    [[] -> [t]] has exactly one instruction in it. *)
Lemma decode_const_expr_ok : forall data pos env expected,
  exists r, module_decode_const_expr data pos env expected = Ok r
            /\ forall ce p', r = Core_result_Result_Ok (ce, p') ->
                 to_Z pos < to_Z p' /\ to_Z p' <= dlen data.
Proof.
  intros data pos env expected. unfold module_decode_const_expr.
  destruct (read_byte_total data pos) as [r Hr]. rewrite Hr. cbn [bind].
  destruct r as [[op p]|e]; [|try_err_post].
  rewrite branch_ok. cbn [bind].
  pose proof (read_byte_le_len _ _ _ _ Hr) as Hple.
  pose proof (proj2 (read_byte_ok _ _ _ _ Hr)) as Hplt.
  repeat first
    [ solve [eexists; split; [reflexivity|]; intros ? ? Hc; discriminate]
    | match goal with
      | [ |- context [if ?c then _ else _] ] => destruct c
      end
    | match goal with
      | [ |- context [reader_read_s32_leb ?d ?j] ] =>
          let r := fresh "r" in let E := fresh "E" in
          let a := fresh "a" in let q := fresh "q" in
          destruct (read_s32_leb_ok d j) as [r E]; rewrite E; cbn [bind];
          destruct r as [[a q]|];
          [ rewrite branch_ok; cbn [bind];
            pose proof (read_s32_leb_le_len _ _ _ _ E);
            pose proof (read_s32_leb_mono _ _ _ _ E)
          | try_err_post ]
      | [ |- context [reader_read_s64_leb ?d ?j] ] =>
          let r := fresh "r" in let E := fresh "E" in
          let a := fresh "a" in let q := fresh "q" in
          destruct (read_s64_leb_ok d j) as [r E]; rewrite E; cbn [bind];
          destruct r as [[a q]|];
          [ rewrite branch_ok; cbn [bind];
            pose proof (read_s64_leb_le_len _ _ _ _ E);
            pose proof (read_s64_leb_mono _ _ _ _ E)
          | try_err_post ]
      | [ |- context [reader_read_f32_bits ?d ?j] ] =>
          let r := fresh "r" in let E := fresh "E" in
          let a := fresh "a" in let q := fresh "q" in
          destruct (read_f32_bits_ok d j) as [r E]; rewrite E; cbn [bind];
          destruct r as [[a q]|];
          [ rewrite branch_ok; cbn [bind];
            pose proof (read_f32_bits_le_len _ _ _ _ E);
            pose proof (read_f32_bits_mono _ _ _ _ E)
          | try_err_post ]
      | [ |- context [reader_read_f64_bits ?d ?j] ] =>
          let r := fresh "r" in let E := fresh "E" in
          let a := fresh "a" in let q := fresh "q" in
          destruct (read_f64_bits_ok d j) as [r E]; rewrite E; cbn [bind];
          destruct r as [[a q]|];
          [ rewrite branch_ok; cbn [bind];
            pose proof (read_f64_bits_le_len _ _ _ _ E);
            pose proof (read_f64_bits_mono _ _ _ _ E)
          | try_err_post ]
      | [ |- context [reader_read_u32_leb ?d ?j] ] =>
          let r := fresh "r" in let E := fresh "E" in
          let a := fresh "a" in let q := fresh "q" in
          destruct (read_u32_leb_ok d j) as [r E]; rewrite E; cbn [bind];
          destruct r as [[a q]|];
          [ rewrite branch_ok; cbn [bind];
            pose proof (read_u32_leb_le_len _ _ _ _ E);
            pose proof (read_u32_leb_mono _ _ _ _ E)
          | try_err_post ]
      | [ |- context [module_const_global ?e ?j] ] =>
          let r := fresh "r" in let E := fresh "E" in let g := fresh "g" in
          destruct (const_global_ok e j) as [r E]; rewrite E; cbn [bind];
          destruct r as [g|];
          [ rewrite branch_ok; cbn [bind] | try_err_post ]
      | [ |- context [module_expect_const_type ?x ?y] ] =>
          let r := fresh "r" in let E := fresh "E" in let u := fresh "u" in
          destruct (expect_const_type_ok x y) as [r E]; rewrite E; cbn [bind];
          destruct r as [u|];
          [ rewrite branch_ok; cbn [bind]; destruct u | try_err_post ]
      | [ |- context [module_read_expr_end ?d ?j] ] =>
          let r := fresh "r" in let E := fresh "E" in
          let q := fresh "q" in let P := fresh "Hend" in
          destruct (read_expr_end_ok d j) as [r [E P]]; rewrite E; cbn [bind];
          destruct r as [q|];
          [ rewrite branch_ok; cbn [bind];
            pose proof (P _ (ltac:(reflexivity)))
          | try_err_post ]
      end ].
  all: eexists; split; [reflexivity|]; intros ce p' Hc;
       injection Hc as _ <-; split; lia.
Qed.

(* ================================================================== *)
(** ** The environment's sections                                     *)
(* ================================================================== *)

(** Re-establishing the invariant after a push. Every field but the pushed one
    is untouched, and the cursor has only moved on, so the arithmetic is the
    same in each case; the vector that grew is the one the rewrite fires on. *)
Ltac env_push Hpush Henv :=
  destruct Henv; constructor; cbn;
    try (rewrite (vec_push_spec _ _ _ Hpush); rewrite List.app_length;
         cbn [List.length]);
    try lia; assumption.

(** The section loops' skeleton: the exit arm, the spent-budget contradiction,
    and the arm where the entry decoder rejected. *)
Ltac sec_loop_start Henv :=
  eexists; eexists; split; [reflexivity|]; intros ? Hc; injection Hc as <-;
  split; [lia|]; split; [lia | exact Henv].

Ltac sec_loop_err :=
  rewrite branch_err; cbn [bind];
  first [rewrite from_residual_err | rewrite from_residual_op_err];
  cbn [bind]; eexists; eexists; split; [reflexivity|];
  intros ? Hc; discriminate.

Ltac sec_done :=
  eexists; eexists; split; [reflexivity|]; intros ? Hc; discriminate.

(** Spec 5.5.7 and 5.5.8. Wasm 1.0 allows one table and one memory, counting
    imports, so these two are the loops whose vector is capped by the language
    rather than by the input. *)
Lemma decode_table_section_loop_ok : forall m data env count q i,
  to_Z count - to_Z i <= Z.of_nat m ->
  env_small env q ->
  to_Z q <= dlen data ->
  dlen data <= module_bytes ->
  exists r e, module_decode_table_section_loop data env count q i = Ok (r, e)
              /\ forall q', r = Core_result_Result_Ok q' ->
                   to_Z q <= to_Z q' /\ to_Z q' <= dlen data /\ env_small e q'.
Proof.
  induction m as [|m IH]; intros data env count q i Hmeas Henv Hq Hlen;
    unfold module_decode_table_section_loop; rewrite loop_unfold; cbn beta iota;
    destruct (i s>= count) eqn:Hge;
    [sec_loop_start Henv | | sec_loop_start Henv | ].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (decode_table_type_ok data q) as [r Hr]. rewrite Hr. cbn [bind].
    destruct r as [[tt1 q1]|e]; [|sec_loop_err].
    rewrite branch_ok. cbn [bind].
    destruct (decode_table_type_step _ _ _ _ Hr) as [Hlt Hq1].
    pose proof (es_tables Henv) as Het.
    destruct (vec_push_ok env.(module_Env_table_types) tt1 (ltac:(fits)))
      as [v Hpush].
    rewrite Hpush. cbn [bind].
    destruct (alloc_vec_Vec_len v s> limits_max_tables); [sec_done|].
    assert (Hu1 : to_Z 1%u32 = 1) by reflexivity.
    pose proof (u32_bounds count).
    destruct (u32_add_ok i 1%u32 (ltac:(lia))) as [i2 [Hadd Hi2]].
    rewrite Hadd. cbn [bind]. cbn beta iota.
    match goal with
    | [ |- context [loop _ (?e, _, _)] ] =>
        destruct (IH data e count q1 i2) as [r2 [e2 [Hr2 Hpost2]]]
    end.
    + rewrite Nat2Z.inj_succ in Hmeas. lia.
    + env_push Hpush Henv.
    + exact Hq1.
    + exact Hlen.
    + exists r2, e2. split; [exact Hr2|].
      intros q' Hc. destruct (Hpost2 _ Hc) as [A [B C]].
      split; [lia|]. split; [lia | exact C].
Qed.

Lemma decode_memory_section_loop_ok : forall m data env count q i,
  to_Z count - to_Z i <= Z.of_nat m ->
  env_small env q ->
  to_Z q <= dlen data ->
  dlen data <= module_bytes ->
  exists r e, module_decode_memory_section_loop data env count q i = Ok (r, e)
              /\ forall q', r = Core_result_Result_Ok q' ->
                   to_Z q <= to_Z q' /\ to_Z q' <= dlen data /\ env_small e q'.
Proof.
  induction m as [|m IH]; intros data env count q i Hmeas Henv Hq Hlen;
    unfold module_decode_memory_section_loop; rewrite loop_unfold;
    cbn beta iota; destruct (i s>= count) eqn:Hge;
    [sec_loop_start Henv | | sec_loop_start Henv | ].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (decode_mem_type_ok data q) as [r Hr]. rewrite Hr. cbn [bind].
    destruct r as [[mt q1]|e]; [|sec_loop_err].
    rewrite branch_ok. cbn [bind].
    destruct (decode_mem_type_step _ _ _ _ Hr) as [Hlt Hq1].
    pose proof (es_mems Henv) as Hem.
    destruct (vec_push_ok env.(module_Env_mem_types) mt (ltac:(fits)))
      as [v Hpush].
    rewrite Hpush. cbn [bind].
    destruct (alloc_vec_Vec_len v s> limits_max_memories); [sec_done|].
    assert (Hu1 : to_Z 1%u32 = 1) by reflexivity.
    pose proof (u32_bounds count).
    destruct (u32_add_ok i 1%u32 (ltac:(lia))) as [i2 [Hadd Hi2]].
    rewrite Hadd. cbn [bind]. cbn beta iota.
    match goal with
    | [ |- context [loop _ (?e, _, _)] ] =>
        destruct (IH data e count q1 i2) as [r2 [e2 [Hr2 Hpost2]]]
    end.
    + rewrite Nat2Z.inj_succ in Hmeas. lia.
    + env_push Hpush Henv.
    + exact Hq1.
    + exact Hlen.
    + exists r2, e2. split; [exact Hr2|].
      intros q' Hc. destruct (Hpost2 _ Hc) as [A [B C]].
      split; [lia|]. split; [lia | exact C].
Qed.

Ltac env_push2 H1 H2 Henv :=
  destruct Henv; constructor; cbn;
    try (rewrite (vec_push_spec _ _ _ H1); rewrite List.app_length;
         cbn [List.length]);
    try (rewrite (vec_push_spec _ _ _ H2); rewrite List.app_length;
         cbn [List.length]);
    try lia; assumption.

(** Spec 5.5.6. Two pushes per entry, one to each of the two index spaces the
    function section feeds, and both paid for by the same byte. *)
Lemma decode_function_section_loop_ok : forall m data env count q i,
  to_Z count - to_Z i <= Z.of_nat m ->
  env_small env q ->
  to_Z q <= dlen data ->
  dlen data <= module_bytes ->
  exists r e, module_decode_function_section_loop data env count q i = Ok (r, e)
              /\ forall q', r = Core_result_Result_Ok q' ->
                   to_Z q <= to_Z q' /\ to_Z q' <= dlen data /\ env_small e q'.
Proof.
  induction m as [|m IH]; intros data env count q i Hmeas Henv Hq Hlen;
    unfold module_decode_function_section_loop; rewrite loop_unfold;
    cbn beta iota; destruct (i s>= count) eqn:Hge;
    [sec_loop_start Henv | | sec_loop_start Henv | ].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (read_u32_leb_ok data q) as [r Hr]. rewrite Hr. cbn [bind].
    destruct r as [[idx q1]|e]; [|sec_loop_err].
    rewrite branch_ok. cbn [bind].
    pose proof (read_u32_leb_lt _ _ _ _ Hr) as Hlt.
    pose proof (read_u32_leb_le_len _ _ _ _ Hr) as Hq1.
    destruct (lookup_type_ok env idx (es_params Henv)) as [r1 [Hr1 Hft]].
    rewrite Hr1. cbn [bind].
    destruct r1 as [ft|e]; [|sec_loop_err].
    rewrite branch_ok. cbn [bind].
    pose proof (Hft _ (ltac:(reflexivity))) as Hsmall.
    pose proof (es_ftypes Henv) as Hef. pose proof (es_findices Henv) as Hei.
    destruct (vec_push_ok env.(module_Env_func_types) ft (ltac:(fits)))
      as [v Hpush].
    rewrite Hpush. cbn [bind].
    destruct (vec_push_ok env.(module_Env_func_type_indices) idx (ltac:(fits)))
      as [v1 Hpush1].
    rewrite Hpush1. cbn [bind].
    assert (Hu1 : to_Z 1%u32 = 1) by reflexivity.
    pose proof (u32_bounds count).
    destruct (u32_add_ok i 1%u32 (ltac:(lia))) as [i2 [Hadd Hi2]].
    rewrite Hadd. cbn [bind]. cbn beta iota.
    match goal with
    | [ |- context [loop _ (?e, _, _)] ] =>
        destruct (IH data e count q1 i2) as [r2 [e2 [Hr2 Hpost2]]]
    end.
    + rewrite Nat2Z.inj_succ in Hmeas. lia.
    + env_push2 Hpush Hpush1 Henv.
    + exact Hq1.
    + exact Hlen.
    + exists r2, e2. split; [exact Hr2|].
      intros q' Hc. destruct (Hpost2 _ Hc) as [A [B C]].
      split; [lia|]. split; [lia | exact C].
Qed.

(** Spec 5.5.9. A global is a type and an initialiser, and the initialiser is
    where the environment is read back: it may name an imported global. *)
Lemma decode_global_section_loop_ok : forall m data env count q i,
  to_Z count - to_Z i <= Z.of_nat m ->
  env_small env q ->
  to_Z q <= dlen data ->
  dlen data <= module_bytes ->
  exists r e, module_decode_global_section_loop data env count q i = Ok (r, e)
              /\ forall q', r = Core_result_Result_Ok q' ->
                   to_Z q <= to_Z q' /\ to_Z q' <= dlen data /\ env_small e q'.
Proof.
  induction m as [|m IH]; intros data env count q i Hmeas Henv Hq Hlen;
    unfold module_decode_global_section_loop; rewrite loop_unfold;
    cbn beta iota; destruct (i s>= count) eqn:Hge;
    [sec_loop_start Henv | | sec_loop_start Henv | ].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (decode_global_type_ok data q) as [r Hr]. rewrite Hr. cbn [bind].
    destruct r as [[gt q1]|e]; [|sec_loop_err].
    rewrite branch_ok. cbn [bind].
    destruct (decode_global_type_step _ _ _ _ Hr) as [Hlt Hq1].
    destruct (decode_const_expr_ok data q1 env gt.(types_GlobalType_valtype))
      as [r1 [Hr1 Hce]].
    rewrite Hr1. cbn [bind].
    destruct r1 as [[init q2]|e]; [|sec_loop_err].
    rewrite branch_ok. cbn [bind].
    destruct (Hce _ _ (ltac:(reflexivity))) as [Hlt2 Hq2].
    pose proof (es_gtypes Henv) as Heg. pose proof (es_globals Henv) as Heb.
    destruct (vec_push_ok env.(module_Env_global_types) gt (ltac:(fits)))
      as [v Hpush].
    rewrite Hpush. cbn [bind].
    destruct (vec_push_ok env.(module_Env_globals)
                {| module_Global_gtype := gt; module_Global_init := init |}
                (ltac:(fits))) as [v1 Hpush1].
    rewrite Hpush1. cbn [bind].
    assert (Hu1 : to_Z 1%u32 = 1) by reflexivity.
    pose proof (u32_bounds count).
    destruct (u32_add_ok i 1%u32 (ltac:(lia))) as [i2 [Hadd Hi2]].
    rewrite Hadd. cbn [bind]. cbn beta iota.
    match goal with
    | [ |- context [loop _ (?e, _, _)] ] =>
        destruct (IH data e count q2 i2) as [r2 [e2 [Hr2 Hpost2]]]
    end.
    + rewrite Nat2Z.inj_succ in Hmeas. lia.
    + env_push2 Hpush Hpush1 Henv.
    + exact Hq2.
    + exact Hlen.
    + exists r2, e2. split; [exact Hr2|].
      intros q' Hc. destruct (Hpost2 _ Hc) as [A [B C]].
      split; [lia|]. split; [lia | exact C].
Qed.

(** Spec 5.5.10. The export names have to be distinct (spec 3.4.11), which is
    checked as each one is decoded, so there is no second pass. *)
Lemma export_desc_ok : forall env kind idx,
  exists r, module_export_desc env kind idx = Ok r.
Proof.
  intros env kind idx. unfold module_export_desc.
  destruct (scalar_cast_u32_usize idx) as [i [Hcast Hi]].
  rewrite Hcast. cbn [bind].
  repeat (match goal with
          | [ |- context [if ?c then _ else _] ] => destruct c
          end); eexists; reflexivity.
Qed.

Lemma decode_export_section_loop_ok : forall m data env count q i,
  to_Z count - to_Z i <= Z.of_nat m ->
  env_small env q ->
  to_Z q <= dlen data ->
  dlen data <= module_bytes ->
  exists r e, module_decode_export_section_loop data env count q i = Ok (r, e)
              /\ forall q', r = Core_result_Result_Ok q' ->
                   to_Z q <= to_Z q' /\ to_Z q' <= dlen data /\ env_small e q'.
Proof.
  induction m as [|m IH]; intros data env count q i Hmeas Henv Hq Hlen;
    unfold module_decode_export_section_loop; rewrite loop_unfold;
    cbn beta iota; destruct (i s>= count) eqn:Hge;
    [sec_loop_start Henv | | sec_loop_start Henv | ].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (decode_name_ok data q Hq Hlen) as [r Hr]. rewrite Hr. cbn [bind].
    destruct r as [[name q1]|e]; [|sec_loop_err].
    rewrite branch_ok. cbn [bind].
    destruct (decode_name_step _ _ _ _ Hr Hq) as [Hlt Hq1].
    rewrite vec_deref_spec.
    destruct (export_name_taken_ok env name) as [b Hb]. rewrite Hb. cbn [bind].
    destruct b; [sec_done|].
    destruct (read_byte_total data q1) as [r1 Hr1]. rewrite Hr1. cbn [bind].
    destruct r1 as [[kind q2]|e]; [|sec_loop_err].
    rewrite branch_ok. cbn [bind].
    pose proof (read_byte_le_len _ _ _ _ Hr1) as Hq2.
    pose proof (proj2 (read_byte_ok _ _ _ _ Hr1)) as Hlt2.
    destruct (read_u32_leb_ok data q2) as [r2 Hr2]. rewrite Hr2. cbn [bind].
    destruct r2 as [[idx q3]|e]; [|sec_loop_err].
    rewrite branch_ok. cbn [bind].
    pose proof (read_u32_leb_le_len _ _ _ _ Hr2) as Hq3.
    pose proof (read_u32_leb_mono _ _ _ _ Hr2) as Hlt3.
    destruct (export_desc_ok env kind idx) as [r3 Hr3]. rewrite Hr3. cbn [bind].
    destruct r3 as [desc|e]; [|sec_loop_err].
    rewrite branch_ok. cbn [bind].
    pose proof (es_exports Henv) as Hee.
    destruct (vec_push_ok env.(module_Env_exports)
                {| module_Export_name := name; module_Export_desc := desc |}
                (ltac:(fits))) as [v Hpush].
    rewrite Hpush. cbn [bind].
    assert (Hu1 : to_Z 1%u32 = 1) by reflexivity.
    pose proof (u32_bounds count).
    destruct (u32_add_ok i 1%u32 (ltac:(lia))) as [i2 [Hadd Hi2]].
    rewrite Hadd. cbn [bind]. cbn beta iota.
    match goal with
    | [ |- context [loop _ (?e, _, _)] ] =>
        destruct (IH data e count q3 i2) as [r4 [e2 [Hr4 Hpost2]]]
    end.
    + rewrite Nat2Z.inj_succ in Hmeas. lia.
    + env_push Hpush Henv.
    + exact Hq3.
    + exact Hlen.
    + exists r4, e2. split; [exact Hr4|].
      intros q' Hc. destruct (Hpost2 _ Hc) as [A [B C]].
      split; [lia|]. split; [lia | exact C].
Qed.

(** Spec 5.5.12's [y*:vec(funcidx)], and the element section around it. *)
Lemma decode_func_indices_loop_ok : forall m data env count out q i,
  to_Z count - to_Z i <= Z.of_nat m ->
  Z.of_nat (List.length (vec_list out)) <= to_Z q ->
  to_Z q <= dlen data ->
  dlen data <= module_bytes ->
  exists r, module_decode_func_indices_loop data env count out q i = Ok r
            /\ forall out' q', r = Core_result_Result_Ok (out', q') ->
                 to_Z q <= to_Z q' /\ to_Z q' <= dlen data
                 /\ Z.of_nat (List.length (vec_list out')) <= to_Z q'.
Proof.
  induction m as [|m IH]; intros data env count out q i Hmeas Hacc Hq Hlen;
    unfold module_decode_func_indices_loop; rewrite loop_unfold; cbn beta iota;
    destruct (i s>= count) eqn:Hge;
    [ eexists; split; [reflexivity|]; intros ? ? Hc; injection Hc as <- <-;
      repeat split; lia
    | | eexists; split; [reflexivity|]; intros ? ? Hc; injection Hc as <- <-;
        repeat split; lia
    | ].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (read_u32_leb_ok data q) as [r Hr]. rewrite Hr. cbn [bind].
    destruct r as [[idx q1]|e]; [|try_err_post].
    rewrite branch_ok. cbn [bind].
    pose proof (read_u32_leb_lt _ _ _ _ Hr) as Hlt.
    pose proof (read_u32_leb_le_len _ _ _ _ Hr) as Hq1.
    destruct (scalar_cast_u32_usize idx) as [j [Hcast Hj]].
    rewrite Hcast. cbn [bind].
    destruct (j s>= alloc_vec_Vec_len env.(module_Env_func_types));
      [eexists; split; [reflexivity|]; intros ? ? Hc; discriminate|].
    destruct (vec_push_ok out idx (ltac:(fits))) as [out2 Hpush].
    rewrite Hpush. cbn [bind].
    assert (Hu1 : to_Z 1%u32 = 1) by reflexivity.
    pose proof (u32_bounds count).
    destruct (u32_add_ok i 1%u32 (ltac:(lia))) as [i2 [Hadd Hi2]].
    rewrite Hadd. cbn [bind].
    destruct (IH data env count out2 q1 i2) as [r2 [Hr2 Hpost]].
    + rewrite Nat2Z.inj_succ in Hmeas. lia.
    + rewrite (vec_push_spec _ _ _ Hpush). rewrite List.app_length.
      cbn [List.length]. lia.
    + exact Hq1.
    + exact Hlen.
    + exists r2. split; [exact Hr2|].
      intros out' q' Hc. destruct (Hpost _ _ Hc) as [A [B C]].
      repeat split; lia.
Qed.

Lemma decode_func_indices_ok : forall data pos env,
  to_Z pos <= dlen data ->
  dlen data <= module_bytes ->
  exists r, module_decode_func_indices data pos env = Ok r
            /\ forall out q', r = Core_result_Result_Ok (out, q') ->
                 to_Z pos < to_Z q' /\ to_Z q' <= dlen data.
Proof.
  intros data pos env Hpos Hlen. unfold module_decode_func_indices.
  destruct (read_u32_leb_ok data pos) as [r Hr]. rewrite Hr. cbn [bind].
  destruct r as [[count p]|e]; [|try_err_post].
  rewrite branch_ok. cbn [bind].
  pose proof (read_u32_leb_lt _ _ _ _ Hr) as Hlt.
  pose proof (read_u32_leb_le_len _ _ _ _ Hr) as Hple.
  assert (Hz : to_Z 0%u32 = 0) by reflexivity.
  pose proof (u32_bounds count).
  destruct (decode_func_indices_loop_ok (Z.to_nat (to_Z count)) data env count
              (alloc_vec_Vec_new u32) p 0%u32) as [r2 [Hr2 Hpost]].
  - rewrite Z2Nat.id by lia. lia.
  - cbn [vec_list alloc_vec_Vec_new proj1_sig List.length].
    pose proof (usize_nonneg p). lia.
  - exact Hple.
  - exact Hlen.
  - exists r2. split; [exact Hr2|].
    intros out q' Hc. destruct (Hpost _ _ Hc) as [A [B C]]. split; lia.
Qed.

Lemma decode_element_section_loop_ok : forall m data env count q i,
  to_Z count - to_Z i <= Z.of_nat m ->
  env_small env q ->
  to_Z q <= dlen data ->
  dlen data <= module_bytes ->
  exists r e, module_decode_element_section_loop data env count q i = Ok (r, e)
              /\ forall q', r = Core_result_Result_Ok q' ->
                   to_Z q <= to_Z q' /\ to_Z q' <= dlen data /\ env_small e q'.
Proof.
  induction m as [|m IH]; intros data env count q i Hmeas Henv Hq Hlen;
    unfold module_decode_element_section_loop; rewrite loop_unfold;
    cbn beta iota; destruct (i s>= count) eqn:Hge;
    [sec_loop_start Henv | | sec_loop_start Henv | ].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (read_u32_leb_ok data q) as [r Hr]. rewrite Hr. cbn [bind].
    destruct r as [[table_idx q1]|e]; [|sec_loop_err].
    rewrite branch_ok. cbn [bind].
    pose proof (read_u32_leb_lt _ _ _ _ Hr) as Hlt.
    pose proof (read_u32_leb_le_len _ _ _ _ Hr) as Hq1.
    destruct (scalar_cast_u32_usize table_idx) as [j [Hcast Hj]].
    rewrite Hcast. cbn [bind].
    destruct (j s>= alloc_vec_Vec_len env.(module_Env_table_types)); [sec_done|].
    destruct (decode_const_expr_ok data q1 env Types_ValueType_I32)
      as [r1 [Hr1 Hce]].
    rewrite Hr1. cbn [bind].
    destruct r1 as [[offset q2]|e]; [|sec_loop_err].
    rewrite branch_ok. cbn [bind].
    destruct (Hce _ _ (ltac:(reflexivity))) as [Hlt2 Hq2].
    destruct (decode_func_indices_ok data q2 env Hq2 Hlen) as [r2 [Hr2 Hfi]].
    rewrite Hr2. cbn [bind].
    destruct r2 as [[init q3]|e]; [|sec_loop_err].
    rewrite branch_ok. cbn [bind].
    destruct (Hfi _ _ (ltac:(reflexivity))) as [Hlt3 Hq3].
    pose proof (es_elements Henv) as Hel.
    destruct (vec_push_ok env.(module_Env_elements)
                {| module_Element_table_idx := table_idx;
                   module_Element_offset := offset;
                   module_Element_init := init |} (ltac:(fits))) as [v Hpush].
    rewrite Hpush. cbn [bind].
    assert (Hu1 : to_Z 1%u32 = 1) by reflexivity.
    pose proof (u32_bounds count).
    destruct (u32_add_ok i 1%u32 (ltac:(lia))) as [i2 [Hadd Hi2]].
    rewrite Hadd. cbn [bind]. cbn beta iota.
    match goal with
    | [ |- context [loop _ (?e, _, _)] ] =>
        destruct (IH data e count q3 i2) as [r4 [e2 [Hr4 Hpost2]]]
    end.
    + rewrite Nat2Z.inj_succ in Hmeas. lia.
    + env_push Hpush Henv.
    + exact Hq3.
    + exact Hlen.
    + exists r4, e2. split; [exact Hr4|].
      intros q' Hc. destruct (Hpost2 _ Hc) as [A [B C]].
      split; [lia|]. split; [lia | exact C].
Qed.

(** Every section wrapper is the same three lines: read the entry count, then
    run the loop from the position after it. *)
Ltac sec_wrap L data pos env Henv Hpos Hlen :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  let count := fresh "count" in let p := fresh "p" in let e := fresh "e" in
  let Hlt := fresh "Hlt" in let Hple := fresh "Hple" in
  let Hz := fresh "Hz" in let Hc := fresh "Hc" in
  let r2 := fresh "r2" in let e2 := fresh "e2" in
  let Hr2 := fresh "Hr2" in let Hpost := fresh "Hpost" in
  let A := fresh "A" in let B := fresh "B" in let C := fresh "C" in
  destruct (read_u32_leb_ok data pos) as [r Hr]; rewrite Hr; cbn [bind];
  destruct r as [[count p]|e];
    [ rewrite branch_ok; cbn [bind]
    | rewrite branch_err; cbn [bind]; rewrite from_residual_op_err; cbn [bind];
      eexists; eexists; split; [reflexivity|]; intros ? Hc; discriminate ];
  pose proof (read_u32_leb_lt _ _ _ _ Hr) as Hlt;
  pose proof (read_u32_leb_le_len _ _ _ _ Hr) as Hple;
  assert (Hz : to_Z 0%u32 = 0) by reflexivity;
  pose proof (u32_bounds count);
  destruct (L (Z.to_nat (to_Z count)) data env count p 0%u32)
    as [r2 [e2 [Hr2 Hpost]]];
  [ rewrite Z2Nat.id by lia; lia
  | apply (env_small_mono _ pos); [exact Henv | lia]
  | exact Hple
  | exact Hlen
  | exists r2, e2; split; [exact Hr2|];
    intros ? Hc; destruct (Hpost _ Hc) as [A [B C]];
    split; [lia|]; split; [lia | exact C] ].

Lemma decode_table_section_ok : forall data pos env,
  env_small env pos -> to_Z pos <= dlen data -> dlen data <= module_bytes ->
  exists r e, module_decode_table_section data pos env = Ok (r, e)
              /\ forall q', r = Core_result_Result_Ok q' ->
                   to_Z pos <= to_Z q' /\ to_Z q' <= dlen data /\ env_small e q'.
Proof.
  intros data pos env Henv Hpos Hlen. unfold module_decode_table_section.
  sec_wrap decode_table_section_loop_ok data pos env Henv Hpos Hlen.
Qed.

Lemma decode_memory_section_ok : forall data pos env,
  env_small env pos -> to_Z pos <= dlen data -> dlen data <= module_bytes ->
  exists r e, module_decode_memory_section data pos env = Ok (r, e)
              /\ forall q', r = Core_result_Result_Ok q' ->
                   to_Z pos <= to_Z q' /\ to_Z q' <= dlen data /\ env_small e q'.
Proof.
  intros data pos env Henv Hpos Hlen. unfold module_decode_memory_section.
  sec_wrap decode_memory_section_loop_ok data pos env Henv Hpos Hlen.
Qed.

Lemma decode_function_section_ok : forall data pos env,
  env_small env pos -> to_Z pos <= dlen data -> dlen data <= module_bytes ->
  exists r e, module_decode_function_section data pos env = Ok (r, e)
              /\ forall q', r = Core_result_Result_Ok q' ->
                   to_Z pos <= to_Z q' /\ to_Z q' <= dlen data /\ env_small e q'.
Proof.
  intros data pos env Henv Hpos Hlen. unfold module_decode_function_section.
  sec_wrap decode_function_section_loop_ok data pos env Henv Hpos Hlen.
Qed.

Lemma decode_global_section_ok : forall data pos env,
  env_small env pos -> to_Z pos <= dlen data -> dlen data <= module_bytes ->
  exists r e, module_decode_global_section data pos env = Ok (r, e)
              /\ forall q', r = Core_result_Result_Ok q' ->
                   to_Z pos <= to_Z q' /\ to_Z q' <= dlen data /\ env_small e q'.
Proof.
  intros data pos env Henv Hpos Hlen. unfold module_decode_global_section.
  sec_wrap decode_global_section_loop_ok data pos env Henv Hpos Hlen.
Qed.

Lemma decode_export_section_ok : forall data pos env,
  env_small env pos -> to_Z pos <= dlen data -> dlen data <= module_bytes ->
  exists r e, module_decode_export_section data pos env = Ok (r, e)
              /\ forall q', r = Core_result_Result_Ok q' ->
                   to_Z pos <= to_Z q' /\ to_Z q' <= dlen data /\ env_small e q'.
Proof.
  intros data pos env Henv Hpos Hlen. unfold module_decode_export_section.
  sec_wrap decode_export_section_loop_ok data pos env Henv Hpos Hlen.
Qed.

Lemma decode_element_section_ok : forall data pos env,
  env_small env pos -> to_Z pos <= dlen data -> dlen data <= module_bytes ->
  exists r e, module_decode_element_section data pos env = Ok (r, e)
              /\ forall q', r = Core_result_Result_Ok q' ->
                   to_Z pos <= to_Z q' /\ to_Z q' <= dlen data /\ env_small e q'.
Proof.
  intros data pos env Henv Hpos Hlen. unfold module_decode_element_section.
  sec_wrap decode_element_section_loop_ok data pos env Henv Hpos Hlen.
Qed.

(** Spec 5.5.5. The one entry decoder with four shapes, and the only place
    the two import counters move. Each arm pushes onto the import list and
    onto the index space its kind belongs to; the counters are bounded the
    same way the vectors are, so incrementing one cannot overflow either. *)
Lemma decode_import_ok : forall data pos env,
  env_small env pos ->
  to_Z pos <= dlen data ->
  dlen data <= module_bytes ->
  exists r e, module_decode_import data pos env = Ok (r, e)
              /\ forall q', r = Core_result_Result_Ok q' ->
                   to_Z pos < to_Z q' /\ to_Z q' <= dlen data /\ env_small e q'.
Proof.
  intros data pos env Henv Hpos Hlen. unfold module_decode_import.
  destruct (decode_name_ok data pos Hpos Hlen) as [r Hr]. rewrite Hr. cbn [bind].
  destruct r as [[modname p1]|e]; [|sec_loop_err].
  rewrite branch_ok. cbn [bind].
  destruct (decode_name_step _ _ _ _ Hr Hpos) as [Hlt1 Hp1].
  destruct (decode_name_ok data p1 Hp1 Hlen) as [r1 Hr1]. rewrite Hr1. cbn [bind].
  destruct r1 as [[name p2]|e]; [|sec_loop_err].
  rewrite branch_ok. cbn [bind].
  destruct (decode_name_step _ _ _ _ Hr1 Hp1) as [Hlt2 Hp2].
  destruct (read_byte_total data p2) as [r2 Hr2]. rewrite Hr2. cbn [bind].
  destruct r2 as [[kind p3]|e]; [|sec_loop_err].
  rewrite branch_ok. cbn [bind].
  pose proof (read_byte_le_len _ _ _ _ Hr2) as Hp3.
  pose proof (proj2 (read_byte_ok _ _ _ _ Hr2)) as Hlt3.
  pose proof (es_types Henv) as Het. pose proof (es_imports Henv) as Hei.
  pose proof (es_ftypes Henv) as Hef. pose proof (es_tables Henv) as Hetab.
  pose proof (es_mems Henv) as Hem. pose proof (es_gtypes Henv) as Heg.
  pose proof (es_nfuncs Henv) as Henf. pose proof (es_nglobals Henv) as Heng.
  assert (Hone : to_Z 1%usize = 1) by reflexivity.
  destruct (kind s= 0%u8).
  { destruct (read_u32_leb_ok data p3) as [r3 Hr3]. rewrite Hr3. cbn [bind].
    destruct r3 as [[idx p4]|e]; [|sec_loop_err].
    rewrite branch_ok. cbn [bind].
    pose proof (read_u32_leb_le_len _ _ _ _ Hr3) as Hp4.
    pose proof (read_u32_leb_mono _ _ _ _ Hr3) as Hlt4.
    destruct (lookup_type_ok env idx (es_params Henv)) as [r4 [Hr4 Hft]].
    rewrite Hr4. cbn [bind].
    destruct r4 as [ft|e]; [|sec_loop_err].
    rewrite branch_ok. cbn [bind].
    pose proof (Hft _ (ltac:(reflexivity))) as Hsmall.
    destruct (vec_push_ok env.(module_Env_func_types) ft (ltac:(fits)))
      as [v Hpush]. rewrite Hpush. cbn [bind].
    destruct (usize_add_ok env.(module_Env_num_imported_funcs) 1%usize
                (ltac:(fits))) as [n [Hadd Hn]]. rewrite Hadd. cbn [bind].
    destruct (vec_push_ok env.(module_Env_imports)
                {| module_Import_module := modname; module_Import_name := name;
                   module_Import_desc := Module_ImportDesc_Func idx |}
                (ltac:(fits))) as [v1 Hpush1]. rewrite Hpush1. cbn [bind].
    eexists. eexists. split; [reflexivity|]. intros q' Hc. injection Hc as <-.
    split; [lia|]. split; [lia|].
    apply (env_small_mono _ p3); [|lia]. env_push2 Hpush Hpush1 Henv. }
  destruct (kind s= 1%u8).
  { destruct (decode_table_type_ok data p3) as [r3 Hr3]. rewrite Hr3. cbn [bind].
    destruct r3 as [[tt1 p4]|e]; [|sec_loop_err].
    rewrite branch_ok. cbn [bind].
    destruct (decode_table_type_step _ _ _ _ Hr3) as [Hlt4 Hp4].
    destruct (vec_push_ok env.(module_Env_table_types) tt1 (ltac:(fits)))
      as [v Hpush]. rewrite Hpush. cbn [bind].
    destruct (alloc_vec_Vec_len v s> limits_max_tables); [sec_done|].
    destruct (vec_push_ok env.(module_Env_imports)
                {| module_Import_module := modname; module_Import_name := name;
                   module_Import_desc := Module_ImportDesc_Table tt1 |}
                (ltac:(fits))) as [v1 Hpush1]. rewrite Hpush1. cbn [bind].
    eexists. eexists. split; [reflexivity|]. intros q' Hc. injection Hc as <-.
    split; [lia|]. split; [lia|].
    apply (env_small_mono _ p3); [|lia]. env_push2 Hpush Hpush1 Henv. }
  destruct (kind s= 2%u8).
  { destruct (decode_mem_type_ok data p3) as [r3 Hr3]. rewrite Hr3. cbn [bind].
    destruct r3 as [[mt p4]|e]; [|sec_loop_err].
    rewrite branch_ok. cbn [bind].
    destruct (decode_mem_type_step _ _ _ _ Hr3) as [Hlt4 Hp4].
    destruct (vec_push_ok env.(module_Env_mem_types) mt (ltac:(fits)))
      as [v Hpush]. rewrite Hpush. cbn [bind].
    destruct (alloc_vec_Vec_len v s> limits_max_memories); [sec_done|].
    destruct (vec_push_ok env.(module_Env_imports)
                {| module_Import_module := modname; module_Import_name := name;
                   module_Import_desc := Module_ImportDesc_Memory mt |}
                (ltac:(fits))) as [v1 Hpush1]. rewrite Hpush1. cbn [bind].
    eexists. eexists. split; [reflexivity|]. intros q' Hc. injection Hc as <-.
    split; [lia|]. split; [lia|].
    apply (env_small_mono _ p3); [|lia]. env_push2 Hpush Hpush1 Henv. }
  destruct (kind s= 3%u8); [|sec_done].
  destruct (decode_global_type_ok data p3) as [r3 Hr3]. rewrite Hr3. cbn [bind].
  destruct r3 as [[gt p4]|e]; [|sec_loop_err].
  rewrite branch_ok. cbn [bind].
  destruct (decode_global_type_step _ _ _ _ Hr3) as [Hlt4 Hp4].
  destruct (vec_push_ok env.(module_Env_global_types) gt (ltac:(fits)))
    as [v Hpush]. rewrite Hpush. cbn [bind].
  destruct (usize_add_ok env.(module_Env_num_imported_globals) 1%usize
              (ltac:(fits))) as [n [Hadd Hn]]. rewrite Hadd. cbn [bind].
  destruct (vec_push_ok env.(module_Env_imports)
              {| module_Import_module := modname; module_Import_name := name;
                 module_Import_desc := Module_ImportDesc_Global gt |}
              (ltac:(fits))) as [v1 Hpush1]. rewrite Hpush1. cbn [bind].
  eexists. eexists. split; [reflexivity|]. intros q' Hc. injection Hc as <-.
  split; [lia|]. split; [lia|].
  apply (env_small_mono _ p3); [|lia]. env_push2 Hpush Hpush1 Henv.
Qed.

Lemma decode_import_section_loop_ok : forall m data env count q i,
  to_Z count - to_Z i <= Z.of_nat m ->
  env_small env q ->
  to_Z q <= dlen data ->
  dlen data <= module_bytes ->
  exists r e, module_decode_import_section_loop data env count q i = Ok (r, e)
              /\ forall q', r = Core_result_Result_Ok q' ->
                   to_Z q <= to_Z q' /\ to_Z q' <= dlen data /\ env_small e q'.
Proof.
  induction m as [|m IH]; intros data env count q i Hmeas Henv Hq Hlen;
    unfold module_decode_import_section_loop; rewrite loop_unfold;
    cbn beta iota; destruct (i s>= count) eqn:Hge;
    [sec_loop_start Henv | | sec_loop_start Henv | ].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (decode_import_ok data q env Henv Hq Hlen) as [r [e [Hr Hpost]]].
    rewrite Hr. cbn [bind].
    destruct r as [q1|er];
      [|rewrite branch_err; cbn [bind]; rewrite from_residual_err; cbn [bind];
        eexists; eexists; split; [reflexivity|]; intros ? Hc; discriminate].
    rewrite branch_ok. cbn [bind].
    destruct (Hpost _ (ltac:(reflexivity))) as [Hlt [Hq1 Henv1]].
    assert (Hu1 : to_Z 1%u32 = 1) by reflexivity.
    pose proof (u32_bounds count).
    destruct (u32_add_ok i 1%u32 (ltac:(lia))) as [i2 [Hadd Hi2]].
    rewrite Hadd. cbn [bind]. cbn beta iota.
    destruct (IH data e count q1 i2) as [r2 [e2 [Hr2 Hpost2]]].
    + rewrite Nat2Z.inj_succ in Hmeas. lia.
    + exact Henv1.
    + exact Hq1.
    + exact Hlen.
    + exists r2, e2. split; [exact Hr2|].
      intros q' Hc. destruct (Hpost2 _ Hc) as [A [B C]].
      split; [lia|]. split; [lia | exact C].
Qed.

Lemma decode_import_section_ok : forall data pos env,
  env_small env pos -> to_Z pos <= dlen data -> dlen data <= module_bytes ->
  exists r e, module_decode_import_section data pos env = Ok (r, e)
              /\ forall q', r = Core_result_Result_Ok q' ->
                   to_Z pos <= to_Z q' /\ to_Z q' <= dlen data /\ env_small e q'.
Proof.
  intros data pos env Henv Hpos Hlen. unfold module_decode_import_section.
  sec_wrap decode_import_section_loop_ok data pos env Henv Hpos Hlen.
Qed.

(* ================================================================== *)
(** ** The environment as a whole                                     *)
(* ================================================================== *)

Lemma decode_env_section_ok : forall data pos id env,
  env_small env pos -> to_Z pos <= dlen data -> dlen data <= module_bytes ->
  exists r e, module_decode_env_section data pos id env = Ok (r, e)
              /\ forall q', r = Core_result_Result_Ok q' ->
                   to_Z pos <= to_Z q' /\ to_Z q' <= dlen data /\ env_small e q'.
Proof.
  intros data pos id env Henv Hpos Hlen. unfold module_decode_env_section.
  repeat first
    [ solve [apply decode_type_section_ok; assumption]
    | solve [apply decode_import_section_ok; assumption]
    | solve [apply decode_function_section_ok; assumption]
    | solve [apply decode_table_section_ok; assumption]
    | solve [apply decode_memory_section_ok; assumption]
    | solve [apply decode_global_section_ok; assumption]
    | solve [apply decode_export_section_ok; assumption]
    | solve [apply decode_start_section_ok; assumption]
    | solve [apply decode_element_section_ok; assumption]
    | solve [eexists; eexists; split; [reflexivity|]; intros ? Hc; discriminate]
    | match goal with
      | [ |- context [if ?c then _ else _] ] => destruct c
      end ].
Qed.

(** Every module hook returns. The module visitor has one hook, so this is one
    conjunct where [OpIter_Visit.hooks_total] is 174, but it is the same claim
    and it is discharged the same way: a hook is unverified code, and nothing
    in its type stops it looping or failing. *)
Definition module_hooks_total {V : Type} (inst : module_ModuleVisitor_t V) : Prop :=
  forall v c, exists r v',
    inst.(module_ModuleVisitor_t_on_custom_section) v c = Ok (r, v').

Lemma nop_module_hooks_total :
  module_hooks_total module_EmptyModuleVisitor_Insts_ItascaModuleModuleVisitor.
Proof.
  unfold module_hooks_total,
         module_EmptyModuleVisitor_Insts_ItascaModuleModuleVisitor.
  intros v c. cbn [module_ModuleVisitor_t_on_custom_section].
  unfold module_EmptyModuleVisitor_Insts_ItascaModuleModuleVisitor_on_custom_section.
  eexists. eexists. reflexivity.
Qed.

(** Spec 5.5.16 up to the code section. The measure is the bytes left: a
    section header ends strictly after the position it was read at, so the
    cursor advances even for an empty section. *)
Lemma validate_env_with_loop_ok :
  forall V (inst : module_ModuleVisitor_t V) m data vis env q last_id,
  module_hooks_total inst ->
  dlen data - to_Z q <= Z.of_nat m ->
  env_small env q ->
  to_Z q <= dlen data ->
  dlen data <= module_bytes ->
  exists r vis',
    module_validate_env_with_loop inst data vis env q last_id = Ok (r, vis')
    /\ forall e q', r = Core_result_Result_Ok (e, q') ->
         to_Z q' <= dlen data /\ env_small e q'.
Proof.
  intros V inst m. induction m as [|m IH];
    intros data vis env q last_id Hhooks Hmeas Henv Hq Hlen;
    unfold module_validate_env_with_loop; rewrite loop_unfold; cbn beta iota;
    destruct (q s>= slice_len data) eqn:Hge;
    [ eexists; eexists; split; [reflexivity|]; intros ? ? Hc;
      injection Hc as <- <-; split; [lia | exact Henv]
    | | eexists; eexists; split; [reflexivity|]; intros ? ? Hc;
        injection Hc as <- <-; split; [lia | exact Henv]
    | ].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (read_section_header_ok data q Hq) as [r Hr]. rewrite Hr. cbn [bind].
    destruct r as [[[id start] end1]|e]; [|try_err_post].
    rewrite branch_ok. cbn [bind].
    destruct (read_section_header_step _ _ _ _ _ Hr) as [Hlt [Hse Hend]].
    destruct (id s= module_section_custom).
    { destruct (decode_custom_section_ok data start end1 (ltac:(lia)) Hlen)
        as [r1 Hr1]. rewrite Hr1. cbn [bind].
      destruct r1 as [c|e]; [|try_err_post].
      rewrite branch_ok. cbn [bind].
      (* the consumer is shown the section, and its hook returns *)
      destruct (Hhooks vis c) as [rh [vis1 Hh]]. rewrite Hh. cbn [bind].
      destruct rh as [u|ev];
        [|cbn beta iota; finish_post].
      cbn beta iota.
      destruct (IH data vis1 env end1 last_id) as [r2 [vis2 [Hr2 Hpost]]].
      - exact Hhooks.
      - rewrite Nat2Z.inj_succ in Hmeas. lia.
      - apply (env_small_mono _ q); [exact Henv | lia].
      - lia.
      - exact Hlen.
      - exists r2. exists vis2. split; [exact Hr2|]. exact Hpost. }
    destruct (id s>= module_section_code).
    { eexists; eexists; split; [reflexivity|]; intros ? ? Hc;
      injection Hc as <- <-. split; [lia | exact Henv]. }
    destruct (id s<= last_id);
      [eexists; eexists; split; [reflexivity|]; intros ? ? Hc; discriminate|].
    destruct (decode_env_section_ok data start id env
                (ltac:(apply (env_small_mono _ q); [exact Henv | lia]))
                (ltac:(lia)) Hlen) as [r1 [e1 [Hr1 Hpost1]]].
    rewrite Hr1. cbn [bind].
    destruct r1 as [p|er]; [|try_err_post].
    rewrite branch_ok. cbn [bind].
    destruct (Hpost1 _ (ltac:(reflexivity))) as [Hp1 [Hp2 Henv1]].
    destruct (p s<> end1) eqn:Hne;
      [eexists; eexists; split; [reflexivity|]; intros ? ? Hc; discriminate|].
    apply Bool.negb_false_iff in Hne. apply scalar_eqb_true in Hne.
    cbn beta iota.
    destruct (IH data vis e1 end1 id) as [r2 [vis2 [Hr2 Hpost]]].
    + exact Hhooks.
    + rewrite Nat2Z.inj_succ in Hmeas. lia.
    + apply (env_small_mono _ p); [exact Henv1 | lia].
    + lia.
    + exact Hlen.
    + exists r2. exists vis2. split; [exact Hr2|]. exact Hpost.
Qed.

(** The bridges between a decoder and its `_with` form at the do-nothing
    consumer, the same pair [code_entry_nop] and [code_entry_nop_inv] are one
    level down. The projection is the only content: [validate_env] is
    [validate_env_with] at [tt] with the visitor state thrown away. *)
Lemma validate_env_nop : forall data r,
  module_validate_env_with module_EmptyModuleVisitor_Insts_ItascaModuleModuleVisitor
    data tt = Ok (r, tt) ->
  module_validate_env data = Ok r.
Proof.
  intros data r H. unfold module_validate_env. rewrite H. cbn [bind]. reflexivity.
Qed.

Lemma validate_tail_nop : forall data pos env r,
  module_validate_tail_with module_EmptyModuleVisitor_Insts_ItascaModuleModuleVisitor
    data pos env tt = Ok (r, tt) ->
  module_validate_tail data pos env = Ok r.
Proof.
  intros data pos env r H. unfold module_validate_tail. rewrite H. cbn [bind].
  reflexivity.
Qed.

Lemma validate_env_with_ok : forall V (inst : module_ModuleVisitor_t V) vis data,
  module_hooks_total inst ->
  dlen data <= module_bytes ->
  exists r vis', module_validate_env_with inst data vis = Ok (r, vis')
            /\ forall e q', r = Core_result_Result_Ok (e, q') ->
                 to_Z q' <= dlen data /\ env_small e q'.
Proof.
  intros V inst vis data Hhooks Hlen. unfold module_validate_env_with.
  destruct module_Env_new as [env0|] eqn:Hnew; cbn [bind]; [|discriminate Hnew].
  destruct (read_header_ok data) as [r Hr]. rewrite Hr. cbn [bind].
  destruct r as [p|e]; [|try_err_post].
  rewrite branch_ok. cbn [bind].
  pose proof (read_header_step _ _ Hr) as Hp.
  pose proof (usize_nonneg p).
  destruct (validate_env_with_loop_ok V inst (Z.to_nat (dlen data)) data vis env0
              p 0%u8) as [r2 [vis2 [Hr2 Hpost]]].
  - exact Hhooks.
  - rewrite Z2Nat.id by (pose proof (usize_nonneg (slice_len data)); lia). lia.
  - exact (env_small_new p env0 Hnew).
  - exact Hp.
  - exact Hlen.
  - exists r2. exists vis2. split; [exact Hr2|]. exact Hpost.
Qed.

Corollary validate_env_ok : forall data,
  dlen data <= module_bytes ->
  exists r, module_validate_env data = Ok r
            /\ forall e q', r = Core_result_Result_Ok (e, q') ->
                 to_Z q' <= dlen data /\ env_small e q'.
Proof.
  intros data Hlen.
  destruct (validate_env_with_ok _
              module_EmptyModuleVisitor_Insts_ItascaModuleModuleVisitor tt data
              nop_module_hooks_total Hlen) as [r [vis' [Hr Hpost]]].
  exists r. split; [|exact Hpost].
  apply validate_env_nop. destruct vis'. exact Hr.
Qed.

(* ================================================================== *)
(** ** The code section                                               *)
(* ================================================================== *)

(** One code entry. Everything before the body is the same accounting as the
    rest of the file; the body itself is the one sub-slice the decoder takes,
    and [validate_body_no_panic] carries it from there. *)
(** [validate_code_entry] is [validate_code_entry_with] at [EmptyOpVisitor], whose
    state is the unit, so a run of the one is a run of the other. Every proof
    below is about the generic function; these two carry it across. *)
(** The frame hook, named on its own so the entry's totality proof does not
    destructure the whole conjunction. *)
Lemma frame_hook_total : forall V (inst : code_OpVisitor_t V) v ctx tidx bb ee,
  hooks_total inst ->
  exists r v', inst.(code_OpVisitor_t_on_function_start) v ctx tidx bb ee
               = Ok (r, v').
Proof.
  intros V inst v ctx tidx bb ee H. unfold hooks_total in H.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  eauto.
Qed.

Lemma code_entry_nop : forall data pos env index r,
  module_validate_code_entry_with code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor
    data pos env index tt = Ok (r, tt) ->
  module_validate_code_entry data pos env index = Ok r.
Proof.
  intros data pos env index r H. unfold module_validate_code_entry.
  rewrite H. cbn [bind]. reflexivity.
Qed.

Lemma code_entry_nop_inv : forall data pos env index r,
  module_validate_code_entry data pos env index = Ok r ->
  module_validate_code_entry_with code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor
    data pos env index tt = Ok (r, tt).
Proof.
  intros data pos env index r H. unfold module_validate_code_entry in H.
  destruct (module_validate_code_entry_with
              code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor data pos env index tt)
    as [[r0 v0]|] eqn:Hw; cbn [bind] in H; [|discriminate].
  injection H as <-. destruct v0. reflexivity.
Qed.

Lemma validate_code_entry_with_ok : forall V (inst : code_OpVisitor_t V) vis
                                          data pos env index,
  hooks_total inst ->
  env_small env pos ->
  to_Z pos <= dlen data ->
  dlen data <= module_bytes ->
  exists r vis',
    module_validate_code_entry_with inst data pos env index vis = Ok (r, vis')
    /\ forall q', r = Core_result_Result_Ok q' ->
         to_Z pos < to_Z q' /\ to_Z q' <= dlen data.
Proof.
  intros V inst vis data pos env index Hvt Henv Hpos Hlen.
  unfold module_validate_code_entry_with.
  destruct (index s>= alloc_vec_Vec_len env.(module_Env_func_type_indices)) eqn:Hix;
    [finish_post|].
  destruct (read_u32_leb_ok data pos) as [r Hr]. rewrite Hr. cbn [bind].
  destruct r as [[size p]|e]; [|try_err_post].
  rewrite branch_ok. cbn [bind].
  pose proof (read_u32_leb_lt _ _ _ _ Hr) as Hlt.
  pose proof (read_u32_leb_le_len _ _ _ _ Hr) as Hple.
  destruct (scalar_cast_u32_usize size) as [n [Hcast Hn]].
  rewrite Hcast. cbn [bind].
  destruct (have_bytes_ok data p n Hple) as [rh [Hh Hcase]].
  rewrite Hh. cbn [bind].
  destruct Hcase as [-> | ->]; [|try_err_post].
  rewrite branch_ok. cbn [bind].
  pose proof (have_bytes_room data p n Hh) as Hroom.
  pose proof (usize_nonneg n).
  destruct (usize_add_ok p n (ltac:(fits))) as [end1 [Hadd Hend]].
  rewrite Hadd. cbn [bind].
  destruct (vec_index_ok env.(module_Env_func_type_indices) index Hix)
    as [tidx Hidx].
  rewrite Hidx. cbn [bind].
  destruct (scalar_cast_u32_usize tidx) as [t [Hcast2 Ht]].
  rewrite Hcast2. cbn [bind].
  destruct (t s>= alloc_vec_Vec_len env.(module_Env_types)) eqn:Hty;
    [finish_post|].
  destruct (vec_index_ok env.(module_Env_types) t Hty) as [ft Hft].
  rewrite Hft. cbn [bind].
  assert (Hsmall : ft_small ft).
  { pose proof (es_params Henv) as Hall.
    rewrite vec_index_spec in Hft.
    destruct (List.nth_error (vec_list env.(module_Env_types))
                (Z.to_nat (to_Z t))) as [x|] eqn:Hnth; [|discriminate].
    injection Hft as <-.
    rewrite List.Forall_forall in Hall. apply Hall.
    eapply List.nth_error_In. exact Hnth. }
  unfold ft_small in Hsmall.
  rewrite vec_deref_spec.
  destruct (decode_and_build_locals_ok data p ft.(types_FuncType_params)
    Hple ltac:(rewrite slice_len_spec; exact Hsmall)) as [r1 [Hr1 Hloc]].
  rewrite Hr1. cbn [bind].
  destruct r1 as [[locals p1]|e]; [|try_err_post].
  rewrite branch_ok. cbn [bind].
  destruct (Hloc _ _ (ltac:(reflexivity))) as [Hlt1 [Hp1 Hdec]].
  destruct (p1 s> end1) eqn:Hover; [finish_post|].
  apply scalar_gtb_false in Hover.
  rewrite vec_deref_spec.
  destruct (single_result_ok ft.(types_FuncType_results)) as [res Hres].
  rewrite Hres. cbn [bind].
  (* the frame hook returns, since the consumer's hooks do *)
  destruct (frame_hook_total V inst vis
              {| code_Context_locals := locals;
                 code_Context_results := res |} tidx p1 end1 Hvt) as [rf [vf Hhk]].
  rewrite Hhk. cbn [bind].
  destruct rf as [uf|ef]; cbn beta iota; [|finish_post].
  destruct (slice_range_ok data p1 end1 (ltac:(lia)) (ltac:(rewrite <- slice_len_spec; lia)))
    as [body [Hbody _]].
  rewrite Hbody. cbn [bind].
  destruct (validate_body_with_no_panic V inst vf body env
              {| code_Context_locals := locals;
                 code_Context_results := res |} Hvt) as [rb Hrb].
  rewrite Hrb. cbn [bind].
  destruct rb as [rb0 vb]. destruct rb0 as [u|eb].
  - eexists. eexists. split; [reflexivity|]. intros q' Hc.
    injection Hc as <-. lia.
  - eexists. eexists. split; [reflexivity|]. intros ? Hc. discriminate.
Qed.

(** The same for the validating-only consumer, which is what [validate_code]
    drives, and whose hooks are total by computation. *)
Corollary validate_code_entry_ok : forall data pos env index,
  env_small env pos ->
  to_Z pos <= dlen data ->
  dlen data <= module_bytes ->
  exists r, module_validate_code_entry data pos env index = Ok r
            /\ forall q', r = Core_result_Result_Ok q' ->
                 to_Z pos < to_Z q' /\ to_Z q' <= dlen data.
Proof.
  intros data pos env index Henv Hpos Hlen.
  destruct (validate_code_entry_with_ok _
              code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor tt data pos env index
              nop_hooks_total Henv Hpos Hlen) as [r [vis' [Hw Hq]]].
  destruct vis'. exists r. split; [apply code_entry_nop; exact Hw | exact Hq].
Qed.

(** The framing step: reading a size prefix cannot fail on any bytes, and what
    it reports moves the cursor forward and stays inside the input. Both halves
    are what the walk's measure and its next read need. *)
Lemma code_entry_extent_ok : forall data pos,
  to_Z pos <= dlen data ->
  dlen data <= module_bytes ->
  exists r, module_code_entry_extent data pos = Ok r
            /\ forall b e, r = Core_result_Result_Ok (b, e) ->
                 to_Z pos < to_Z b /\ to_Z b <= to_Z e /\ to_Z e <= dlen data.
Proof.
  intros data pos Hpos Hlen. unfold module_code_entry_extent.
  destruct (read_u32_leb_ok data pos) as [r Hr]. rewrite Hr. cbn [bind].
  destruct r as [[size p]|e];
    [|try_err_rw; solve [eexists; split; [reflexivity | intros ? ? Hc; discriminate]]].
  rewrite branch_ok. cbn [bind].
  pose proof (read_u32_leb_lt _ _ _ _ Hr) as Hlt.
  pose proof (read_u32_leb_le_len _ _ _ _ Hr) as Hple.
  destruct (scalar_cast_u32_usize size) as [n [Hcast Hn]].
  rewrite Hcast. cbn [bind].
  destruct (have_bytes_ok data p n Hple) as [rh [Hh Hcase]].
  rewrite Hh. cbn [bind].
  destruct Hcase as [-> | ->];
    [|try_err_rw; solve [eexists; split; [reflexivity | intros ? ? Hc; discriminate]]].
  rewrite branch_ok. cbn [bind].
  pose proof (have_bytes_room data p n Hh) as Hroom.
  pose proof (usize_nonneg n).
  destruct (usize_add_ok p n (ltac:(fits))) as [q [Hadd Hq]].
  rewrite Hadd. cbn [bind].
  eexists. split; [reflexivity|]. intros b e Hc. injection Hc as <- <-. lia.
Qed.

(** Framing an entry reads its size prefix and nothing else, so the contents
    begin at most [MAX_LEB_BYTES] along. This is the bound the walk's first
    [on_need_bytes] per entry reports, so it is what makes that wait cover the
    read that follows it. The second wait per entry is reported as the entry's
    own end, which [Module_Sound.code_entry_extent_frames] pins to the
    validator's. *)
Lemma code_entry_extent_span : forall data pos contents fin,
  module_code_entry_extent data pos
    = Ok (Core_result_Result_Ok (contents, fin)) ->
  to_Z contents <= to_Z pos + to_Z limits_max_leb_bytes.
Proof.
  intros data pos contents fin H. unfold module_code_entry_extent in H.
  destruct (reader_read_u32_leb data pos) as [r|] eqn:Hr; cbn [bind] in H;
    [|discriminate].
  destruct r as [[size p]|e]; [|err_absurd H].
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_u32_leb_span _ _ _ _ Hr) as Hp.
  destruct (scalar_cast U32 Usize size) as [n|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  destruct (module_have_bytes data p n) as [rh|] eqn:Hh; cbn [bind] in H;
    [|discriminate].
  destruct rh as [u|e]; [|err_absurd H]. destruct u.
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (usize_add p n) as [e2|] eqn:Hadd; cbn [bind] in H; [|discriminate].
  injection H as <- _. lia.
Qed.

(** Every code hook returns.
    [on_need_bytes] is unconditional; [on_code_entry] is not, because its
    default *is* [validate_code_entry], and that is total only where the
    environment is small and the position is inside the input. So this is
    indexed by the bytes and the environment rather than closed, and the walk
    establishes the guards before it fires the hook. The one place the
    [hooks_total] pattern does not copy verbatim from [OpIter_Visit]. *)
Definition code_hooks_total {V : Type} (inst : module_CodeVisitor_t V)
                            (data : slice u8) (env : module_Env_t) : Prop :=
  (forall v e, exists r v',
     inst.(module_CodeVisitor_t_on_need_bytes) v e = Ok (r, v'))
  /\ (forall v index pos contents fin,
        env_small env pos ->
        to_Z pos <= dlen data ->
        dlen data <= module_bytes ->
        exists r v',
          inst.(module_CodeVisitor_t_on_code_entry) v data env index pos contents fin
            = Ok (r, v')).

Lemma validating_code_hooks_total : forall data env,
  code_hooks_total
    module_ValidatingCodeVisitor_Insts_ItascaModuleCodeVisitor data env.
Proof.
  intros data env. unfold code_hooks_total,
    module_ValidatingCodeVisitor_Insts_ItascaModuleCodeVisitor.
  split.
  - intros v e. cbn [module_CodeVisitor_t_on_need_bytes].
    unfold module_ValidatingCodeVisitor_Insts_ItascaModuleCodeVisitor_on_need_bytes.
    eexists. eexists. reflexivity.
  - intros v index pos contents fin Henv Hpos Hlen.
    cbn [module_CodeVisitor_t_on_code_entry].
    unfold module_ValidatingCodeVisitor_Insts_ItascaModuleCodeVisitor_on_code_entry.
    destruct (validate_code_entry_ok data pos env index Henv Hpos Hlen)
      as [r [Hr _]].
    rewrite Hr. cbn [bind].
    destruct r as [q|e]; [|try_err_rw; eexists; eexists; reflexivity].
    rewrite branch_ok. cbn [bind]. eexists. eexists. reflexivity.
Qed.

Lemma validate_code_entries_with_loop_ok :
  forall V (inst : module_CodeVisitor_t V) m data env vis q i,
  code_hooks_total inst data env ->
  Z.of_nat (List.length (vec_list env.(module_Env_func_type_indices))) - to_Z i
    <= Z.of_nat m ->
  env_small env q ->
  to_Z q <= dlen data ->
  dlen data <= module_bytes ->
  exists r vis',
    module_validate_code_entries_with_loop inst data env vis q i = Ok (r, vis')
    /\ forall q', r = Core_result_Result_Ok q' ->
         to_Z q <= to_Z q' /\ to_Z q' <= dlen data.
Proof.
  intros V inst m. induction m as [|m IH];
    intros data env vis q i [Hneed Hentry] Hmeas Henv Hq Hlen;
    unfold module_validate_code_entries_with_loop; rewrite loop_unfold;
    cbn beta iota;
    destruct (i s>= alloc_vec_Vec_len env.(module_Env_func_type_indices)) eqn:Hge;
    [ eexists; eexists; split; [reflexivity|]; intros ? Hc; injection Hc as <-;
      split; lia
    | | eexists; eexists; split; [reflexivity|]; intros ? Hc; injection Hc as <-;
        split; lia
    | ].
  - exfalso. apply scalar_geb_false_lt in Hge. rewrite vec_len_spec in Hge.
    cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge. rewrite vec_len_spec in Hge.
    (* the framing read's own bound: the cursor is inside a file no bigger than
       the module cap, so asking for five more bytes cannot overflow *)
    pose proof (usize_nonneg q).
    assert (Hadd5 : to_Z q + to_Z limits_max_leb_bytes <= usize_max).
    { unfold limits_max_leb_bytes. pose proof module_bytes_fits. cbn. lia. }
    destruct (usize_add_ok q limits_max_leb_bytes Hadd5) as [qw [Hqw _]].
    rewrite Hqw. cbn [bind].
    destruct (Hneed vis qw) as [rn [vis1 Hn]]. rewrite Hn. cbn [bind].
    destruct rn as [u|en]; [|try_err_post].
    rewrite branch_ok. cbn [bind].
    destruct (code_entry_extent_ok data q Hq Hlen) as [rx [Hx Hxpost]].
    rewrite Hx. cbn [bind].
    destruct rx as [[contents fin]|ex]; [|try_err_post].
    rewrite branch_ok. cbn [bind].
    destruct (Hxpost _ _ (ltac:(reflexivity))) as [Hlt [Hbe Hfd]].
    destruct (Hneed vis1 fin) as [rn2 [vis2 Hn2]]. rewrite Hn2. cbn [bind].
    destruct rn2 as [u2|en2]; [|try_err_post].
    rewrite branch_ok. cbn [bind].
    destruct (Hentry vis2 i q contents fin Henv Hq Hlen) as [re [vis3 He]].
    rewrite He. cbn [bind].
    destruct re as [u3|ee]; [|try_err_post].
    rewrite branch_ok. cbn [bind].
    destruct (usize_add_1_ok i (ltac:(pose proof (usize_le_max
                (alloc_vec_Vec_len env.(module_Env_func_type_indices)));
                rewrite vec_len_spec in *; lia))) as [i2 [Hadd Hi2]].
    rewrite Hadd. cbn [bind].
    destruct (IH data env vis3 fin i2) as [r2 [vis4 [Hr2 Hpost2]]].
    + split; [exact Hneed | exact Hentry].
    + rewrite Nat2Z.inj_succ in Hmeas. lia.
    + apply (env_small_mono _ q); [exact Henv | lia].
    + lia.
    + exact Hlen.
    + exists r2. exists vis4. split; [exact Hr2|].
      intros q' Hc. destruct (Hpost2 _ Hc) as [A B]. split; lia.
Qed.

Lemma no_code_section_ok : forall env,
  exists r, module_no_code_section env = Ok r
            /\ forall cs, r = Core_result_Result_Ok cs -> cs = None.
Proof.
  intros env. unfold module_no_code_section.
  rewrite vec_is_empty_spec. cbn [bind].
  destruct (match vec_list env.(module_Env_func_type_indices) with
            | [] => true | _ => false end);
    (eexists; split; [reflexivity|]; intros cs Hc);
    [injection Hc as <-; reflexivity | discriminate].
Qed.

(** Reading the header cannot fail either, and what it reports frames the
    entries: they start inside the file and the section ends inside it. Named on
    its own because [validate_code] and a consumer driving the entries itself
    both start here. *)
Lemma code_section_ok : forall data pos env,
  to_Z pos <= dlen data ->
  exists r, module_code_section data pos env = Ok r
            /\ forall cs, r = Core_result_Result_Ok (Some cs) ->
                 to_Z pos <= to_Z cs.(module_CodeSection_entries)
                 /\ to_Z cs.(module_CodeSection_entries) <= dlen data
                 /\ to_Z pos <= to_Z cs.(module_CodeSection_end)
                 /\ to_Z cs.(module_CodeSection_end) <= dlen data.
Proof.
  intros data pos env Hpos. unfold module_code_section.
  destruct (pos s>= slice_len data) eqn:Hge.
  { destruct (no_code_section_ok env) as [r [Hr Hno]].
    exists r. split; [exact Hr|]. intros cs Hc.
    discriminate (Hno _ Hc). }
  apply scalar_geb_false_lt in Hge. rewrite slice_len_spec in Hge.
  destruct (read_section_header_ok data pos (ltac:(lia))) as [r Hr].
  rewrite Hr. cbn [bind].
  destruct r as [[[id start] end1]|e]; [|try_err_post].
  rewrite branch_ok. cbn [bind].
  destruct (read_section_header_step _ _ _ _ _ Hr) as [Hlt [Hse Hend]].
  destruct (id s<> module_section_code).
  { destruct (no_code_section_ok env) as [r1 [Hr1 Hno]].
    exists r1. split; [exact Hr1|]. intros cs Hc.
    discriminate (Hno _ Hc). }
  destruct (read_u32_leb_ok data start) as [r1 Hr1]. rewrite Hr1. cbn [bind].
  destruct r1 as [[count p]|e]; [|try_err_post].
  rewrite branch_ok. cbn [bind].
  pose proof (read_u32_leb_lt _ _ _ _ Hr1) as Hlt1.
  pose proof (read_u32_leb_le_len _ _ _ _ Hr1) as Hple.
  destruct (scalar_cast_u32_usize count) as [n [Hcast Hn]].
  rewrite Hcast. cbn [bind].
  destruct (n s<> alloc_vec_Vec_len env.(module_Env_func_type_indices));
    [eexists; split; [reflexivity|]; intros ? Hc; discriminate|].
  eexists. split; [reflexivity|]. intros cs Hc. injection Hc as <-.
  cbn. lia.
Qed.

(** The header's extent, which is what [validate_code_with] waits for before
    reading it: an id byte, a size, and an entry count, so the first entry
    starts at most [MAX_CODE_HEADER_BYTES] along. The absent cases return
    [None] and read nothing past the header, so the [Some] case is the whole
    of the obligation. *)
Lemma code_section_span : forall data pos env cs,
  module_code_section data pos env
    = Ok (Core_result_Result_Ok (Some cs)) ->
  to_Z cs.(module_CodeSection_entries)
    <= to_Z pos + to_Z limits_max_code_header_bytes.
Proof.
  intros data pos env cs H. unfold module_code_section in H.
  assert (Hh : to_Z limits_max_code_header_bytes = 11) by reflexivity.
  rewrite Hh.
  (* the two absent cases return [None], so neither can be this run *)
  assert (Hnone : forall r, module_no_code_section env
                    = Ok (Core_result_Result_Ok (Some r)) -> False).
  { intros r Hno. unfold module_no_code_section in Hno.
    rewrite vec_is_empty_spec in Hno. cbn [bind] in Hno.
    destruct (vec_list env.(module_Env_func_type_indices)); discriminate. }
  destruct (pos s>= slice_len data); [exfalso; exact (Hnone _ H)|].
  destruct (module_read_section_header data pos) as [r|] eqn:Hhdr;
    cbn [bind] in H; [|discriminate].
  destruct r as [[[id start] fin]|e]; [|err_absurd H].
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_section_header_span _ _ _ _ _ Hhdr) as Hstart.
  assert (H5 : to_Z limits_max_leb_bytes = 5) by reflexivity.
  rewrite H5 in Hstart.
  destruct (id s<> module_section_code); [exfalso; exact (Hnone _ H)|].
  destruct (reader_read_u32_leb data start) as [r1|] eqn:Hr1; cbn [bind] in H;
    [|discriminate].
  destruct r1 as [[count p]|e]; [|err_absurd H].
  rewrite branch_ok in H. cbn [bind] in H.
  pose proof (read_u32_leb_span _ _ _ _ Hr1) as Hp. rewrite H5 in Hp.
  destruct (scalar_cast U32 Usize count) as [n|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  destruct (n s<> alloc_vec_Vec_len env.(module_Env_func_type_indices));
    [discriminate|].
  injection H as <-. cbn [module_CodeSection_entries]. lia.
Qed.

Lemma validate_code_with_ok :
  forall V (inst : module_CodeVisitor_t V) data pos env vis,
  code_hooks_total inst data env ->
  env_small env pos ->
  to_Z pos <= dlen data ->
  dlen data <= module_bytes ->
  exists r vis', module_validate_code_with inst data pos env vis = Ok (r, vis')
            /\ forall q', r = Core_result_Result_Ok q' ->
                 to_Z pos <= to_Z q' /\ to_Z q' <= dlen data.
Proof.
  intros V inst data pos env vis Hhooks Henv Hpos Hlen.
  pose proof Hhooks as [Hneed _].
  unfold module_validate_code_with.
  (* the header's own read, waited for before it happens *)
  pose proof (usize_nonneg pos).
  assert (Hhdr : to_Z pos + to_Z limits_max_code_header_bytes <= usize_max).
  { unfold limits_max_code_header_bytes, limits_max_code_header_bytes_body.
    pose proof module_bytes_fits. cbn. lia. }
  destruct (usize_add_ok pos limits_max_code_header_bytes Hhdr) as [pw [Hpw _]].
  rewrite Hpw. cbn [bind].
  destruct (Hneed vis pw) as [rn [vis1 Hn]]. rewrite Hn. cbn [bind].
  destruct rn as [u|en]; [|try_err_post].
  rewrite branch_ok. cbn [bind].
  destruct (code_section_ok data pos env Hpos) as [r [Hr Hpost]].
  rewrite Hr. cbn [bind].
  destruct r as [oc|e]; [|try_err_post].
  rewrite branch_ok. cbn [bind].
  destruct oc as [cs|].
  - (* the section is here, so the entries follow and have to fill it *)
    destruct (Hpost cs (ltac:(reflexivity))) as [Hpe [Hple [Hpen Hend]]].
    unfold module_validate_code_entries_with.
    destruct (validate_code_entries_with_loop_ok V inst
                (List.length (vec_list env.(module_Env_func_type_indices)))
                data env vis1 cs.(module_CodeSection_entries) 0%usize)
      as [r2 [vis2 [Hr2 Hpost2]]].
    + exact Hhooks.
    + assert (Hz : to_Z 0%usize = 0) by reflexivity. lia.
    + apply (env_small_mono _ pos); [exact Henv | lia].
    + exact Hple.
    + exact Hlen.
    + rewrite Hr2. cbn [bind].
      destruct r2 as [q1|e]; [|try_err_post].
      rewrite branch_ok. cbn [bind].
      destruct (Hpost2 _ (ltac:(reflexivity))) as [Hlt2 Hq1].
      destruct (q1 s<> cs.(module_CodeSection_end));
        [eexists; eexists; split; [reflexivity|]; intros ? Hc; discriminate|].
      eexists. eexists. split; [reflexivity|]. intros q' Hc. injection Hc as <-.
      split; lia.
  - (* no section, and the module declared no functions *)
    eexists. eexists. split; [reflexivity|]. intros q' Hc. injection Hc as <-.
    split; lia.
Qed.

(** [validate_code] is the walk at the consumer that validates each entry where
    it stands, so its own totality needs no hypothesis about hooks. *)
Lemma validate_code_nop : forall data pos env r,
  module_validate_code_with
    module_ValidatingCodeVisitor_Insts_ItascaModuleCodeVisitor data pos env tt
    = Ok (r, tt) ->
  module_validate_code data pos env = Ok r.
Proof.
  intros data pos env r H. unfold module_validate_code. rewrite H. cbn [bind].
  reflexivity.
Qed.

Corollary validate_code_ok : forall data pos env,
  env_small env pos ->
  to_Z pos <= dlen data ->
  dlen data <= module_bytes ->
  exists r, module_validate_code data pos env = Ok r
            /\ forall q', r = Core_result_Result_Ok q' ->
                 to_Z pos <= to_Z q' /\ to_Z q' <= dlen data.
Proof.
  intros data pos env Henv Hpos Hlen.
  destruct (validate_code_with_ok _
              module_ValidatingCodeVisitor_Insts_ItascaModuleCodeVisitor data
              pos env tt (validating_code_hooks_total data env) Henv Hpos Hlen)
    as [r [vis' [Hr Hpost]]].
  exists r. split; [|exact Hpost].
  apply validate_code_nop. destruct vis'. exact Hr.
Qed.

(* ================================================================== *)
(** ** The tail, and the theorem                                      *)
(* ================================================================== *)

Lemma decode_data_segment_ok : forall data pos env,
  to_Z pos <= dlen data ->
  dlen data <= module_bytes ->
  exists r, module_decode_data_segment data pos env = Ok r
            /\ forall seg q', r = Core_result_Result_Ok (seg, q') ->
                 to_Z pos < to_Z q' /\ to_Z q' <= dlen data.
Proof.
  intros data pos env Hpos Hlen. unfold module_decode_data_segment.
  destruct (read_u32_leb_ok data pos) as [r Hr]. rewrite Hr. cbn [bind].
  destruct r as [[midx p1]|e]; [|try_err_post].
  rewrite branch_ok. cbn [bind].
  pose proof (read_u32_leb_lt _ _ _ _ Hr) as Hlt.
  pose proof (read_u32_leb_le_len _ _ _ _ Hr) as Hp1.
  destruct (scalar_cast_u32_usize midx) as [j [Hcast Hj]].
  rewrite Hcast. cbn [bind].
  destruct (j s>= alloc_vec_Vec_len env.(module_Env_mem_types));
    [eexists; split; [reflexivity|]; intros ? ? Hc; discriminate|].
  destruct (decode_const_expr_ok data p1 env Types_ValueType_I32)
    as [r1 [Hr1 Hce]].
  rewrite Hr1. cbn [bind].
  destruct r1 as [[offset p2]|e]; [|try_err_post].
  rewrite branch_ok. cbn [bind].
  destruct (Hce _ _ (ltac:(reflexivity))) as [Hlt2 Hp2].
  destruct (read_u32_leb_ok data p2) as [r2 Hr2]. rewrite Hr2. cbn [bind].
  destruct r2 as [[len p3]|e]; [|try_err_post].
  rewrite branch_ok. cbn [bind].
  pose proof (read_u32_leb_lt _ _ _ _ Hr2) as Hlt3.
  pose proof (read_u32_leb_le_len _ _ _ _ Hr2) as Hp3.
  destruct (scalar_cast_u32_usize len) as [n [Hcast2 Hn]].
  rewrite Hcast2. cbn [bind].
  destruct (have_bytes_ok data p3 n Hp3) as [rh [Hh Hcase]].
  rewrite Hh. cbn [bind].
  destruct Hcase as [-> | ->]; [|try_err_post].
  rewrite branch_ok. cbn [bind].
  pose proof (have_bytes_room data p3 n Hh) as Hroom.
  pose proof (usize_nonneg n).
  destruct (usize_add_ok p3 n (ltac:(fits))) as [q2 [Hadd Hq2]].
  rewrite Hadd. cbn [bind].
  destruct (copy_bytes_ok data p3 q2 (ltac:(lia)) (ltac:(lia)) Hlen)
    as [init Hinit].
  rewrite Hinit. cbn [bind].
  eexists. split; [reflexivity|]. intros seg q' Hc. injection Hc as _ <-.
  split; lia.
Qed.

Lemma decode_data_section_loop_ok : forall m data env count out q i,
  to_Z count - to_Z i <= Z.of_nat m ->
  Z.of_nat (List.length (vec_list out)) <= to_Z q ->
  to_Z q <= dlen data ->
  dlen data <= module_bytes ->
  exists r, module_decode_data_section_loop data env count out q i = Ok r
            /\ forall out' q', r = Core_result_Result_Ok (out', q') ->
                 to_Z q <= to_Z q' /\ to_Z q' <= dlen data
                 /\ Z.of_nat (List.length (vec_list out')) <= to_Z q'.
Proof.
  induction m as [|m IH]; intros data env count out q i Hmeas Hacc Hq Hlen;
    unfold module_decode_data_section_loop; rewrite loop_unfold; cbn beta iota;
    destruct (i s>= count) eqn:Hge;
    [ eexists; split; [reflexivity|]; intros ? ? Hc; injection Hc as <- <-;
      repeat split; lia
    | | eexists; split; [reflexivity|]; intros ? ? Hc; injection Hc as <- <-;
        repeat split; lia
    | ].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (decode_data_segment_ok data q env Hq Hlen) as [r [Hr Hpost]].
    rewrite Hr. cbn [bind].
    destruct r as [[seg q1]|e]; [|try_err_post].
    rewrite branch_ok. cbn [bind].
    destruct (Hpost _ _ (ltac:(reflexivity))) as [Hlt Hq1].
    destruct (vec_push_ok out seg (ltac:(fits))) as [out2 Hpush].
    rewrite Hpush. cbn [bind].
    assert (Hu1 : to_Z 1%u32 = 1) by reflexivity.
    pose proof (u32_bounds count).
    destruct (u32_add_ok i 1%u32 (ltac:(lia))) as [i2 [Hadd Hi2]].
    rewrite Hadd. cbn [bind].
    destruct (IH data env count out2 q1 i2) as [r2 [Hr2 Hpost2]].
    + rewrite Nat2Z.inj_succ in Hmeas. lia.
    + rewrite (vec_push_spec _ _ _ Hpush). rewrite List.app_length.
      cbn [List.length]. lia.
    + exact Hq1.
    + exact Hlen.
    + exists r2. split; [exact Hr2|].
      intros out' q' Hc. destruct (Hpost2 _ _ Hc) as [A [B C]].
      repeat split; lia.
Qed.

Lemma decode_data_section_ok : forall data pos env,
  to_Z pos <= dlen data ->
  dlen data <= module_bytes ->
  exists r, module_decode_data_section data pos env = Ok r
            /\ forall out q', r = Core_result_Result_Ok (out, q') ->
                 to_Z pos <= to_Z q' /\ to_Z q' <= dlen data
                 /\ Z.of_nat (List.length (vec_list out)) <= to_Z q'.
Proof.
  intros data pos env Hpos Hlen. unfold module_decode_data_section.
  destruct (read_u32_leb_ok data pos) as [r Hr]. rewrite Hr. cbn [bind].
  destruct r as [[count p]|e]; [|try_err_post].
  rewrite branch_ok. cbn [bind].
  pose proof (read_u32_leb_lt _ _ _ _ Hr) as Hlt.
  pose proof (read_u32_leb_le_len _ _ _ _ Hr) as Hple.
  assert (Hz : to_Z 0%u32 = 0) by reflexivity.
  pose proof (u32_bounds count).
  destruct (decode_data_section_loop_ok (Z.to_nat (to_Z count)) data env count
              (alloc_vec_Vec_new module_Data_t) p 0%u32) as [r2 [Hr2 Hpost]].
  - rewrite Z2Nat.id by lia. lia.
  - cbn [vec_list alloc_vec_Vec_new proj1_sig List.length].
    pose proof (usize_nonneg p). lia.
  - exact Hple.
  - exact Hlen.
  - exists r2. split; [exact Hr2|].
    intros out q' Hc. destruct (Hpost _ _ Hc) as [A [B C]]. repeat split; lia.
Qed.

(** Spec 5.5.16 from the code section on: the data section, and custom
    sections around it. Same measure as [validate_env_loop]. *)
Lemma validate_tail_with_loop_ok :
  forall V (inst : module_ModuleVisitor_t V) m data env vis segments q seen,
  module_hooks_total inst ->
  dlen data - to_Z q <= Z.of_nat m ->
  Z.of_nat (List.length (vec_list segments)) <= to_Z q ->
  to_Z q <= dlen data ->
  dlen data <= module_bytes ->
  exists r vis',
    module_validate_tail_with_loop inst data env vis segments q seen = Ok (r, vis').
Proof.
  intros V inst m. induction m as [|m IH];
    intros data env vis segments q seen Hhooks Hmeas Hacc Hq Hlen;
    unfold module_validate_tail_with_loop; rewrite loop_unfold; cbn beta iota;
    destruct (q s>= slice_len data) eqn:Hge;
    [eexists; eexists; reflexivity| |eexists; eexists; reflexivity|].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (read_section_header_ok data q (ltac:(lia))) as [r Hr].
    rewrite Hr. cbn [bind].
    destruct r as [[[id start] end1]|e];
      [|rewrite branch_err; cbn [bind]; rewrite from_residual_err;
        cbn [bind]; eexists; eexists; reflexivity].
    rewrite branch_ok. cbn [bind].
    destruct (read_section_header_step _ _ _ _ _ Hr) as [Hlt [Hse Hend]].
    destruct (id s= module_section_custom).
    { destruct (decode_custom_section_ok data start end1 (ltac:(lia)) Hlen)
        as [r1 Hr1]. rewrite Hr1. cbn [bind].
      destruct r1 as [c|e];
        [|rewrite branch_err; cbn [bind]; rewrite from_residual_err;
          cbn [bind]; eexists; eexists; reflexivity].
      rewrite branch_ok. cbn [bind].
      destruct (Hhooks vis c) as [rh [vis1 Hh]]. rewrite Hh. cbn [bind].
      destruct rh as [u|ev];
        [|cbn beta iota; eexists; eexists; reflexivity].
      cbn beta iota.
      apply (IH data env vis1 segments end1 seen);
        [exact Hhooks | rewrite Nat2Z.inj_succ in Hmeas; lia
        | lia | lia | exact Hlen]. }
    destruct (id s<> module_section_data); [eexists; eexists; reflexivity|].
    destruct seen; [eexists; eexists; reflexivity|].
    destruct (decode_data_section_ok data start env (ltac:(lia)) Hlen)
      as [r1 [Hr1 Hpost]].
    rewrite Hr1. cbn [bind].
    destruct r1 as [[decoded p]|e];
      [|rewrite branch_err; cbn [bind]; rewrite from_residual_err;
        cbn [bind]; eexists; eexists; reflexivity].
    rewrite branch_ok. cbn [bind].
    destruct (Hpost _ _ (ltac:(reflexivity))) as [Hlt1 [Hp Hdl]].
    destruct (p s<> end1) eqn:Hne; [eexists; eexists; reflexivity|].
    apply Bool.negb_false_iff in Hne. apply scalar_eqb_true in Hne.
    cbn beta iota.
    apply (IH data env vis decoded end1 true);
      [exact Hhooks | rewrite Nat2Z.inj_succ in Hmeas; lia
      | lia | lia | exact Hlen].
Qed.

Lemma validate_tail_with_ok :
  forall V (inst : module_ModuleVisitor_t V) data pos env vis,
  module_hooks_total inst ->
  to_Z pos <= dlen data ->
  dlen data <= module_bytes ->
  exists r vis', module_validate_tail_with inst data pos env vis = Ok (r, vis').
Proof.
  intros V inst data pos env vis Hhooks Hpos Hlen.
  unfold module_validate_tail_with.
  pose proof (usize_nonneg pos).
  apply (validate_tail_with_loop_ok V inst (Z.to_nat (dlen data)) data env vis
           (alloc_vec_Vec_new module_Data_t) pos false).
  - exact Hhooks.
  - rewrite Z2Nat.id by (pose proof (usize_nonneg (slice_len data)); lia). lia.
  - cbn [vec_list alloc_vec_Vec_new proj1_sig List.length]. lia.
  - exact Hpos.
  - exact Hlen.
Qed.

Corollary validate_tail_ok : forall data pos env,
  to_Z pos <= dlen data ->
  dlen data <= module_bytes ->
  exists r, module_validate_tail data pos env = Ok r.
Proof.
  intros data pos env Hpos Hlen.
  destruct (validate_tail_with_ok _
              module_EmptyModuleVisitor_Insts_ItascaModuleModuleVisitor data pos
              env tt nop_module_hooks_total Hpos Hlen) as [r [vis' Hr]].
  exists r. apply validate_tail_nop. destruct vis'. exact Hr.
Qed.

(* ================================================================== *)
(** ** The theorem                                                    *)
(* ================================================================== *)

(** No input makes the module validator panic or diverge. Unconditional: the
    size check is inside [validate_module], so there is no precondition for a
    caller to get wrong, exactly as [validate_body_no_panic] has none. *)
Theorem validate_module_no_panic : forall data,
  exists r, module_validate_module data = Ok r.
Proof.
  intros data. unfold module_validate_module.
  destruct (slice_len data s> limits_max_module_bytes) eqn:Hbig;
    [eexists; reflexivity|].
  apply scalar_gtb_false in Hbig. rewrite max_module_bytes_val in Hbig.
  destruct (validate_env_ok data Hbig) as [r [Hr Hpost]]. rewrite Hr. cbn [bind].
  destruct r as [[env code_pos]|e]; [|try_err].
  rewrite branch_ok. cbn [bind].
  destruct (Hpost _ _ (ltac:(reflexivity))) as [Hcp Henv].
  destruct (validate_code_ok data code_pos env Henv Hcp Hbig) as [r1 [Hr1 Hvc]].
  rewrite Hr1. cbn [bind].
  destruct r1 as [tail_pos|e]; [|try_err].
  rewrite branch_ok. cbn [bind].
  destruct (Hvc _ (ltac:(reflexivity))) as [_ Htp].
  destruct (validate_tail_ok data tail_pos env Htp Hbig) as [r2 Hr2].
  rewrite Hr2. cbn [bind].
  destruct r2 as [tail|e]; [|try_err].
  rewrite branch_ok. cbn [bind]. eexists. reflexivity.
Qed.
