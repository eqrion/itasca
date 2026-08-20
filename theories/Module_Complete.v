(** * The module decoder accepts what the format admits

    The completeness direction for everything around a function body: no false
    rejects. Where [Module_Sound.v] shows an accepting run means the input is a
    Wasm 1.0 module binary the type system accepts, this file works towards the
    converse, against [Spec_Module.repr_module] and WasmCert's
    [module_type_checker].

    Every lemma has the same shape,

      repr_x (bytes_from data pos) v rest
      -> exists v' p', decode_x data pos = Ok (Ok (v', p'))
                       /\ translate_x v' = v
                       /\ bytes_from data p' = rest

    and the last two conjuncts are never proved by hand: the first conjunct is
    the work, and the identification then falls out of the soundness lemma for
    the same decoder plus the [_det] lemma for the same rule. That is what keeps
    this file from being a second decoder correspondence; [ident] below is that
    step written once.

    The corollary is that the *only* thing to prove is that no error branch is
    taken, because [Module_NoPanic.v] already says the run returns something.
    Every [Err] site in [module.rs] is either a format rule, contradicted by the
    derivation in hand, or a validity check, contradicted by the type checker. *)

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
Require Import Veriwasm.Spec_Expr.
Require Import Veriwasm.Spec_Module.
Require Import Veriwasm.OpIter_State.
Require Import Veriwasm.OpIter_Decode.
Require Import Veriwasm.OpIter_Sim.
(* for [op_spec_invert]: the opcode table read backwards, which is what the
   constant-expression reader's fallthrough needs *)
Require Import Veriwasm.OpIter_Table.
Require Import Veriwasm.OpIter_Visit.
Require Import Veriwasm.OpIter_Complete.
Require Import Veriwasm.Module_NoPanic.
Require Import Veriwasm.Module_Sound.

(* [type_checker_reflects_typing] is only here for [context_reverseK]: the two
   contexts differ by one [context_reverse], and undoing it needs the involution *)
From Wasm Require Import datatypes typing type_checker type_checker_reflects_typing.

Local Open Scope list_scope.
Open Scope Z_scope.

(* ================================================================== *)
(** ** Identifying what the decoder produced                           *)
(* ================================================================== *)

(** The lever. A decoder that ran successfully has a soundness lemma saying
    what its bytes encode; the derivation in hand says the same bytes encode
    something else; determinism identifies the two. So no completeness proof
    re-derives a correspondence, and the price of a decoder is its [Err] sites
    and nothing more. *)
Ltac ident L Hsound Hspec :=
  let Ha := fresh "Ha" in let Hb := fresh "Hb" in
  destruct (L _ _ _ _ _ Hsound Hspec) as [Ha Hb];
  split; [exact Ha | exact Hb].

(** Every lemma below takes the run as *given* rather than building it, which is
    what [validate_module_no_panic] is for: the run returns something
    unconditionally, so a completeness proof never has to show that a push or a
    cursor increment succeeds. It only has to show the result is not an error,
    and the sub-runs come out of the given one by [destruct]. *)

(** Step past a guard against a literal that cannot be the byte in hand, and
    take the one that can. The hypothesis-side twins of [OpIter_Complete]'s
    [guard_false] and [guard_true]. *)
Ltac guard_false_in Hw Hb :=
  let E := fresh "Eg" in
  match type of Hw with
  | context [ if (?x s= ?y) then _ else _ ] =>
      destruct (x s= y) eqn:E;
      [ exfalso; apply scalar_eqb_true in E; rewrite Hb in E; cbn in E;
        discriminate E
      | clear E ]
  end.

Ltac guard_true_in Hw Hb :=
  let E := fresh "Eg" in
  match type of Hw with
  | context [ if (?x s= ?y) then _ else _ ] =>
      assert (E : (x s= y) = true)
        by (apply scalar_eqb_of_eq; rewrite Hb; reflexivity);
      rewrite E in Hw; clear E
  end.

(** A tag byte the format writes out, tested by the code with [!=]. *)
Ltac tag_in Hw Hb :=
  let E := fresh "Et" in
  match type of Hw with
  | context [ if (?x s<> ?y) then _ else _ ] =>
      assert (E : (x s<> y) = false)
        by (unfold scalar_neqb; apply Bool.negb_false_iff;
            apply scalar_eqb_of_eq; rewrite Hb; reflexivity);
      rewrite E in Hw; clear E
  end.

(* ================================================================== *)
(** ** Inverting a rule stated over a non-variable stream              *)
(* ================================================================== *)

(** [inversion] on [repr_x (bytes_from data pos) v rest] leaves the stream
    equation the wrong way round and cannot substitute it, because
    [bytes_from data pos] is not a variable. Each rule therefore gets an
    inversion lemma stated over variables, where [inversion; subst] does work.
    They are also the readable form: a rule's premises as an [exists]. *)

Lemma repr_valtype_inv : forall bs vt rest,
  repr_valtype bs vt rest ->
  exists b, bs = b :: rest /\ valtype_spec b = Some vt.
Proof.
  intros bs vt rest H. inversion H; subst.
  eexists. split; [reflexivity | assumption].
Qed.

Lemma repr_vec_inv : forall A (R : list Z -> A -> list Z -> Prop) bs xs rest,
  repr_vec R bs xs rest ->
  exists n mid, repr_u32 bs n mid /\ repr_rep R (Z.to_nat n) mid xs rest.
Proof.
  intros A R bs xs rest H. inversion H; subst.
  eexists. eexists. split; eassumption.
Qed.

Lemma repr_functype_inv : forall bs ft rest,
  repr_functype bs ft rest ->
  exists p0 t1 mid t2,
    bs = 96 :: p0 /\ ft = Tf t1 t2
    /\ repr_resulttype p0 t1 mid /\ repr_resulttype mid t2 rest.
Proof.
  intros bs ft rest H. inversion H; subst.
  do 4 eexists. split; [reflexivity|]. split; [reflexivity|].
  split; eassumption.
Qed.

Lemma repr_limits_inv : forall bs lim rest,
  repr_limits bs lim rest ->
  (exists p0 n, bs = 0 :: p0 /\ repr_u32 p0 n rest
                /\ lim = {| lim_min := Z.to_N n; lim_max := None |})
  \/ (exists p0 n mid m,
        bs = 1 :: p0 /\ repr_u32 p0 n mid /\ repr_u32 mid m rest
        /\ lim = {| lim_min := Z.to_N n; lim_max := Some (Z.to_N m) |}).
Proof.
  intros bs lim rest H. inversion H; subst.
  - left. do 2 eexists. split; [reflexivity|]. split; [eassumption|reflexivity].
  - right. do 4 eexists. split; [reflexivity|]. split; [eassumption|].
    split; [eassumption|reflexivity].
Qed.

Lemma repr_tabletype_inv : forall bs tt rest,
  repr_tabletype bs tt rest ->
  exists p0 lim,
    bs = 112 :: p0 /\ repr_limits p0 lim rest
    /\ tt = {| tt_limits := lim; tt_elem_type := T_funcref |}.
Proof.
  intros bs tt rest H. inversion H; subst.
  do 2 eexists. split; [reflexivity|]. split; [eassumption|reflexivity].
Qed.

Lemma repr_mut_inv : forall bs m rest,
  repr_mut bs m rest ->
  (bs = 0 :: rest /\ m = MUT_const) \/ (bs = 1 :: rest /\ m = MUT_var).
Proof.
  intros bs m rest H. inversion H; subst;
    [left | right]; split; reflexivity.
Qed.

Lemma repr_globaltype_inv : forall bs gt rest,
  repr_globaltype bs gt rest ->
  exists t mid m,
    repr_valtype bs t mid /\ repr_mut mid m rest
    /\ gt = {| tg_mut := m; tg_t := t |}.
Proof.
  intros bs gt rest H. inversion H; subst.
  do 3 eexists. split; [eassumption|]. split; [eassumption|reflexivity].
Qed.

Lemma repr_idx_inv : forall bs x rest,
  repr_idx bs x rest -> exists z, repr_u32 bs z rest /\ x = Z.to_N z.
Proof.
  intros bs x rest H. inversion H; subst.
  eexists. split; [eassumption|reflexivity].
Qed.

Lemma repr_name_inv : forall bs nm rest,
  repr_name bs nm rest ->
  exists zs, repr_vec repr_byte bs zs rest
             /\ Forall2 name_byte_is zs nm /\ utf8_valid zs.
Proof.
  intros bs nm rest H. inversion H; subst.
  eexists. split; [eassumption|]. split; eassumption.
Qed.

Lemma repr_bytevec_inv : forall bs bys rest,
  repr_bytevec bs bys rest ->
  exists zs, repr_vec repr_byte bs zs rest /\ Forall2 data_byte_is zs bys.
Proof.
  intros bs bys rest H. inversion H; subst.
  eexists. split; eassumption.
Qed.

Lemma repr_table_inv : forall bs t rest,
  repr_table bs t rest ->
  exists tt, repr_tabletype bs tt rest /\ t = {| modtab_type := tt |}.
Proof.
  intros bs t rest H. inversion H; subst.
  eexists. split; [eassumption | reflexivity].
Qed.

Lemma repr_mem_inv : forall bs m rest,
  repr_mem bs m rest ->
  exists mt, repr_memtype bs mt rest /\ m = {| modmem_type := mt |}.
Proof.
  intros bs m rest H. inversion H; subst.
  eexists. split; [eassumption | reflexivity].
Qed.

Lemma repr_global_inv : forall bs g rest,
  repr_global bs g rest ->
  exists gt mid e,
    repr_globaltype bs gt mid /\ repr_expr mid e rest
    /\ g = {| modglob_type := gt; modglob_init := e |}.
Proof.
  intros bs g rest H. inversion H; subst.
  do 3 eexists. split; [eassumption|]. split; [eassumption | reflexivity].
Qed.

Lemma repr_elem_inv : forall bs el rest,
  repr_elem bs el rest ->
  exists x m1 e m2 ys,
    repr_idx bs x m1 /\ repr_expr m1 e m2 /\ repr_vec repr_idx m2 ys rest
    /\ el = {| modelem_type := T_funcref;
               modelem_init := List.map (fun y => [BI_ref_func y]) ys;
               modelem_mode := ME_active x e |}.
Proof.
  intros bs el rest H. inversion H; subst.
  do 5 eexists. split; [eassumption|]. split; [eassumption|].
  split; [eassumption | reflexivity].
Qed.

(* ================================================================== *)
(** ** Positions, lengths and runs of bytes                            *)
(* ================================================================== *)

Lemma firstn_app_exact : forall A (l1 l2 : list A),
  List.firstn (List.length l1) (l1 ++ l2) = l1.
Proof.
  intros A l1 l2. rewrite List.firstn_app. rewrite List.firstn_all.
  replace (List.length l1 - List.length l1)%nat with 0%nat by lia.
  cbn [List.firstn]. apply app_nil_r.
Qed.

Lemma skipn_app_exact : forall A (l1 l2 : list A),
  List.skipn (List.length l1) (l1 ++ l2) = l2.
Proof.
  intros A l1 l2. rewrite List.skipn_app. rewrite List.skipn_all.
  replace (List.length l1 - List.length l1)%nat with 0%nat by lia.
  reflexivity.
Qed.

(** A split of the stream at a cursor bounds the cursor plus the prefix by the
    input's length. The cursor's own bound is a hypothesis and not derivable:
    past the end the stream is empty and so is the prefix, and then the
    conclusion is false. Every use has it from a reader's [_le_len]. *)
Lemma bytes_from_app_len : forall data (p : usize) pre rest,
  to_Z p <= dlen data ->
  bytes_from data p = pre ++ rest ->
  to_Z p + Z.of_nat (List.length pre) <= dlen data.
Proof.
  intros data p pre rest Hp Heq.
  assert (Hlen : List.length (bytes_from data p)
                 = (List.length (byte_list data) - Z.to_nat (to_Z p))%nat)
    by (unfold bytes_from; apply List.skipn_length).
  rewrite Heq in Hlen. rewrite List.app_length in Hlen.
  rewrite byte_list_length in Hlen. rewrite slice_len_spec in *.
  pose proof (usize_nonneg p).
  assert (Hle : (Z.to_nat (to_Z p) <= List.length (vec_list data))%nat)
    by (apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; lia).
  apply Nat2Z.inj_le in Hle. rewrite Z2Nat.id in Hle by lia.
  lia.
Qed.

(** [have_bytes]'s converse. It rejects exactly when the run is not there, so
    the room being there is the whole content of the premise. *)
Lemma have_bytes_complete : forall data pos n,
  to_Z pos + to_Z n <= dlen data ->
  module_have_bytes data pos n = Ok (Core_result_Result_Ok tt).
Proof.
  intros data pos n Hroom. unfold module_have_bytes.
  pose proof (usize_nonneg pos). pose proof (usize_nonneg n).
  destruct (usize_sub_ok (slice_len data) pos (ltac:(lia))) as [d [Hsub Hd]].
  rewrite Hsub. cbn [bind].
  rewrite (scalar_gtb_of_le n d) by lia. reflexivity.
Qed.

(** [repr_rep repr_byte] says nothing but that the bytes are there, so a
    derivation over it is a split of the stream at a known length. The inverse
    of [Module_Sound.repr_rep_byte_firstn]. *)
Lemma repr_rep_byte_inv : forall k bs zs rest,
  repr_rep repr_byte k bs zs rest ->
  bs = zs ++ rest /\ List.length zs = k.
Proof.
  induction k as [|k IH]; intros bs zs rest H.
  - inversion H; subst. split; reflexivity.
  - inversion H as [|n bs' z mid zs' rest' Hz Hrep]; subst.
    inversion Hz; subst.
    destruct (IH _ _ _ Hrep) as [-> Hlen].
    split; [reflexivity | cbn [List.length]; lia].
Qed.

(** A [vec(byte)] whose bytes the specification has put in the stream: the
    length prefix reads, the run is there, and [copy_bytes] copies exactly it.
    Shared by a name and a data segment's contents, which is where
    [Module_Sound.decode_bytevec_sound] sits on the other side. *)
Lemma decode_bytevec_complete : forall data pos zs rest,
  dlen data <= module_bytes ->
  repr_vec repr_byte (bytes_from data pos) zs rest ->
  exists (len : scalar U32) (n p q : usize) v,
    reader_read_u32_leb data pos = Ok (Core_result_Result_Ok (len, p))
    /\ scalar_cast U32 Usize len = Ok n
    /\ module_have_bytes data p n = Ok (Core_result_Result_Ok tt)
    /\ usize_add p n = Ok q
    /\ module_copy_bytes data p q = Ok v
    /\ List.map to_Z (vec_list v) = zs
    /\ bytes_from data q = rest.
Proof.
  intros data pos zs rest Hmod Hvec.
  destruct (repr_vec_inv _ _ _ _ _ Hvec) as [n0 [mid [Hn Hrep]]].
  destruct (repr_rep_byte_inv _ _ _ _ Hrep) as [Hmid Hcnt].
  pose proof (repr_u32_nonneg _ _ _ Hn) as Hn0.
  destruct (read_u32_leb_complete _ _ _ _ Hn) as [len [p [Hrun [Hval Hp]]]].
  pose proof (read_u32_leb_le_len _ _ _ _ Hrun) as Hple.
  destruct (cast_u32_usize_ok len) as [n [Hcast Hn2]].
  rewrite <- Hp in Hmid.
  assert (Hzs : Z.of_nat (List.length zs) = to_Z n)
    by (rewrite Hcnt; rewrite Z2Nat.id by lia; lia).
  assert (Hroom : to_Z p + to_Z n <= dlen data)
    by (rewrite <- Hzs; exact (bytes_from_app_len _ _ _ _ Hple Hmid)).
  pose proof (usize_nonneg p). pose proof (usize_nonneg n).
  destruct (usize_add_ok p n) as [q [Hadd Hq]];
    [pose proof (usize_le_max (slice_len data)); lia|].
  destruct (copy_bytes_ok data p q (ltac:(lia)) Hmod) as [v Hcopy].
  destruct (copy_bytes_sound _ _ _ _ Hcopy) as [Hmap _].
  exists len, n, p, q, v.
  split; [exact Hrun|]. split; [exact Hcast|].
  split; [apply have_bytes_complete; lia|].
  split; [exact Hadd|]. split; [exact Hcopy|].
  assert (Hqz : to_Z q = to_Z p + Z.of_nat (List.length zs)) by lia.
  assert (Hcnt2 : Z.to_nat (to_Z q - to_Z p) = List.length zs).
  { rewrite Hqz. rewrite Z.add_simpl_l. apply Z_to_nat_of_nat. }
  split.
  - rewrite Hmap. rewrite Hcnt2.
    rewrite <- bytes_from_at. rewrite Hmid. apply firstn_app_exact.
  - rewrite bytes_from_at. rewrite (bytes_at_congr data (to_Z q) _ Hqz).
    rewrite bytes_at_skipn by lia. rewrite <- bytes_from_at.
    rewrite Hmid. apply skipn_app_exact.
Qed.

(* ================================================================== *)
(** ** 5.3.1 Value types                                               *)
(* ================================================================== *)

(** The specification's table fixes the byte, so the code's comparison chain has
    to reach the matching arm. The two chains are in the same order, and the
    fallthrough closes because the four literals are the four the table has. *)
Lemma decode_value_type_complete : forall data pos r vt rest,
  module_decode_value_type data pos = Ok r ->
  repr_valtype (bytes_from data pos) vt rest ->
  exists vt' p',
    r = Core_result_Result_Ok (vt', p')
    /\ translate_vt_v vt' = vt
    /\ bytes_from data p' = rest.
Proof.
  intros data pos r vt rest Hrun H.
  destruct (repr_valtype_inv _ _ _ H) as [b [Hbs Hspec]].
  destruct (read_byte_complete _ _ _ _ Hbs) as [b' [p' [Hrb [Hz Hrest]]]].
  pose proof Hrun as Hw. unfold module_decode_value_type in Hw.
  rewrite Hrb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
  cbn [bind] in Hw.
  assert (Hok : exists vt', r = Core_result_Result_Ok (vt', p')).
  { destruct (b' s= 127%u8) eqn:E127;
      [injection Hw as <-; eexists; reflexivity|].
    destruct (b' s= 126%u8) eqn:E126;
      [injection Hw as <-; eexists; reflexivity|].
    destruct (b' s= 125%u8) eqn:E125;
      [injection Hw as <-; eexists; reflexivity|].
    destruct (b' s= 124%u8) eqn:E124;
      [injection Hw as <-; eexists; reflexivity|].
    exfalso.
    apply scalar_eqb_false in E127. apply scalar_eqb_false in E126.
    apply scalar_eqb_false in E125. apply scalar_eqb_false in E124.
    assert (H127 : to_Z 127%u8 = 127) by reflexivity.
    assert (H126 : to_Z 126%u8 = 126) by reflexivity.
    assert (H125 : to_Z 125%u8 = 125) by reflexivity.
    assert (H124 : to_Z 124%u8 = 124) by reflexivity.
    unfold valtype_spec in Hspec.
    destruct (Z.eqb b 127) eqn:Q1; [apply Z.eqb_eq in Q1; lia|].
    destruct (Z.eqb b 126) eqn:Q2; [apply Z.eqb_eq in Q2; lia|].
    destruct (Z.eqb b 125) eqn:Q3; [apply Z.eqb_eq in Q3; lia|].
    destruct (Z.eqb b 124) eqn:Q4; [apply Z.eqb_eq in Q4; lia|].
    discriminate. }
  destruct Hok as [vt' ->]. exists vt', p'. split; [reflexivity|].
  ident repr_valtype_det (decode_value_type_sound _ _ _ _ Hrun) H.
Qed.

(* ================================================================== *)
(** ** 5.1.3 Vectors, and 5.3.2 result types                           *)
(* ================================================================== *)

Lemma repr_rep_O_inv : forall A (R : list Z -> A -> list Z -> Prop) bs xs rest,
  repr_rep R 0 bs xs rest -> xs = [] /\ rest = bs.
Proof.
  intros A R bs xs rest H. inversion H; subst. split; reflexivity.
Qed.

Lemma repr_rep_S_inv : forall A (R : list Z -> A -> list Z -> Prop) k bs xs rest,
  repr_rep R (S k) bs xs rest ->
  exists x mid xs',
    xs = x :: xs' /\ R bs x mid /\ repr_rep R k mid xs' rest.
Proof.
  intros A R k bs xs rest H. inversion H; subst.
  do 3 eexists. split; [reflexivity|]. split; eassumption.
Qed.

(** A count the loop has left to run. [lia] does not see through [Z.to_nat], so
    the two directions of "the index is the count" are spelt out once. *)
Lemma count_zero : forall (count i : scalar U32),
  Z.to_nat (to_Z count - to_Z i) = 0%nat -> to_Z count <= to_Z i.
Proof.
  intros count i Hk.
  destruct (Z_le_gt_dec (to_Z count - to_Z i) 0) as [Hle|Hgt]; [lia|].
  rewrite <- (Z2Nat.id (to_Z count - to_Z i)) in Hgt by lia.
  rewrite Hk in Hgt. cbn in Hgt. lia.
Qed.

Lemma count_succ : forall (count i : scalar U32) k,
  Z.to_nat (to_Z count - to_Z i) = S k ->
  to_Z count - to_Z i = Z.of_nat (S k).
Proof.
  intros count i k Hk.
  destruct (Z_le_gt_dec (to_Z count - to_Z i) 0) as [Hle|Hgt].
  - rewrite to_nat_nonpos in Hk by lia. discriminate.
  - rewrite <- Hk. rewrite Z2Nat.id by lia. reflexivity.
Qed.

(** The loop. It appends to a vector that already holds something, so the
    elements the specification supplies are the ones it *appends*. *)
Lemma decode_value_types_loop_complete :
  forall k data count out q i r vts rest,
  Z.to_nat (to_Z count - to_Z i) = k ->
  module_decode_value_types_loop data count out q i = Ok r ->
  repr_rep repr_valtype k (bytes_from data q) vts rest ->
  exists out' q',
    r = Core_result_Result_Ok (out', q')
    /\ List.map translate_vt_v (vec_list out')
       = List.map translate_vt_v (vec_list out) ++ vts
    /\ bytes_from data q' = rest.
Proof.
  induction k as [|k IH];
    intros data count out q i r vts rest Hk Hw Hrep;
    unfold module_decode_value_types_loop in Hw; rewrite loop_unfold in Hw;
    cbn beta iota in Hw; destruct (i s>= count) eqn:Hge.
  - injection Hw as <-.
    destruct (repr_rep_O_inv _ _ _ _ _ Hrep) as [-> ->].
    exists out, q. rewrite app_nil_r. split; [reflexivity|].
    split; reflexivity.
  - exfalso. apply scalar_geb_false_lt in Hge.
    pose proof (count_zero _ _ Hk). lia.
  - exfalso. apply scalar_geb_true_ge in Hge.
    pose proof (count_succ _ _ _ Hk) as Hcnt.
    rewrite Nat2Z.inj_succ in Hcnt. pose proof (Nat2Z.is_nonneg k). lia.
  - pose proof (count_succ _ _ _ Hk) as Hcnt.
    destruct (repr_rep_S_inv _ _ _ _ _ _ Hrep) as [vt [mid [vts' [-> [Hvt Hrest]]]]].
    destruct (module_decode_value_type data q) as [r1|] eqn:Evt;
      cbn [bind] in Hw; [|discriminate].
    destruct (decode_value_type_complete _ _ _ _ _ Evt Hvt)
      as [vt' [q1 [-> [Hvt' Hq1]]]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    destruct (alloc_vec_Vec_push out vt') as [out2|] eqn:Hpush;
      cbn [bind] in Hw; [|discriminate].
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in Hw;
      [|discriminate].
    assert (Hi2 : to_Z i2 = to_Z i + 1).
    { unfold u32_add, scalar_add in Hadd. apply mk_scalar_ok_to_Z in Hadd.
      assert (H1 : to_Z 1%u32 = 1) by reflexivity. lia. }
    destruct (IH data count out2 q1 i2 r vts' rest
                (ltac:(rewrite Hi2; f_equal; lia)) Hw
                (ltac:(rewrite Hq1; exact Hrest)))
      as [out' [q' [-> [Hout Hq']]]].
    exists out', q'. split; [reflexivity|]. split; [|exact Hq'].
    rewrite Hout. rewrite (vec_push_spec _ _ _ Hpush).
    rewrite List.map_app. cbn [List.map]. rewrite <- app_assoc.
    rewrite Hvt'. reflexivity.
Qed.

Lemma decode_value_types_complete : forall data pos r vts rest,
  module_decode_value_types data pos = Ok r ->
  repr_resulttype (bytes_from data pos) vts rest ->
  exists out q,
    r = Core_result_Result_Ok (out, q)
    /\ List.map translate_vt_v (vec_list out) = vts
    /\ bytes_from data q = rest.
Proof.
  intros data pos r vts rest Hrun H.
  destruct (repr_vec_inv _ _ _ _ _ H) as [n [mid [Hn Hrep]]].
  destruct (read_u32_leb_complete _ _ _ _ Hn) as [count [p [Hleb [Hval Hp]]]].
  pose proof Hrun as Hw. unfold module_decode_value_types in Hw.
  rewrite Hleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
  cbn [bind] in Hw.
  assert (H0 : to_Z 0%u32 = 0) by reflexivity.
  destruct (decode_value_types_loop_complete (Z.to_nat n) data count
              (alloc_vec_Vec_new types_ValueType_t) p 0%u32 r vts rest
              (ltac:(rewrite H0; rewrite Hval; f_equal; lia)) Hw
              (ltac:(rewrite Hp; exact Hrep)))
    as [out [q [-> [Hout Hq]]]].
  exists out, q. split; [reflexivity|]. split; [|exact Hq].
  rewrite Hout. cbn [vec_list alloc_vec_Vec_new proj1_sig List.map List.app].
  reflexivity.
Qed.

(* ================================================================== *)
(** ** 5.3.3 Function types                                            *)
(* ================================================================== *)

(** Wasm 1.0's "at most one result". It is a validation rule rather than a
    decoding one, so [repr_functype] does not mention it and completeness has to
    take it as a hypothesis: the decoder rejects a multi-value type on purpose,
    and a module the 2.0-shaped type system accepts may well have one. *)
Definition functype_wasm10 (ft : function_type) : Prop :=
  match ft with Tf _ t2 => (List.length t2 <= 1)%nat end.

Lemma decode_func_type_complete : forall data pos r ft rest,
  module_decode_func_type data pos = Ok r ->
  repr_functype (bytes_from data pos) ft rest ->
  functype_wasm10 ft ->
  exists ft' p',
    r = Core_result_Result_Ok (ft', p')
    /\ translate_functype ft' = ft
    /\ bytes_from data p' = rest.
Proof.
  intros data pos r ft rest Hrun H Hw10.
  destruct (repr_functype_inv _ _ _ H) as [p0 [t1 [mid [t2 [Hbs [Hft [H1 H2]]]]]]].
  destruct (read_byte_complete _ _ _ _ Hbs) as [tag [p [Hrb [Hz Hp]]]].
  pose proof Hrun as Hw. unfold module_decode_func_type in Hw.
  rewrite Hrb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
  cbn [bind] in Hw. tag_in Hw Hz.
  destruct (module_decode_value_types data p) as [r1|] eqn:E1;
    cbn [bind] in Hw; [|discriminate].
  destruct (decode_value_types_complete _ _ _ _ _ E1
              (ltac:(rewrite Hp; exact H1))) as [params [p1 [-> [Hpar Hp1]]]].
  rewrite branch_ok in Hw. cbn [bind] in Hw.
  destruct (module_decode_value_types data p1) as [r2|] eqn:E2;
    cbn [bind] in Hw; [|discriminate].
  destruct (decode_value_types_complete _ _ _ _ _ E2
              (ltac:(rewrite Hp1; exact H2))) as [results [p2 [-> [Hres Hp2]]]].
  rewrite branch_ok in Hw. cbn [bind] in Hw.
  (* the result-count check: the specification's list is short, and the
     decoded vector maps onto it, so the vector is short too *)
  assert (Hlen : (List.length (vec_list results) <= 1)%nat).
  { rewrite Hft in Hw10. cbn [functype_wasm10] in Hw10.
    rewrite <- Hres in Hw10. rewrite List.map_length in Hw10. exact Hw10. }
  assert (Hmax : to_Z limits_max_results = 1) by reflexivity.
  rewrite (scalar_gtb_of_le (alloc_vec_Vec_len results) limits_max_results)
    in Hw by (rewrite vec_len_spec; lia).
  injection Hw as <-.
  eexists. exists p2. split; [reflexivity|].
  ident repr_functype_det (decode_func_type_sound _ _ _ _ Hrun) H.
Qed.

(* ================================================================== *)
(** ** 5.3.4 to 5.3.8 Limits, memories, tables and globals             *)
(* ================================================================== *)

Lemma decode_limits_complete : forall data pos r lim rest,
  module_decode_limits data pos = Ok r ->
  repr_limits (bytes_from data pos) lim rest ->
  exists lim' p',
    r = Core_result_Result_Ok (lim', p')
    /\ translate_limits lim' = lim
    /\ bytes_from data p' = rest.
Proof.
  intros data pos r lim rest Hrun H.
  assert (Hok : exists lim' p', r = Core_result_Result_Ok (lim', p')).
  { pose proof Hrun as Hw. unfold module_decode_limits in Hw.
    destruct (repr_limits_inv _ _ _ H)
      as [[p0 [n [Hbs [Hn _]]]] | [p0 [n [mid [m [Hbs [Hn [Hm _]]]]]]]].
    - destruct (read_byte_complete _ _ _ _ Hbs) as [flag [p [Hrb [Hz Hp]]]].
      rewrite Hrb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
      cbn [bind] in Hw. guard_true_in Hw Hz.
      destruct (read_u32_leb_complete data p n rest (ltac:(rewrite Hp; exact Hn)))
        as [min [p1 [Hleb _]]].
      rewrite Hleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
      cbn [bind] in Hw. injection Hw as <-. do 2 eexists. reflexivity.
    - destruct (read_byte_complete _ _ _ _ Hbs) as [flag [p [Hrb [Hz Hp]]]].
      rewrite Hrb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
      cbn [bind] in Hw. guard_false_in Hw Hz. guard_true_in Hw Hz.
      destruct (read_u32_leb_complete data p n mid (ltac:(rewrite Hp; exact Hn)))
        as [min [p1 [Hleb [_ Hp1]]]].
      rewrite Hleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
      cbn [bind] in Hw.
      destruct (read_u32_leb_complete data p1 m rest
                  (ltac:(rewrite Hp1; exact Hm))) as [max [p2 [Hleb2 _]]].
      rewrite Hleb2 in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
      cbn [bind] in Hw. injection Hw as <-. do 2 eexists. reflexivity. }
  destruct Hok as [lim' [p' ->]]. exists lim', p'. split; [reflexivity|].
  ident repr_limits_det (decode_limits_sound _ _ _ _ Hrun) H.
Qed.

(** The converse of [Module_Sound.validate_limits_valid]. Spec 3.2.1 is three
    comparisons on both sides, so this is three implications in the other
    direction. *)
Lemma validate_limits_complete : forall lim bound k,
  to_Z bound = Z.of_N k ->
  limit_valid_range (translate_limits lim) k = true ->
  limits_validate_limits lim bound = Ok (Core_result_Result_Ok tt).
Proof.
  intros lim bound k Hk H.
  unfold limit_valid_range, translate_limits in H. cbn [lim_min lim_max] in H.
  apply Bool.andb_true_iff in H as [Hlow Hhigh].
  apply N.leb_le in Hlow. apply N2Z.inj_le in Hlow.
  pose proof (u32_nonneg lim.(limits_Limits_min)) as Hmin0.
  rewrite Z2N.id in Hlow by lia.
  unfold limits_validate_limits.
  rewrite (scalar_gtb_of_le _ bound) by lia.
  destruct lim.(limits_Limits_max) as [max|] eqn:Hmax;
    cbn [option_map] in Hhigh; [|reflexivity].
  pose proof (u32_nonneg max) as Hmax0.
  apply Bool.andb_true_iff in Hhigh as [Hmm Hmk].
  apply N.leb_le in Hmm. apply N2Z.inj_le in Hmm.
  apply N.leb_le in Hmk. apply N2Z.inj_le in Hmk.
  rewrite Z2N.id in Hmm by lia. rewrite Z2N.id in Hmm by lia.
  rewrite Z2N.id in Hmk by lia.
  rewrite (scalar_gtb_of_le max bound) by lia.
  rewrite (scalar_gtb_of_le _ max) by lia.
  reflexivity.
Qed.

Lemma decode_mem_type_complete : forall data pos r mt rest,
  module_decode_mem_type data pos = Ok r ->
  repr_memtype (bytes_from data pos) mt rest ->
  memtype_valid mt = true ->
  exists mt' p',
    r = Core_result_Result_Ok (mt', p')
    /\ translate_memtype mt' = mt
    /\ bytes_from data p' = rest.
Proof.
  intros data pos r mt rest Hrun H Hvalid.
  assert (Hok : exists mt' p', r = Core_result_Result_Ok (mt', p')).
  { pose proof Hrun as Hw. unfold module_decode_mem_type in Hw.
    destruct (module_decode_limits data pos) as [r1|] eqn:E1;
      cbn [bind] in Hw; [|discriminate].
    destruct (decode_limits_complete _ _ _ _ _ E1 H) as [lim [p [-> [Hlim _]]]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    rewrite (validate_limits_complete lim limits_max_memory_pages
               mem_limit_bound (ltac:(reflexivity))
               (ltac:(rewrite Hlim; exact Hvalid))) in Hw.
    cbn [bind] in Hw. rewrite branch_ok in Hw. cbn [bind] in Hw.
    injection Hw as <-. do 2 eexists. reflexivity. }
  destruct Hok as [mt' [p' ->]]. exists mt', p'. split; [reflexivity|].
  ident repr_memtype_det (decode_mem_type_sound _ _ _ _ Hrun) H.
Qed.

Lemma decode_table_type_complete : forall data pos r tt rest,
  module_decode_table_type data pos = Ok r ->
  repr_tabletype (bytes_from data pos) tt rest ->
  tabletype_valid tt = true ->
  exists tt' p',
    r = Core_result_Result_Ok (tt', p')
    /\ translate_tabletype tt' = tt
    /\ bytes_from data p' = rest.
Proof.
  intros data pos r tt rest Hrun H Hvalid.
  assert (Hok : exists tt' p', r = Core_result_Result_Ok (tt', p')).
  { pose proof Hrun as Hw. unfold module_decode_table_type in Hw.
    destruct (repr_tabletype_inv _ _ _ H) as [p0 [lim0 [Hbs [Hlim0 Htt]]]].
    destruct (read_byte_complete _ _ _ _ Hbs) as [elem [p [Hrb [Hz Hp]]]].
    rewrite Hrb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
    cbn [bind] in Hw. tag_in Hw Hz.
    destruct (module_decode_limits data p) as [r1|] eqn:E1;
      cbn [bind] in Hw; [|discriminate].
    destruct (decode_limits_complete _ _ _ _ _ E1
                (ltac:(rewrite Hp; exact Hlim0))) as [lim [p1 [-> [Hlim _]]]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    rewrite (validate_limits_complete lim limits_max_table_elems
               table_limit_bound (ltac:(reflexivity))
               (ltac:(rewrite Hlim; rewrite Htt in Hvalid;
                      unfold tabletype_valid in Hvalid;
                      cbn [tt_limits] in Hvalid; exact Hvalid))) in Hw.
    cbn [bind] in Hw. rewrite branch_ok in Hw. cbn [bind] in Hw.
    injection Hw as <-. do 2 eexists. reflexivity. }
  destruct Hok as [tt' [p' ->]]. exists tt', p'. split; [reflexivity|].
  ident repr_tabletype_det (decode_table_type_sound _ _ _ _ Hrun) H.
Qed.

Lemma decode_global_type_complete : forall data pos r gt rest,
  module_decode_global_type data pos = Ok r ->
  repr_globaltype (bytes_from data pos) gt rest ->
  exists gt' p',
    r = Core_result_Result_Ok (gt', p')
    /\ translate_globaltype gt' = gt
    /\ bytes_from data p' = rest.
Proof.
  intros data pos r gt rest Hrun H.
  assert (Hok : exists gt' p', r = Core_result_Result_Ok (gt', p')).
  { pose proof Hrun as Hw. unfold module_decode_global_type in Hw.
    destruct (repr_globaltype_inv _ _ _ H) as [t [mid [mu [Ht [Hmu _]]]]].
    destruct (module_decode_value_type data pos) as [r1|] eqn:E1;
      cbn [bind] in Hw; [|discriminate].
    destruct (decode_value_type_complete _ _ _ _ _ E1 Ht)
      as [vt [p [-> [_ Hp]]]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    destruct (repr_mut_inv _ _ _ Hmu) as [[Hbs _]|[Hbs _]];
      rewrite <- Hp in Hbs;
      destruct (read_byte_complete _ _ _ _ Hbs) as [m [p1 [Hrb [Hz _]]]];
      rewrite Hrb in Hw; cbn [bind] in Hw; rewrite branch_ok in Hw;
      cbn [bind] in Hw.
    - guard_true_in Hw Hz. injection Hw as <-. do 2 eexists. reflexivity.
    - guard_false_in Hw Hz. guard_true_in Hw Hz.
      injection Hw as <-. do 2 eexists. reflexivity. }
  destruct Hok as [gt' [p' ->]]. exists gt', p'. split; [reflexivity|].
  ident repr_globaltype_det (decode_global_type_sound _ _ _ _ Hrun) H.
Qed.

(* ================================================================== *)
(** ** 5.2.4 Names, and the UTF-8 table in the other direction         *)
(* ================================================================== *)

(** The soundness direction walks whatever tree the extraction produced and lets
    the constructor be picked by which one's side conditions hold. Completeness
    goes the other way: the constructor is given, so the arm is known, and the
    work is reaching it through the guard chain and showing every [utf8_cont] in
    it accepts. Four pieces carry it -- the offsets a sequence occupies, the
    guard walk, one continuation byte, and then ten arms that are each three
    lines. *)

Lemma bytes_at_uncons : forall data (i : usize) b l,
  bytes_at data (to_Z i) = b :: l ->
  exists b' : u8, slice_index_usize data i = Ok b' /\ to_Z b' = b.
Proof.
  intros data i b l H. rewrite <- bytes_from_at in H.
  destruct (bytes_from_uncons _ _ _ _ H) as [b' [p2 [Hidx [Hz _]]]].
  exists b'. split; [exact Hidx | exact Hz].
Qed.

Lemma bytes_at_cons_lt : forall data z b l,
  0 <= z -> bytes_at data z = b :: l -> z < dlen data.
Proof.
  intros data z b l Hz Heq.
  destruct (Z_le_gt_dec (dlen data) z) as [Hle|Hgt]; [|lia].
  rewrite bytes_at_end in Heq; [discriminate|].
  rewrite slice_len_spec in Hle. exact Hle.
Qed.

Lemma bytes_at_nil_ge : forall data z,
  0 <= z -> bytes_at data z = [] -> dlen data <= z.
Proof.
  intros data z Hz Heq. unfold bytes_at in Heq.
  apply (f_equal (@List.length _)) in Heq.
  rewrite List.skipn_length in Heq. rewrite byte_list_length in Heq.
  cbn [List.length] in Heq. rewrite slice_len_spec.
  apply (proj1 (Nat.sub_0_le _ _)) in Heq.
  apply Nat2Z.inj_le in Heq. rewrite Z2Nat.id in Heq by lia. exact Heq.
Qed.

Lemma bytes_at_lt_cons : forall data z,
  0 <= z -> z < dlen data -> exists b l, bytes_at data z = b :: l.
Proof.
  intros data z Hz Hlt.
  destruct (bytes_at data z) as [|b l] eqn:Heq; [|exists b, l; reflexivity].
  exfalso. pose proof (bytes_at_nil_ge _ _ Hz Heq). lia.
Qed.

(** The offsets a multi-byte sequence occupies. The reader computes [i+1], [i+2]
    and [i+3] from [i], so each step's tail has to be spelt the way the next
    step's head is; that is all these do. *)
Lemma off_1 : forall data (i : usize) b l,
  bytes_at data (to_Z i) = b :: l -> bytes_at data (to_Z i + 1) = l.
Proof.
  intros data i b l H. symmetry.
  eapply bytes_at_tail; [apply usize_nonneg | exact H].
Qed.

Lemma off_2 : forall data (i : usize) b l,
  bytes_at data (to_Z i + 1) = b :: l -> bytes_at data (to_Z i + 2) = l.
Proof.
  intros data i b l H. pose proof (usize_nonneg i).
  rewrite (bytes_at_congr data (to_Z i + 2) (to_Z i + 1 + 1)) by lia.
  symmetry. eapply bytes_at_tail; [lia | exact H].
Qed.

Lemma off_3 : forall data (i : usize) b l,
  bytes_at data (to_Z i + 2) = b :: l -> bytes_at data (to_Z i + 3) = l.
Proof.
  intros data i b l H. pose proof (usize_nonneg i).
  rewrite (bytes_at_congr data (to_Z i + 3) (to_Z i + 2 + 1)) by lia.
  symmetry. eapply bytes_at_tail; [lia | exact H].
Qed.

Lemma off_4 : forall data (i : usize) b l,
  bytes_at data (to_Z i + 3) = b :: l -> bytes_at data (to_Z i + 4) = l.
Proof.
  intros data i b l H. pose proof (usize_nonneg i).
  rewrite (bytes_at_congr data (to_Z i + 4) (to_Z i + 3 + 1)) by lia.
  symmetry. eapply bytes_at_tail; [lia | exact H].
Qed.

Lemma off_lt : forall data (i : usize) k b l,
  0 <= k -> bytes_at data (to_Z i + k) = b :: l -> to_Z i + k < dlen data.
Proof.
  intros data i k b l Hk H. pose proof (usize_nonneg i).
  eapply bytes_at_cons_lt; [lia | exact H].
Qed.

(** One continuation byte. The position is given by its numeric value rather
    than by the cursor, so a run computed as [i+2] and a stream fact spelt at
    offset 2 line up without renormalising. *)
Lemma utf8_cont_complete : forall bytes (j : usize) lo hi r z b l,
  module_utf8_cont bytes j lo hi = Ok r ->
  to_Z j = z ->
  bytes_at bytes z = b :: l ->
  to_Z lo <= b -> b <= to_Z hi ->
  r = Core_result_Result_Ok tt.
Proof.
  intros bytes j lo hi r z b l Hrun Hj Hs Hlo Hhi.
  unfold module_utf8_cont in Hrun. rewrite <- Hj in Hs.
  destruct (bytes_at_uncons _ _ _ _ Hs) as [b' [Hidx Hb]].
  pose proof (bytes_at_cons_lt _ _ _ _ (usize_nonneg j) Hs) as Hlt.
  rewrite (scalar_lt_geb_false j (slice_len bytes) Hlt) in Hrun.
  rewrite Hidx in Hrun. cbn [bind] in Hrun.
  rewrite (scalar_ltb_of_ge b' lo) in Hrun by lia.
  rewrite (scalar_gtb_of_le b' hi) in Hrun by lia.
  injection Hrun as <-. reflexivity.
Qed.

(** A guard against a literal, resolved by computing the literal's value. Every
    guard in [utf8_sequence_len] is one of these three, and which way it goes is
    decided by [lia] against the lead byte's known value or range. *)
Ltac lit y :=
  let v := eval vm_compute in (to_Z y) in
  let H := fresh "Hv" in
  assert (H : to_Z y = v) by reflexivity.

Ltac gval_in Hw :=
  match type of Hw with
  | context [ if (?x s<= ?y) then _ else _ ] =>
      lit y;
      first [ rewrite (scalar_leb_of_le x y) in Hw by lia
            | rewrite (scalar_leb_of_gt x y) in Hw by lia ]
  | context [ if (?x s>= ?y) then _ else _ ] =>
      lit y;
      first [ rewrite (scalar_ge_geb_true x y) in Hw by lia
            | rewrite (scalar_lt_geb_false x y) in Hw by lia ]
  | context [ if (?x s= ?y) then _ else _ ] =>
      lit y;
      first [ rewrite (scalar_eqb_of_eq x y) in Hw by lia
            | rewrite (scalar_eqb_of_ne x y) in Hw by lia ]
  end.

(** One [usize_add] and the [utf8_cont] it feeds. The addition cannot overflow
    because the byte it is about to read is inside the input, which is what the
    [off_lt] facts in context say. *)
Ltac cstep Hw :=
  match type of Hw with
  | context [ usize_add ?i ?k ] =>
      let j := fresh "j" in let Ej := fresh "Ej" in let Hj := fresh "Hj" in
      lit k;
      destruct (usize_add_ok i k ltac:(lia)) as [j [Ej Hj]];
      rewrite Ej in Hw; cbn [bind] in Hw
  end;
  match type of Hw with
  | context [ module_utf8_cont ?bs ?j ?lo ?hi ] =>
      let rc := fresh "rc" in let Ec := fresh "Ec" in let Hc := fresh "Hc" in
      destruct (module_utf8_cont bs j lo hi) as [rc|] eqn:Ec;
        cbn [bind] in Hw; [|discriminate];
      lit lo; lit hi;
      assert (Hc : rc = Core_result_Result_Ok tt)
        by (eapply utf8_cont_complete;
            [exact Ec | eassumption | eassumption | lia | lia]);
      rewrite Hc in Hw; rewrite branch_ok in Hw; cbn [bind] in Hw
  end.

(** Close an arm: the length it returns, the room it needed, and the stream past
    the sequence. The length comes back as a [usize] literal, and the [off_lt]
    facts in context are what say the input really had that many bytes. *)
Ltac arm_done Hw :=
  injection Hw as <-; eexists; split; [reflexivity|];
  (* the length comes back as a [usize] literal, and substituting one of those
     loses the notation, so take the whole [to_Z n] term out of the goal rather
     than writing it down again *)
  match goal with
  | [ |- 1 <= ?z /\ _ ] =>
      let v := eval vm_compute in z in
      let Hn := fresh "Hn" in
      assert (Hn : z = v) by reflexivity;
      split; [lia|]; split; [lia|]; rewrite Hn
  end.

Lemma utf8_sequence_len_complete : forall bytes (i : usize) zs r,
  utf8_valid zs ->
  bytes_at bytes (to_Z i) = zs ->
  zs <> [] ->
  module_utf8_sequence_len bytes i = Ok r ->
  exists n, r = Core_result_Result_Ok n
            /\ 1 <= to_Z n
            /\ to_Z i + to_Z n <= dlen bytes
            /\ utf8_valid (bytes_at bytes (to_Z i + to_Z n)).
Proof.
  intros bytes i zs r Hvalid Hzs Hne Hrun.
  pose proof (usize_nonneg i). pose proof (usize_le_max (slice_len bytes)).
  pose proof Hrun as Hw. unfold module_utf8_sequence_len in Hw.
  destruct Hvalid as
    [ | b tl Hb Hrec
      | b1 b2 tl Hb1 Hb2 Hrec
      | b2 b3 tl Hb2 Hb3 Hrec
      | b1 b2 b3 tl Hb1 Hb2 Hb3 Hrec
      | b2 b3 tl Hb2 Hb3 Hrec
      | b1 b2 b3 tl Hb1 Hb2 Hb3 Hrec
      | b2 b3 b4 tl Hb2 Hb3 Hb4 Hrec
      | b1 b2 b3 b4 tl Hb1 Hb2 Hb3 Hb4 Hrec
      | b2 b3 b4 tl Hb2 Hb3 Hb4 Hrec ].
  - exfalso. apply Hne. reflexivity.
  (* one byte *)
  - destruct (bytes_at_uncons _ _ _ _ Hzs) as [b0 [Hidx Hb0]].
    pose proof (off_1 _ _ _ _ Hzs) as Hs1.
    pose proof (off_lt _ _ 0 _ _ ltac:(lia)
                  (ltac:(rewrite (bytes_at_congr bytes (to_Z i + 0) (to_Z i))
                           by lia; exact Hzs))) as Hl0.
    rewrite Hidx in Hw. cbn [bind] in Hw.
    repeat gval_in Hw.
    arm_done Hw. rewrite Hs1. exact Hrec.
  (* two bytes *)
  - destruct (bytes_at_uncons _ _ _ _ Hzs) as [b0 [Hidx Hb0]].
    pose proof (off_1 _ _ _ _ Hzs) as Hs1.
    pose proof (off_2 _ _ _ _ Hs1) as Hs2.
    pose proof (off_lt _ _ 1 _ _ ltac:(lia) Hs1) as Hl1.
    rewrite Hidx in Hw. cbn [bind] in Hw.
    repeat gval_in Hw. cstep Hw.
    arm_done Hw. rewrite Hs2. exact Hrec.
  (* three bytes, lead 0xE0 *)
  - destruct (bytes_at_uncons _ _ _ _ Hzs) as [b0 [Hidx Hb0]].
    pose proof (off_1 _ _ _ _ Hzs) as Hs1.
    pose proof (off_2 _ _ _ _ Hs1) as Hs2.
    pose proof (off_3 _ _ _ _ Hs2) as Hs3.
    pose proof (off_lt _ _ 1 _ _ ltac:(lia) Hs1) as Hl1.
    pose proof (off_lt _ _ 2 _ _ ltac:(lia) Hs2) as Hl2.
    rewrite Hidx in Hw. cbn [bind] in Hw.
    repeat gval_in Hw. cstep Hw. cstep Hw.
    arm_done Hw. rewrite Hs3. exact Hrec.
  (* three bytes, 0xE1 to 0xEC *)
  - destruct (bytes_at_uncons _ _ _ _ Hzs) as [b0 [Hidx Hb0]].
    pose proof (off_1 _ _ _ _ Hzs) as Hs1.
    pose proof (off_2 _ _ _ _ Hs1) as Hs2.
    pose proof (off_3 _ _ _ _ Hs2) as Hs3.
    pose proof (off_lt _ _ 1 _ _ ltac:(lia) Hs1) as Hl1.
    pose proof (off_lt _ _ 2 _ _ ltac:(lia) Hs2) as Hl2.
    rewrite Hidx in Hw. cbn [bind] in Hw.
    repeat gval_in Hw. cstep Hw. cstep Hw.
    arm_done Hw. rewrite Hs3. exact Hrec.
  (* three bytes, lead 0xED *)
  - destruct (bytes_at_uncons _ _ _ _ Hzs) as [b0 [Hidx Hb0]].
    pose proof (off_1 _ _ _ _ Hzs) as Hs1.
    pose proof (off_2 _ _ _ _ Hs1) as Hs2.
    pose proof (off_3 _ _ _ _ Hs2) as Hs3.
    pose proof (off_lt _ _ 1 _ _ ltac:(lia) Hs1) as Hl1.
    pose proof (off_lt _ _ 2 _ _ ltac:(lia) Hs2) as Hl2.
    rewrite Hidx in Hw. cbn [bind] in Hw.
    repeat gval_in Hw. cstep Hw. cstep Hw.
    arm_done Hw. rewrite Hs3. exact Hrec.
  (* three bytes, 0xEE and 0xEF. The one arm whose lead byte the Rust tests by
     equality twice -- it writes [... || b == 0xEE || b == 0xEF] -- so the range
     has to be split before the guard walk can decide anything. *)
  - assert (Hcase : b1 = 238 \/ b1 = 239) by lia.
    destruct Hcase as [Hc|Hc]; subst b1;
      (destruct (bytes_at_uncons _ _ _ _ Hzs) as [b0 [Hidx Hb0]];
       pose proof (off_1 _ _ _ _ Hzs) as Hs1;
       pose proof (off_2 _ _ _ _ Hs1) as Hs2;
       pose proof (off_3 _ _ _ _ Hs2) as Hs3;
       pose proof (off_lt _ _ 1 _ _ ltac:(lia) Hs1) as Hl1;
       pose proof (off_lt _ _ 2 _ _ ltac:(lia) Hs2) as Hl2;
       rewrite Hidx in Hw; cbn [bind] in Hw;
       repeat gval_in Hw; cstep Hw; cstep Hw;
       arm_done Hw; rewrite Hs3; exact Hrec).
  (* four bytes, lead 0xF0 *)
  - destruct (bytes_at_uncons _ _ _ _ Hzs) as [b0 [Hidx Hb0]].
    pose proof (off_1 _ _ _ _ Hzs) as Hs1.
    pose proof (off_2 _ _ _ _ Hs1) as Hs2.
    pose proof (off_3 _ _ _ _ Hs2) as Hs3.
    pose proof (off_4 _ _ _ _ Hs3) as Hs4.
    pose proof (off_lt _ _ 1 _ _ ltac:(lia) Hs1) as Hl1.
    pose proof (off_lt _ _ 2 _ _ ltac:(lia) Hs2) as Hl2.
    pose proof (off_lt _ _ 3 _ _ ltac:(lia) Hs3) as Hl3.
    rewrite Hidx in Hw. cbn [bind] in Hw.
    repeat gval_in Hw. cstep Hw. cstep Hw. cstep Hw.
    arm_done Hw. rewrite Hs4. exact Hrec.
  (* four bytes, 0xF1 to 0xF3 *)
  - destruct (bytes_at_uncons _ _ _ _ Hzs) as [b0 [Hidx Hb0]].
    pose proof (off_1 _ _ _ _ Hzs) as Hs1.
    pose proof (off_2 _ _ _ _ Hs1) as Hs2.
    pose proof (off_3 _ _ _ _ Hs2) as Hs3.
    pose proof (off_4 _ _ _ _ Hs3) as Hs4.
    pose proof (off_lt _ _ 1 _ _ ltac:(lia) Hs1) as Hl1.
    pose proof (off_lt _ _ 2 _ _ ltac:(lia) Hs2) as Hl2.
    pose proof (off_lt _ _ 3 _ _ ltac:(lia) Hs3) as Hl3.
    rewrite Hidx in Hw. cbn [bind] in Hw.
    repeat gval_in Hw. cstep Hw. cstep Hw. cstep Hw.
    arm_done Hw. rewrite Hs4. exact Hrec.
  (* four bytes, lead 0xF4 *)
  - destruct (bytes_at_uncons _ _ _ _ Hzs) as [b0 [Hidx Hb0]].
    pose proof (off_1 _ _ _ _ Hzs) as Hs1.
    pose proof (off_2 _ _ _ _ Hs1) as Hs2.
    pose proof (off_3 _ _ _ _ Hs2) as Hs3.
    pose proof (off_4 _ _ _ _ Hs3) as Hs4.
    pose proof (off_lt _ _ 1 _ _ ltac:(lia) Hs1) as Hl1.
    pose proof (off_lt _ _ 2 _ _ ltac:(lia) Hs2) as Hl2.
    pose proof (off_lt _ _ 3 _ _ ltac:(lia) Hs3) as Hl3.
    rewrite Hidx in Hw. cbn [bind] in Hw.
    repeat gval_in Hw. cstep Hw. cstep Hw. cstep Hw.
    arm_done Hw. rewrite Hs4. exact Hrec.
Qed.

(** The loop, one sequence at a time. Every sequence is at least one byte, which
    is what makes the measure decrease; the length it returns is what says how
    far the next one starts. *)
Lemma validate_utf8_loop_complete : forall m bytes (i : usize) r,
  dlen bytes - to_Z i <= Z.of_nat m ->
  utf8_valid (bytes_at bytes (to_Z i)) ->
  module_validate_utf8_loop bytes i = Ok r ->
  r = Core_result_Result_Ok tt.
Proof.
  induction m as [|m IH]; intros bytes i r Hmeas Hvalid Hw;
    pose proof (usize_nonneg i);
    unfold module_validate_utf8_loop in Hw; rewrite loop_unfold in Hw;
    cbn beta iota in Hw; destruct (i s>= slice_len bytes) eqn:Hge.
  1,3: injection Hw as <-; reflexivity.
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    destruct (bytes_at_lt_cons bytes (to_Z i) (ltac:(lia)) Hge)
      as [b [l Hzs]].
    rewrite Hzs in Hvalid.
    destruct (module_utf8_sequence_len bytes i) as [rn|] eqn:Eseq;
      cbn [bind] in Hw; [|discriminate].
    destruct (utf8_sequence_len_complete bytes i _ _ Hvalid Hzs
                (ltac:(discriminate)) Eseq) as [n [-> [Hn1 [Hroom Hnext]]]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    pose proof (usize_le_max (slice_len bytes)).
    destruct (usize_add_ok i n (ltac:(lia))) as [i2 [Hadd Hi2]].
    rewrite Hadd in Hw. cbn [bind] in Hw.
    apply (IH bytes i2 r); [lia | rewrite Hi2; exact Hnext | exact Hw].
Qed.

Lemma validate_utf8_complete : forall bytes r,
  utf8_valid (byte_list bytes) ->
  module_validate_utf8 bytes = Ok r ->
  r = Core_result_Result_Ok tt.
Proof.
  intros bytes r Hvalid Hw. unfold module_validate_utf8 in Hw.
  apply (validate_utf8_loop_complete (Z.to_nat (dlen bytes)) bytes 0%usize r);
    [ assert (H0 : to_Z 0%usize = 0) by reflexivity;
      rewrite Z2Nat.id by (rewrite slice_len_spec; lia); lia
    | exact Hvalid
    | exact Hw ].
Qed.

(** A name. The [vec(byte)] is shared with a data segment's contents; what a
    name adds is the UTF-8 side condition, and the two byte types line up
    pointwise, so the name the decoder built is the one the derivation names by
    [Forall2] determinism. *)
Lemma decode_name_complete : forall data pos r nm rest,
  dlen data <= module_bytes ->
  module_decode_name data pos = Ok r ->
  repr_name (bytes_from data pos) nm rest ->
  exists v p',
    r = Core_result_Result_Ok (v, p')
    /\ translate_name v = nm
    /\ bytes_from data p' = rest.
Proof.
  intros data pos r nm rest Hmod Hrun H.
  destruct (repr_name_inv _ _ _ H) as [zs [Hvec [Hf2 Hutf8]]].
  destruct (decode_bytevec_complete _ _ _ _ Hmod Hvec)
    as [len [n [p [q [v [Hleb [Hcast [Hhb [Hadd [Hcopy [Hmap Hq]]]]]]]]]]].
  assert (Hok : r = Core_result_Result_Ok (v, q)).
  { pose proof Hrun as Hw. unfold module_decode_name in Hw.
    rewrite Hleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
    cbn [bind] in Hw. rewrite Hcast in Hw. cbn [bind] in Hw.
    rewrite Hhb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
    cbn [bind] in Hw. rewrite Hadd in Hw. cbn [bind] in Hw.
    rewrite Hcopy in Hw. cbn [bind] in Hw. rewrite vec_deref_spec in Hw.
    destruct (module_validate_utf8 v) as [ru|] eqn:Eu; cbn [bind] in Hw;
      [|discriminate].
    rewrite (validate_utf8_complete v ru
               (ltac:(unfold byte_list; rewrite Hmap; exact Hutf8)) Eu) in Hw.
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    injection Hw as <-. reflexivity. }
  subst r. exists v, q. split; [reflexivity|].
  ident repr_name_det (decode_name_sound _ _ _ _ Hrun) H.
Qed.

(* ================================================================== *)
(** ** Indices                                                         *)
(* ================================================================== *)

(** Every index in the format is a [u32] read by [read_u32_leb], so there is no
    decoder of its own. *)
Lemma read_idx_complete : forall data pos x rest,
  repr_idx (bytes_from data pos) x rest ->
  exists (v : scalar U32) p',
    reader_read_u32_leb data pos = Ok (Core_result_Result_Ok (v, p'))
    /\ translate_idx v = x
    /\ bytes_from data p' = rest.
Proof.
  intros data pos x rest H.
  destruct (repr_idx_inv _ _ _ H) as [z [Hz ->]].
  destruct (read_u32_leb_complete _ _ _ _ Hz) as [v [p' [Hrun [Hval Hp]]]].
  exists v, p'. split; [exact Hrun|].
  split; [unfold translate_idx; rewrite Hval; reflexivity | exact Hp].
Qed.

(* ================================================================== *)
(** ** 5.5.16 The header, and 5.5.2 a section's frame                  *)
(* ================================================================== *)

(** Eight bytes, all of them fixed, so eight reads and eight guards. *)
Lemma read_header_complete : forall data r rest,
  module_read_header data = Ok r ->
  repr_magic_version (byte_list data) rest ->
  exists p, r = Core_result_Result_Ok p
            /\ bytes_from data p = rest
            /\ to_Z p <= dlen data.
Proof.
  intros data r rest Hrun H. unfold repr_magic_version in H.
  rewrite <- bytes_from_zero in H.
  pose proof Hrun as Hw. unfold module_read_header in Hw.
  destruct (read_byte_complete _ _ _ _ H)  as [c0 [q1 [E0 [Z0 H1]]]].
  rewrite E0 in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw. cbn [bind] in Hw.
  destruct (read_byte_complete _ _ _ _ H1) as [c1 [q2 [E1 [Z1 H2]]]].
  rewrite E1 in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw. cbn [bind] in Hw.
  destruct (read_byte_complete _ _ _ _ H2) as [c2 [q3 [E2 [Z2 H3]]]].
  rewrite E2 in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw. cbn [bind] in Hw.
  destruct (read_byte_complete _ _ _ _ H3) as [c3 [q4 [E3 [Z3 H4]]]].
  rewrite E3 in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw. cbn [bind] in Hw.
  tag_in Hw Z0. tag_in Hw Z1. tag_in Hw Z2. tag_in Hw Z3.
  destruct (read_byte_complete _ _ _ _ H4) as [d0 [q5 [E4 [W0 H5]]]].
  rewrite E4 in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw. cbn [bind] in Hw.
  destruct (read_byte_complete _ _ _ _ H5) as [d1 [q6 [E5 [W1 H6]]]].
  rewrite E5 in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw. cbn [bind] in Hw.
  destruct (read_byte_complete _ _ _ _ H6) as [d2 [q7 [E6 [W2 H7]]]].
  rewrite E6 in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw. cbn [bind] in Hw.
  destruct (read_byte_complete _ _ _ _ H7) as [d3 [q8 [E7 [W3 H8]]]].
  rewrite E7 in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw. cbn [bind] in Hw.
  tag_in Hw W0. tag_in Hw W1. tag_in Hw W2. tag_in Hw W3.
  injection Hw as <-. exists q8. split; [reflexivity|].
  split; [exact H8 | exact (read_byte_le_len _ _ _ _ E7)].
Qed.

(** Spec 5.5.2's framing, the converse of [Module_Sound.read_section_header_sound].
    [repr_section] pins the contents down by splitting the input, so what the
    derivation hands over is a split, and what the code needs of it is that the
    declared size is the prefix's length -- which is [have_bytes]' premise. *)
Lemma read_section_header_complete :
  forall data (pos : usize) r idz p0 sz content rest,
  bytes_from data pos = idz :: p0 ->
  repr_u32 p0 sz (content ++ rest) ->
  Z.of_nat (List.length content) = sz ->
  module_read_section_header data pos = Ok r ->
  exists (id : u8) (start fin : usize),
    r = Core_result_Result_Ok (id, start, fin)
    /\ to_Z id = idz
    /\ section_content data start fin = content
    /\ bytes_from data start = content ++ rest
    /\ bytes_from data fin = rest
    /\ to_Z fin <= dlen data
    /\ to_Z start <= to_Z fin.
Proof.
  intros data pos r idz p0 sz content rest Hbs Hn Hlen Hrun.
  pose proof Hrun as Hw. unfold module_read_section_header in Hw.
  destruct (read_byte_complete _ _ _ _ Hbs) as [id [p [Eb [Hz Hp]]]].
  rewrite Eb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw. cbn [bind] in Hw.
  rewrite <- Hp in Hn.
  destruct (read_u32_leb_complete _ _ _ _ Hn) as [size [q [Eleb [Hval Hq]]]].
  rewrite Eleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
  cbn [bind] in Hw.
  pose proof (read_u32_leb_le_len _ _ _ _ Eleb) as Hqle.
  destruct (cast_u32_usize_ok size) as [n [Hcast Hn2]].
  rewrite Hcast in Hw. cbn [bind] in Hw.
  assert (Hcl : Z.of_nat (List.length content) = to_Z n) by lia.
  assert (Hroom : to_Z q + to_Z n <= dlen data)
    by (rewrite <- Hcl; exact (bytes_from_app_len _ _ _ _ Hqle Hq)).
  rewrite (have_bytes_complete _ _ _ Hroom) in Hw. cbn [bind] in Hw.
  rewrite branch_ok in Hw. cbn [bind] in Hw.
  pose proof (usize_le_max (slice_len data)).
  pose proof (usize_nonneg q). pose proof (usize_nonneg n).
  destruct (usize_add_ok q n (ltac:(lia))) as [fin [Hadd Hfin]].
  rewrite Hadd in Hw. cbn [bind] in Hw. injection Hw as <-.
  exists id, q, fin.
  assert (Hcnt : Z.to_nat (to_Z fin - to_Z q) = List.length content)
    by (rewrite Hfin; rewrite Z.add_simpl_l; rewrite <- Hcl;
        apply Z_to_nat_of_nat).
  assert (Hskip : bytes_from data fin
                  = List.skipn (List.length content) (bytes_from data q))
    by (apply bytes_from_skipn; lia).
  split; [reflexivity|]. split; [exact Hz|].
  split; [unfold section_content; rewrite Hcnt; rewrite Hq;
          apply firstn_app_exact|].
  split; [exact Hq|].
  split; [rewrite Hskip; rewrite Hq; apply skipn_app_exact|].
  split; lia.
Qed.

(** A section's contents and what follows it are a split of the stream at the
    section's start, which is the other direction of the two [section_contents]
    lemmas: soundness pushes a run over the whole input down into the section,
    completeness lifts a run over the section back out. [reads_prefix] is what
    allows the lift, and the note in [Spec_Module.v] says why determinism would
    not have been enough. *)
Lemma section_content_app : forall data (start fin : usize),
  to_Z start <= to_Z fin ->
  bytes_from data start = section_content data start fin ++ bytes_from data fin.
Proof.
  intros data start fin Hle. unfold section_content.
  rewrite (bytes_from_skipn data start fin (Z.to_nat (to_Z fin - to_Z start)))
    by (rewrite Z2Nat.id; lia).
  symmetry. apply List.firstn_skipn.
Qed.

Lemma section_lift : forall A (R : list Z -> A -> list Z -> Prop)
                            data (start fin : usize) x mid,
  reads_prefix R ->
  R (section_content data start fin) x mid ->
  to_Z start <= to_Z fin ->
  R (bytes_from data start) x (mid ++ bytes_from data fin).
Proof.
  intros A R data start fin x mid HR Hrun Hle.
  destruct (HR _ _ _ Hrun) as [pre [Heq Hall]].
  rewrite (section_content_app data start fin Hle). rewrite Heq.
  rewrite <- app_assoc. apply Hall.
Qed.

(** Two cursors ordered by how much stream is left at each. *)
Lemma bytes_from_len_le : forall data (p q : usize),
  to_Z p <= dlen data -> to_Z q <= dlen data ->
  (List.length (bytes_from data q) <= List.length (bytes_from data p))%nat ->
  to_Z p <= to_Z q.
Proof.
  intros data p q Hp Hq Hlen. unfold bytes_from in Hlen.
  rewrite List.skipn_length in Hlen. rewrite List.skipn_length in Hlen.
  rewrite byte_list_length in Hlen. rewrite slice_len_spec in *.
  pose proof (usize_nonneg p). pose proof (usize_nonneg q).
  assert (Hpn : (Z.to_nat (to_Z p) <= List.length (vec_list data))%nat)
    by (apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; lia).
  assert (Hqn : (Z.to_nat (to_Z q) <= List.length (vec_list data))%nat)
    by (apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; lia).
  apply Nat2Z.inj_le in Hlen. rewrite Nat2Z.inj_sub in Hlen by exact Hqn.
  rewrite Nat2Z.inj_sub in Hlen by exact Hpn.
  rewrite Z2Nat.id in Hlen by lia. rewrite Z2Nat.id in Hlen by lia. lia.
Qed.

(** Spec 5.5.3. All the rule asks is that a name starts the section, so all the
    decoder can reject on is the name itself and whether it fits, and the
    derivation says it does: what follows the name inside the section is what
    the rule leaves unconstrained. *)
Lemma decode_custom_section_complete :
  forall data (start fin : usize) r nm mid,
  dlen data <= module_bytes ->
  to_Z start <= to_Z fin ->
  to_Z fin <= dlen data ->
  repr_name (section_content data start fin) nm mid ->
  module_decode_custom_section data start fin = Ok r ->
  exists c, r = Core_result_Result_Ok c.
Proof.
  intros data start fin r nm mid Hmod Hle Hfin Hnm Hrun.
  pose proof (usize_nonneg start).
  pose proof (section_lift _ repr_name data start fin nm mid
                repr_name_prefix Hnm Hle) as Hlift.
  pose proof Hrun as Hw. unfold module_decode_custom_section in Hw.
  destruct (module_decode_name data start) as [rn|] eqn:En; cbn [bind] in Hw;
    [|discriminate].
  destruct (decode_name_complete _ _ _ _ _ Hmod En Hlift)
    as [v [p [-> [_ Hp]]]].
  rewrite branch_ok in Hw. cbn [bind] in Hw.
  destruct (decode_name_step _ _ _ _ En (ltac:(lia))) as [_ Hple].
  (* the name fits: what is left at [p] is the section's tail plus everything
     after the section, so [p] is no further than the section's end *)
  rewrite (scalar_gtb_of_le p fin) in Hw.
  2: { apply (bytes_from_len_le data p fin Hple Hfin).
       rewrite Hp. rewrite List.app_length. lia. }
  injection Hw as <-. eexists. reflexivity.
Qed.

(* ================================================================== *)
(** ** 5.4.1 Constant expressions                                      *)
(* ================================================================== *)

(** An expression of one unstructured instruction, the converse of
    [Module_Sound.repr_expr_single]. [else_sugar] has nothing to do in either
    direction here, because the instruction opens no frame, so the stream is
    already lean and the two [keep] steps pin it down. *)
(** The shape condition comes *after* the derivation, so that
    [ltac:(reflexivity)] can discharge it: the instruction is an evar until the
    derivation is elaborated. The same ordering trap as
    [Spec_Expr.else_sugar_keep_inv]. *)
Lemma repr_expr_single_inv : forall be bs rest,
  repr_expr bs [be] rest ->
  flat_of_one be = [FO_plain be] ->
  exists mid, repr_op bs (FO_plain be) mid /\ repr_op mid FO_end rest.
Proof.
  intros be bs rest [ops [Hsug Hops]] Hflat.
  rewrite flat_of_single in Hsug. rewrite Hflat in Hsug.
  cbn [List.app] in Hsug.
  destruct (else_sugar_keep_inv _ _ _ Hsug (ltac:(discriminate)))
    as [l1 [-> Hs1]].
  destruct (else_sugar_keep_inv _ _ _ Hs1 (ltac:(discriminate)))
    as [l2 [-> Hs2]].
  apply else_sugar_nil_inv in Hs2. subst l2.
  destruct (repr_ops_cons_inv _ _ _ _ Hops) as [mid [Hop1 Hops1]].
  destruct (repr_ops_cons_inv _ _ _ _ Hops1) as [mid2 [Hop2 Hops2]].
  apply repr_ops_nil_rest in Hops2.
  exists mid. split; [exact Hop1 | rewrite Hops2; exact Hop2].
Qed.

(** Taking a [repr_op] derivation for a *named* operator apart. [repr_op_inv]
    gives the fourteen rules; what closes thirteen of them is either a
    constructor clash on the operator or, for the two rules that carry an
    instruction of their own, [op_spec_invert]'s disequalities. The byte comes
    from the same lemma.

    The fourteen cases are flattened into fourteen goals rather than matched with
    a fourteen-deep intro pattern, which the note in the handoff says is easy to
    miscount; the goals are then in rule order and each is one line. *)
Local Ltac split_cases :=
  repeat match goal with
         | [ Hc : _ \/ _ |- _ ] => destruct Hc as [Hc|Hc]
         end.

Lemma repr_op_end_inv : forall bs rest,
  repr_op bs FO_end rest -> bs = 11 :: rest.
Proof.
  intros bs rest H.
  destruct (repr_op_inv _ _ _ H) as [b [bs' [Hbs Hc]]].
  split_cases.
  2: { destruct Hc as [Hsp [_ ->]].
       destruct (op_spec_invert _ _ Hsp) as [Hend _].
       rewrite Hbs. rewrite (Hend (ltac:(reflexivity))). reflexivity. }
  1: destruct Hc as [be [_ [Hop _]]]; discriminate Hop.
  all: repeat (match goal with
               | [ Hc : exists _, _ |- _ ] =>
                   let x := fresh "x" in destruct Hc as [x Hc]
               | [ Hc : _ /\ _ |- _ ] =>
                   let h := fresh "Hp" in destruct Hc as [h Hc]
               end).
  all: discriminate.
Qed.

Lemma repr_op_const_inv : forall bs v rest,
  repr_op bs (FO_plain (BI_const_num v)) rest ->
  exists b bs', bs = b :: bs'
  /\ ((b = 65 /\ exists z, repr_s32 bs' z rest /\ v = const_val T_i32 z)
      \/ (b = 66 /\ exists z, repr_sN 64 bs' z rest /\ v = const_val T_i64 z)
      \/ (b = 67 /\ exists w, repr_bytes_le 4 bs' w rest
                              /\ v = fconst_val T_f32 w)
      \/ (b = 68 /\ exists w, repr_bytes_le 8 bs' w rest
                              /\ v = fconst_val T_f64 w)).
Proof.
  intros bs v rest H.
  destruct (repr_op_inv _ _ _ H) as [b [bs' [Hbs Hc]]].
  exists b, bs'. split; [exact Hbs|]. clear H Hbs.
  split_cases.
  (* the named goals are taken in *descending* order, because closing one
     renumbers everything after it *)
  (* the index rule names one of eight instructions, none of them a const *)
  10: { destruct Hc as [io [x [_ [_ Hop]]]]. destruct io; discriminate Hop. }
  9: { destruct Hc as [nt [w [Hsp [Hw Hop]]]]. injection Hop as Hop.
       destruct (op_spec_invert _ _ Hsp) as [_ [_ [Hfc _]]].
       destruct (Hfc nt (ltac:(reflexivity))) as [[Hnt Hb]|[Hnt Hb]];
         subst nt; subst b.
       - right. right. left. split; [reflexivity|]. exists w.
         split; [exact Hw | exact Hop].
       - right. right. right. split; [reflexivity|]. exists w.
         split; [exact Hw | exact Hop]. }
  8: { destruct Hc as [nt [z [Hsp [Hz Hop]]]]. injection Hop as Hop.
       destruct (op_spec_invert _ _ Hsp) as [_ [Hcst _]].
       destruct (Hcst nt (ltac:(reflexivity))) as [[Hnt Hb]|[Hnt Hb]];
         subst nt; subst b.
       - left. split; [reflexivity|]. exists z. split; [exact Hz | exact Hop].
       - right. left. split; [reflexivity|]. exists z.
         split; [exact Hz | exact Hop]. }
  (* Sh_nullary and Sh_reserved carry the instruction, so only the table rules
     them out: no row names a [const] that way *)
  7: { destruct Hc as [be [r [Hsp [_ [Hop _]]]]]. injection Hop as Hop.
       exfalso.
       destruct (op_spec_invert _ _ Hsp) as [_ [_ [_ [_ [_ [Hnr _]]]]]].
       apply (Hnr v). rewrite <- Hop. reflexivity. }
  1: { destruct Hc as [be [Hsp [Hop _]]]. injection Hop as Hop. exfalso.
       destruct (op_spec_invert _ _ Hsp) as [_ [_ [_ [_ [Hnn _]]]]].
       apply (Hnn v). rewrite <- Hop. reflexivity. }
  all: repeat (match goal with
               | [ Hc : exists _, _ |- _ ] =>
                   let x := fresh "x" in destruct Hc as [x Hc]
               | [ Hc : _ /\ _ |- _ ] =>
                   let h := fresh "Hp" in destruct Hc as [h Hc]
               end).
  all: discriminate.
Qed.

Lemma repr_op_global_get_inv : forall bs x rest,
  repr_op bs (FO_plain (BI_global_get x)) rest ->
  exists bs' z, bs = 35 :: bs' /\ repr_u32 bs' z rest /\ x = Z.to_N z.
Proof.
  intros bs x rest H.
  destruct (repr_op_inv _ _ _ H) as [b [bs' [Hbs Hc]]].
  split_cases.
  10: { destruct Hc as [io [z [Hsp [Hz Hop]]]].
        destruct (op_spec_invert _ _ Hsp) as [_ [_ [_ [Hgg _]]]].
        destruct io; try discriminate Hop.
        injection Hop as Hop.
        exists bs', z. rewrite Hbs.
        rewrite (Hgg (ltac:(reflexivity))).
        split; [reflexivity|]. split; [exact Hz | exact Hop]. }
  7: { destruct Hc as [be [r [Hsp [_ [Hop _]]]]]. injection Hop as Hop.
       exfalso.
       destruct (op_spec_invert _ _ Hsp) as [_ [_ [_ [_ [_ [_ [_ Hnr]]]]]]].
       apply (Hnr x). rewrite <- Hop. reflexivity. }
  1: { destruct Hc as [be [Hsp [Hop _]]]. injection Hop as Hop. exfalso.
       destruct (op_spec_invert _ _ Hsp) as [_ [_ [_ [_ [_ [_ [Hnn _]]]]]]].
       apply (Hnn x). rewrite <- Hop. reflexivity. }
  all: repeat (match goal with
               | [ Hc : exists _, _ |- _ ] =>
                   let x := fresh "x" in destruct Hc as [x Hc]
               | [ Hc : _ /\ _ |- _ ] =>
                   let h := fresh "Hp" in destruct Hc as [h Hc]
               end).
  all: discriminate.
Qed.

(** What the decoder can reject a constant expression on, besides the bytes.
    [decode_const_expr] reads exactly one instruction, so the hypothesis has to
    say the expression is one -- and one of the five the format's [ConstExpr] can
    hold. That is not a weakening: spec 3.4.10 restricts an initialiser to
    constant instructions and 3.4.4 types it [[] -> [t]], and every constant
    instruction pushes exactly one value, so an expression of that type has
    exactly one instruction in it. Deriving this from
    [module_global_type_checker] is where that argument goes; here it is the
    premise, in the same terms [Module_Sound.const_expr_ok] reports.
    The declared type is stated as a WasmCert [value_type], since that is what a
    module's global carries; [translate_vt_v] is injective on the four number
    types, which is what lets the decoded one be identified with it. *)
Definition const_ok (env : env_Env_t) (t : value_type) (e : expr) : Prop :=
  exists ce vt,
    e = [translate_const_expr ce]
    /\ translate_vt_v vt = t
    /\ const_expr_ok env vt ce.

Lemma translate_vt_v_inj : forall a b, translate_vt_v a = translate_vt_v b -> a = b.
Proof. intros a b H. destruct a, b; solve [reflexivity | discriminate]. Qed.

Lemma expect_const_type_complete : forall a b r,
  module_expect_const_type a b = Ok r ->
  a = b ->
  r = Core_result_Result_Ok tt.
Proof.
  intros a b r H <-. unfold module_expect_const_type in H.
  rewrite vt_ne_spec in H. cbn [bind] in H.
  destruct a; cbn [types_ValueType_t_beq negb] in H; injection H as <-;
    reflexivity.
Qed.

Lemma const_global_complete : forall env (idx : scalar U32) r gt,
  module_const_global env idx = Ok r ->
  List.nth_error (vec_list env.(env_Env_global_types))
                 (Z.to_nat (to_Z idx)) = Some gt ->
  gt.(types_GlobalType_mutability) = Types_Mut_Const ->
  to_Z idx < to_Z env.(env_Env_num_imported_globals) ->
  r = Core_result_Result_Ok gt.
Proof.
  intros env idx r gt H Hnth Hmut Himp. unfold module_const_global in H.
  destruct (scalar_cast U32 Usize idx) as [i|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  assert (Hi : to_Z i = to_Z idx)
    by (unfold scalar_cast in Hcast; apply mk_scalar_ok_to_Z in Hcast;
        exact Hcast).
  (* the index is in range because the lookup found something there *)
  assert (Hlt : to_Z i < to_Z (alloc_vec_Vec_len env.(env_Env_global_types))).
  { rewrite vec_len_spec. rewrite Hi.
    assert (Hsome : List.nth_error (vec_list env.(env_Env_global_types))
                      (Z.to_nat (to_Z idx)) <> None)
      by (rewrite Hnth; discriminate).
    apply List.nth_error_Some in Hsome.
    pose proof (u32_nonneg idx).
    apply Nat2Z.inj_lt in Hsome. rewrite Z2Nat.id in Hsome by lia.
    exact Hsome. }
  rewrite (scalar_lt_geb_false _ _ Hlt) in H.
  rewrite (scalar_lt_geb_false i env.(env_Env_num_imported_globals))
    in H by lia.
  rewrite vec_index_spec in H. rewrite Hi in H. rewrite Hnth in H.
  cbn [bind] in H. rewrite mut_ne_spec in H. cbn [bind] in H.
  rewrite Hmut in H. cbn [types_Mut_t_beq negb] in H.
  injection H as <-. reflexivity.
Qed.

Lemma read_expr_end_complete : forall data pos r rest,
  module_read_expr_end data pos = Ok r ->
  repr_op (bytes_from data pos) FO_end rest ->
  exists p', r = Core_result_Result_Ok p' /\ bytes_from data p' = rest.
Proof.
  intros data pos r rest Hrun Hop.
  pose proof (repr_op_end_inv _ _ Hop) as Hbs.
  destruct (read_byte_complete _ _ _ _ Hbs) as [b [p [Eb [Hz Hp]]]].
  pose proof Hrun as Hw. unfold module_read_expr_end in Hw.
  rewrite Eb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
  cbn [bind] in Hw. tag_in Hw Hz. injection Hw as <-.
  exists p. split; [reflexivity | exact Hp].
Qed.

(** The five arms. Each is: the operator names its opcode, so the guard chain
    reaches its branch; the immediate reads because the derivation put it there;
    the type check passes because [const_expr_ok] says the declared type is the
    instruction's; and the terminating [end] is the second operator the
    expression's derivation carries. *)
Lemma decode_const_expr_complete :
  forall data pos env expected r e rest,
  module_decode_const_expr data pos env expected = Ok r ->
  repr_expr (bytes_from data pos) e rest ->
  const_ok env (translate_vt_v expected) e ->
  exists ce p',
    r = Core_result_Result_Ok (ce, p')
    /\ [translate_const_expr ce] = e
    /\ bytes_from data p' = rest.
Proof.
  intros data pos env expected r e rest Hrun Hexpr [ce0 [vt0 [-> [Hvt0 Hok]]]].
  apply translate_vt_v_inj in Hvt0. subst vt0.
  assert (Hshape : exists ce p', r = Core_result_Result_Ok (ce, p')).
  { pose proof Hrun as Hw. unfold module_decode_const_expr in Hw.
    destruct ce0 as [v | v | w | w | x];
      cbn [translate_const_expr] in Hexpr, Hok;
      destruct (repr_expr_single_inv _ _ _ Hexpr (ltac:(reflexivity)))
        as [mid [Hop1 Hop2]].
    - (* i32.const *)
      destruct (repr_op_const_inv _ _ _ Hop1) as [b [bs' [Hbs Hcs]]].
      destruct Hcs as [[-> [z [Hz Hval]]]
                      |[[_ [z [_ Hval]]]
                      |[[_ [u [_ Hval]]] | [_ [u [_ Hval]]]]]];
        [|discriminate Hval|discriminate Hval|discriminate Hval].
      destruct (read_byte_complete _ _ _ _ Hbs) as [op [p [Eb [Hzb Hp]]]].
      rewrite Eb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
      cbn [bind] in Hw. guard_true_in Hw Hzb.
      destruct (read_s32_leb_complete data p z mid
                  (ltac:(rewrite Hp; exact Hz))) as [v1 [p1 [Ev [_ Hp1]]]].
      rewrite Ev in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
      cbn [bind] in Hw.
      destruct (module_expect_const_type Types_ValueType_I32 expected)
        as [rt|] eqn:Et; cbn [bind] in Hw; [|discriminate].
      rewrite (expect_const_type_complete _ _ _ Et (ltac:(now rewrite Hok)))
        in Hw.
      rewrite branch_ok in Hw. cbn [bind] in Hw.
      destruct (module_read_expr_end data p1) as [re|] eqn:Ee;
        cbn [bind] in Hw; [|discriminate].
      destruct (read_expr_end_complete data p1 re rest Ee
                  (ltac:(rewrite Hp1; exact Hop2))) as [p2 [-> _]].
      rewrite branch_ok in Hw. cbn [bind] in Hw.
      injection Hw as <-. do 2 eexists. reflexivity.
    - (* i64.const *)
      destruct (repr_op_const_inv _ _ _ Hop1) as [b [bs' [Hbs Hcs]]].
      destruct Hcs as [[_ [z [_ Hval]]]
                      |[[-> [z [Hz Hval]]]
                      |[[_ [u [_ Hval]]] | [_ [u [_ Hval]]]]]];
        [discriminate Hval| |discriminate Hval|discriminate Hval].
      destruct (read_byte_complete _ _ _ _ Hbs) as [op [p [Eb [Hzb Hp]]]].
      rewrite Eb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
      cbn [bind] in Hw. guard_false_in Hw Hzb. guard_true_in Hw Hzb.
      destruct (read_s64_leb_complete data p z mid
                  (ltac:(rewrite Hp; exact Hz))) as [v1 [p1 [Ev [_ Hp1]]]].
      rewrite Ev in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
      cbn [bind] in Hw.
      destruct (module_expect_const_type Types_ValueType_I64 expected)
        as [rt|] eqn:Et; cbn [bind] in Hw; [|discriminate].
      rewrite (expect_const_type_complete _ _ _ Et (ltac:(now rewrite Hok)))
        in Hw.
      rewrite branch_ok in Hw. cbn [bind] in Hw.
      destruct (module_read_expr_end data p1) as [re|] eqn:Ee;
        cbn [bind] in Hw; [|discriminate].
      destruct (read_expr_end_complete data p1 re rest Ee
                  (ltac:(rewrite Hp1; exact Hop2))) as [p2 [-> _]].
      rewrite branch_ok in Hw. cbn [bind] in Hw.
      injection Hw as <-. do 2 eexists. reflexivity.
    - (* f32.const *)
      destruct (repr_op_const_inv _ _ _ Hop1) as [b [bs' [Hbs Hcs]]].
      destruct Hcs as [[_ [z [_ Hval]]]
                      |[[_ [z [_ Hval]]]
                      |[[-> [u [Hu Hval]]] | [_ [u [_ Hval]]]]]];
        [discriminate Hval|discriminate Hval| |discriminate Hval].
      destruct (read_byte_complete _ _ _ _ Hbs) as [op [p [Eb [Hzb Hp]]]].
      rewrite Eb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
      cbn [bind] in Hw.
      guard_false_in Hw Hzb. guard_false_in Hw Hzb. guard_true_in Hw Hzb.
      destruct (read_f32_bits_complete data p u mid
                  (ltac:(rewrite Hp; exact Hu))) as [v1 [p1 [Ev [_ Hp1]]]].
      rewrite Ev in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
      cbn [bind] in Hw.
      destruct (module_expect_const_type Types_ValueType_F32 expected)
        as [rt|] eqn:Et; cbn [bind] in Hw; [|discriminate].
      rewrite (expect_const_type_complete _ _ _ Et (ltac:(now rewrite Hok)))
        in Hw.
      rewrite branch_ok in Hw. cbn [bind] in Hw.
      destruct (module_read_expr_end data p1) as [re|] eqn:Ee;
        cbn [bind] in Hw; [|discriminate].
      destruct (read_expr_end_complete data p1 re rest Ee
                  (ltac:(rewrite Hp1; exact Hop2))) as [p2 [-> _]].
      rewrite branch_ok in Hw. cbn [bind] in Hw.
      injection Hw as <-. do 2 eexists. reflexivity.
    - (* f64.const *)
      destruct (repr_op_const_inv _ _ _ Hop1) as [b [bs' [Hbs Hcs]]].
      destruct Hcs as [[_ [z [_ Hval]]]
                      |[[_ [z [_ Hval]]]
                      |[[_ [u [_ Hval]]] | [-> [u [Hu Hval]]]]]];
        [discriminate Hval|discriminate Hval|discriminate Hval|].
      destruct (read_byte_complete _ _ _ _ Hbs) as [op [p [Eb [Hzb Hp]]]].
      rewrite Eb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
      cbn [bind] in Hw.
      guard_false_in Hw Hzb. guard_false_in Hw Hzb. guard_false_in Hw Hzb.
      guard_true_in Hw Hzb.
      destruct (read_f64_bits_complete data p u mid
                  (ltac:(rewrite Hp; exact Hu))) as [v1 [p1 [Ev [_ Hp1]]]].
      rewrite Ev in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
      cbn [bind] in Hw.
      destruct (module_expect_const_type Types_ValueType_F64 expected)
        as [rt|] eqn:Et; cbn [bind] in Hw; [|discriminate].
      rewrite (expect_const_type_complete _ _ _ Et (ltac:(now rewrite Hok)))
        in Hw.
      rewrite branch_ok in Hw. cbn [bind] in Hw.
      destruct (module_read_expr_end data p1) as [re|] eqn:Ee;
        cbn [bind] in Hw; [|discriminate].
      destruct (read_expr_end_complete data p1 re rest Ee
                  (ltac:(rewrite Hp1; exact Hop2))) as [p2 [-> _]].
      rewrite branch_ok in Hw. cbn [bind] in Hw.
      injection Hw as <-. do 2 eexists. reflexivity.
    - (* global.get: the one arm with a lookup in it *)
      destruct Hok as [gt [Hnth [Hmut [Hvt Himp]]]].
      destruct (repr_op_global_get_inv _ _ _ Hop1) as [bs' [z [Hbs [Hz Hxz]]]].
      destruct (read_byte_complete _ _ _ _ Hbs) as [op [p [Eb [Hzb Hp]]]].
      rewrite Eb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
      cbn [bind] in Hw.
      guard_false_in Hw Hzb. guard_false_in Hw Hzb. guard_false_in Hw Hzb.
      guard_false_in Hw Hzb. guard_true_in Hw Hzb.
      destruct (read_u32_leb_complete data p z mid
                  (ltac:(rewrite Hp; exact Hz))) as [idx [p1 [Ev [Hidx Hp1]]]].
      rewrite Ev in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
      cbn [bind] in Hw.
      (* the index the derivation names is the one the environment has. The
         derivation carries it as an [N] and the environment as a [u32], so the
         two cross through [Z.to_N]'s injectivity on non-negatives. *)
      assert (Hxeq : to_Z x = z).
      { apply (f_equal Z.of_N) in Hxz.
        rewrite Z2N.id in Hxz by apply u32_nonneg.
        rewrite Z2N.id in Hxz by exact (repr_u32_nonneg _ _ _ Hz).
        exact Hxz. }
      assert (Hnth' : List.nth_error (vec_list env.(env_Env_global_types))
                        (Z.to_nat (to_Z idx)) = Some gt)
        by (rewrite Hidx; rewrite <- Hxeq; exact Hnth).
      assert (Himp' : to_Z idx < to_Z env.(env_Env_num_imported_globals))
        by (rewrite Hidx; rewrite <- Hxeq; exact Himp).
      destruct (module_const_global env idx) as [rg|] eqn:Eg;
        cbn [bind] in Hw; [|discriminate].
      rewrite (const_global_complete env idx rg gt Eg Hnth' Hmut Himp') in Hw.
      rewrite branch_ok in Hw. cbn [bind] in Hw.
      destruct (module_expect_const_type gt.(types_GlobalType_valtype) expected)
        as [rt|] eqn:Et; cbn [bind] in Hw; [|discriminate].
      rewrite (expect_const_type_complete _ _ _ Et Hvt) in Hw.
      rewrite branch_ok in Hw. cbn [bind] in Hw.
      destruct (module_read_expr_end data p1) as [re|] eqn:Ee;
        cbn [bind] in Hw; [|discriminate].
      destruct (read_expr_end_complete data p1 re rest Ee
                  (ltac:(rewrite Hp1; exact Hop2))) as [p2 [-> _]].
      rewrite branch_ok in Hw. cbn [bind] in Hw.
      injection Hw as <-. do 2 eexists. reflexivity. }
  destruct Hshape as [ce [p' ->]]. exists ce, p'. split; [reflexivity|].
  ident expr_det (decode_const_expr_sound _ _ _ _ _ _ Hrun) Hexpr.
Qed.

(* ================================================================== *)
(** ** Which section the dispatch runs                                 *)
(* ================================================================== *)

(** The soundness direction has [Module_Sound.env_section_is_type] and friends,
    which read an accepting run of the dispatch as a run of one section.
    Completeness needs the equation for an arbitrary result, so that the section
    lemma applies to whatever the dispatch returned. Nine lines, one tactic. *)
Ltac sec_dispatch Hid :=
  unfold module_decode_env_section;
  repeat match goal with
         | [ |- context [ if (?i s= ?c) then _ else _ ] ] =>
             first [ rewrite (scalar_eqb_of_eq i c)
                       by (rewrite Hid; reflexivity)
                   | rewrite (scalar_eqb_of_ne i c)
                       by (rewrite Hid; cbn; lia) ]
         end; reflexivity.

Lemma env_section_eq_type : forall data pos (id : u8) env,
  to_Z id = 1 ->
  module_decode_env_section data pos id env
    = module_decode_type_section data pos env.
Proof. intros data pos id env Hid. sec_dispatch Hid. Qed.

Lemma env_section_eq_import : forall data pos (id : u8) env,
  to_Z id = 2 ->
  module_decode_env_section data pos id env
    = module_decode_import_section data pos env.
Proof. intros data pos id env Hid. sec_dispatch Hid. Qed.

Lemma env_section_eq_function : forall data pos (id : u8) env,
  to_Z id = 3 ->
  module_decode_env_section data pos id env
    = module_decode_function_section data pos env.
Proof. intros data pos id env Hid. sec_dispatch Hid. Qed.

Lemma env_section_eq_table : forall data pos (id : u8) env,
  to_Z id = 4 ->
  module_decode_env_section data pos id env
    = module_decode_table_section data pos env.
Proof. intros data pos id env Hid. sec_dispatch Hid. Qed.

Lemma env_section_eq_memory : forall data pos (id : u8) env,
  to_Z id = 5 ->
  module_decode_env_section data pos id env
    = module_decode_memory_section data pos env.
Proof. intros data pos id env Hid. sec_dispatch Hid. Qed.

Lemma env_section_eq_global : forall data pos (id : u8) env,
  to_Z id = 6 ->
  module_decode_env_section data pos id env
    = module_decode_global_section data pos env.
Proof. intros data pos id env Hid. sec_dispatch Hid. Qed.

Lemma env_section_eq_export : forall data pos (id : u8) env,
  to_Z id = 7 ->
  module_decode_env_section data pos id env
    = module_decode_export_section data pos env.
Proof. intros data pos id env Hid. sec_dispatch Hid. Qed.

Lemma env_section_eq_start : forall data pos (id : u8) env,
  to_Z id = 8 ->
  module_decode_env_section data pos id env
    = module_decode_start_section data pos env.
Proof. intros data pos id env Hid. sec_dispatch Hid. Qed.

Lemma env_section_eq_element : forall data pos (id : u8) env,
  to_Z id = 9 ->
  module_decode_env_section data pos id env
    = module_decode_element_section data pos env.
Proof. intros data pos id env Hid. sec_dispatch Hid. Qed.

(* ================================================================== *)
(** ** 5.5.4 The type section                                          *)
(* ================================================================== *)

(** The first of the nine, and the shape all of them share: an induction on the
    count with the specification's [repr_rep] index marching down beside it, the
    element decoder's completeness lemma for the body, and the validity
    hypotheses split by [Forall] as the loop consumes them.

    The conclusion is deliberately thin -- the position, and where the stream got
    to. What the section put in the environment is not restated here, because the
    soundness lemma for the same run already says it, and the chain wants it in
    exactly the form soundness produces. *)
Lemma decode_type_section_loop_complete :
  forall k data env count q i r env2 vs rest,
  Z.to_nat (to_Z count - to_Z i) = k ->
  module_decode_type_section_loop data env count q i = Ok (r, env2) ->
  repr_rep repr_functype k (bytes_from data q) vs rest ->
  List.Forall functype_wasm10 vs ->
  exists q', r = Core_result_Result_Ok q' /\ bytes_from data q' = rest.
Proof.
  induction k as [|k IH];
    intros data env count q i r env2 vs rest Hk Hw Hrep Hall;
    unfold module_decode_type_section_loop in Hw; rewrite loop_unfold in Hw;
    cbn beta iota in Hw; destruct (i s>= count) eqn:Hge.
  - injection Hw as <- <-.
    destruct (repr_rep_O_inv _ _ _ _ _ Hrep) as [-> ->].
    exists q. split; reflexivity.
  - exfalso. apply scalar_geb_false_lt in Hge.
    pose proof (count_zero _ _ Hk). lia.
  - exfalso. apply scalar_geb_true_ge in Hge.
    pose proof (count_succ _ _ _ Hk) as Hcnt.
    rewrite Nat2Z.inj_succ in Hcnt. pose proof (Nat2Z.is_nonneg k). lia.
  - pose proof (count_succ _ _ _ Hk) as Hcnt.
    destruct (repr_rep_S_inv _ _ _ _ _ _ Hrep)
      as [ft [mid [vts [-> [Hft Hrest]]]]].
    apply List.Forall_cons_iff in Hall as [Hft10 Hall].
    destruct (module_decode_func_type data q) as [r1|] eqn:E1;
      cbn [bind] in Hw; [|discriminate].
    destruct (decode_func_type_complete _ _ _ _ _ E1 Hft Hft10)
      as [ft' [q1 [-> [_ Hq1]]]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    destruct (alloc_vec_Vec_push env.(env_Env_types) ft') as [v|] eqn:Hpush;
      cbn [bind] in Hw; [|discriminate].
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in Hw;
      [|discriminate].
    assert (Hi2 : to_Z i2 = to_Z i + 1).
    { unfold u32_add, scalar_add in Hadd. apply mk_scalar_ok_to_Z in Hadd.
      assert (H1 : to_Z 1%u32 = 1) by reflexivity. lia. }
    exact (IH data _ count q1 i2 r env2 vts rest
             (ltac:(rewrite Hi2; f_equal; lia)) Hw
             (ltac:(rewrite Hq1; exact Hrest)) Hall).
Qed.

(** The wrapper every section shares: read the entry count, then run the loop
    from the position after it. *)
Lemma decode_type_section_complete : forall data pos env r env2 vs rest,
  module_decode_type_section data pos env = Ok (r, env2) ->
  repr_vec repr_functype (bytes_from data pos) vs rest ->
  List.Forall functype_wasm10 vs ->
  exists q', r = Core_result_Result_Ok q' /\ bytes_from data q' = rest.
Proof.
  intros data pos env r env2 vs rest Hrun H Hall.
  destruct (repr_vec_inv _ _ _ _ _ H) as [n [mid [Hn Hrep]]].
  destruct (read_u32_leb_complete _ _ _ _ Hn) as [count [p [Hleb [Hval Hp]]]].
  pose proof Hrun as Hw. unfold module_decode_type_section in Hw.
  rewrite Hleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
  cbn [bind] in Hw.
  assert (H0 : to_Z 0%u32 = 0) by reflexivity.
  exact (decode_type_section_loop_complete (Z.to_nat n) data env count p 0%u32
           r env2 vs rest (ltac:(rewrite H0; rewrite Hval; f_equal; lia)) Hw
           (ltac:(rewrite Hp; exact Hrep)) Hall).
Qed.

(* ================================================================== *)
(** ** 5.5.6 The function section                                      *)
(* ================================================================== *)

(** The type index has to resolve, which is the section's one check. Nothing in
    the section writes [types], so the range condition is stated against the
    environment the loop was handed and travels unchanged: the record the loop
    rebuilds has [env_Env_types] copied across, so the projection reduces. *)
Lemma lookup_type_complete : forall env (idx : scalar U32) r,
  module_lookup_type env idx = Ok r ->
  (Z.to_nat (to_Z idx) < List.length (vec_list env.(env_Env_types)))%nat ->
  exists ft, r = Core_result_Result_Ok ft.
Proof.
  intros env idx r Hrun Hlt. unfold module_lookup_type in Hrun.
  destruct (scalar_cast U32 Usize idx) as [i|] eqn:Hcast; cbn [bind] in Hrun;
    [|discriminate].
  assert (Hi : to_Z i = to_Z idx)
    by (unfold scalar_cast in Hcast; apply mk_scalar_ok_to_Z in Hcast;
        exact Hcast).
  assert (Hge : (i s>= alloc_vec_Vec_len env.(env_Env_types)) = false).
  { apply scalar_lt_geb_false. rewrite vec_len_spec. rewrite Hi.
    pose proof (u32_nonneg idx).
    apply Nat2Z.inj_lt in Hlt. rewrite Z2Nat.id in Hlt by lia. exact Hlt. }
  rewrite Hge in Hrun.
  destruct (vec_index_ok env.(env_Env_types) i Hge) as [ft Hidx].
  rewrite Hidx in Hrun. cbn [bind] in Hrun.
  destruct (copy_func_type_ok ft) as [ft' [Hcopy _]].
  rewrite Hcopy in Hrun. cbn [bind] in Hrun.
  injection Hrun as <-. eexists. reflexivity.
Qed.

Definition typeidx_in_range (env : env_Env_t) (x : N) : Prop :=
  (N.to_nat x < List.length (vec_list env.(env_Env_types)))%nat.

Lemma decode_function_section_loop_complete :
  forall k data env count q i r env2 vs rest,
  Z.to_nat (to_Z count - to_Z i) = k ->
  module_decode_function_section_loop data env count q i = Ok (r, env2) ->
  repr_rep repr_idx k (bytes_from data q) vs rest ->
  List.Forall (typeidx_in_range env) vs ->
  exists q', r = Core_result_Result_Ok q' /\ bytes_from data q' = rest.
Proof.
  induction k as [|k IH];
    intros data env count q i r env2 vs rest Hk Hw Hrep Hall;
    unfold module_decode_function_section_loop in Hw; rewrite loop_unfold in Hw;
    cbn beta iota in Hw; destruct (i s>= count) eqn:Hge.
  - injection Hw as <- <-.
    destruct (repr_rep_O_inv _ _ _ _ _ Hrep) as [-> ->].
    exists q. split; reflexivity.
  - exfalso. apply scalar_geb_false_lt in Hge.
    pose proof (count_zero _ _ Hk). lia.
  - exfalso. apply scalar_geb_true_ge in Hge.
    pose proof (count_succ _ _ _ Hk) as Hcnt.
    rewrite Nat2Z.inj_succ in Hcnt. pose proof (Nat2Z.is_nonneg k). lia.
  - pose proof (count_succ _ _ _ Hk) as Hcnt.
    destruct (repr_rep_S_inv _ _ _ _ _ _ Hrep)
      as [x [mid [vts [-> [Hx Hrest]]]]].
    apply List.Forall_cons_iff in Hall as [Hxr Hall].
    destruct (read_idx_complete _ _ _ _ Hx) as [idx [q1 [Eleb [Hidx Hq1]]]].
    rewrite Eleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
    cbn [bind] in Hw.
    destruct (module_lookup_type env idx) as [r1|] eqn:E1; cbn [bind] in Hw;
      [|discriminate].
    destruct (lookup_type_complete env idx r1 E1
                (ltac:(unfold typeidx_in_range, translate_idx in *;
                       rewrite <- Hidx in Hxr; rewrite N_to_nat_Z_to_N in Hxr;
                       exact Hxr))) as [ft ->].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    destruct (alloc_vec_Vec_push env.(env_Env_func_types) ft) as [v|] eqn:Hp1;
      cbn [bind] in Hw; [|discriminate].
    destruct (alloc_vec_Vec_push env.(env_Env_func_type_indices) idx)
      as [v1|] eqn:Hp2; cbn [bind] in Hw; [|discriminate].
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in Hw;
      [|discriminate].
    assert (Hi2 : to_Z i2 = to_Z i + 1).
    { unfold u32_add, scalar_add in Hadd. apply mk_scalar_ok_to_Z in Hadd.
      assert (H1 : to_Z 1%u32 = 1) by reflexivity. lia. }
    exact (IH data _ count q1 i2 r env2 vts rest
             (ltac:(rewrite Hi2; f_equal; lia)) Hw
             (ltac:(rewrite Hq1; exact Hrest)) Hall).
Qed.

Lemma decode_function_section_complete : forall data pos env r env2 vs rest,
  module_decode_function_section data pos env = Ok (r, env2) ->
  repr_vec repr_idx (bytes_from data pos) vs rest ->
  List.Forall (typeidx_in_range env) vs ->
  exists q', r = Core_result_Result_Ok q' /\ bytes_from data q' = rest.
Proof.
  intros data pos env r env2 vs rest Hrun H Hall.
  destruct (repr_vec_inv _ _ _ _ _ H) as [n [mid [Hn Hrep]]].
  destruct (read_u32_leb_complete _ _ _ _ Hn) as [count [p [Hleb [Hval Hp]]]].
  pose proof Hrun as Hw. unfold module_decode_function_section in Hw.
  rewrite Hleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
  cbn [bind] in Hw.
  assert (H0 : to_Z 0%u32 = 0) by reflexivity.
  exact (decode_function_section_loop_complete (Z.to_nat n) data env count p
           0%u32 r env2 vs rest (ltac:(rewrite H0; rewrite Hval; f_equal; lia))
           Hw (ltac:(rewrite Hp; exact Hrep)) Hall).
Qed.

(* ================================================================== *)
(** ** 5.5.7 and 5.5.8 The table and memory sections                   *)
(* ================================================================== *)

(** Wasm 1.0 allows one table and one memory, and the check is made after each
    push, so the room left is what the loop carries: what is already in the index
    space plus what is still to come has to fit. Both sections are the same
    argument at a different field. *)
Lemma decode_table_section_loop_complete :
  forall k data env count q i r env2 vs rest,
  Z.to_nat (to_Z count - to_Z i) = k ->
  module_decode_table_section_loop data env count q i = Ok (r, env2) ->
  repr_rep repr_table k (bytes_from data q) vs rest ->
  List.Forall (fun t => tabletype_valid t.(modtab_type) = true) vs ->
  Z.of_nat (List.length (vec_list env.(env_Env_table_types)))
    + Z.of_nat k <= 1 ->
  exists q', r = Core_result_Result_Ok q' /\ bytes_from data q' = rest.
Proof.
  induction k as [|k IH];
    intros data env count q i r env2 vs rest Hk Hw Hrep Hall Hroom;
    unfold module_decode_table_section_loop in Hw; rewrite loop_unfold in Hw;
    cbn beta iota in Hw; destruct (i s>= count) eqn:Hge.
  - injection Hw as <- <-.
    destruct (repr_rep_O_inv _ _ _ _ _ Hrep) as [-> ->].
    exists q. split; reflexivity.
  - exfalso. apply scalar_geb_false_lt in Hge.
    pose proof (count_zero _ _ Hk). lia.
  - exfalso. apply scalar_geb_true_ge in Hge.
    pose proof (count_succ _ _ _ Hk) as Hcnt.
    rewrite Nat2Z.inj_succ in Hcnt. pose proof (Nat2Z.is_nonneg k). lia.
  - pose proof (count_succ _ _ _ Hk) as Hcnt.
    destruct (repr_rep_S_inv _ _ _ _ _ _ Hrep)
      as [t [mid [vts [-> [Ht Hrest]]]]].
    apply List.Forall_cons_iff in Hall as [Httv Hall].
    destruct (repr_table_inv _ _ _ Ht) as [tt [Htt ->]].
    cbn [modtab_type] in Httv.
    destruct (module_decode_table_type data q) as [r1|] eqn:E1;
      cbn [bind] in Hw; [|discriminate].
    destruct (decode_table_type_complete _ _ _ _ _ E1 Htt Httv)
      as [tt' [q1 [-> [_ Hq1]]]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    destruct (alloc_vec_Vec_push env.(env_Env_table_types) tt') as [v|] eqn:Hp1;
      cbn [bind] in Hw; [|discriminate].
    assert (Hlen : Z.of_nat (List.length (vec_list v))
                   = Z.of_nat (List.length (vec_list env.(env_Env_table_types)))
                     + 1)
      by (rewrite (vec_push_spec _ _ _ Hp1); rewrite List.app_length;
          cbn [List.length]; lia).
    rewrite (scalar_gtb_of_le (alloc_vec_Vec_len v) limits_max_tables) in Hw.
    2: { assert (Hm : to_Z limits_max_tables = 1) by reflexivity.
         rewrite vec_len_spec. rewrite Nat2Z.inj_succ in Hroom.
         pose proof (Nat2Z.is_nonneg k). lia. }
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in Hw;
      [|discriminate].
    assert (Hi2 : to_Z i2 = to_Z i + 1).
    { unfold u32_add, scalar_add in Hadd. apply mk_scalar_ok_to_Z in Hadd.
      assert (H1 : to_Z 1%u32 = 1) by reflexivity. lia. }
    apply (IH data _ count q1 i2 r env2 vts rest
             (ltac:(rewrite Hi2; f_equal; lia)) Hw
             (ltac:(rewrite Hq1; exact Hrest)) Hall).
    cbn [env_Env_table_types]. rewrite Nat2Z.inj_succ in Hroom. lia.
Qed.

Lemma decode_table_section_complete : forall data pos env r env2 vs rest,
  module_decode_table_section data pos env = Ok (r, env2) ->
  repr_vec repr_table (bytes_from data pos) vs rest ->
  List.Forall (fun t => tabletype_valid t.(modtab_type) = true) vs ->
  Z.of_nat (List.length (vec_list env.(env_Env_table_types)))
    + Z.of_nat (List.length vs) <= 1 ->
  exists q', r = Core_result_Result_Ok q' /\ bytes_from data q' = rest.
Proof.
  intros data pos env r env2 vs rest Hrun H Hall Hroom.
  destruct (repr_vec_inv _ _ _ _ _ H) as [n [mid [Hn Hrep]]].
  destruct (read_u32_leb_complete _ _ _ _ Hn) as [count [p [Hleb [Hval Hp]]]].
  pose proof Hrun as Hw. unfold module_decode_table_section in Hw.
  rewrite Hleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
  cbn [bind] in Hw.
  assert (H0 : to_Z 0%u32 = 0) by reflexivity.
  (* the count and the list's length agree, which is what carries the room *)
  pose proof (repr_rep_length _ _ _ _ _ _ Hrep) as Hn2.
  apply (decode_table_section_loop_complete (Z.to_nat n) data env count p 0%u32
           r env2 vs rest (ltac:(rewrite H0; rewrite Hval; f_equal; lia)) Hw
           (ltac:(rewrite Hp; exact Hrep)) Hall).
  rewrite <- Hn2. exact Hroom.
Qed.

Lemma decode_memory_section_loop_complete :
  forall k data env count q i r env2 vs rest,
  Z.to_nat (to_Z count - to_Z i) = k ->
  module_decode_memory_section_loop data env count q i = Ok (r, env2) ->
  repr_rep repr_mem k (bytes_from data q) vs rest ->
  List.Forall (fun m => memtype_valid m.(modmem_type) = true) vs ->
  Z.of_nat (List.length (vec_list env.(env_Env_mem_types)))
    + Z.of_nat k <= 1 ->
  exists q', r = Core_result_Result_Ok q' /\ bytes_from data q' = rest.
Proof.
  induction k as [|k IH];
    intros data env count q i r env2 vs rest Hk Hw Hrep Hall Hroom;
    unfold module_decode_memory_section_loop in Hw; rewrite loop_unfold in Hw;
    cbn beta iota in Hw; destruct (i s>= count) eqn:Hge.
  - injection Hw as <- <-.
    destruct (repr_rep_O_inv _ _ _ _ _ Hrep) as [-> ->].
    exists q. split; reflexivity.
  - exfalso. apply scalar_geb_false_lt in Hge.
    pose proof (count_zero _ _ Hk). lia.
  - exfalso. apply scalar_geb_true_ge in Hge.
    pose proof (count_succ _ _ _ Hk) as Hcnt.
    rewrite Nat2Z.inj_succ in Hcnt. pose proof (Nat2Z.is_nonneg k). lia.
  - pose proof (count_succ _ _ _ Hk) as Hcnt.
    destruct (repr_rep_S_inv _ _ _ _ _ _ Hrep)
      as [m0 [mid [vts [-> [Hm0 Hrest]]]]].
    apply List.Forall_cons_iff in Hall as [Hmtv Hall].
    destruct (repr_mem_inv _ _ _ Hm0) as [mt [Hmt ->]].
    cbn [modmem_type] in Hmtv.
    destruct (module_decode_mem_type data q) as [r1|] eqn:E1;
      cbn [bind] in Hw; [|discriminate].
    destruct (decode_mem_type_complete _ _ _ _ _ E1 Hmt Hmtv)
      as [mt' [q1 [-> [_ Hq1]]]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    destruct (alloc_vec_Vec_push env.(env_Env_mem_types) mt') as [v|] eqn:Hp1;
      cbn [bind] in Hw; [|discriminate].
    assert (Hlen : Z.of_nat (List.length (vec_list v))
                   = Z.of_nat (List.length (vec_list env.(env_Env_mem_types)))
                     + 1)
      by (rewrite (vec_push_spec _ _ _ Hp1); rewrite List.app_length;
          cbn [List.length]; lia).
    rewrite (scalar_gtb_of_le (alloc_vec_Vec_len v) limits_max_memories) in Hw.
    2: { assert (Hm : to_Z limits_max_memories = 1) by reflexivity.
         rewrite vec_len_spec. rewrite Nat2Z.inj_succ in Hroom.
         pose proof (Nat2Z.is_nonneg k). lia. }
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in Hw;
      [|discriminate].
    assert (Hi2 : to_Z i2 = to_Z i + 1).
    { unfold u32_add, scalar_add in Hadd. apply mk_scalar_ok_to_Z in Hadd.
      assert (H1 : to_Z 1%u32 = 1) by reflexivity. lia. }
    apply (IH data _ count q1 i2 r env2 vts rest
             (ltac:(rewrite Hi2; f_equal; lia)) Hw
             (ltac:(rewrite Hq1; exact Hrest)) Hall).
    cbn [env_Env_mem_types]. rewrite Nat2Z.inj_succ in Hroom. lia.
Qed.

Lemma decode_memory_section_complete : forall data pos env r env2 vs rest,
  module_decode_memory_section data pos env = Ok (r, env2) ->
  repr_vec repr_mem (bytes_from data pos) vs rest ->
  List.Forall (fun m => memtype_valid m.(modmem_type) = true) vs ->
  Z.of_nat (List.length (vec_list env.(env_Env_mem_types)))
    + Z.of_nat (List.length vs) <= 1 ->
  exists q', r = Core_result_Result_Ok q' /\ bytes_from data q' = rest.
Proof.
  intros data pos env r env2 vs rest Hrun H Hall Hroom.
  destruct (repr_vec_inv _ _ _ _ _ H) as [n [mid [Hn Hrep]]].
  destruct (read_u32_leb_complete _ _ _ _ Hn) as [count [p [Hleb [Hval Hp]]]].
  pose proof Hrun as Hw. unfold module_decode_memory_section in Hw.
  rewrite Hleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
  cbn [bind] in Hw.
  assert (H0 : to_Z 0%u32 = 0) by reflexivity.
  pose proof (repr_rep_length _ _ _ _ _ _ Hrep) as Hn2.
  apply (decode_memory_section_loop_complete (Z.to_nat n) data env count p
           0%u32 r env2 vs rest (ltac:(rewrite H0; rewrite Hval; f_equal; lia))
           Hw (ltac:(rewrite Hp; exact Hrep)) Hall).
  rewrite <- Hn2. exact Hroom.
Qed.

(* ================================================================== *)
(** ** 5.5.9 The global section                                        *)
(* ================================================================== *)

(** The only section whose check reads the environment it is building, and the
    reason it still works is that what an initialiser may name is an *imported*
    global: the loop grows [global_types] but not [num_imported_globals], so
    [const_expr_ok] survives the growth, which is what
    [Module_Sound.const_expr_ok_grow] says. The hypothesis is therefore stated
    against the environment the loop was handed. *)
Lemma const_ok_grow : forall env env' t e more,
  vec_list env'.(env_Env_global_types)
    = vec_list env.(env_Env_global_types) ++ more ->
  to_Z env'.(env_Env_num_imported_globals)
    = to_Z env.(env_Env_num_imported_globals) ->
  const_ok env t e -> const_ok env' t e.
Proof.
  intros env env' t e more Hg Hn [ce [vt [He [Hvt Hok]]]].
  exists ce, vt. split; [exact He|]. split; [exact Hvt|].
  exact (const_expr_ok_grow env env' _ _ more Hg Hn Hok).
Qed.

Lemma decode_global_section_loop_complete :
  forall k data env count q i r env2 vs rest,
  Z.to_nat (to_Z count - to_Z i) = k ->
  module_decode_global_section_loop data env count q i = Ok (r, env2) ->
  repr_rep repr_global k (bytes_from data q) vs rest ->
  List.Forall (fun g => const_ok env (tg_t g.(modglob_type))
                          g.(modglob_init)) vs ->
  exists q', r = Core_result_Result_Ok q' /\ bytes_from data q' = rest.
Proof.
  induction k as [|k IH];
    intros data env count q i r env2 vs rest Hk Hw Hrep Hall;
    unfold module_decode_global_section_loop in Hw; rewrite loop_unfold in Hw;
    cbn beta iota in Hw; destruct (i s>= count) eqn:Hge.
  - injection Hw as <- <-.
    destruct (repr_rep_O_inv _ _ _ _ _ Hrep) as [-> ->].
    exists q. split; reflexivity.
  - exfalso. apply scalar_geb_false_lt in Hge.
    pose proof (count_zero _ _ Hk). lia.
  - exfalso. apply scalar_geb_true_ge in Hge.
    pose proof (count_succ _ _ _ Hk) as Hcnt.
    rewrite Nat2Z.inj_succ in Hcnt. pose proof (Nat2Z.is_nonneg k). lia.
  - pose proof (count_succ _ _ _ Hk) as Hcnt.
    destruct (repr_rep_S_inv _ _ _ _ _ _ Hrep)
      as [g [mid [vts [-> [Hg Hrest]]]]].
    apply List.Forall_cons_iff in Hall as [Hgok Hall].
    destruct (repr_global_inv _ _ _ Hg) as [gt0 [p1 [e0 [Hgt0 [He0 ->]]]]].
    cbn [modglob_type modglob_init] in Hgok.
    destruct (module_decode_global_type data q) as [r1|] eqn:E1;
      cbn [bind] in Hw; [|discriminate].
    destruct (decode_global_type_complete _ _ _ _ _ E1 Hgt0)
      as [gt [q1 [-> [Hgt Hq1]]]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    destruct (module_decode_const_expr data q1 env
                gt.(types_GlobalType_valtype)) as [r2|] eqn:E2;
      cbn [bind] in Hw; [|discriminate].
    destruct (decode_const_expr_complete _ _ _ _ _ _ _ E2
                (ltac:(rewrite Hq1; exact He0))
                (ltac:(rewrite <- Hgt in Hgok;
                       unfold translate_globaltype in Hgok;
                       cbn [tg_t] in Hgok; exact Hgok)))
      as [init [q2 [-> [_ Hq2]]]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    destruct (alloc_vec_Vec_push env.(env_Env_global_types) gt) as [v|] eqn:Hp1;
      cbn [bind] in Hw; [|discriminate].
    destruct (alloc_vec_Vec_push env.(env_Env_globals)
                {| env_Global_gtype := gt; env_Global_init := init |})
      as [v1|] eqn:Hp2; cbn [bind] in Hw; [|discriminate].
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in Hw;
      [|discriminate].
    assert (Hi2 : to_Z i2 = to_Z i + 1).
    { unfold u32_add, scalar_add in Hadd. apply mk_scalar_ok_to_Z in Hadd.
      assert (H1 : to_Z 1%u32 = 1) by reflexivity. lia. }
    apply (IH data _ count q2 i2 r env2 vts rest
             (ltac:(rewrite Hi2; f_equal; lia)) Hw
             (ltac:(rewrite Hq2; exact Hrest))).
    (* the remaining initialisers' condition survives the push *)
    eapply List.Forall_impl; [|exact Hall].
    intros g0 Hg0.
    eapply (const_ok_grow env _ _ _ [gt]); [|reflexivity|exact Hg0].
    cbn [env_Env_global_types]. apply (vec_push_spec _ _ _ Hp1).
Qed.

Lemma decode_global_section_complete : forall data pos env r env2 vs rest,
  module_decode_global_section data pos env = Ok (r, env2) ->
  repr_vec repr_global (bytes_from data pos) vs rest ->
  List.Forall (fun g => const_ok env (tg_t g.(modglob_type))
                          g.(modglob_init)) vs ->
  exists q', r = Core_result_Result_Ok q' /\ bytes_from data q' = rest.
Proof.
  intros data pos env r env2 vs rest Hrun H Hall.
  destruct (repr_vec_inv _ _ _ _ _ H) as [n [mid [Hn Hrep]]].
  destruct (read_u32_leb_complete _ _ _ _ Hn) as [count [p [Hleb [Hval Hp]]]].
  pose proof Hrun as Hw. unfold module_decode_global_section in Hw.
  rewrite Hleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
  cbn [bind] in Hw.
  assert (H0 : to_Z 0%u32 = 0) by reflexivity.
  exact (decode_global_section_loop_complete (Z.to_nat n) data env count p
           0%u32 r env2 vs rest (ltac:(rewrite H0; rewrite Hval; f_equal; lia))
           Hw (ltac:(rewrite Hp; exact Hrep)) Hall).
Qed.

(* ================================================================== *)
(** ** 5.5.11 The start section                                        *)
(* ================================================================== *)

(** One index, and spec 3.4.13's condition on the function it names. Not a loop,
    so the whole section is one walk. *)
Definition start_wasm10 (env : env_Env_t) (s : module_start) : Prop :=
  exists ft,
    List.nth_error (vec_list env.(env_Env_func_types))
                   (N.to_nat s.(modstart_func)) = Some ft
    /\ vec_list ft.(types_FuncType_params) = []
    /\ vec_list ft.(types_FuncType_results) = [].

Lemma decode_start_section_complete : forall data pos env r env2 st rest,
  module_decode_start_section data pos env = Ok (r, env2) ->
  repr_start (bytes_from data pos) st rest ->
  (forall s, st = Some s -> start_wasm10 env s) ->
  exists q', r = Core_result_Result_Ok q' /\ bytes_from data q' = rest.
Proof.
  intros data pos env r env2 st rest Hrun [x [Hx ->]] Hst.
  destruct (Hst _ (ltac:(reflexivity))) as [ft [Hnth [Hpar Hres]]].
  cbn [modstart_func] in Hnth.
  destruct (read_idx_complete _ _ _ _ Hx) as [idx [p [Hleb [Hidx Hp]]]].
  pose proof Hrun as Hw. unfold module_decode_start_section in Hw.
  rewrite Hleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
  cbn [bind] in Hw.
  destruct (scalar_cast U32 Usize idx) as [i|] eqn:Hcast; cbn [bind] in Hw;
    [|discriminate].
  assert (Hi : to_Z i = to_Z idx)
    by (unfold scalar_cast in Hcast; apply mk_scalar_ok_to_Z in Hcast;
        exact Hcast).
  (* the lookup found a function there, so the index is in range *)
  assert (Hnth' : List.nth_error (vec_list env.(env_Env_func_types))
                    (Z.to_nat (to_Z i)) = Some ft).
  { rewrite Hi. unfold translate_idx in Hidx. rewrite <- Hidx in Hnth.
    rewrite N_to_nat_Z_to_N in Hnth. exact Hnth. }
  assert (Hge : (i s>= alloc_vec_Vec_len env.(env_Env_func_types)) = false).
  { apply scalar_lt_geb_false. rewrite vec_len_spec.
    assert (Hsome : List.nth_error (vec_list env.(env_Env_func_types))
                      (Z.to_nat (to_Z i)) <> None)
      by (rewrite Hnth'; discriminate).
    apply List.nth_error_Some in Hsome.
    pose proof (usize_nonneg i).
    apply Nat2Z.inj_lt in Hsome. rewrite Z2Nat.id in Hsome by lia.
    exact Hsome. }
  rewrite Hge in Hw.
  rewrite vec_index_spec in Hw. rewrite Hnth' in Hw. cbn [bind] in Hw.
  rewrite vec_is_empty_spec in Hw. cbn [bind] in Hw. rewrite Hpar in Hw.
  cbn beta iota in Hw.
  rewrite vec_is_empty_spec in Hw. cbn [bind] in Hw. rewrite Hres in Hw.
  cbn beta iota in Hw.
  injection Hw as <- <-. exists p. split; [reflexivity | exact Hp].
Qed.

(* ================================================================== *)
(** ** 5.5.12 The element section                                      *)
(* ================================================================== *)

(** The function-index vector, which is the one place a Wasm 1.0 element segment
    differs in shape from the 2.0 value it denotes: the specification's vector of
    indices becomes one [ref.func] expression each, so the derivation in hand is
    over the indices and the module's field is the [map]. *)
Definition funcidx_in_range (env : env_Env_t) (x : N) : Prop :=
  (N.to_nat x < List.length (vec_list env.(env_Env_func_types)))%nat.

Lemma decode_func_indices_loop_complete :
  forall k data env count out q i r vs rest,
  Z.to_nat (to_Z count - to_Z i) = k ->
  module_decode_func_indices_loop data env count out q i = Ok r ->
  repr_rep repr_idx k (bytes_from data q) vs rest ->
  List.Forall (funcidx_in_range env) vs ->
  exists out' q', r = Core_result_Result_Ok (out', q')
                  /\ bytes_from data q' = rest.
Proof.
  induction k as [|k IH];
    intros data env count out q i r vs rest Hk Hw Hrep Hall;
    unfold module_decode_func_indices_loop in Hw; rewrite loop_unfold in Hw;
    cbn beta iota in Hw; destruct (i s>= count) eqn:Hge.
  - injection Hw as <-.
    destruct (repr_rep_O_inv _ _ _ _ _ Hrep) as [-> ->].
    exists out, q. split; reflexivity.
  - exfalso. apply scalar_geb_false_lt in Hge.
    pose proof (count_zero _ _ Hk). lia.
  - exfalso. apply scalar_geb_true_ge in Hge.
    pose proof (count_succ _ _ _ Hk) as Hcnt.
    rewrite Nat2Z.inj_succ in Hcnt. pose proof (Nat2Z.is_nonneg k). lia.
  - pose proof (count_succ _ _ _ Hk) as Hcnt.
    destruct (repr_rep_S_inv _ _ _ _ _ _ Hrep)
      as [x [mid [vts [-> [Hx Hrest]]]]].
    apply List.Forall_cons_iff in Hall as [Hxr Hall].
    destruct (read_idx_complete _ _ _ _ Hx) as [idx [q1 [Eleb [Hidx Hq1]]]].
    rewrite Eleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
    cbn [bind] in Hw.
    destruct (scalar_cast U32 Usize idx) as [j|] eqn:Hcast; cbn [bind] in Hw;
      [|discriminate].
    assert (Hj : to_Z j = to_Z idx)
      by (unfold scalar_cast in Hcast; apply mk_scalar_ok_to_Z in Hcast;
          exact Hcast).
    rewrite (scalar_lt_geb_false j
               (alloc_vec_Vec_len env.(env_Env_func_types))) in Hw.
    2: { rewrite vec_len_spec. rewrite Hj.
         unfold funcidx_in_range, translate_idx in *. rewrite <- Hidx in Hxr.
         rewrite N_to_nat_Z_to_N in Hxr.
         pose proof (u32_nonneg idx).
         apply Nat2Z.inj_lt in Hxr. rewrite Z2Nat.id in Hxr by lia.
         exact Hxr. }
    destruct (alloc_vec_Vec_push out idx) as [out2|] eqn:Hp;
      cbn [bind] in Hw; [|discriminate].
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in Hw;
      [|discriminate].
    assert (Hi2 : to_Z i2 = to_Z i + 1).
    { unfold u32_add, scalar_add in Hadd. apply mk_scalar_ok_to_Z in Hadd.
      assert (H1 : to_Z 1%u32 = 1) by reflexivity. lia. }
    exact (IH data env count out2 q1 i2 r vts rest
             (ltac:(rewrite Hi2; f_equal; lia)) Hw
             (ltac:(rewrite Hq1; exact Hrest)) Hall).
Qed.

Lemma decode_func_indices_complete : forall data pos env r vs rest,
  module_decode_func_indices data pos env = Ok r ->
  repr_vec repr_idx (bytes_from data pos) vs rest ->
  List.Forall (funcidx_in_range env) vs ->
  exists out q', r = Core_result_Result_Ok (out, q')
                 /\ bytes_from data q' = rest.
Proof.
  intros data pos env r vs rest Hrun H Hall.
  destruct (repr_vec_inv _ _ _ _ _ H) as [n [mid [Hn Hrep]]].
  destruct (read_u32_leb_complete _ _ _ _ Hn) as [count [p [Hleb [Hval Hp]]]].
  pose proof Hrun as Hw. unfold module_decode_func_indices in Hw.
  rewrite Hleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
  cbn [bind] in Hw.
  assert (H0 : to_Z 0%u32 = 0) by reflexivity.
  (* [u32] here is WasmCert's [N] alias, which shadows Primitives'; the
     vector's element type is the scalar one *)
  exact (decode_func_indices_loop_complete (Z.to_nat n) data env count
           (alloc_vec_Vec_new Primitives.u32) p 0%u32 r vs rest
           (ltac:(rewrite H0; rewrite Hval; f_equal; lia)) Hw
           (ltac:(rewrite Hp; exact Hrep)) Hall).
Qed.

(** What an element segment needs of the environment, read off the 2.0-shaped
    value: the table it names exists, its offset is a constant [i32] expression,
    and every function it lists exists. The [ref.func] wrapper is where the
    indices live in the 2.0 shape, so the condition is stated through it. *)
Definition element_wasm10 (env : env_Env_t) (el : module_element) : Prop :=
  match el.(modelem_mode) with
  | ME_active x _ =>
      (N.to_nat x < List.length (vec_list env.(env_Env_table_types)))%nat
  | _ => False
  end
  /\ (match el.(modelem_mode) with
      | ME_active _ e => const_ok env (T_num T_i32) e
      | _ => False
      end)
  /\ List.Forall (fun ie => exists x, ie = [BI_ref_func x]
                                      /\ funcidx_in_range env x)
       el.(modelem_init).

Lemma decode_element_section_loop_complete :
  forall k data env count q i r env2 vs rest,
  Z.to_nat (to_Z count - to_Z i) = k ->
  module_decode_element_section_loop data env count q i = Ok (r, env2) ->
  repr_rep repr_elem k (bytes_from data q) vs rest ->
  List.Forall (element_wasm10 env) vs ->
  exists q', r = Core_result_Result_Ok q' /\ bytes_from data q' = rest.
Proof.
  induction k as [|k IH];
    intros data env count q i r env2 vs rest Hk Hw Hrep Hall;
    unfold module_decode_element_section_loop in Hw; rewrite loop_unfold in Hw;
    cbn beta iota in Hw; destruct (i s>= count) eqn:Hge.
  - injection Hw as <- <-.
    destruct (repr_rep_O_inv _ _ _ _ _ Hrep) as [-> ->].
    exists q. split; reflexivity.
  - exfalso. apply scalar_geb_false_lt in Hge.
    pose proof (count_zero _ _ Hk). lia.
  - exfalso. apply scalar_geb_true_ge in Hge.
    pose proof (count_succ _ _ _ Hk) as Hcnt.
    rewrite Nat2Z.inj_succ in Hcnt. pose proof (Nat2Z.is_nonneg k). lia.
  - pose proof (count_succ _ _ _ Hk) as Hcnt.
    destruct (repr_rep_S_inv _ _ _ _ _ _ Hrep)
      as [el [mid [vts [-> [Hel Hrest]]]]].
    apply List.Forall_cons_iff in Hall as [Helok Hall].
    destruct (repr_elem_inv _ _ _ Hel)
      as [x [m1 [e0 [m2 [ys [Hx [He0 [Hys ->]]]]]]]].
    destruct Helok as [Htab [Hoff Hinit]].
    cbn [modelem_mode modelem_init] in Htab, Hoff, Hinit.
    (* the table index *)
    destruct (read_idx_complete _ _ _ _ Hx) as [tix [q1 [Eleb [Hidx Hq1]]]].
    rewrite Eleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
    cbn [bind] in Hw.
    destruct (scalar_cast U32 Usize tix) as [j|] eqn:Hcast; cbn [bind] in Hw;
      [|discriminate].
    assert (Hj : to_Z j = to_Z tix)
      by (unfold scalar_cast in Hcast; apply mk_scalar_ok_to_Z in Hcast;
          exact Hcast).
    rewrite (scalar_lt_geb_false j
               (alloc_vec_Vec_len env.(env_Env_table_types))) in Hw.
    2: { rewrite vec_len_spec. rewrite Hj.
         unfold translate_idx in Hidx. rewrite <- Hidx in Htab.
         rewrite N_to_nat_Z_to_N in Htab.
         pose proof (u32_nonneg tix).
         apply Nat2Z.inj_lt in Htab. rewrite Z2Nat.id in Htab by lia.
         exact Htab. }
    (* the offset *)
    destruct (module_decode_const_expr data q1 env Types_ValueType_I32)
      as [r1|] eqn:E1; cbn [bind] in Hw; [|discriminate].
    destruct (decode_const_expr_complete _ _ _ _ _ _ _ E1
                (ltac:(rewrite Hq1; exact He0))
                (ltac:(cbn [translate_vt_v]; exact Hoff)))
      as [offset [q2 [-> [_ Hq2]]]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    (* the function indices *)
    destruct (module_decode_func_indices data q2 env) as [r2|] eqn:E2;
      cbn [bind] in Hw; [|discriminate].
    destruct (decode_func_indices_complete _ _ _ _ _ _ E2
                (ltac:(rewrite Hq2; exact Hys))
                (ltac:(clear - Hinit; induction ys as [|y ys IHy];
                       [apply List.Forall_nil|];
                       cbn [List.map] in Hinit;
                       apply List.Forall_cons_iff in Hinit as [Hy Hinit];
                       destruct Hy as [x0 [Heq Hx0]]; injection Heq as <-;
                       apply List.Forall_cons; [exact Hx0 | apply IHy; exact Hinit])))
      as [init [q3 [-> Hq3]]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    destruct (alloc_vec_Vec_push env.(env_Env_elements)
                {| env_Element_table_idx := tix;
                   env_Element_offset := offset;
                   env_Element_init := init |}) as [v|] eqn:Hp;
      cbn [bind] in Hw; [|discriminate].
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in Hw;
      [|discriminate].
    assert (Hi2 : to_Z i2 = to_Z i + 1).
    { unfold u32_add, scalar_add in Hadd. apply mk_scalar_ok_to_Z in Hadd.
      assert (H1 : to_Z 1%u32 = 1) by reflexivity. lia. }
    exact (IH data _ count q3 i2 r env2 vts rest
             (ltac:(rewrite Hi2; f_equal; lia)) Hw
             (ltac:(rewrite Hq3; exact Hrest)) Hall).
Qed.

Lemma decode_element_section_complete : forall data pos env r env2 vs rest,
  module_decode_element_section data pos env = Ok (r, env2) ->
  repr_vec repr_elem (bytes_from data pos) vs rest ->
  List.Forall (element_wasm10 env) vs ->
  exists q', r = Core_result_Result_Ok q' /\ bytes_from data q' = rest.
Proof.
  intros data pos env r env2 vs rest Hrun H Hall.
  destruct (repr_vec_inv _ _ _ _ _ H) as [n [mid [Hn Hrep]]].
  destruct (read_u32_leb_complete _ _ _ _ Hn) as [count [p [Hleb [Hval Hp]]]].
  pose proof Hrun as Hw. unfold module_decode_element_section in Hw.
  rewrite Hleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
  cbn [bind] in Hw.
  assert (H0 : to_Z 0%u32 = 0) by reflexivity.
  exact (decode_element_section_loop_complete (Z.to_nat n) data env count p
           0%u32 r env2 vs rest (ltac:(rewrite H0; rewrite Hval; f_equal; lia))
           Hw (ltac:(rewrite Hp; exact Hrep)) Hall).
Qed.

(* ================================================================== *)
(** ** 5.5.10 The export section                                       *)
(* ================================================================== *)

(** Spec 3.4.11's uniqueness rule is the one check in the file with no format
    rule behind it, and it is the only one whose completeness needs a *soundness*
    lemma that was not there: [names_equal_true] says equal byte strings compare
    equal, and what is needed here is the converse, so that a scan reporting
    "taken" really did find the name. *)
Lemma names_equal_loop_sound : forall m (a b : slice u8) i,
  Z.of_nat (List.length (vec_list a)) - to_Z i <= Z.of_nat m ->
  0 <= to_Z i ->
  List.length (vec_list a) = List.length (vec_list b) ->
  module_names_equal_loop a b i = Ok true ->
  List.skipn (Z.to_nat (to_Z i)) (byte_list a)
    = List.skipn (Z.to_nat (to_Z i)) (byte_list b).
Proof.
  induction m as [|m IH]; intros a b i Hmeas Hi Hlen Hw;
    unfold module_names_equal_loop in Hw; rewrite loop_unfold in Hw;
    cbn beta iota in Hw; destruct (i s>= slice_len a) eqn:Hgef.
  (* past the end of both, so both tails are empty. The length goes through
     [byte_list_length] and not through [List.map_length]: the latter lands in
     the [scalar U8] spelling of the element type where [Hlen] is in the [u8]
     one, and then neither [rewrite] nor [lia] sees the two as the same. *)
  1,3: pose proof (scalar_geb_true_ge _ _ Hgef) as Hge;
       rewrite slice_len_spec in Hge; apply Z.ge_le in Hge;
       do 2 (rewrite List.skipn_all2 by
               (rewrite byte_list_length; try rewrite <- Hlen;
                apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; exact Hge));
       reflexivity.
  - exfalso. pose proof (scalar_geb_false_lt _ _ Hgef) as Hge.
    rewrite slice_len_spec in Hge. cbn in Hmeas. lia.
  - pose proof (scalar_geb_false_lt _ _ Hgef) as Hge.
    rewrite slice_len_spec in Hge.
    destruct (slice_index_usize a i) as [x|] eqn:Hx; cbn [bind] in Hw;
      [|discriminate].
    destruct (slice_index_usize b i) as [y|] eqn:Hy; cbn [bind] in Hw;
      [|discriminate].
    destruct (x s<> y) eqn:Hne; [discriminate|].
    apply scalar_neqb_false in Hne. cbn [bind] in Hw.
    destruct (usize_add i 1%usize) as [i2|] eqn:Hadd; cbn [bind] in Hw;
      [|discriminate].
    pose proof (scalar_add_val _ _ _ 1 Hadd eq_refl) as Hi2.
    rewrite slice_index_usize_spec in Hx. rewrite slice_index_usize_spec in Hy.
    destruct (List.nth_error (vec_list a) (Z.to_nat (to_Z i))) as [x0|] eqn:Hna;
      [|discriminate].
    destruct (List.nth_error (vec_list b) (Z.to_nat (to_Z i))) as [y0|] eqn:Hnb;
      [|discriminate].
    injection Hx as <-. injection Hy as <-.
    unfold byte_list.
    rewrite (skipn_map_nth to_Z _ _ _ Hna).
    rewrite (skipn_map_nth to_Z _ _ _ Hnb).
    rewrite Hne. f_equal.
    rewrite <- (Z_to_nat_add1 _ Hi). rewrite <- Hi2.
    apply (IH a b i2); [lia | lia | exact Hlen | exact Hw].
Qed.

Lemma names_equal_sound : forall (a b : slice u8),
  module_names_equal a b = Ok true -> byte_list a = byte_list b.
Proof.
  intros a b Hw. unfold module_names_equal in Hw.
  destruct (slice_len a s<> slice_len b) eqn:Hne; [discriminate|].
  apply scalar_neqb_false in Hne.
  rewrite slice_len_spec in Hne. rewrite slice_len_spec in Hne.
  assert (H0 : to_Z 0%usize = 0) by reflexivity.
  pose proof (names_equal_loop_sound (List.length (vec_list a)) a b 0%usize
                (ltac:(lia)) (ltac:(lia)) (ltac:(lia)) Hw) as Hs.
  rewrite H0 in Hs. cbn [Z.to_nat List.skipn] in Hs. exact Hs.
Qed.

Lemma names_equal_neq : forall (a b : slice u8) v,
  module_names_equal a b = Ok v -> byte_list a <> byte_list b -> v = false.
Proof.
  intros a b v Hw Hne. destruct v; [|reflexivity].
  exfalso. exact (Hne (names_equal_sound _ _ Hw)).
Qed.

Lemma export_name_taken_loop_complete : forall m env nm i r,
  Z.of_nat (List.length (vec_list env.(env_Env_exports))) - to_Z i
    <= Z.of_nat m ->
  0 <= to_Z i ->
  (forall e, List.In e (vec_list env.(env_Env_exports)) ->
     byte_list e.(env_Export_name) <> byte_list nm) ->
  module_export_name_taken_loop env nm i = Ok r ->
  r = false.
Proof.
  induction m as [|m IH]; intros env nm i r Hmeas Hi Hfresh Hw;
    unfold module_export_name_taken_loop in Hw; rewrite loop_unfold in Hw;
    cbn beta iota in Hw;
    destruct (i s>= alloc_vec_Vec_len env.(env_Env_exports)) eqn:Hgef.
  1,3: injection Hw as <-; reflexivity.
  - exfalso. pose proof (scalar_geb_false_lt _ _ Hgef) as Hge.
    rewrite vec_len_spec in Hge. cbn in Hmeas. lia.
  - pose proof (scalar_geb_false_lt _ _ Hgef) as Hge.
    rewrite vec_len_spec in Hge.
    destruct (alloc_vec_Vec_index
                (core_slice_index_SliceIndexUsizeSliceInst env_Export_t)
                env.(env_Env_exports) i) as [e|] eqn:He; cbn [bind] in Hw;
      [|discriminate].
    rewrite vec_index_spec in He.
    destruct (List.nth_error (vec_list env.(env_Env_exports))
                (Z.to_nat (to_Z i))) as [e0|] eqn:Hnth; [|discriminate].
    injection He as <-.
    rewrite vec_deref_spec in Hw.
    destruct (module_names_equal e0.(env_Export_name) nm) as [b|] eqn:Heq;
      cbn [bind] in Hw; [|discriminate].
    rewrite (names_equal_neq _ _ _ Heq
               (Hfresh e0 (List.nth_error_In _ _ Hnth))) in Hw.
    cbn beta iota in Hw.
    destruct (usize_add i 1%usize) as [i2|] eqn:Hadd; cbn [bind] in Hw;
      [|discriminate].
    pose proof (scalar_add_val _ _ _ 1 Hadd eq_refl) as Hi2.
    apply (IH env nm i2 r); [lia | lia | exact Hfresh | exact Hw].
Qed.

Lemma export_name_taken_complete : forall env nm r,
  (forall e, List.In e (vec_list env.(env_Env_exports)) ->
     byte_list e.(env_Export_name) <> byte_list nm) ->
  module_export_name_taken env nm = Ok r ->
  r = false.
Proof.
  intros env nm r Hfresh Hw. unfold module_export_name_taken in Hw.
  assert (H0 : to_Z 0%usize = 0) by reflexivity.
  apply (export_name_taken_loop_complete
           (List.length (vec_list env.(env_Env_exports))) env nm 0%usize r
           (ltac:(lia)) (ltac:(lia)) Hfresh Hw).
Qed.

(** A specification name as the byte string the decoder compares. The two byte
    types line up pointwise, so a name has one byte string and
    [Forall2 name_byte_is] is what identifies it. *)
Definition name_bytes (nm : name) : list Z :=
  List.map (fun b => Z.of_N (Byte.to_N b)) nm.

(** Spec 3.4.14: an export's index is in the space its kind names. *)
Definition exportdesc_wasm10 (env : env_Env_t) (d : module_export_desc)
  : Prop :=
  match d with
  | MED_func x =>
      (N.to_nat x < List.length (vec_list env.(env_Env_func_types)))%nat
  | MED_table x =>
      (N.to_nat x < List.length (vec_list env.(env_Env_table_types)))%nat
  | MED_mem x =>
      (N.to_nat x < List.length (vec_list env.(env_Env_mem_types)))%nat
  | MED_global x =>
      (N.to_nat x < List.length (vec_list env.(env_Env_global_types)))%nat
  end.

Lemma repr_exportdesc_inv : forall bs d rest,
  repr_exportdesc bs d rest ->
  exists p0 x,
    repr_idx p0 x rest
    /\ ((bs = 0 :: p0 /\ d = MED_func x)
        \/ (bs = 1 :: p0 /\ d = MED_table x)
        \/ (bs = 2 :: p0 /\ d = MED_mem x)
        \/ (bs = 3 :: p0 /\ d = MED_global x)).
Proof.
  intros bs d rest H. inversion H; subst; do 2 eexists;
    (split; [eassumption|]).
  - left. split; reflexivity.
  - right. left. split; reflexivity.
  - right. right. left. split; reflexivity.
  - right. right. right. split; reflexivity.
Qed.

(** The kind byte and the index, one guard chain. Which arm is taken is decided
    by the specification's rule, and the range check in it is
    [exportdesc_wasm10]. *)
Lemma export_desc_complete :
  forall env (kind : u8) (idx : scalar U32) r d x,
  Veriwasm.Aeneas_Specs.module_export_desc env kind idx = Ok r ->
  exportdesc_wasm10 env d ->
  translate_idx idx = x ->
  ((to_Z kind = 0 /\ d = MED_func x) \/ (to_Z kind = 1 /\ d = MED_table x)
   \/ (to_Z kind = 2 /\ d = MED_mem x) \/ (to_Z kind = 3 /\ d = MED_global x)) ->
  exists d', r = Core_result_Result_Ok d'.
Proof.
  intros env kind idx r d x Hrun Hok Hidx Hcase.
  pose proof Hrun as Hw.
  unfold Veriwasm.Aeneas_Specs.module_export_desc in Hw.
  destruct (scalar_cast U32 Usize idx) as [i|] eqn:Hcast; cbn [bind] in Hw;
    [|discriminate].
  assert (Hi : to_Z i = to_Z idx)
    by (unfold scalar_cast in Hcast; apply mk_scalar_ok_to_Z in Hcast;
        exact Hcast).
  (* the range condition, transported to the cursor the code casts to *)
  assert (Hrange : forall T (v : alloc_vec_Vec T),
            (N.to_nat x < List.length (vec_list v))%nat ->
            (i s>= alloc_vec_Vec_len v) = false).
  { intros T v Hlt. apply scalar_lt_geb_false. rewrite vec_len_spec.
    rewrite Hi.
    unfold translate_idx in Hidx. rewrite <- Hidx in Hlt.
    rewrite N_to_nat_Z_to_N in Hlt.
    pose proof (u32_nonneg idx).
    apply Nat2Z.inj_lt in Hlt. rewrite Z2Nat.id in Hlt by lia. exact Hlt. }
  destruct Hcase as [[Hk ->]|[[Hk ->]|[[Hk ->]|[Hk ->]]]];
    cbn [exportdesc_wasm10] in Hok.
  - rewrite (scalar_eqb_of_eq kind 0%u8) in Hw by (rewrite Hk; reflexivity).
    rewrite (Hrange _ _ Hok) in Hw. injection Hw as <-. eexists. reflexivity.
  - rewrite (scalar_eqb_of_ne kind 0%u8) in Hw by (rewrite Hk; cbn; lia).
    rewrite (scalar_eqb_of_eq kind 1%u8) in Hw by (rewrite Hk; reflexivity).
    rewrite (Hrange _ _ Hok) in Hw. injection Hw as <-. eexists. reflexivity.
  - rewrite (scalar_eqb_of_ne kind 0%u8) in Hw by (rewrite Hk; cbn; lia).
    rewrite (scalar_eqb_of_ne kind 1%u8) in Hw by (rewrite Hk; cbn; lia).
    rewrite (scalar_eqb_of_eq kind 2%u8) in Hw by (rewrite Hk; reflexivity).
    rewrite (Hrange _ _ Hok) in Hw. injection Hw as <-. eexists. reflexivity.
  - rewrite (scalar_eqb_of_ne kind 0%u8) in Hw by (rewrite Hk; cbn; lia).
    rewrite (scalar_eqb_of_ne kind 1%u8) in Hw by (rewrite Hk; cbn; lia).
    rewrite (scalar_eqb_of_ne kind 2%u8) in Hw by (rewrite Hk; cbn; lia).
    rewrite (scalar_eqb_of_eq kind 3%u8) in Hw by (rewrite Hk; reflexivity).
    rewrite (Hrange _ _ Hok) in Hw. injection Hw as <-. eexists. reflexivity.
Qed.


Lemma repr_export_inv : forall bs e rest,
  repr_export bs e rest ->
  exists nm mid d,
    repr_name bs nm mid /\ repr_exportdesc mid d rest
    /\ e = {| modexp_name := nm; modexp_desc := d |}.
Proof.
  intros bs e rest H. inversion H; subst.
  do 3 eexists. split; [eassumption|]. split; [eassumption | reflexivity].
Qed.

(** The name the decoder copied out, as the byte string the uniqueness scan
    compares: [translate_name] and [name_bytes] are inverse on the values a [u8]
    can hold. *)
Lemma byte_list_name_bytes : forall v : alloc_vec_Vec u8,
  byte_list v = name_bytes (translate_name v).
Proof.
  intros v. unfold byte_list, name_bytes, translate_name.
  rewrite List.map_map. apply List.map_ext_in. intros x _.
  pose proof (name_byte_is_translate x) as H. unfold name_byte_is in H.
  rewrite <- H. rewrite Z2N.id by (pose proof (u8_bounds x); lia).
  reflexivity.
Qed.

(** Spec 3.4.11's uniqueness, as a condition on the section's own list: the names
    it declares are pairwise distinct and none of them is already in the
    environment. The loop checks each new name against everything it has pushed
    so far, so this is exactly the invariant that survives one step. *)
Definition exports_fresh (env : env_Env_t) (exps : list module_export) : Prop :=
  List.NoDup (List.map (fun e => name_bytes e.(modexp_name)) exps)
  /\ forall e0, List.In e0 (vec_list env.(env_Env_exports)) ->
       ~ List.In (byte_list e0.(env_Export_name))
           (List.map (fun e => name_bytes e.(modexp_name)) exps).

Lemma decode_export_section_loop_complete :
  forall k data env count q i r env2 vs rest,
  Z.to_nat (to_Z count - to_Z i) = k ->
  module_decode_export_section_loop data env count q i = Ok (r, env2) ->
  repr_rep repr_export k (bytes_from data q) vs rest ->
  dlen data <= module_bytes ->
  exports_fresh env vs ->
  List.Forall (fun e => exportdesc_wasm10 env e.(modexp_desc)) vs ->
  exists q', r = Core_result_Result_Ok q' /\ bytes_from data q' = rest.
Proof.
  induction k as [|k IH];
    intros data env count q i r env2 vs rest Hk Hw Hrep Hmod Hfresh Hall;
    unfold module_decode_export_section_loop in Hw; rewrite loop_unfold in Hw;
    cbn beta iota in Hw; destruct (i s>= count) eqn:Hge.
  - injection Hw as <- <-.
    destruct (repr_rep_O_inv _ _ _ _ _ Hrep) as [-> ->].
    exists q. split; reflexivity.
  - exfalso. apply scalar_geb_false_lt in Hge.
    pose proof (count_zero _ _ Hk). lia.
  - exfalso. apply scalar_geb_true_ge in Hge.
    pose proof (count_succ _ _ _ Hk) as Hcnt.
    rewrite Nat2Z.inj_succ in Hcnt. pose proof (Nat2Z.is_nonneg k). lia.
  - pose proof (count_succ _ _ _ Hk) as Hcnt.
    destruct (repr_rep_S_inv _ _ _ _ _ _ Hrep)
      as [e [mid [vts [-> [He Hrest]]]]].
    apply List.Forall_cons_iff in Hall as [Hdok Hall].
    destruct Hfresh as [Hnd Hnew].
    destruct (repr_export_inv _ _ _ He) as [nm [m1 [d [Hnm [Hd ->]]]]].
    cbn [modexp_name modexp_desc] in Hdok.
    cbn [List.map modexp_name] in Hnd, Hnew.
    apply List.NoDup_cons_iff in Hnd as [Hhead Hnd].
    (* the name, and the byte string the scan will compare it against *)
    destruct (module_decode_name data q) as [r1|] eqn:E1; cbn [bind] in Hw;
      [|discriminate].
    destruct (decode_name_complete _ _ _ _ _ Hmod E1 Hnm)
      as [v [q1 [-> [Hv Hq1]]]].
    rewrite branch_ok in Hw. cbn [bind] in Hw. rewrite vec_deref_spec in Hw.
    assert (Hvb : byte_list v = name_bytes nm)
      by (rewrite byte_list_name_bytes; rewrite Hv; reflexivity).
    destruct (module_export_name_taken env v) as [b|] eqn:E2;
      cbn [bind] in Hw; [|discriminate].
    rewrite (export_name_taken_complete env v b
               (ltac:(intros e0 Hin Heqb; apply (Hnew e0 Hin);
                      left; rewrite Heqb; symmetry; exact Hvb)) E2) in Hw.
    cbn beta iota in Hw.
    (* the kind byte and the index *)
    destruct (repr_exportdesc_inv _ _ _ Hd) as [p0 [x [Hx Hcase]]].
    assert (Hkind : exists kz, m1 = kz :: p0
                    /\ ((kz = 0 /\ d = MED_func x) \/ (kz = 1 /\ d = MED_table x)
                        \/ (kz = 2 /\ d = MED_mem x)
                        \/ (kz = 3 /\ d = MED_global x))).
    { destruct Hcase as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]];
        [exists 0|exists 1|exists 2|exists 3];
        (split; [reflexivity|]);
        [left|right;left|right;right;left|right;right;right];
        split; reflexivity. }
    destruct Hkind as [kz [Hm1 Hkcase]].
    rewrite <- Hq1 in Hm1.
    destruct (read_byte_complete _ _ _ _ Hm1) as [kind [q2 [Eb [Hkz Hq2]]]].
    rewrite Eb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
    cbn [bind] in Hw.
    destruct (read_idx_complete data q2 x mid (ltac:(rewrite Hq2; exact Hx)))
      as [idx [q3 [Eleb [Hidx Hq3]]]].
    rewrite Eleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
    cbn [bind] in Hw.
    destruct (Veriwasm.Aeneas_Specs.module_export_desc env kind idx)
      as [r3|] eqn:E3; cbn [bind] in Hw; [|discriminate].
    assert (Hkc : (to_Z kind = 0 /\ d = MED_func x)
                  \/ (to_Z kind = 1 /\ d = MED_table x)
                  \/ (to_Z kind = 2 /\ d = MED_mem x)
                  \/ (to_Z kind = 3 /\ d = MED_global x))
      by (rewrite Hkz; exact Hkcase).
    destruct (export_desc_complete env kind idx r3 d x E3 Hdok Hidx Hkc)
      as [d' ->].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    destruct (alloc_vec_Vec_push env.(env_Env_exports)
                {| env_Export_name := v; env_Export_desc := d' |})
      as [w|] eqn:Hp; cbn [bind] in Hw; [|discriminate].
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in Hw;
      [|discriminate].
    assert (Hi2 : to_Z i2 = to_Z i + 1).
    { unfold u32_add, scalar_add in Hadd. apply mk_scalar_ok_to_Z in Hadd.
      assert (H1 : to_Z 1%u32 = 1) by reflexivity. lia. }
    apply (IH data _ count q3 i2 r env2 vts rest
             (ltac:(rewrite Hi2; f_equal; lia)) Hw
             (ltac:(rewrite Hq3; exact Hrest)) Hmod).
    + (* freshness survives the push: the name just added is the head's, and
         [NoDup] says the head's name is not among the rest *)
      split; [exact Hnd|].
      cbn [env_Env_exports]. rewrite (vec_push_spec _ _ _ Hp).
      intros e0 Hin. apply List.in_app_iff in Hin as [Hin|Hin].
      * intros Hbad. apply (Hnew e0 Hin). right. exact Hbad.
      * destruct Hin as [<-|Hbad]; [|exact (False_ind _ Hbad)].
        cbn [env_Export_name]. rewrite Hvb. exact Hhead.
    + exact Hall.
Qed.

Lemma decode_export_section_complete : forall data pos env r env2 vs rest,
  module_decode_export_section data pos env = Ok (r, env2) ->
  repr_vec repr_export (bytes_from data pos) vs rest ->
  dlen data <= module_bytes ->
  exports_fresh env vs ->
  List.Forall (fun e => exportdesc_wasm10 env e.(modexp_desc)) vs ->
  exists q', r = Core_result_Result_Ok q' /\ bytes_from data q' = rest.
Proof.
  intros data pos env r env2 vs rest Hrun H Hmod Hfresh Hall.
  destruct (repr_vec_inv _ _ _ _ _ H) as [n [mid [Hn Hrep]]].
  destruct (read_u32_leb_complete _ _ _ _ Hn) as [count [p [Hleb [Hval Hp]]]].
  pose proof Hrun as Hw. unfold module_decode_export_section in Hw.
  rewrite Hleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
  cbn [bind] in Hw.
  assert (H0 : to_Z 0%u32 = 0) by reflexivity.
  exact (decode_export_section_loop_complete (Z.to_nat n) data env count p
           0%u32 r env2 vs rest (ltac:(rewrite H0; rewrite Hval; f_equal; lia))
           Hw (ltac:(rewrite Hp; exact Hrep)) Hmod Hfresh Hall).
Qed.

(* ================================================================== *)
(** ** 5.5.5 The import section                                        *)
(* ================================================================== *)

(** The one entry decoder with four shapes, and the only place the two import
    counters move. Each arm pushes onto the import list and onto the index space
    its kind belongs to, so the table and memory bounds are the same accounting
    as the table and memory sections -- except that the entries are interleaved
    with the other kinds, so what the loop carries is how many of each are still
    to come. *)
Definition spec_imported_tables (imps : list module_import) : list table_type :=
  List.flat_map (fun im => match im.(imp_desc) with
                           | MID_table t => [t]
                           | _ => []
                           end) imps.

Definition spec_imported_mems (imps : list module_import) : list memory_type :=
  List.flat_map (fun im => match im.(imp_desc) with
                           | MID_mem m => [m]
                           | _ => []
                           end) imps.

Definition importdesc_wasm10 (env : env_Env_t) (d : module_import_desc)
  : Prop :=
  match d with
  | MID_func x => typeidx_in_range env x
  | MID_table t => tabletype_valid t = true
  | MID_mem m => memtype_valid m = true
  | MID_global _ => True
  end.

Lemma repr_import_inv : forall bs im rest,
  repr_import bs im rest ->
  exists md m1 nm m2 d,
    repr_name bs md m1 /\ repr_name m1 nm m2 /\ repr_importdesc m2 d rest
    /\ im = {| imp_module := md; imp_name := nm; imp_desc := d |}.
Proof.
  intros bs im rest H. inversion H; subst.
  do 5 eexists. split; [eassumption|]. split; [eassumption|].
  split; [eassumption | reflexivity].
Qed.

Lemma repr_importdesc_inv : forall bs d rest,
  repr_importdesc bs d rest ->
  (exists p0 x, bs = 0 :: p0 /\ repr_idx p0 x rest /\ d = MID_func x)
  \/ (exists p0 t, bs = 1 :: p0 /\ repr_tabletype p0 t rest /\ d = MID_table t)
  \/ (exists p0 m, bs = 2 :: p0 /\ repr_memtype p0 m rest /\ d = MID_mem m)
  \/ (exists p0 g, bs = 3 :: p0 /\ repr_globaltype p0 g rest
                   /\ d = MID_global g).
Proof.
  intros bs d rest H. inversion H; subst.
  - left. do 2 eexists. split; [reflexivity|].
    split; [eassumption | reflexivity].
  - right. left. do 2 eexists. split; [reflexivity|].
    split; [eassumption | reflexivity].
  - right. right. left. do 2 eexists. split; [reflexivity|].
    split; [eassumption | reflexivity].
  - right. right. right. do 2 eexists. split; [reflexivity|].
    split; [eassumption | reflexivity].
Qed.

Lemma decode_import_complete : forall data pos env r env2 im rest,
  module_decode_import data pos env = Ok (r, env2) ->
  repr_import (bytes_from data pos) im rest ->
  dlen data <= module_bytes ->
  importdesc_wasm10 env im.(imp_desc) ->
  (forall t, im.(imp_desc) = MID_table t ->
     Z.of_nat (List.length (vec_list env.(env_Env_table_types))) + 1 <= 1) ->
  (forall m, im.(imp_desc) = MID_mem m ->
     Z.of_nat (List.length (vec_list env.(env_Env_mem_types))) + 1 <= 1) ->
  exists q',
    r = Core_result_Result_Ok q'
    /\ bytes_from data q' = rest
    /\ List.length (vec_list env2.(env_Env_types))
       = List.length (vec_list env.(env_Env_types))
    /\ (List.length (vec_list env2.(env_Env_table_types))
        = List.length (vec_list env.(env_Env_table_types))
          + List.length (spec_imported_tables [im]))%nat
    /\ (List.length (vec_list env2.(env_Env_mem_types))
        = List.length (vec_list env.(env_Env_mem_types))
          + List.length (spec_imported_mems [im]))%nat.
Proof.
  intros data pos env r env2 im rest Hrun H Hmod Hdok Htab Hmem.
  destruct (repr_import_inv _ _ _ H) as [md [m1 [nm [m2 [d [Hmd [Hnm [Hd ->]]]]]]]].
  cbn [imp_desc] in Hdok, Htab, Hmem.
  pose proof Hrun as Hw. unfold module_decode_import in Hw.
  destruct (module_decode_name data pos) as [r1|] eqn:E1; cbn [bind] in Hw;
    [|discriminate].
  destruct (decode_name_complete _ _ _ _ _ Hmod E1 Hmd) as [v1 [p1 [-> [_ Hp1]]]].
  rewrite branch_ok in Hw. cbn [bind] in Hw.
  destruct (module_decode_name data p1) as [r2|] eqn:E2; cbn [bind] in Hw;
    [|discriminate].
  destruct (decode_name_complete _ _ _ _ _ Hmod E2
              (ltac:(rewrite Hp1; exact Hnm))) as [v2 [p2 [-> [_ Hp2]]]].
  rewrite branch_ok in Hw. cbn [bind] in Hw.
  destruct (repr_importdesc_inv _ _ _ Hd)
    as [[p0 [x [Hbs [Hx ->]]]]
       |[[p0 [t [Hbs [Ht ->]]]]
       |[[p0 [m [Hbs [Hm ->]]]] | [p0 [g [Hbs [Hg ->]]]]]]];
    rewrite <- Hp2 in Hbs;
    destruct (read_byte_complete _ _ _ _ Hbs) as [kind [p3 [Eb [Hkz Hp3]]]];
    rewrite Eb in Hw; cbn [bind] in Hw; rewrite branch_ok in Hw;
    cbn [bind] in Hw; cbn [importdesc_wasm10] in Hdok.
  - (* a function: the type index has to resolve *)
    guard_true_in Hw Hkz.
    destruct (read_idx_complete data p3 x rest (ltac:(rewrite Hp3; exact Hx)))
      as [idx [p4 [Eleb [Hidx Hp4]]]].
    rewrite Eleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
    cbn [bind] in Hw.
    destruct (module_lookup_type env idx) as [r3|] eqn:E3; cbn [bind] in Hw;
      [|discriminate].
    destruct (lookup_type_complete env idx r3 E3
                (ltac:(unfold typeidx_in_range, translate_idx in *;
                       rewrite <- Hidx in Hdok; rewrite N_to_nat_Z_to_N in Hdok;
                       exact Hdok))) as [ft ->].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    destruct (alloc_vec_Vec_push env.(env_Env_func_types) ft) as [w|] eqn:Hp;
      cbn [bind] in Hw; [|discriminate].
    destruct (usize_add env.(env_Env_num_imported_funcs) 1%usize) as [c|] eqn:Hc;
      cbn [bind] in Hw; [|discriminate].
    destruct (alloc_vec_Vec_push env.(env_Env_imports) _) as [w1|] eqn:Hp';
      cbn [bind] in Hw; [|discriminate].
    injection Hw as <- <-. exists p4.
    split; [reflexivity|]. split; [exact Hp4|].
    unfold spec_imported_tables, spec_imported_mems.
    cbn [env_Env_types env_Env_table_types env_Env_mem_types imp_desc
         List.flat_map List.app List.length].
    split; [reflexivity|]. split; lia.
  - (* a table: valid limits, and room for one *)
    guard_false_in Hw Hkz. guard_true_in Hw Hkz.
    destruct (module_decode_table_type data p3) as [r3|] eqn:E3;
      cbn [bind] in Hw; [|discriminate].
    destruct (decode_table_type_complete _ _ _ _ _ E3
                (ltac:(rewrite Hp3; exact Ht)) Hdok) as [tt [p4 [-> [_ Hp4]]]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    destruct (alloc_vec_Vec_push env.(env_Env_table_types) tt) as [w|] eqn:Hp;
      cbn [bind] in Hw; [|discriminate].
    rewrite (scalar_gtb_of_le (alloc_vec_Vec_len w) limits_max_tables) in Hw.
    2: { assert (Hmx : to_Z limits_max_tables = 1) by reflexivity.
         rewrite vec_len_spec. rewrite (vec_push_spec _ _ _ Hp).
         rewrite List.app_length. cbn [List.length].
         pose proof (Htab t (ltac:(reflexivity))). lia. }
    destruct (alloc_vec_Vec_push env.(env_Env_imports) _) as [w1|] eqn:Hp';
      cbn [bind] in Hw; [|discriminate].
    injection Hw as <- <-. exists p4.
    split; [reflexivity|]. split; [exact Hp4|].
    unfold spec_imported_tables, spec_imported_mems.
    cbn [env_Env_types env_Env_table_types env_Env_mem_types imp_desc
         List.flat_map List.app List.length].
    split; [reflexivity|]. split; [|lia].
    rewrite (vec_push_spec _ _ _ Hp). rewrite List.app_length.
    cbn [List.length]. lia.
  - (* a memory: the same, at the other index space *)
    guard_false_in Hw Hkz. guard_false_in Hw Hkz. guard_true_in Hw Hkz.
    destruct (module_decode_mem_type data p3) as [r3|] eqn:E3;
      cbn [bind] in Hw; [|discriminate].
    destruct (decode_mem_type_complete _ _ _ _ _ E3
                (ltac:(rewrite Hp3; exact Hm)) Hdok) as [mt [p4 [-> [_ Hp4]]]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    destruct (alloc_vec_Vec_push env.(env_Env_mem_types) mt) as [w|] eqn:Hp;
      cbn [bind] in Hw; [|discriminate].
    rewrite (scalar_gtb_of_le (alloc_vec_Vec_len w) limits_max_memories) in Hw.
    2: { assert (Hmx : to_Z limits_max_memories = 1) by reflexivity.
         rewrite vec_len_spec. rewrite (vec_push_spec _ _ _ Hp).
         rewrite List.app_length. cbn [List.length].
         pose proof (Hmem m (ltac:(reflexivity))). lia. }
    destruct (alloc_vec_Vec_push env.(env_Env_imports) _) as [w1|] eqn:Hp';
      cbn [bind] in Hw; [|discriminate].
    injection Hw as <- <-. exists p4.
    split; [reflexivity|]. split; [exact Hp4|].
    unfold spec_imported_tables, spec_imported_mems.
    cbn [env_Env_types env_Env_table_types env_Env_mem_types imp_desc
         List.flat_map List.app List.length].
    split; [reflexivity|]. split; [lia|].
    rewrite (vec_push_spec _ _ _ Hp). rewrite List.app_length.
    cbn [List.length]. lia.
  - (* a global: nothing to check beyond the type itself *)
    guard_false_in Hw Hkz. guard_false_in Hw Hkz. guard_false_in Hw Hkz.
    guard_true_in Hw Hkz.
    destruct (module_decode_global_type data p3) as [r3|] eqn:E3;
      cbn [bind] in Hw; [|discriminate].
    destruct (decode_global_type_complete _ _ _ _ _ E3
                (ltac:(rewrite Hp3; exact Hg))) as [gt [p4 [-> [_ Hp4]]]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    destruct (alloc_vec_Vec_push env.(env_Env_global_types) gt) as [w|] eqn:Hp;
      cbn [bind] in Hw; [|discriminate].
    destruct (usize_add env.(env_Env_num_imported_globals) 1%usize)
      as [c|] eqn:Hc; cbn [bind] in Hw; [|discriminate].
    destruct (alloc_vec_Vec_push env.(env_Env_imports) _) as [w1|] eqn:Hp';
      cbn [bind] in Hw; [|discriminate].
    injection Hw as <- <-. exists p4.
    split; [reflexivity|]. split; [exact Hp4|].
    unfold spec_imported_tables, spec_imported_mems.
    cbn [env_Env_types env_Env_table_types env_Env_mem_types imp_desc
         List.flat_map List.app List.length].
    split; [reflexivity|]. split; lia.
Qed.

(** Nothing in the section writes [types], so a function import's range
    condition travels along the loop unchanged. *)
Lemma importdesc_wasm10_keep : forall env env' d,
  List.length (vec_list env'.(env_Env_types))
    = List.length (vec_list env.(env_Env_types)) ->
  importdesc_wasm10 env d -> importdesc_wasm10 env' d.
Proof.
  intros env env' d Hlen H. destruct d; try exact H.
  unfold importdesc_wasm10, typeidx_in_range in *. rewrite Hlen. exact H.
Qed.

Lemma decode_import_section_loop_complete :
  forall k data env count q i r env2 vs rest,
  Z.to_nat (to_Z count - to_Z i) = k ->
  module_decode_import_section_loop data env count q i = Ok (r, env2) ->
  repr_rep repr_import k (bytes_from data q) vs rest ->
  dlen data <= module_bytes ->
  List.Forall (fun im => importdesc_wasm10 env im.(imp_desc)) vs ->
  Z.of_nat (List.length (vec_list env.(env_Env_table_types)))
    + Z.of_nat (List.length (spec_imported_tables vs)) <= 1 ->
  Z.of_nat (List.length (vec_list env.(env_Env_mem_types)))
    + Z.of_nat (List.length (spec_imported_mems vs)) <= 1 ->
  exists q', r = Core_result_Result_Ok q' /\ bytes_from data q' = rest.
Proof.
  induction k as [|k IH];
    intros data env count q i r env2 vs rest Hk Hw Hrep Hmod Hall Htab Hmem;
    unfold module_decode_import_section_loop in Hw; rewrite loop_unfold in Hw;
    cbn beta iota in Hw; destruct (i s>= count) eqn:Hge.
  - injection Hw as <- <-.
    destruct (repr_rep_O_inv _ _ _ _ _ Hrep) as [-> ->].
    exists q. split; reflexivity.
  - exfalso. apply scalar_geb_false_lt in Hge.
    pose proof (count_zero _ _ Hk). lia.
  - exfalso. apply scalar_geb_true_ge in Hge.
    pose proof (count_succ _ _ _ Hk) as Hcnt.
    rewrite Nat2Z.inj_succ in Hcnt. pose proof (Nat2Z.is_nonneg k). lia.
  - pose proof (count_succ _ _ _ Hk) as Hcnt.
    destruct (repr_rep_S_inv _ _ _ _ _ _ Hrep)
      as [im [mid [vts [-> [Him Hrest]]]]].
    apply List.Forall_cons_iff in Hall as [Hdok Hall].
    (* the head's own room, split out of the section's *)
    unfold spec_imported_tables, spec_imported_mems in Htab, Hmem.
    cbn [List.flat_map] in Htab, Hmem.
    rewrite List.app_length in Htab. rewrite List.app_length in Hmem.
    destruct (module_decode_import data q env) as [pr|] eqn:E1;
      cbn [bind] in Hw; [|discriminate].
    destruct pr as [r1 envm].
    destruct (decode_import_complete _ _ _ _ _ _ _ E1 Him Hmod Hdok
                (ltac:(intros t Ht; rewrite Ht in Htab; cbn in Htab; lia))
                (ltac:(intros m Hm; rewrite Hm in Hmem; cbn in Hmem; lia)))
      as [q1 [-> [Hq1 [Hlt [Hlta Hlma]]]]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in Hw;
      [|discriminate].
    assert (Hi2 : to_Z i2 = to_Z i + 1).
    { unfold u32_add, scalar_add in Hadd. apply mk_scalar_ok_to_Z in Hadd.
      assert (H1 : to_Z 1%u32 = 1) by reflexivity. lia. }
    unfold spec_imported_tables, spec_imported_mems in Hlta, Hlma.
    apply (IH data envm count q1 i2 r env2 vts rest
             (ltac:(rewrite Hi2; f_equal; lia)) Hw
             (ltac:(rewrite Hq1; exact Hrest)) Hmod).
    + eapply List.Forall_impl; [|exact Hall].
      intros im0 Him0. exact (importdesc_wasm10_keep env envm _ Hlt Him0).
    + unfold spec_imported_tables. rewrite Hlta.
      cbn [List.flat_map]. rewrite List.app_nil_r. lia.
    + unfold spec_imported_mems. rewrite Hlma.
      cbn [List.flat_map]. rewrite List.app_nil_r. lia.
Qed.

Lemma decode_import_section_complete : forall data pos env r env2 vs rest,
  module_decode_import_section data pos env = Ok (r, env2) ->
  repr_vec repr_import (bytes_from data pos) vs rest ->
  dlen data <= module_bytes ->
  List.Forall (fun im => importdesc_wasm10 env im.(imp_desc)) vs ->
  Z.of_nat (List.length (vec_list env.(env_Env_table_types)))
    + Z.of_nat (List.length (spec_imported_tables vs)) <= 1 ->
  Z.of_nat (List.length (vec_list env.(env_Env_mem_types)))
    + Z.of_nat (List.length (spec_imported_mems vs)) <= 1 ->
  exists q', r = Core_result_Result_Ok q' /\ bytes_from data q' = rest.
Proof.
  intros data pos env r env2 vs rest Hrun H Hmod Hall Htab Hmem.
  destruct (repr_vec_inv _ _ _ _ _ H) as [n [mid [Hn Hrep]]].
  destruct (read_u32_leb_complete _ _ _ _ Hn) as [count [p [Hleb [Hval Hp]]]].
  pose proof Hrun as Hw. unfold module_decode_import_section in Hw.
  rewrite Hleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
  cbn [bind] in Hw.
  assert (H0 : to_Z 0%u32 = 0) by reflexivity.
  exact (decode_import_section_loop_complete (Z.to_nat n) data env count p
           0%u32 r env2 vs rest (ltac:(rewrite H0; rewrite Hval; f_equal; lia))
           Hw (ltac:(rewrite Hp; exact Hrep)) Hmod Hall Htab Hmem).
Qed.

(* ================================================================== *)
(** ** 5.5.14 The data section                                         *)
(* ================================================================== *)

(** The tail's one section, and the only one that does not touch the
    environment: it reads it for the memory index space and the initialiser's
    globals, and hands its segments back separately. So there is no invariant to
    carry through the loop at all. *)
Lemma repr_data_inv : forall bs d rest,
  repr_data bs d rest ->
  exists x m1 e m2 bys,
    repr_idx bs x m1 /\ repr_expr m1 e m2 /\ repr_bytevec m2 bys rest
    /\ d = {| moddata_init := bys; moddata_mode := MD_active x e |}.
Proof.
  intros bs d rest H. inversion H; subst.
  do 5 eexists. split; [eassumption|]. split; [eassumption|].
  split; [eassumption | reflexivity].
Qed.

Definition data_wasm10 (env : env_Env_t) (d : module_data) : Prop :=
  match d.(moddata_mode) with
  | MD_active x _ =>
      (N.to_nat x < List.length (vec_list env.(env_Env_mem_types)))%nat
  | _ => False
  end
  /\ match d.(moddata_mode) with
     | MD_active _ e => const_ok env (T_num T_i32) e
     | _ => False
     end.

Lemma decode_data_segment_complete : forall data pos env r d rest,
  module_decode_data_segment data pos env = Ok r ->
  repr_data (bytes_from data pos) d rest ->
  dlen data <= module_bytes ->
  data_wasm10 env d ->
  exists d' p', r = Core_result_Result_Ok (d', p')
                /\ bytes_from data p' = rest.
Proof.
  intros data pos env r d rest Hrun H Hmod [Hmem Hoff].
  destruct (repr_data_inv _ _ _ H) as [x [m1 [e0 [m2 [bys [Hx [He0 [Hby ->]]]]]]]].
  cbn [moddata_mode] in Hmem, Hoff.
  pose proof Hrun as Hw. unfold module_decode_data_segment in Hw.
  (* the memory index *)
  destruct (read_idx_complete _ _ _ _ Hx) as [mix [p1 [Eleb [Hidx Hp1]]]].
  rewrite Eleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
  cbn [bind] in Hw.
  destruct (scalar_cast U32 Usize mix) as [j|] eqn:Hcast; cbn [bind] in Hw;
    [|discriminate].
  assert (Hj : to_Z j = to_Z mix)
    by (unfold scalar_cast in Hcast; apply mk_scalar_ok_to_Z in Hcast;
        exact Hcast).
  rewrite (scalar_lt_geb_false j
             (alloc_vec_Vec_len env.(env_Env_mem_types))) in Hw.
  2: { rewrite vec_len_spec. rewrite Hj.
       unfold translate_idx in Hidx. rewrite <- Hidx in Hmem.
       rewrite N_to_nat_Z_to_N in Hmem.
       pose proof (u32_nonneg mix).
       apply Nat2Z.inj_lt in Hmem. rewrite Z2Nat.id in Hmem by lia.
       exact Hmem. }
  (* the offset *)
  destruct (module_decode_const_expr data p1 env Types_ValueType_I32)
    as [r1|] eqn:E1; cbn [bind] in Hw; [|discriminate].
  destruct (decode_const_expr_complete _ _ _ _ _ _ _ E1
              (ltac:(rewrite Hp1; exact He0))
              (ltac:(cbn [translate_vt_v]; exact Hoff)))
    as [offset [p2 [-> [_ Hp2]]]].
  rewrite branch_ok in Hw. cbn [bind] in Hw.
  (* the contents, which is the same [vec(byte)] a name is built on *)
  destruct (repr_bytevec_inv _ _ _ Hby) as [zs [Hvec Hf2]].
  destruct (decode_bytevec_complete data p2 zs rest Hmod
              (ltac:(rewrite Hp2; exact Hvec)))
    as [len [n [p3 [q [v [Hleb2 [Hcast2 [Hhb [Hadd [Hcopy [_ Hq]]]]]]]]]]].
  (* the reader the code runs at [p2] is the one the [vec(byte)] lemma ran *)
  rewrite Hleb2 in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
  cbn [bind] in Hw. rewrite Hcast2 in Hw. cbn [bind] in Hw.
  rewrite Hhb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
  cbn [bind] in Hw. rewrite Hadd in Hw. cbn [bind] in Hw.
  rewrite Hcopy in Hw. cbn [bind] in Hw.
  injection Hw as <-. exists {| module_Data_memory_idx := mix;
                                module_Data_offset := offset;
                                module_Data_init := v |}, q.
  split; [reflexivity | exact Hq].
Qed.

Lemma decode_data_section_loop_complete :
  forall k data env count out q i r vs rest,
  Z.to_nat (to_Z count - to_Z i) = k ->
  module_decode_data_section_loop data env count out q i = Ok r ->
  repr_rep repr_data k (bytes_from data q) vs rest ->
  dlen data <= module_bytes ->
  List.Forall (data_wasm10 env) vs ->
  exists out' q', r = Core_result_Result_Ok (out', q')
                  /\ bytes_from data q' = rest.
Proof.
  induction k as [|k IH];
    intros data env count out q i r vs rest Hk Hw Hrep Hmod Hall;
    unfold module_decode_data_section_loop in Hw; rewrite loop_unfold in Hw;
    cbn beta iota in Hw; destruct (i s>= count) eqn:Hge.
  - injection Hw as <-.
    destruct (repr_rep_O_inv _ _ _ _ _ Hrep) as [-> ->].
    exists out, q. split; reflexivity.
  - exfalso. apply scalar_geb_false_lt in Hge.
    pose proof (count_zero _ _ Hk). lia.
  - exfalso. apply scalar_geb_true_ge in Hge.
    pose proof (count_succ _ _ _ Hk) as Hcnt.
    rewrite Nat2Z.inj_succ in Hcnt. pose proof (Nat2Z.is_nonneg k). lia.
  - pose proof (count_succ _ _ _ Hk) as Hcnt.
    destruct (repr_rep_S_inv _ _ _ _ _ _ Hrep)
      as [d [mid [vts [-> [Hd Hrest]]]]].
    apply List.Forall_cons_iff in Hall as [Hdok Hall].
    destruct (module_decode_data_segment data q env) as [r1|] eqn:E1;
      cbn [bind] in Hw; [|discriminate].
    destruct (decode_data_segment_complete _ _ _ _ _ _ E1 Hd Hmod Hdok)
      as [seg [q1 [-> Hq1]]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    destruct (alloc_vec_Vec_push out seg) as [out2|] eqn:Hp;
      cbn [bind] in Hw; [|discriminate].
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in Hw;
      [|discriminate].
    assert (Hi2 : to_Z i2 = to_Z i + 1).
    { unfold u32_add, scalar_add in Hadd. apply mk_scalar_ok_to_Z in Hadd.
      assert (H1 : to_Z 1%u32 = 1) by reflexivity. lia. }
    exact (IH data env count out2 q1 i2 r vts rest
             (ltac:(rewrite Hi2; f_equal; lia)) Hw
             (ltac:(rewrite Hq1; exact Hrest)) Hmod Hall).
Qed.

Lemma decode_data_section_complete : forall data pos env r vs rest,
  module_decode_data_section data pos env = Ok r ->
  repr_vec repr_data (bytes_from data pos) vs rest ->
  dlen data <= module_bytes ->
  List.Forall (data_wasm10 env) vs ->
  exists out q', r = Core_result_Result_Ok (out, q')
                 /\ bytes_from data q' = rest.
Proof.
  intros data pos env r vs rest Hrun H Hmod Hall.
  destruct (repr_vec_inv _ _ _ _ _ H) as [n [mid [Hn Hrep]]].
  destruct (read_u32_leb_complete _ _ _ _ Hn) as [count [p [Hleb [Hval Hp]]]].
  pose proof Hrun as Hw. unfold module_decode_data_section in Hw.
  rewrite Hleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
  cbn [bind] in Hw.
  assert (H0 : to_Z 0%u32 = 0) by reflexivity.
  exact (decode_data_section_loop_complete (Z.to_nat n) data env count
           (alloc_vec_Vec_new module_Data_t) p 0%u32 r vs rest
           (ltac:(rewrite H0; rewrite Hval; f_equal; lia)) Hw
           (ltac:(rewrite Hp; exact Hrep)) Hmod Hall).
Qed.

(* ================================================================== *)
(** ** 5.5.2 A section in the stream, and the runs of custom sections  *)
(* ================================================================== *)

(** Everything above is one *entry* at a time. The three loops that remain --
    [decode_env]'s chain, [validate_code] and the tail -- loop over *sections*,
    and what they have in common is this: the specification writes every position
    as [customs* Xsec], and the code reads one header and decides from its id.
    So a step is: take the [repr_customs] derivation apart, and the byte the
    header reports says which case it was in. *)

Lemma repr_customs_inv : forall bs rest,
  repr_customs bs rest ->
  (~ begins_with 0 bs /\ rest = bs)
  \/ (exists mid, repr_section 0 repr_custom bs tt mid /\ repr_customs mid rest).
Proof.
  intros bs rest H. inversion H; subst.
  - left. split; [assumption | reflexivity].
  - right. eexists. split; eassumption.
Qed.

Lemma repr_section_inv : forall A (id : Z) (R : list Z -> A -> list Z -> Prop)
                                bs x rest,
  repr_section id R bs x rest ->
  exists p0 size content,
    bs = id :: p0
    /\ repr_u32 p0 size (content ++ rest)
    /\ Z.of_nat (List.length content) = size
    /\ R content x [].
Proof.
  (* [subst] eats the length equation, because its right side is a variable, so
     the size conjunct may come back as a [reflexivity] rather than a
     hypothesis *)
  intros A id R bs x rest H. inversion H; subst.
  do 3 eexists. split; [reflexivity|]. split; [eassumption|].
  split; [first [reflexivity | eassumption] | assumption].
Qed.

Lemma repr_optsec_inv : forall A (id : Z) (R : list Z -> A -> list Z -> Prop)
                               absent bs x rest,
  repr_optsec id R absent bs x rest ->
  repr_section id R bs x rest
  \/ (~ begins_with id bs /\ x = absent /\ rest = bs).
Proof.
  intros A id R absent bs x rest H. inversion H; subst.
  - left. assumption.
  - right. split; [assumption|]. split; reflexivity.
Qed.

(** A section the specification put at the cursor: the header reads, its id is
    the one the rule names, and its contents are the bytes the rule framed off.
    [to_Z start <= to_Z fin] and [to_Z fin <= dlen data] are what the contents'
    own lemmas need, and both come out of the framing. *)
Lemma section_here : forall data (q : usize) idz A
                            (R : list Z -> A -> list Z -> Prop) x rest r,
  repr_section idz R (bytes_from data q) x rest ->
  module_read_section_header data q = Ok r ->
  exists (id : u8) (start fin : usize),
    r = Core_result_Result_Ok (id, start, fin)
    /\ to_Z id = idz
    /\ R (section_content data start fin) x []
    /\ bytes_from data fin = rest
    /\ to_Z fin <= dlen data
    /\ to_Z start <= to_Z fin.
Proof.
  intros data q idz A R x rest r Hsec Hrun.
  destruct (repr_section_inv _ _ _ _ _ _ Hsec)
    as [p0 [size [content [Hbs [Hn [Hlen HR]]]]]].
  destruct (read_section_header_complete data q r idz p0 size content rest
              Hbs Hn Hlen Hrun)
    as [id [start [fin [-> [Hid [Hcont [_ [Hfin [Hle Hsf]]]]]]]]].
  exists id, start, fin. split; [reflexivity|]. split; [exact Hid|].
  split; [rewrite Hcont; exact HR|].
  split; [exact Hfin|]. split; [exact Hle | exact Hsf].
Qed.

(** A custom section the specification put at the cursor. What the rule leaves
    unconstrained is the trailing bytes, so all the decoder can reject on is the
    name, and the derivation says the name is there. *)
(** The name is handed back rather than the custom decoder's verdict, because
    [destruct (decode_custom_section ...) eqn:] rewrites the hypotheses too, so a
    conclusion mentioning that call would be spoilt by the very [destruct] that
    needs it. *)
Lemma custom_here : forall data (q : usize) mid rh,
  repr_section 0 repr_custom (bytes_from data q) tt mid ->
  module_read_section_header data q = Ok rh ->
  exists (id : u8) (start fin : usize) nm m0,
    rh = Core_result_Result_Ok (id, start, fin)
    /\ to_Z id = 0
    /\ bytes_from data fin = mid
    /\ to_Z fin <= dlen data
    /\ to_Z start <= to_Z fin
    /\ repr_name (section_content data start fin) nm m0.
Proof.
  intros data q mid rh Hsec Hrun.
  destruct (section_here data q 0 _ repr_custom tt mid rh Hsec Hrun)
    as [id [start [fin [-> [Hid [HR [Hfin [Hle Hsf]]]]]]]].
  destruct HR as [nm [m0 [Hnm _]]].
  exists id, start, fin, nm, m0. split; [reflexivity|]. split; [exact Hid|].
  split; [exact Hfin|]. split; [exact Hle|]. split; [exact Hsf | exact Hnm].
Qed.

(** Two cursors with the same stream left are the same cursor, which is what
    turns "the decoder stopped where the section ends" into the equality the
    [p != end] check compares. *)
Lemma bytes_from_pos_eq : forall data (p q : usize),
  to_Z p <= dlen data -> to_Z q <= dlen data ->
  bytes_from data p = bytes_from data q -> to_Z p = to_Z q.
Proof.
  intros data p q Hp Hq Heq.
  pose proof (bytes_from_len_le data p q Hp Hq (ltac:(rewrite Heq; lia))).
  pose proof (bytes_from_len_le data q p Hq Hp (ltac:(rewrite Heq; lia))).
  lia.
Qed.

(** The position a section's own decoder stops at, from the no-panic
    postcondition for the same run. Threading the bound through every
    completeness lemma instead would reach all the way down to the readers. *)
Lemma data_section_pos : forall data pos env out q',
  to_Z pos <= dlen data -> dlen data <= module_bytes ->
  module_decode_data_section data pos env
    = Ok (Core_result_Result_Ok (out, q')) ->
  to_Z q' <= dlen data.
Proof.
  intros data pos env out q' Hpos Hlen Hrun.
  destruct (decode_data_section_ok data pos env Hpos Hlen) as [r0 [Hr0 Hpost]].
  rewrite Hr0 in Hrun. injection Hrun as Hr1.
  destruct (Hpost out q' Hr1) as [_ [Hle _]]. exact Hle.
Qed.



Lemma scalar_neqb_of_eq : forall {ty} (x y : scalar ty),
  to_Z x = to_Z y -> (x s<> y) = false.
Proof.
  intros ty x y H. unfold scalar_neqb. apply Bool.negb_false_iff.
  apply scalar_eqb_of_eq. exact H.
Qed.

(* ================================================================== *)
(** ** The tail                                                        *)
(* ================================================================== *)

(** Spec 5.5.16 from the code section on: [customs* datasec customs*]. Two states
    rather than the chain's nine, so the invariant is one [if] on the [seen_data]
    flag, and it is the cheap place to see the shape the chain will have.

    The case analysis is the whole argument, and it is short because inside the
    loop body the stream is known to have a byte left:

    - the [repr_customs] derivation is [more], so that byte is [0], so the code
      takes the custom-section arm;
    - or it is [done], so the byte is not [0], and then the optional data section
      has to be *present* -- because if it were absent the trailing
      [repr_customs] would have to consume a non-empty stream that does not begin
      with [0], and no derivation does that. *)
Definition tail_inv (data : slice u8) (q : usize) (seen : bool)
                    (datas : list module_data) : Prop :=
  if seen then repr_customs (bytes_from data q) []
  else exists mid fin,
         repr_customs (bytes_from data q) mid
         /\ repr_optsec 11 (repr_vec repr_data) [] mid datas fin
         /\ repr_customs fin [].

Lemma repr_customs_nil_nonempty : forall bs,
  repr_customs bs [] -> bs <> [] ->
  exists mid, repr_section 0 repr_custom bs tt mid /\ repr_customs mid [].
Proof.
  intros bs H Hne. destruct (repr_customs_inv _ _ H) as [[_ Hbs]|[mid Hm]].
  - exfalso. apply Hne. symmetry. exact Hbs.
  - exists mid. exact Hm.
Qed.

(** Every module hook returns [Ok]: the consumer accepts what it is shown.
    Completeness needs this rather than totality, for the same reason
    [OpIter_Visit.hooks_accept] does: a consumer that declines a module that
    was fine stops the decode, and reporting that is the interface working. *)
Definition module_hooks_accept {V : Type} (inst : module_ModuleVisitor_t V) : Prop :=
  forall v c, exists v',
    inst.(module_ModuleVisitor_t_on_custom_section) v c
      = Ok (Core_result_Result_Ok tt, v').

Lemma nop_module_hooks_accept :
  module_hooks_accept module_NopModuleVisitor_Insts_VeriwasmModuleModuleVisitor.
Proof.
  unfold module_hooks_accept,
         module_NopModuleVisitor_Insts_VeriwasmModuleModuleVisitor.
  intros v c. cbn [module_ModuleVisitor_t_on_custom_section].
  unfold module_NopModuleVisitor_Insts_VeriwasmModuleModuleVisitor_on_custom_section.
  eexists. reflexivity.
Qed.

Lemma decode_tail_with_loop_complete :
  forall V (inst : module_ModuleVisitor_t V) m data env vis vis' segments q seen r datas,
  module_hooks_accept inst ->
  dlen data - to_Z q <= Z.of_nat m ->
  to_Z q <= dlen data ->
  dlen data <= module_bytes ->
  tail_inv data q seen datas ->
  List.Forall (data_wasm10 env) datas ->
  module_decode_tail_with_loop inst data env vis segments q seen = Ok (r, vis') ->
  exists t, r = Core_result_Result_Ok t.
Proof.
  intros V inst m. induction m as [|m IH];
    intros data env vis vis' segments q seen r datas Hacc Hmeas Hq Hmod Hinv Hall Hw;
    unfold module_decode_tail_with_loop in Hw; rewrite loop_unfold in Hw;
    cbn beta iota in Hw; destruct (q s>= slice_len data) eqn:Hge.
  1,3: injection Hw as <- <-; eexists; reflexivity.
  - exfalso. apply scalar_geb_false_lt in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge.
    pose proof (usize_nonneg q). rewrite Nat2Z.inj_succ in Hmeas.
    assert (Hne : bytes_from data q <> []).
    { rewrite bytes_from_at. intros Hbad.
      pose proof (bytes_at_nil_ge data (to_Z q) (ltac:(lia)) Hbad). lia. }
    destruct (module_read_section_header data q) as [rh|] eqn:Eh;
      cbn [bind] in Hw; [|discriminate].
    destruct seen.
    + (* the data section is behind us: only custom sections are left, and the
         stream has a byte, so one of them is here *)
      destruct (repr_customs_nil_nonempty _ Hinv Hne) as [mid [Hsec Hrest]].
      destruct (custom_here data q mid rh Hsec Eh)
        as [id [start [fin [nm [m0 [-> [Hid [Hfineq [Hle [Hsf Hnm]]]]]]]]]].
      destruct (read_section_header_step _ _ _ _ _ Eh) as [Hqs [_ Hfl]].
      rewrite branch_ok in Hw. cbn [bind] in Hw.
      guard_true_in Hw Hid.
      destruct (module_decode_custom_section data start fin) as [rc|] eqn:Ec;
        cbn [bind] in Hw; [|discriminate].
      destruct (decode_custom_section_complete data start fin rc nm m0 Hmod Hsf
                  Hle Hnm Ec) as [c ->].
      rewrite branch_ok in Hw. cbn [bind] in Hw.
      destruct (Hacc vis c) as [vis1 Hh]. rewrite Hh in Hw. cbn [bind] in Hw.
      cbn beta iota in Hw.
      apply (IH data env vis1 vis' segments fin true r datas Hacc
               (ltac:(lia)) Hle Hmod
               (ltac:(cbn [tail_inv]; rewrite Hfineq; exact Hrest)) Hall Hw).
    + destruct Hinv as [mid [fin0 [Hcm [Hopt Htr]]]].
      destruct (repr_customs_inv _ _ Hcm) as [[Hnb Hmideq]|[mid' [Hsec Hrest]]].
      * (* no custom section here, so the data section has to be present *)
        rewrite Hmideq in Hopt.
        destruct (repr_optsec_inv _ _ _ _ _ _ _ Hopt)
          as [Hpres|[Hnb11 [Hdats Hfin0]]].
        -- destruct (section_here data q 11 _ (repr_vec repr_data) datas fin0
                      rh Hpres Eh)
             as [id [start [fin [-> [Hid [HR [Hfineq [Hle Hsf]]]]]]]].
           destruct (read_section_header_step _ _ _ _ _ Eh) as [Hqs [_ Hfl]].
           rewrite branch_ok in Hw. cbn [bind] in Hw.
           guard_false_in Hw Hid. tag_in Hw Hid. cbn beta iota in Hw.
           destruct (module_decode_data_section data start env) as [rd|] eqn:Ed;
             cbn [bind] in Hw; [|discriminate].
           destruct (decode_data_section_complete data start env rd datas
                       (bytes_from data fin) Ed
                       (section_lift _ (repr_vec repr_data) data start fin
                          datas [] (repr_vec_prefix _ _ repr_data_prefix) HR
                          Hsf)
                       Hmod Hall) as [out [q' [-> Hq']]].
           rewrite branch_ok in Hw. cbn [bind] in Hw.
           rewrite (scalar_neqb_of_eq q' fin) in Hw.
           2: { apply (bytes_from_pos_eq data q' fin);
                [ exact (data_section_pos data start env out q'
                           (ltac:(lia)) Hmod Ed)
                | exact Hle
                | rewrite Hq'; reflexivity ]. }
           cbn beta iota in Hw.
           apply (IH data env vis vis' out fin true r datas Hacc
                    (ltac:(lia)) Hle Hmod
                    (ltac:(cbn [tail_inv]; rewrite Hfineq; exact Htr)) Hall Hw).
        -- (* absent: the trailing customs would have to eat a non-empty stream
              that does not begin with [0] *)
           exfalso. rewrite Hfin0 in Htr.
           destruct (repr_customs_nil_nonempty _ Htr Hne) as [mid2 [Hsec2 _]].
           destruct (repr_section_inv _ _ _ _ _ _ Hsec2)
             as [p0 [sz [content [Hbs _]]]].
           apply Hnb. exists p0. exact Hbs.
      * (* a custom section is here *)
        destruct (custom_here data q mid' rh Hsec Eh)
          as [id [start [fin [nm [m0 [-> [Hid [Hfineq [Hle [Hsf Hnm]]]]]]]]]].
        destruct (read_section_header_step _ _ _ _ _ Eh) as [Hqs [_ Hfl]].
        rewrite branch_ok in Hw. cbn [bind] in Hw.
        guard_true_in Hw Hid.
        destruct (module_decode_custom_section data start fin) as [rc|] eqn:Ec;
          cbn [bind] in Hw; [|discriminate].
        destruct (decode_custom_section_complete data start fin rc nm m0 Hmod Hsf
                    Hle Hnm Ec) as [c ->].
        rewrite branch_ok in Hw. cbn [bind] in Hw.
        destruct (Hacc vis c) as [vis1 Hh]. rewrite Hh in Hw. cbn [bind] in Hw.
        cbn beta iota in Hw.
        apply (IH data env vis1 vis' segments fin false r datas Hacc
                 (ltac:(lia)) Hle Hmod
                 (ltac:(cbn [tail_inv]; exists mid, fin0;
                        split; [rewrite Hfineq; exact Hrest|];
                        split; [exact Hopt | exact Htr])) Hall Hw).
Qed.

Lemma decode_tail_complete : forall data pos env r datas mid fin,
  to_Z pos <= dlen data ->
  dlen data <= module_bytes ->
  repr_customs (bytes_from data pos) mid ->
  repr_optsec 11 (repr_vec repr_data) [] mid datas fin ->
  repr_customs fin [] ->
  List.Forall (data_wasm10 env) datas ->
  module_decode_tail data pos env = Ok r ->
  exists t, r = Core_result_Result_Ok t.
Proof.
  intros data pos env r datas mid fin Hpos Hmod Hcm Hopt Htr Hall Hw0.
  pose proof (Module_Sound.decode_tail_nop_inv _ _ _ _ Hw0) as Hw. clear Hw0.
  unfold module_decode_tail_with in Hw.
  pose proof (usize_nonneg pos).
  apply (decode_tail_with_loop_complete _
           module_NopModuleVisitor_Insts_VeriwasmModuleModuleVisitor
           (Z.to_nat (dlen data)) data env tt tt
           (alloc_vec_Vec_new module_Data_t) pos false r datas);
    [ exact nop_module_hooks_accept
    | rewrite Z2Nat.id by (pose proof (usize_nonneg (slice_len data)); lia); lia
    | exact Hpos | exact Hmod
    | cbn [tail_inv]; exists mid, fin;
      split; [exact Hcm|]; split; [exact Hopt | exact Htr]
    | exact Hall | exact Hw ].
Qed.

(* ================================================================== *)
(** ** 5.5.13 Locals                                                   *)
(* ================================================================== *)

(** [locals ::= n:u32 t:valtype => t^n], run-length encoded and flattened. The
    count has no byte cost, so it is the one place in the format where a couple
    of bytes can ask for an unbounded allocation, and [MAX_LOCALS] is the bound
    the decoder puts on it. That bound is a Wasm 1.0 restriction with no format
    rule behind it, so it is a side condition here, and it is checked after each
    group: what the loop carries is that the total still fits. *)
Lemma repr_locals_inv : forall bs g rest,
  repr_locals bs g rest ->
  exists n mid t,
    repr_u32 bs n mid /\ repr_valtype mid t rest
    /\ g = List.repeat t (Z.to_nat n).
Proof.
  intros bs g rest H. inversion H; subst.
  do 3 eexists. split; [eassumption|]. split; [eassumption | reflexivity].
Qed.

Lemma decode_locals_loop_complete :
  forall k data groups out q i r gs rest,
  Z.to_nat (to_Z groups - to_Z i) = k ->
  module_decode_locals_loop data groups out q i = Ok r ->
  repr_rep repr_locals k (bytes_from data q) gs rest ->
  Z.of_nat (List.length (vec_list out))
    + Z.of_nat (List.length (List.concat gs)) <= 50000 ->
  exists out' q', r = Core_result_Result_Ok (out', q')
                  /\ bytes_from data q' = rest.
Proof.
  induction k as [|k IH];
    intros data groups out q i r gs rest Hk Hw Hrep Hroom;
    unfold module_decode_locals_loop in Hw; rewrite loop_unfold in Hw;
    cbn beta iota in Hw; destruct (i s>= groups) eqn:Hge.
  - injection Hw as <-.
    destruct (repr_rep_O_inv _ _ _ _ _ Hrep) as [-> ->].
    exists out, q. split; reflexivity.
  - exfalso. apply scalar_geb_false_lt in Hge.
    pose proof (count_zero _ _ Hk). lia.
  - exfalso. apply scalar_geb_true_ge in Hge.
    pose proof (count_succ _ _ _ Hk) as Hcnt.
    rewrite Nat2Z.inj_succ in Hcnt. pose proof (Nat2Z.is_nonneg k). lia.
  - pose proof (count_succ _ _ _ Hk) as Hcnt.
    destruct (repr_rep_S_inv _ _ _ _ _ _ Hrep)
      as [g [mid [gs' [-> [Hg Hrest]]]]].
    destruct (repr_locals_inv _ _ _ Hg) as [n [m1 [t [Hn [Ht Hgeq]]]]].
    cbn [List.concat] in Hroom. rewrite List.app_length in Hroom.
    rewrite Hgeq in Hroom. rewrite List.repeat_length in Hroom.
    pose proof (repr_u32_nonneg _ _ _ Hn) as Hn0.
    rewrite Nat2Z.inj_add in Hroom. rewrite Z2Nat.id in Hroom by lia.
    destruct (read_u32_leb_complete _ _ _ _ Hn) as [count [q1 [Eleb [Hcv Hq1]]]].
    rewrite Eleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
    cbn [bind] in Hw.
    destruct (module_decode_value_type data q1) as [r1|] eqn:E1;
      cbn [bind] in Hw; [|discriminate].
    destruct (decode_value_type_complete _ _ _ _ _ E1
                (ltac:(rewrite Hq1; exact Ht))) as [vt [q2 [-> [Hvt Hq2]]]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    destruct (scalar_cast U32 Usize count) as [j|] eqn:Hcast; cbn [bind] in Hw;
      [|discriminate].
    assert (Hj : to_Z j = to_Z count)
      by (unfold scalar_cast in Hcast; apply mk_scalar_ok_to_Z in Hcast;
          exact Hcast).
    assert (Hmx : to_Z limits_max_locals = 50000) by reflexivity.
    destruct (usize_sub limits_max_locals (alloc_vec_Vec_len out)) as [d|] eqn:Hd;
      cbn [bind] in Hw; [|discriminate].
    unfold usize_sub, scalar_sub in Hd. apply mk_scalar_ok_to_Z in Hd.
    rewrite vec_len_spec in Hd.
    (* the group fits, because the whole run of groups does *)
    rewrite (scalar_gtb_of_le j d) in Hw
      by (rewrite Hj; rewrite Hcv; rewrite Hd; lia).
    destruct (module_push_locals out count vt) as [out2|] eqn:Hp;
      cbn [bind] in Hw; [|discriminate].
    destruct (u32_add i 1%u32) as [i2|] eqn:Hadd; cbn [bind] in Hw;
      [|discriminate].
    assert (Hi2 : to_Z i2 = to_Z i + 1).
    { unfold u32_add, scalar_add in Hadd. apply mk_scalar_ok_to_Z in Hadd.
      assert (H1 : to_Z 1%u32 = 1) by reflexivity. lia. }
    apply (IH data groups out2 q2 i2 r gs' rest
             (ltac:(rewrite Hi2; f_equal; lia)) Hw
             (ltac:(rewrite Hq2; exact Hrest))).
    (* the room the loop has left, after this group's own *)
    pose proof (push_locals_sound out count vt out2 Hp) as Hpl.
    rewrite Hpl. rewrite List.app_length. rewrite List.repeat_length.
    rewrite Nat2Z.inj_add. rewrite Z2Nat.id by (rewrite Hcv; lia).
    rewrite Hcv. lia.
Qed.

Lemma decode_locals_complete : forall data pos r gs rest,
  module_decode_locals data pos = Ok r ->
  repr_vec repr_locals (bytes_from data pos) gs rest ->
  Z.of_nat (List.length (List.concat gs)) <= 50000 ->
  exists out q', r = Core_result_Result_Ok (out, q')
                 /\ bytes_from data q' = rest.
Proof.
  intros data pos r gs rest Hrun H Hroom.
  destruct (repr_vec_inv _ _ _ _ _ H) as [n [mid [Hn Hrep]]].
  destruct (read_u32_leb_complete _ _ _ _ Hn) as [groups [p [Hleb [Hval Hp]]]].
  pose proof Hrun as Hw. unfold module_decode_locals in Hw.
  rewrite Hleb in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
  cbn [bind] in Hw.
  assert (H0 : to_Z 0%u32 = 0) by reflexivity.
  apply (decode_locals_loop_complete (Z.to_nat n) data groups
           (alloc_vec_Vec_new types_ValueType_t) p 0%u32 r gs rest
           (ltac:(rewrite H0; rewrite Hval; f_equal; lia)) Hw
           (ltac:(rewrite Hp; exact Hrep))).
  cbn [vec_list alloc_vec_Vec_new proj1_sig List.length]. lia.
Qed.

(* ================================================================== *)
(** ** 5.5.13 The code section                                         *)
(* ================================================================== *)

(** A run read inside a frame, lifted back to the stream it was framed off. The
    same step [section_lift] takes, for a frame delimited by a size prefix
    rather than by a section header. *)
Lemma frame_lift : forall A (R : list Z -> A -> list Z -> Prop) bs content rest
                          x mid,
  reads_prefix R -> bs = content ++ rest -> R content x mid ->
  R bs x (mid ++ rest).
Proof.
  intros A R bs content rest x mid HR -> Hrun.
  destruct (HR _ _ _ Hrun) as [pre [Heq Hall]].
  rewrite Heq. rewrite <- app_assoc. apply Hall.
Qed.

Lemma repr_code_inv : forall bs c rest,
  repr_code bs c rest ->
  exists size content,
    repr_u32 bs size (content ++ rest)
    /\ Z.of_nat (List.length content) = size
    /\ repr_func content c [].
Proof.
  intros bs c rest H. inversion H; subst.
  do 2 eexists. split; [eassumption|].
  split; [first [reflexivity | eassumption] | assumption].
Qed.

Lemma repr_func_inv : forall bs c rest,
  repr_func bs c rest ->
  exists gs mid e,
    repr_vec repr_locals bs gs mid /\ repr_expr mid e rest
    /\ c = (List.concat gs, e).
Proof.
  intros bs c rest H. inversion H; subst.
  do 3 eexists. split; [eassumption|]. split; [eassumption | reflexivity].
Qed.

(** The bridge between the two contexts, which is
    [validate_code_entry_sound]'s [Hctx] as a lemma of its own:
    [module_func_type_checker] builds its context one way round and
    [validate_body] proves its obligation in the other, and [context_reverse] is
    exactly the difference. *)
Lemma func_body_context_reverse :
  forall elems datas refs env ft locals results (declared : alloc_vec_Vec types_ValueType_t),
  vec_list locals
    = vec_list ft.(types_FuncType_params) ++ vec_list declared ->
  vec_list results = vec_list ft.(types_FuncType_results) ->
  func_body_context elems datas refs env ft
    (List.map translate_vt_v (vec_list declared))
  = context_reverse
      (upd_label
         (body_context elems datas refs env
            {| opiter_Context_locals := locals;
               opiter_Context_results := results |})
         [translate_typelist (vec_list results)]).
Proof.
  intros elems datas refs env ft locals results declared Hloc Hres.
  unfold func_body_context, context_reverse, upd_label,
         upd_local_label_return, body_context.
  cbn [tc_types tc_funcs tc_tables tc_mems tc_globals tc_elems tc_datas
       tc_locals tc_labels tc_return tc_refs
       opiter_Context_locals opiter_Context_results].
  assert (Hrv : forall l, seq.map rev_tf (List.map translate_ft l)
                          = List.map translate_functype l).
  { intros l. induction l as [|x l IH]; [reflexivity|].
    cbn [List.map seq.map]. rewrite IH. rewrite rev_tf_translate_ft.
    reflexivity. }
  rewrite Hrv. rewrite Hrv.
  rewrite Hloc. rewrite List.map_app.
  unfold translate_typelist. cbn [List.map seq.map option_map].
  rewrite seq.revK. rewrite Hres. reflexivity.
Qed.

(** Two more length facts about cursors, both of them just [skipn_length] with
    the [byte_list] spelling kept straight. *)
Lemma bytes_from_len_mono : forall data (p q : usize),
  to_Z p <= to_Z q ->
  (List.length (bytes_from data q) <= List.length (bytes_from data p))%nat.
Proof.
  intros data p q Hle. unfold bytes_from.
  rewrite List.skipn_length. rewrite List.skipn_length.
  pose proof (usize_nonneg p). pose proof (usize_nonneg q).
  assert (Z.to_nat (to_Z p) <= Z.to_nat (to_Z q))%nat
    by (apply Z2Nat.inj_le; lia).
  lia.
Qed.

Lemma bytes_from_split_len : forall data (p q : usize) pre,
  to_Z p <= dlen data -> to_Z q <= dlen data ->
  bytes_from data p = pre ++ bytes_from data q ->
  Z.to_nat (to_Z q - to_Z p) = List.length pre.
Proof.
  intros data p q pre Hp Hq Heq.
  apply (f_equal (@List.length Z)) in Heq. rewrite List.app_length in Heq.
  unfold bytes_from in Heq. rewrite List.skipn_length in Heq.
  rewrite List.skipn_length in Heq. rewrite byte_list_length in Heq.
  rewrite slice_len_spec in *.
  pose proof (usize_nonneg p). pose proof (usize_nonneg q).
  assert (Hpn : (Z.to_nat (to_Z p) <= List.length (vec_list data))%nat)
    by (apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; lia).
  assert (Hqn : (Z.to_nat (to_Z q) <= List.length (vec_list data))%nat)
    by (apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; lia).
  apply (f_equal Z.of_nat) in Heq.
  rewrite Nat2Z.inj_sub in Heq by exact Hpn.
  rewrite Nat2Z.inj_add in Heq.
  rewrite Nat2Z.inj_sub in Heq by exact Hqn.
  rewrite Z2Nat.id in Heq by lia. rewrite Z2Nat.id in Heq by lia.
  assert (Hd : to_Z q - to_Z p = Z.of_nat (List.length pre)) by lia.
  rewrite Hd. apply Z_to_nat_of_nat.
Qed.

(** One code entry. The frame the size prefix declares is where the body's own
    bytes come from, and it is the one sub-slice the decoder takes.

    The plumbing calls -- [build_func_locals], [copy_value_types], the sub-slice
    -- do not have to be shown to succeed: the run is given, so the [Fail_] arm
    of each is closed by [discriminate], which is the whole point of taking the
    run rather than building it. *)
(** [Module_Sound.code_typed] quantifies over the three context fields no Wasm
    1.0 instruction reads, because the body proof produces it that way. The
    completeness direction consumes one instantiation, so it takes this: the
    same statement at a fixed triple, which the caller chooses. That is what
    lets the module's own element, data and ref index spaces be the choice. *)
Definition code_typed_at (elems : list reference_type) (datas : list ok)
                         (refs : list funcidx) (env : env_Env_t)
                         (tidx : scalar U32) (c : list value_type * expr)
  : Prop :=
  exists ft,
    List.nth_error (vec_list env.(env_Env_types))
                   (Z.to_nat (to_Z tidx)) = Some ft
    /\ (exists ds, fst c = List.map translate_vt_v ds)
    /\ b_e_type_checker (func_body_context elems datas refs env ft (fst c))
         (snd c)
         (Tf [] (List.map translate_vt_v
                   (vec_list ft.(types_FuncType_results)))) = true.

Lemma validate_code_entry_with_complete :
  forall V (inst : visit_OpVisitor_t V) vis vis'
         elems datas refs data pos env index r c rest tidx,
  hooks_accept inst ->
  dlen data <= module_bytes ->
  to_Z pos <= dlen data ->
  Module_Sound.types_wasm10 env ->
  funcs_wasm10 env ->
  List.nth_error (vec_list env.(env_Env_func_type_indices))
                 (Z.to_nat (to_Z index)) = Some tidx ->
  code_typed_at elems datas refs env tidx c ->
  repr_code (bytes_from data pos) c rest ->
  Z.of_nat (List.length (fst c)) <= 50000 ->
  Z.of_nat (List.length (bytes_from data pos))
    - Z.of_nat (List.length rest) <= 7654321 ->
  module_validate_code_entry_with inst data pos env index vis
    = Ok (r, vis') ->
  exists end', r = Core_result_Result_Ok end'
               /\ bytes_from data end' = rest
               /\ to_Z end' <= dlen data.
Proof.
  intros V inst vis vis' elems datas refs data pos env index r c rest tidx
         Hacc Hmod Hpos Htw10
         Hfw10 Hnthi Hct Hcode Hlocs Hbody Hrun.
  destruct (repr_code_inv _ _ _ Hcode) as [size [content [Hn [Hclen Hfunc]]]].
  destruct (repr_func_inv _ _ _ Hfunc) as [gs [m1 [es [Hgs [Hes Hceq]]]]].
  destruct Hct as [ft [Hnthf [[ds Hds] Hchk]]].
  pose proof Hrun as Hw. unfold module_validate_code_entry_with in Hw.
  assert (Hidx : (index s>= alloc_vec_Vec_len env.(env_Env_func_type_indices))
                 = false).
  { apply scalar_lt_geb_false. rewrite vec_len_spec.
    assert (Hsome : List.nth_error (vec_list env.(env_Env_func_type_indices))
                      (Z.to_nat (to_Z index)) <> None)
      by (rewrite Hnthi; discriminate).
    apply List.nth_error_Some in Hsome. pose proof (usize_nonneg index).
    apply Nat2Z.inj_lt in Hsome. rewrite Z2Nat.id in Hsome by lia.
    exact Hsome. }
  rewrite Hidx in Hw.
  (* the size prefix, and the frame it declares *)
  destruct (read_u32_leb_complete _ _ _ _ Hn) as [sz [p [Esz [Hszv Hp]]]].
  rewrite Esz in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
  cbn [bind] in Hw.
  pose proof (read_u32_leb_le_len _ _ _ _ Esz) as Hple.
  pose proof (read_u32_leb_lt _ _ _ _ Esz) as Hplt.
  destruct (cast_u32_usize_ok sz) as [n [Hcast Hnv]].
  rewrite Hcast in Hw. cbn [bind] in Hw.
  assert (Hcl : Z.of_nat (List.length content) = to_Z n) by lia.
  assert (Hroom : to_Z p + to_Z n <= dlen data)
    by (rewrite <- Hcl; exact (bytes_from_app_len _ _ _ _ Hple Hp)).
  rewrite (have_bytes_complete _ _ _ Hroom) in Hw. cbn [bind] in Hw.
  rewrite branch_ok in Hw. cbn [bind] in Hw.
  pose proof (usize_le_max (slice_len data)).
  pose proof (usize_nonneg p). pose proof (usize_nonneg n).
  destruct (usize_add_ok p n (ltac:(lia))) as [end1 [Hadd Hend1]].
  rewrite Hadd in Hw. cbn [bind] in Hw.
  assert (Hend1b : bytes_from data end1 = rest).
  { rewrite (bytes_from_skipn data p end1 (List.length content))
      by (rewrite Hend1; lia).
    rewrite Hp. apply skipn_app_exact. }
  assert (Hdl : Z.of_nat (List.length (vec_list data)) = dlen data)
    by (rewrite slice_len_spec; reflexivity).
  (* the locals, read inside the frame *)
  assert (Hgs' : repr_vec repr_locals (bytes_from data p) gs (m1 ++ rest)).
  { rewrite Hp.
    apply (frame_lift _ (repr_vec repr_locals) _ content rest gs m1
             (repr_vec_prefix _ _ repr_locals_prefix) (ltac:(reflexivity))
             Hgs). }
  destruct (module_decode_locals data p) as [rl|] eqn:El; cbn [bind] in Hw;
    [|discriminate].
  destruct (decode_locals_complete data p rl gs (m1 ++ rest) El Hgs'
              (ltac:(rewrite Hceq in Hlocs; cbn [fst] in Hlocs; exact Hlocs)))
    as [declared [p1 [-> Hp1]]].
  rewrite branch_ok in Hw. cbn [bind] in Hw.
  destruct (decode_locals_ok data p (ltac:(lia))) as [r0 [Hr0 Hpost]].
  rewrite El in Hr0. injection Hr0 as Hr1.
  destruct (Hpost declared p1 (eq_sym Hr1)) as [Hpp1 [Hp1le _]].
  assert (Hp1e : to_Z p1 <= to_Z end1).
  { apply (bytes_from_len_le data p1 end1 Hp1le (ltac:(lia))).
    rewrite Hp1. rewrite Hend1b. rewrite List.app_length. lia. }
  rewrite (scalar_gtb_of_le p1 end1 Hp1e) in Hw.
  (* the entry's signature *)
  destruct (alloc_vec_Vec_index
              (core_slice_index_SliceIndexUsizeSliceInst Primitives.u32)
              env.(env_Env_func_type_indices) index) as [type_idx|] eqn:Htyi;
    cbn [bind] in Hw; [|discriminate].
  rewrite vec_index_spec in Htyi. rewrite Hnthi in Htyi.
  injection Htyi as <-.
  destruct (cast_u32_usize_ok tidx) as [t [Hcast2 Htv]].
  rewrite Hcast2 in Hw. cbn [bind] in Hw.
  assert (Htr : (t s>= alloc_vec_Vec_len env.(env_Env_types)) = false).
  { apply scalar_lt_geb_false. rewrite vec_len_spec. rewrite Htv.
    assert (Hsome : List.nth_error (vec_list env.(env_Env_types))
                      (Z.to_nat (to_Z tidx)) <> None)
      by (rewrite Hnthf; discriminate).
    apply List.nth_error_Some in Hsome. pose proof (u32_nonneg tidx).
    apply Nat2Z.inj_lt in Hsome. rewrite Z2Nat.id in Hsome by lia.
    exact Hsome. }
  rewrite Htr in Hw.
  rewrite vec_index_spec in Hw. rewrite Htv in Hw. rewrite Hnthf in Hw.
  cbn [bind] in Hw. rewrite vec_deref_spec in Hw. rewrite vec_deref_spec in Hw.
  destruct (module_build_func_locals ft.(types_FuncType_params) declared)
    as [locals|] eqn:Hbl; cbn [bind] in Hw; [|discriminate].
  rewrite vec_deref_spec in Hw.
  destruct (module_copy_value_types ft.(types_FuncType_results))
    as [results|] eqn:Hcopy; cbn [bind] in Hw; [|discriminate].
  (* the consumer accepts the frame, so the hook cannot be what stopped it *)
  destruct (frame_hook_accept V inst vis
              {| opiter_Context_locals := locals;
                 opiter_Context_results := results |} tidx p1 end1 Hacc) as [vf Hhk].
  rewrite Hhk in Hw. cbn [bind] in Hw. cbn beta iota in Hw.
  destruct (core_slice_index_Slice_index
              (core_slice_index_SliceIndexRangeUsizeSliceInst u8) data
              {| core_ops_range_Range_start := p1;
                 core_ops_range_Range_end_ := end1 |}) as [sub|] eqn:Hsub;
    cbn [bind] in Hw; [|discriminate].
  (* the body's own bytes are what is left of the frame past the locals *)
  assert (Hm1 : Z.to_nat (to_Z end1 - to_Z p1) = List.length m1)
    by (apply (bytes_from_split_len data p1 end1 m1 Hp1le (ltac:(lia))
                 (ltac:(rewrite Hp1; rewrite Hend1b; reflexivity)))).
  assert (Hbytes : byte_list sub = m1).
  { rewrite (byte_list_sub data p1 end1 sub Hp1e (ltac:(lia)) Hsub).
    unfold section_content. rewrite Hp1. rewrite Hm1.
    apply firstn_app_exact. }
  assert (Hsublen : to_Z (slice_len sub) <= 7654321).
  { rewrite slice_len_spec. rewrite <- byte_list_length. rewrite Hbytes.
    pose proof (bytes_from_len_mono data pos p1 (ltac:(lia))) as Hmn.
    apply (f_equal (@List.length Z)) in Hp1. rewrite List.app_length in Hp1.
    lia. }
  (* the groups the specification names are the locals the decoder read *)
  destruct (decode_locals_sound _ _ _ _ El) as [gs0 [Hflat Hrep0]].
  assert (Hgseq : gs0 = gs).
  { rewrite Hp1 in Hrep0.
    destruct (repr_vec_det _ _ repr_locals_det _ _ _ _ _ Hrep0 Hgs')
      as [Hg1 _]. exact Hg1. }
  rewrite Hgseq in Hflat.
  (* the body checks, so the body validator accepts it *)
  assert (Hlen1 : (List.length (vec_list results) <= 1)%nat).
  { rewrite (copy_value_types_sound _ _ Hcopy).
    apply (Htw10 ft (List.nth_error_In _ _ Hnthf)). }
  destruct (body_context_agrees elems datas refs env
              {| opiter_Context_locals := locals;
                 opiter_Context_results := results |})
    as [Hm [Hl [Hg [Hr [Hf [Htt Htb]]]]]].
  pose proof Hchk as Hc0.
  unfold b_e_type_checker in Hc0.
  rewrite Hceq in Hc0. cbn [fst snd] in Hc0.
  rewrite <- Hflat in Hc0.
  rewrite (func_body_context_reverse elems datas refs env ft locals results
             declared
             (build_func_locals_sound _ _ _ Hbl)
             (copy_value_types_sound _ _ Hcopy)) in Hc0.
  rewrite context_reverseK in Hc0.
  rewrite <- (copy_value_types_sound _ _ Hcopy) in Hc0.
  destruct (opiter_validate_body_with inst sub env
              {| opiter_Context_locals := locals;
                 opiter_Context_results := results |} vf) as [[rb vb]|] eqn:Evb;
    cbn [bind] in Hw; [|discriminate].
  destruct (validate_body_with_complete V inst vf
              _ env _ sub es Hacc Hm Hl Hg Hr Hf Htt Htb
              Hfw10 Htw10 Hlen1 Hsublen
              (ltac:(rewrite Hbytes; exact Hes))
              (ltac:(cbn [opiter_Context_results];
                     unfold translate_typelist; exact Hc0))) as [vb' Hvbok].
  rewrite Evb in Hvbok. injection Hvbok as Hvb _.
  rewrite Hvb in Hw. cbn beta iota in Hw.
  injection Hw as <- _. exists end1. split; [reflexivity|].
  split; [exact Hend1b | lia].
Qed.

(** The same for the validating-only consumer, which accepts every operator by
    computation, so its completeness has no hypothesis about hooks. *)
Corollary validate_code_entry_complete :
  forall elems datas refs data pos env index r c rest tidx,
  dlen data <= module_bytes ->
  to_Z pos <= dlen data ->
  Module_Sound.types_wasm10 env ->
  funcs_wasm10 env ->
  List.nth_error (vec_list env.(env_Env_func_type_indices))
                 (Z.to_nat (to_Z index)) = Some tidx ->
  code_typed_at elems datas refs env tidx c ->
  repr_code (bytes_from data pos) c rest ->
  Z.of_nat (List.length (fst c)) <= 50000 ->
  Z.of_nat (List.length (bytes_from data pos))
    - Z.of_nat (List.length rest) <= 7654321 ->
  module_validate_code_entry data pos env index = Ok r ->
  exists end', r = Core_result_Result_Ok end'
               /\ bytes_from data end' = rest
               /\ to_Z end' <= dlen data.
Proof.
  intros elems datas refs data pos env index r c rest tidx Hmod Hpos Htw10
         Hfw10 Hnthi Hct Hcode Hlocs Hbody Hrun.
  apply (validate_code_entry_with_complete _
           visit_NopVisitor_Insts_VeriwasmVisitOpVisitor tt tt
           elems datas refs data pos env index r c rest tidx nop_hooks_accept
           Hmod Hpos Htw10 Hfw10 Hnthi Hct Hcode Hlocs Hbody).
  apply code_entry_nop_inv. exact Hrun.
Qed.

(** The code entries, with the two Wasm 1.0 bounds each of them has to respect
    threaded along the same structure the format's [vec] gives them. Stating them
    this way rather than as a [Forall] is what keeps them per-entry: the bound is
    on the bytes an entry occupies, and that is not a function of the entry's
    decoded value. *)
Inductive codes_fit : list Z -> list (list value_type * expr) -> list Z -> Prop :=
| codes_fit_nil : forall bs, codes_fit bs [] bs
| codes_fit_cons : forall bs c mid cs rest,
    repr_code bs c mid ->
    Z.of_nat (List.length bs) - Z.of_nat (List.length mid) <= 7654321 ->
    Z.of_nat (List.length (fst c)) <= 50000 ->
    codes_fit mid cs rest ->
    codes_fit bs (c :: cs) rest.

Lemma codes_fit_rep : forall bs cs rest,
  codes_fit bs cs rest -> repr_rep repr_code (List.length cs) bs cs rest.
Proof.
  intros bs cs rest H. induction H as [bs | bs c mid cs rest Hc _ _ Hrec IH].
  - apply repr_rep_nil.
  - cbn [List.length]. eapply repr_rep_cons; [exact Hc | exact IH].
Qed.

(** A run of entries read inside a frame, lifted back to the stream. The bound
    each entry carries is on a *difference* of lengths, so appending the same
    tail to both ends leaves it alone. *)
Lemma codes_fit_app : forall bs cs rest more,
  codes_fit bs cs rest -> codes_fit (bs ++ more) cs (rest ++ more).
Proof.
  intros bs cs rest more H.
  induction H as [bs | bs c mid cs rest Hc Hext Hloc Hrec IH].
  - apply codes_fit_nil.
  - destruct (repr_code_prefix _ _ _ Hc) as [pre [Hbs Hall]].
    eapply codes_fit_cons.
    + rewrite Hbs. rewrite <- app_assoc. apply Hall.
    + rewrite List.app_length. rewrite List.app_length. lia.
    + exact Hloc.
    + exact IH.
Qed.

Definition repr_vec_fit (bs : list Z) (cs : list (list value_type * expr))
                        (rest : list Z) : Prop :=
  exists n mid,
    repr_u32 bs n mid /\ Z.to_nat n = List.length cs /\ codes_fit mid cs rest.

Lemma repr_vec_fit_vec : forall bs cs rest,
  repr_vec_fit bs cs rest -> repr_vec repr_code bs cs rest.
Proof.
  intros bs cs rest [n [mid [Hn [Hcnt Hfit]]]].
  apply repr_vec_intro with (n := n) (mid := mid); [exact Hn|].
  rewrite Hcnt. exact (codes_fit_rep _ _ _ Hfit).
Qed.

Lemma skipn_cons_inv : forall A (l : list A) n x r,
  List.skipn n l = x :: r ->
  List.nth_error l n = Some x /\ List.skipn (S n) l = r.
Proof.
  intros A l n. revert l. induction n as [|n IH]; intros l x r Heq.
  - destruct l as [|a l]; [discriminate|]. cbn [List.skipn] in Heq.
    injection Heq as <- <-. split; reflexivity.
  - destruct l as [|a l]; [discriminate|]. cbn [List.skipn] in Heq.
    destruct (IH l x r Heq) as [H1 H2]. split; [exact H1 | exact H2].
Qed.

Lemma skipn_nil_ge : forall A (l : list A) n,
  List.skipn n l = [] -> (List.length l <= n)%nat.
Proof.
  intros A l n. revert l. induction n as [|n IH]; intros l Heq.
  - destruct l; [apply Nat.le_refl | discriminate].
  - destruct l as [|a l]; [cbn; lia|]. cbn [List.skipn] in Heq.
    cbn [List.length]. pose proof (IH l Heq). lia.
Qed.

(** What a consumer that takes [on_code_entry] must not do: refuse an entry
    the validator accepts. Phrased against the validator rather than
    unconditionally, because the validating consumer's own answer on a bad
    entry is a rejection and that is right; what completeness needs is that a
    good entry is not turned away. *)
Definition code_hooks_accept {V : Type} (inst : module_CodeVisitor_t V)
                             (data : slice u8) (env : env_Env_t) : Prop :=
  (forall v e, exists v',
     inst.(module_CodeVisitor_t_on_need_bytes) v e
       = Ok (Core_result_Result_Ok tt, v'))
  /\ (forall v index pos contents fin q',
        module_validate_code_entry data pos env index
          = Ok (Core_result_Result_Ok q') ->
        exists v',
          inst.(module_CodeVisitor_t_on_code_entry) v data env index pos contents fin
            = Ok (Core_result_Result_Ok tt, v')).

Lemma validating_code_hooks_accept : forall data env,
  code_hooks_accept
    module_ValidatingCodeVisitor_Insts_VeriwasmModuleCodeVisitor data env.
Proof.
  intros data env. split.
  - intros v e. destruct v. exists tt. apply Module_Sound.validating_need_bytes.
  - intros v index pos contents fin q' H. destruct v. exists tt.
    exact (Module_Sound.validating_entry_ok _ _ _ _ contents fin _ H).
Qed.

Lemma validate_code_entries_with_loop_complete :
  forall V (inst : module_CodeVisitor_t V) elems datas refs tidxs data env vis q i r vis' codes rest,
  code_hooks_accept inst data env ->
  dlen data <= module_bytes ->
  to_Z q <= dlen data ->
  Module_NoPanic.env_small env q ->
  Module_Sound.types_wasm10 env ->
  funcs_wasm10 env ->
  List.skipn (Z.to_nat (to_Z i)) (vec_list env.(env_Env_func_type_indices))
    = tidxs ->
  List.Forall2 (code_typed_at elems datas refs env) tidxs codes ->
  codes_fit (bytes_from data q) codes rest ->
  module_validate_code_entries_with_loop inst data env vis q i = Ok (r, vis') ->
  exists q', r = Core_result_Result_Ok q' /\ bytes_from data q' = rest
             /\ to_Z q' <= dlen data.
Proof.
  intros V inst elems datas refs tidxs data env vis q i r vis' codes rest
         [Hneed Hentry] Hmod Hq Hsm Htw10 Hfw10 Hskip Hf2 Hfit Hw.
  revert vis q i r rest Hq Hsm Hskip Hfit Hw.
  induction Hf2 as [|tidx c tidxs' codes' Hct Hf2 IH];
    intros vis q i r rest Hq Hsm Hskip Hfit Hw;
    unfold module_validate_code_entries_with_loop in Hw;
    rewrite loop_unfold in Hw; cbn beta iota in Hw;
    destruct (i s>= alloc_vec_Vec_len env.(env_Env_func_type_indices)) eqn:Hge.
  - injection Hw as <- <-. inversion Hfit; subst.
    exists q. split; [reflexivity|]. split; [reflexivity | exact Hq].
  - (* no entries left, so the index has reached the end *)
    exfalso. apply scalar_geb_false_lt in Hge. rewrite vec_len_spec in Hge.
    pose proof (skipn_nil_ge _ _ _ Hskip) as Hle.
    pose proof (usize_nonneg i).
    apply Nat2Z.inj_le in Hle. rewrite Z2Nat.id in Hle by lia. lia.
  - (* an entry is left, so the index has not *)
    exfalso. apply scalar_geb_true_ge in Hge. rewrite vec_len_spec in Hge.
    destruct (skipn_cons_inv _ _ _ _ _ Hskip) as [Hnth _].
    assert (Hsome : List.nth_error (vec_list env.(env_Env_func_type_indices))
                      (Z.to_nat (to_Z i)) <> None)
      by (rewrite Hnth; discriminate).
    apply List.nth_error_Some in Hsome. pose proof (usize_nonneg i).
    apply Nat2Z.inj_lt in Hsome. rewrite Z2Nat.id in Hsome by lia. lia.
  - destruct (skipn_cons_inv _ _ _ _ _ Hskip) as [Hnth Hskip'].
    inversion Hfit as [|bs0 c0 mid cs0 rest0 Hc Hextent Hlocs Hrec]; subst.
    (* the framing read's wait, then the framing itself *)
    pose proof (usize_nonneg q).
    destruct (usize_add_ok q limits_max_leb_bytes
                (ltac:(unfold limits_max_leb_bytes;
                       pose proof Module_NoPanic.module_bytes_fits; cbn; lia)))
      as [qw [Hqw _]].
    rewrite Hqw in Hw. cbn [bind] in Hw.
    destruct (Hneed vis qw) as [v1 Hn]. rewrite Hn in Hw. cbn [bind] in Hw.
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    (* the walk does not validate the entry, so completeness has to know the
       validator answers at all before it can say what the answer was *)
    destruct (Module_NoPanic.validate_code_entry_ok data q env i Hsm Hq Hmod)
      as [re [Ee Hre]].
    destruct (validate_code_entry_complete elems datas refs data q env i re c
                mid tidx Hmod Hq Htw10 Hfw10 Hnth Hct Hc Hlocs Hextent Ee)
      as [end' [-> [Hend Hendle]]].
    destruct (Hre _ (ltac:(reflexivity))) as [Hqlt Hqle].
    destruct (Module_Sound.code_entry_extent_of_valid data q env i end' Ee)
      as [contents Hx].
    rewrite Hx in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
    cbn [bind] in Hw.
    destruct (Hneed v1 end') as [v2 Hn2]. rewrite Hn2 in Hw. cbn [bind] in Hw.
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    destruct (Hentry v2 i q contents end' end' Ee) as [v3 He].
    rewrite He in Hw. cbn [bind] in Hw. rewrite branch_ok in Hw.
    cbn [bind] in Hw.
    pose proof (usize_le_max (slice_len data)). pose proof (usize_nonneg i).
    destruct (usize_add i 1%usize) as [i2|] eqn:Hadd; cbn [bind] in Hw;
      [|discriminate].
    pose proof (scalar_add_val _ _ _ 1 Hadd eq_refl) as Hi2.
    (* [inversion Hfit; subst] eliminated the tail's name in favour of the
       [skipn] that produced it, so the index step is a computation *)
    apply (IH v3 end' i2 r rest Hendle
             (Module_NoPanic.env_small_mono env q end' Hsm (ltac:(lia)))
             (ltac:(rewrite Hi2; rewrite (Z_to_nat_add1 _ (usize_nonneg i));
                    reflexivity))
             (ltac:(rewrite Hend; exact Hrec)) Hw).
Qed.

Lemma validate_code_entries_with_complete :
  forall V (inst : module_CodeVisitor_t V) elems datas refs data env vis q r vis' codes rest,
  code_hooks_accept inst data env ->
  dlen data <= module_bytes ->
  to_Z q <= dlen data ->
  Module_NoPanic.env_small env q ->
  Module_Sound.types_wasm10 env ->
  funcs_wasm10 env ->
  List.Forall2 (code_typed_at elems datas refs env)
    (vec_list env.(env_Env_func_type_indices)) codes ->
  codes_fit (bytes_from data q) codes rest ->
  module_validate_code_entries_with inst data q env vis = Ok (r, vis') ->
  exists q', r = Core_result_Result_Ok q' /\ bytes_from data q' = rest
             /\ to_Z q' <= dlen data.
Proof.
  intros V inst elems datas refs data env vis q r vis' codes rest Hacc Hmod Hq
         Hsm Htw10 Hfw10 Hf2 Hfit Hw.
  unfold module_validate_code_entries_with in Hw.
  assert (H0 : to_Z 0%usize = 0) by reflexivity.
  apply (validate_code_entries_with_loop_complete V inst elems datas refs _ data
           env vis q 0%usize r vis' codes rest Hacc Hmod Hq Hsm Htw10 Hfw10
           (ltac:(rewrite H0; reflexivity)) Hf2 Hfit Hw).
Qed.

(** Something is framed at the cursor. The code section's absent case still
    reads a header -- the Rust reads one whenever it is not at the end of the
    input -- so completeness has to know a section really is there, and this is
    the least it needs of it. *)
Definition framed (bs : list Z) : Prop :=
  exists idz p0 sz content rest,
    bs = idz :: p0
    /\ repr_u32 p0 sz (content ++ rest)
    /\ Z.of_nat (List.length content) = sz.

Lemma framed_of_section : forall A (id : Z) (R : list Z -> A -> list Z -> Prop)
                                 bs x rest,
  repr_section id R bs x rest -> framed bs.
Proof.
  intros A id R bs x rest H.
  destruct (repr_section_inv _ _ _ _ _ _ H) as [p0 [sz [content [Hbs [Hn [Hl _]]]]]].
  exists id, p0, sz, content, rest. split; [exact Hbs|].
  split; [exact Hn | exact Hl].
Qed.

Lemma framed_here : forall data (q : usize) r,
  framed (bytes_from data q) ->
  module_read_section_header data q = Ok r ->
  exists (id : u8) (start fin : usize),
    r = Core_result_Result_Ok (id, start, fin)
    /\ bytes_from data q = to_Z id :: List.skipn 1 (bytes_from data q).
Proof.
  intros data q r [idz [p0 [sz [content [rest [Hbs [Hn Hl]]]]]]] Hrun.
  destruct (read_section_header_complete data q r idz p0 sz content rest
              Hbs Hn Hl Hrun) as [id [start [fin [-> [Hid _]]]]].
  exists id, start, fin. split; [reflexivity|].
  rewrite Hid. rewrite Hbs. reflexivity.
Qed.

(** The header half of spec 5.5.16's code line, read backwards: given that the
    line is there, the reader finds it, agrees with the function section about
    how many entries there are, and reports where they start and where the
    section ends. Named on its own because a consumer that drives the entries
    itself starts here, so this is the step that says the position it starts
    from is the right one. *)
Lemma code_section_complete : forall data pos env r codes rest,
  to_Z pos <= dlen data ->
  repr_optsec 10 repr_vec_fit [] (bytes_from data pos) codes rest ->
  (bytes_from data pos = [] \/ framed (bytes_from data pos)) ->
  List.length (vec_list env.(env_Env_func_type_indices)) = List.length codes ->
  module_code_section data pos env = Ok r ->
  (exists cs,
     r = Core_result_Result_Ok (Some cs)
     /\ bytes_from data cs.(module_CodeSection_end) = rest
     /\ to_Z cs.(module_CodeSection_end) <= dlen data
     /\ to_Z cs.(module_CodeSection_entries) <= dlen data
     /\ codes_fit (bytes_from data cs.(module_CodeSection_entries)) codes
          (bytes_from data cs.(module_CodeSection_end)))
  \/ (r = Core_result_Result_Ok None
      /\ codes = []
      /\ bytes_from data pos = rest).
Proof.
  intros data pos env r codes rest Hpos Hopt Hfr Hlens Hrun.
  unfold module_code_section in Hrun.
  destruct (repr_optsec_inv _ _ _ _ _ _ _ Hopt) as [Hpres|[Hnb [Hcs Hrest]]].
  - (* the code section is here *)
    assert (Hne : (pos s>= slice_len data) = false).
    { apply scalar_lt_geb_false.
      destruct (repr_section_inv _ _ _ _ _ _ Hpres)
        as [p0 [sz [content [Hbs _]]]].
      pose proof (usize_nonneg pos).
      apply (bytes_at_cons_lt data (to_Z pos) 10 p0 (ltac:(lia))).
      rewrite <- bytes_from_at. exact Hbs. }
    rewrite Hne in Hrun.
    destruct (module_read_section_header data pos) as [rh|] eqn:Eh;
      cbn [bind] in Hrun; [|discriminate].
    destruct (section_here data pos 10 _ repr_vec_fit codes rest rh Hpres Eh)
      as [id [start [fin [-> [Hid [HR [Hfineq [Hle Hsf]]]]]]]].
    rewrite branch_ok in Hrun. cbn [bind] in Hrun. tag_in Hrun Hid.
    (* the entry count, which the function section fixed *)
    destruct HR as [n [mid [Hn [Hcnt Hfit]]]].
    assert (Hlift : repr_u32 (bytes_from data start) n
                      (mid ++ bytes_from data fin)).
    { apply (frame_lift _ repr_u32 _ (section_content data start fin)
               (bytes_from data fin) n mid repr_u32_prefix
               (section_content_app data start fin Hsf) Hn). }
    destruct (read_u32_leb_complete _ _ _ _ Hlift)
      as [count [p [Eleb [Hcv Hp]]]].
    rewrite Eleb in Hrun. cbn [bind] in Hrun. rewrite branch_ok in Hrun.
    cbn [bind] in Hrun.
    destruct (cast_u32_usize_ok count) as [cn [Hcast Hcnv]].
    rewrite Hcast in Hrun. cbn [bind] in Hrun.
    rewrite (scalar_neqb_of_eq cn (alloc_vec_Vec_len
               env.(env_Env_func_type_indices))) in Hrun.
    2: { rewrite vec_len_spec. rewrite Hcnv. rewrite Hcv. rewrite Hlens.
         rewrite <- Hcnt. pose proof (repr_u32_nonneg _ _ _ Hn).
         rewrite Z2Nat.id by lia. reflexivity. }
    cbn beta iota in Hrun. injection Hrun as <-.
    left. eexists. split; [reflexivity|]. cbn.
    split; [exact Hfineq|].
    split; [exact Hle|].
    split; [exact (read_u32_leb_le_len _ _ _ _ Eleb)|].
    rewrite Hp. exact (codes_fit_app _ _ _ (bytes_from data fin) Hfit).
  - (* the code section is absent, so the module declared no functions *)
    assert (Hempty : vec_list env.(env_Env_func_type_indices) = []).
    { rewrite Hcs in Hlens.
      destruct (vec_list env.(env_Env_func_type_indices)) as [|a l];
        [reflexivity | cbn in Hlens; discriminate]. }
    assert (Hnc : module_no_code_section env
                  = Ok (Core_result_Result_Ok None)).
    { unfold module_no_code_section. rewrite vec_is_empty_spec.
      cbn [bind]. rewrite Hempty. reflexivity. }
    destruct (pos s>= slice_len data) eqn:Hge.
    + rewrite Hnc in Hrun. injection Hrun as <-.
      right. split; [reflexivity|]. split; [exact Hcs|].
      rewrite Hrest. reflexivity.
    + (* not at the end, so the header still gets read *)
      destruct Hfr as [Hnil|Hframed].
      { exfalso. apply scalar_geb_false_lt in Hge.
        pose proof (usize_nonneg pos).
        pose proof (bytes_at_nil_ge data (to_Z pos) (ltac:(lia))
                      (ltac:(rewrite <- bytes_from_at; exact Hnil))). lia. }
      destruct (module_read_section_header data pos) as [rh|] eqn:Eh;
        cbn [bind] in Hrun; [|discriminate].
      destruct (framed_here data pos rh Hframed Eh)
        as [id [start [fin [-> Hidb]]]].
      rewrite branch_ok in Hrun. cbn [bind] in Hrun.
      (* the id cannot be the code section's, because the line is absent *)
      rewrite (scalar_neqb_of_neq id module_section_code) in Hrun.
      2: { intros Hbad. apply Hnb. exists (List.skipn 1 (bytes_from data pos)).
           rewrite Hidb. rewrite Hbad. reflexivity. }
      rewrite Hnc in Hrun. injection Hrun as <-.
      right. split; [reflexivity|]. split; [exact Hcs|].
      rewrite Hrest. reflexivity.
Qed.

(** Spec 5.5.16's code line. The header half is above; this is the entries
    filling the section the header framed. *)
Lemma validate_code_with_complete :
  forall V (inst : module_CodeVisitor_t V) elems datas refs data pos env vis r vis' codes rest,
  code_hooks_accept inst data env ->
  dlen data <= module_bytes ->
  to_Z pos <= dlen data ->
  Module_NoPanic.env_small env pos ->
  Module_Sound.types_wasm10 env ->
  funcs_wasm10 env ->
  repr_optsec 10 repr_vec_fit [] (bytes_from data pos) codes rest ->
  (bytes_from data pos = [] \/ framed (bytes_from data pos)) ->
  List.Forall2 (code_typed_at elems datas refs env)
    (vec_list env.(env_Env_func_type_indices)) codes ->
  module_validate_code_with inst data pos env vis = Ok (r, vis') ->
  exists q', r = Core_result_Result_Ok q' /\ bytes_from data q' = rest.
Proof.
  intros V inst elems datas refs data pos env vis r vis' codes rest Hacc Hmod
         Hpos Hsm Htw10 Hfw10 Hopt Hfr Hf2 Hrun.
  pose proof Hacc as [Hneed _].
  pose proof Hrun as Hw. unfold module_validate_code_with in Hw.
  pose proof (usize_nonneg pos).
  destruct (usize_add_ok pos limits_max_code_header_bytes
              (ltac:(unfold limits_max_code_header_bytes,
                            limits_max_code_header_bytes_body;
                     pose proof Module_NoPanic.module_bytes_fits; cbn; lia)))
    as [pw [Hpw _]].
  rewrite Hpw in Hw. cbn [bind] in Hw.
  destruct (Hneed vis pw) as [v1 Hn]. rewrite Hn in Hw. cbn [bind] in Hw.
  rewrite branch_ok in Hw. cbn [bind] in Hw.
  destruct (module_code_section data pos env) as [rcs|] eqn:Ecs;
    cbn [bind] in Hw; [|discriminate].
  assert (Hlens : List.length (vec_list env.(env_Env_func_type_indices))
                  = List.length codes) by (apply (Forall2_length Hf2)).
  destruct (code_section_complete data pos env rcs codes rest Hpos Hopt Hfr
              Hlens Ecs)
    as [[cs [-> [Hfineq [Hle [Hple Hfit]]]]] | [-> [Hcs Hrest]]].
  - (* the section is here, so the entries have to fill it *)
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    (* the entries begin past the header, which is what carries [env_small]
       forward from the section's own position *)
    assert (Hposent : to_Z pos <= to_Z cs.(module_CodeSection_entries)).
    { destruct (Module_Sound.code_section_sound _ _ _ _ Ecs)
        as [id [start [_ [Hhdr [Hcnt _]]]]].
      pose proof (Module_NoPanic.read_section_header_step _ _ _ _ _ Hhdr)
        as [Hlt1 _].
      pose proof (read_u32_leb_lt _ _ _ _ Hcnt). lia. }
    destruct (module_validate_code_entries_with inst data
                cs.(module_CodeSection_entries) env v1) as [[rc v2]|] eqn:Ec;
      cbn [bind] in Hw; [|discriminate].
    destruct (validate_code_entries_with_complete V inst elems datas refs data
                env v1 cs.(module_CodeSection_entries) rc v2 codes
                (bytes_from data cs.(module_CodeSection_end))
                Hacc Hmod Hple
                (Module_NoPanic.env_small_mono env pos
                   cs.(module_CodeSection_entries) Hsm Hposent)
                Htw10 Hfw10 Hf2 Hfit Ec) as [q' [-> [Hq' Hq'le]]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    rewrite (scalar_neqb_of_eq q' cs.(module_CodeSection_end)) in Hw.
    2: { apply (bytes_from_pos_eq data q' cs.(module_CodeSection_end));
         [ exact Hq'le | exact Hle | rewrite Hq'; reflexivity ]. }
    cbn beta iota in Hw. injection Hw as <-.
    exists cs.(module_CodeSection_end). split; [reflexivity | exact Hfineq].
  - (* no section, so no codes, and the cursor has not moved *)
    rewrite branch_ok in Hw. cbn [bind] in Hw. injection Hw as <-.
    exists pos. split; [reflexivity | exact Hrest].
Qed.

Corollary validate_code_complete : forall elems datas refs data pos env r codes rest,
  dlen data <= module_bytes ->
  to_Z pos <= dlen data ->
  Module_NoPanic.env_small env pos ->
  Module_Sound.types_wasm10 env ->
  funcs_wasm10 env ->
  repr_optsec 10 repr_vec_fit [] (bytes_from data pos) codes rest ->
  (bytes_from data pos = [] \/ framed (bytes_from data pos)) ->
  List.Forall2 (code_typed_at elems datas refs env)
    (vec_list env.(env_Env_func_type_indices)) codes ->
  module_validate_code data pos env = Ok r ->
  exists q', r = Core_result_Result_Ok q' /\ bytes_from data q' = rest.
Proof.
  intros elems datas refs data pos env r codes rest Hmod Hpos Hsm Htw10 Hfw10
         Hopt Hfr Hf2 Hrun.
  apply Module_Sound.validate_code_nop_inv in Hrun.
  exact (validate_code_with_complete _ _ elems datas refs data pos env tt r tt
           codes rest (validating_code_hooks_accept data env) Hmod Hpos Hsm
           Htw10 Hfw10 Hopt Hfr Hf2 Hrun).
Qed.

(* ================================================================== *)
(** ** The environment as a function of the module's sections          *)
(* ================================================================== *)

(** The nine values spec 5.5.16's environment lines carry. The chain is a
    statement about these, and [env_at] below is the invariant that says which
    of them the environment has absorbed so far. *)
Record env_secs : Type := {
  es_types : list function_type;
  es_imps  : list module_import;
  es_tidxs : list funcidx;
  es_tabs  : list module_table;
  es_mems  : list module_mem;
  es_globs : list module_global;
  es_exps  : list module_export;
  es_start : option module_start;
  es_els   : list module_element;
}.

(** A field's value once lines [1 .. L] have been read: its own once its line
    is behind us, and the line's absent value before that. *)
Definition upto {A : Type} (k L : Z) (x absent : A) : A :=
  if k <=? L then x else absent.

Definition at_types (es : env_secs) (L : Z) := upto 1 L (es_types es) [].
Definition at_imps  (es : env_secs) (L : Z) := upto 2 L (es_imps es) [].
Definition at_tidxs (es : env_secs) (L : Z) := upto 3 L (es_tidxs es) [].
Definition at_tabs  (es : env_secs) (L : Z) := upto 4 L (es_tabs es) [].
Definition at_mems  (es : env_secs) (L : Z) := upto 5 L (es_mems es) [].
Definition at_globs (es : env_secs) (L : Z) := upto 6 L (es_globs es) [].
Definition at_exps  (es : env_secs) (L : Z) := upto 7 L (es_exps es) [].
Definition at_start (es : env_secs) (L : Z) := upto 8 L (es_start es) None.
Definition at_els   (es : env_secs) (L : Z) := upto 9 L (es_els es) [].

(** The import section's contribution to each index space, spec-side. These are
    the same functions [Module_Sound.imported_tables] and friends compute on the
    extraction's side, which is what makes the two agree by [map]. *)
Definition spec_imported_globals (imps : list module_import) : list global_type :=
  List.flat_map (fun im => match im.(imp_desc) with
                           | MID_global g => [g]
                           | _ => []
                           end) imps.

Definition spec_imported_fidxs (imps : list module_import) : list typeidx :=
  List.flat_map (fun im => match im.(imp_desc) with
                           | MID_func x => [x]
                           | _ => []
                           end) imps.

(** [resolved_types] read on the specification's side: a type index space and a
    list of indices into it. *)
Definition spec_resolve (tfs : list function_type) (xs : list typeidx)
  : list function_type :=
  List.flat_map (fun x => match List.nth_error tfs (N.to_nat x) with
                          | Some ft => [ft]
                          | None => []
                          end) xs.

(** The four index spaces, each the imported entries then the defined ones. *)
Definition at_funcs (es : env_secs) (L : Z) : list function_type :=
  spec_resolve (at_types es L)
    (spec_imported_fidxs (at_imps es L) ++ at_tidxs es L).

Definition at_tabtypes (es : env_secs) (L : Z) : list table_type :=
  spec_imported_tables (at_imps es L)
  ++ List.map modtab_type (at_tabs es L).

Definition at_memtypes (es : env_secs) (L : Z) : list memory_type :=
  spec_imported_mems (at_imps es L)
  ++ List.map modmem_type (at_mems es L).

Definition at_globtypes (es : env_secs) (L : Z) : list global_type :=
  spec_imported_globals (at_imps es L)
  ++ List.map modglob_type (at_globs es L).

(** The loop invariant. A flat conjunction, one clause per field: what the
    environment holds is the translation of what lines [1 .. L] declared.
    Stating it this way rather than as a nested "and for any environment the
    next section could produce" is the decision the whole chain rests on -- the
    conditions each section takes are then *derived* where they are used, out
    of the clause an earlier line established. *)
Definition env_at (env : env_Env_t) (es : env_secs) (L : Z) : Prop :=
  List.map translate_functype (vec_list env.(env_Env_types)) = at_types es L
  /\ List.map translate_import (vec_list env.(env_Env_imports)) = at_imps es L
  /\ List.map translate_idx (vec_list env.(env_Env_func_type_indices))
       = at_tidxs es L
  /\ List.map translate_functype (vec_list env.(env_Env_func_types))
       = at_funcs es L
  /\ List.map translate_tabletype (vec_list env.(env_Env_table_types))
       = at_tabtypes es L
  /\ List.map translate_memtype (vec_list env.(env_Env_mem_types))
       = at_memtypes es L
  /\ List.map translate_globaltype (vec_list env.(env_Env_global_types))
       = at_globtypes es L
  /\ List.map translate_global (vec_list env.(env_Env_globals)) = at_globs es L
  /\ List.map translate_export (vec_list env.(env_Env_exports)) = at_exps es L
  /\ translate_start env.(env_Env_start) = at_start es L
  /\ List.map translate_element (vec_list env.(env_Env_elements)) = at_els es L
  /\ to_Z env.(env_Env_num_imported_globals)
       = Z.of_nat (List.length (spec_imported_globals (at_imps es L))).

(* ================================================================== *)
(** ** Reading a translated vector backwards                           *)
(* ================================================================== *)

(** Every clause of [env_at] is a [map], so every use of it is one of these
    three: a length, an entry, or emptiness. *)
Lemma map_eq_nil_inv : forall A B (f : A -> B) l, List.map f l = [] -> l = [].
Proof. intros A B f l H. destruct l; [reflexivity | discriminate]. Qed.

Lemma map_nth_error_inv : forall A B (f : A -> B) l i y,
  List.nth_error (List.map f l) i = Some y ->
  exists x, List.nth_error l i = Some x /\ f x = y.
Proof.
  intros A B f l. induction l as [|a l IH]; intros [|i] y H; try discriminate.
  - cbn in H. injection H as <-. exists a. split; reflexivity.
  - cbn in H. exact (IH i y H).
Qed.

Lemma nth_error_map_eq : forall A B (f : A -> B) l i x,
  List.nth_error l i = Some x -> List.nth_error (List.map f l) i = Some (f x).
Proof. intros A B f l i x H. apply List.map_nth_error. exact H. Qed.

Lemma nth_error_map_none : forall A B (f : A -> B) l i,
  List.nth_error l i = None -> List.nth_error (List.map f l) i = None.
Proof.
  intros A B f l. induction l as [|a l IH]; intros [|i] H; try reflexivity;
    try discriminate.
  cbn in H |- *. exact (IH i H).
Qed.

Lemma map_length_eq : forall A B (f : A -> B) l m,
  List.map f l = m -> List.length l = List.length m.
Proof. intros A B f l m <-. symmetry. apply List.map_length. Qed.

(** The [resolved_types] of the extraction, read on the specification's side.
    Every use of [at_funcs] goes through this. *)
Lemma resolved_types_spec : forall (tys : list types_FuncType_t) xs,
  resolved_types tys xs
    = spec_resolve (List.map translate_functype tys) (List.map translate_idx xs).
Proof.
  intros tys xs. induction xs as [|x xs IH]; [reflexivity|].
  cbn [resolved_types spec_resolve List.flat_map List.map].
  unfold translate_idx. rewrite N_to_nat_Z_to_N.
  destruct (List.nth_error tys (Z.to_nat (to_Z x))) as [ft|] eqn:Hn.
  - rewrite (nth_error_map_eq _ _ translate_functype _ _ _ Hn).
    unfold resolved_types, spec_resolve in IH. rewrite IH. reflexivity.
  - rewrite (nth_error_map_none _ _ translate_functype _ _ Hn).
    unfold resolved_types, spec_resolve in IH. rewrite IH. reflexivity.
Qed.

(** The four index spaces once every line that writes them has run. Lines 2 to
    6 are their only writers, so from line 6 on these are what [env_at] pins,
    and every condition after that is stated against them. *)
Definition all_funcs (es : env_secs) : list function_type :=
  spec_resolve (es_types es) (spec_imported_fidxs (es_imps es) ++ es_tidxs es).

Definition all_tabtypes (es : env_secs) : list table_type :=
  spec_imported_tables (es_imps es) ++ List.map modtab_type (es_tabs es).

Definition all_memtypes (es : env_secs) : list memory_type :=
  spec_imported_mems (es_imps es) ++ List.map modmem_type (es_mems es).

Definition all_globtypes (es : env_secs) : list global_type :=
  spec_imported_globals (es_imps es) ++ List.map modglob_type (es_globs es).

Ltac upto_true := unfold upto; rewrite Z.leb_le by lia.

Lemma at_funcs_full : forall es L, 3 <= L -> at_funcs es L = all_funcs es.
Proof.
  intros es L HL. unfold at_funcs, all_funcs, at_types, at_imps, at_tidxs, upto.
  rewrite (proj2 (Z.leb_le 1 L) (ltac:(lia))).
  rewrite (proj2 (Z.leb_le 2 L) (ltac:(lia))).
  rewrite (proj2 (Z.leb_le 3 L) (ltac:(lia))). reflexivity.
Qed.

Lemma at_tabtypes_full : forall es L, 4 <= L -> at_tabtypes es L = all_tabtypes es.
Proof.
  intros es L HL. unfold at_tabtypes, all_tabtypes, at_imps, at_tabs, upto.
  rewrite (proj2 (Z.leb_le 2 L) (ltac:(lia))).
  rewrite (proj2 (Z.leb_le 4 L) (ltac:(lia))). reflexivity.
Qed.

Lemma at_memtypes_full : forall es L, 5 <= L -> at_memtypes es L = all_memtypes es.
Proof.
  intros es L HL. unfold at_memtypes, all_memtypes, at_imps, at_mems, upto.
  rewrite (proj2 (Z.leb_le 2 L) (ltac:(lia))).
  rewrite (proj2 (Z.leb_le 5 L) (ltac:(lia))). reflexivity.
Qed.

Lemma at_globtypes_full : forall es L, 6 <= L -> at_globtypes es L = all_globtypes es.
Proof.
  intros es L HL. unfold at_globtypes, all_globtypes, at_imps, at_globs, upto.
  rewrite (proj2 (Z.leb_le 2 L) (ltac:(lia))).
  rewrite (proj2 (Z.leb_le 6 L) (ltac:(lia))). reflexivity.
Qed.

Lemma at_types_full : forall es L, 1 <= L -> at_types es L = es_types es.
Proof.
  intros es L HL. unfold at_types, upto.
  rewrite (proj2 (Z.leb_le 1 L) (ltac:(lia))). reflexivity.
Qed.

Lemma at_imps_full : forall es L, 2 <= L -> at_imps es L = es_imps es.
Proof.
  intros es L HL. unfold at_imps, upto.
  rewrite (proj2 (Z.leb_le 2 L) (ltac:(lia))). reflexivity.
Qed.

(* ================================================================== *)
(** ** The conditions each section takes, stated about the module      *)
(* ================================================================== *)

(** Spec 5.4.1's constant expression, with the environment's global index space
    and its count of imported globals passed in rather than read off an [Env].
    The extracted [ConstExpr] is still existentially quantified, exactly as
    [const_ok] leaves it: what matters here is that nothing mentions [Env]. *)
Definition spec_const_expr_ok (gts : list global_type) (nimp : Z)
                              (expected : types_ValueType_t)
                              (e : types_ConstExpr_t) : Prop :=
  match e with
  | Types_ConstExpr_I32 _ => expected = Types_ValueType_I32
  | Types_ConstExpr_I64 _ => expected = Types_ValueType_I64
  | Types_ConstExpr_F32 _ => expected = Types_ValueType_F32
  | Types_ConstExpr_F64 _ => expected = Types_ValueType_F64
  | Types_ConstExpr_GlobalGet x =>
      exists gt,
        List.nth_error gts (Z.to_nat (to_Z x)) = Some gt
        /\ tg_mut gt = MUT_const
        /\ tg_t gt = translate_vt_v expected
        /\ to_Z x < nimp
  end.

Definition spec_const_ok (gts : list global_type) (nimp : Z)
                         (t : value_type) (e : expr) : Prop :=
  exists ce vt,
    e = [translate_const_expr ce]
    /\ translate_vt_v vt = t
    /\ spec_const_expr_ok gts nimp vt ce.

Definition spec_importdesc_wasm10 (tfs : list function_type)
                                  (d : module_import_desc) : Prop :=
  match d with
  | MID_func x => (N.to_nat x < List.length tfs)%nat
  | MID_table t => tabletype_valid t = true
  | MID_mem m => memtype_valid m = true
  | MID_global _ => True
  end.

Definition spec_exportdesc_wasm10 (es : env_secs)
                                  (d : module_export_desc) : Prop :=
  match d with
  | MED_func x => (N.to_nat x < List.length (all_funcs es))%nat
  | MED_table x => (N.to_nat x < List.length (all_tabtypes es))%nat
  | MED_mem x => (N.to_nat x < List.length (all_memtypes es))%nat
  | MED_global x => (N.to_nat x < List.length (all_globtypes es))%nat
  end.

Definition spec_nimp_globals (es : env_secs) : Z :=
  Z.of_nat (List.length (spec_imported_globals (es_imps es))).

Definition spec_element_wasm10 (es : env_secs) (el : module_element) : Prop :=
  match el.(modelem_mode) with
  | ME_active x e =>
      (N.to_nat x < List.length (all_tabtypes es))%nat
      /\ spec_const_ok (spec_imported_globals (es_imps es))
           (spec_nimp_globals es) (T_num T_i32) e
  | _ => False
  end
  /\ List.Forall (fun ie => exists x, ie = [BI_ref_func x]
                                      /\ (N.to_nat x
                                          < List.length (all_funcs es))%nat)
       el.(modelem_init).

Definition spec_data_wasm10 (es : env_secs) (d : module_data) : Prop :=
  match d.(moddata_mode) with
  | MD_active x e =>
      (N.to_nat x < List.length (all_memtypes es))%nat
      /\ spec_const_ok (spec_imported_globals (es_imps es))
           (spec_nimp_globals es) (T_num T_i32) e
  | _ => False
  end.

(* ================================================================== *)
(** ** From [env_at] to the condition the section's lemma wants        *)
(* ================================================================== *)

Lemma translate_mut_const : forall m, translate_mut m = MUT_const ->
  m = Types_Mut_Const.
Proof. intros [|]; [reflexivity | discriminate]. Qed.

(** An initialiser may only name an *imported* global, so the list its index
    resolves against is a prefix of whatever the environment holds by then, and
    that is what makes one statement serve line 6, line 9 and the tail alike. *)
Lemma nth_error_app_lt : forall A (l m : list A) i,
  (i < List.length l)%nat -> List.nth_error (l ++ m) i = List.nth_error l i.
Proof.
  intros A l. induction l as [|a l IH]; intros m [|i] Hlt; cbn in Hlt |- *;
    solve [ lia | reflexivity | apply IH; lia ].
Qed.

Lemma const_expr_ok_of_prefix : forall env gts more nimp vt ce,
  List.map translate_globaltype (vec_list env.(env_Env_global_types))
    = gts ++ more ->
  to_Z env.(env_Env_num_imported_globals) = nimp ->
  Z.of_nat (List.length gts) = nimp ->
  spec_const_expr_ok gts nimp vt ce -> const_expr_ok env vt ce.
Proof.
  intros env gts more nimp vt ce Hg Hn Hlen H. destruct ce as [z|z|b|b|x];
    try exact H.
  cbn [spec_const_expr_ok] in H. destruct H as [gt [Hnth [Hmut [Hty Hlt]]]].
  assert (Hpre : List.nth_error (gts ++ more) (Z.to_nat (to_Z x)) = Some gt)
    by (rewrite nth_error_app_lt;
        [ exact Hnth
        | pose proof (u32_nonneg x); apply (proj2 (Nat2Z.inj_lt _ _));
          rewrite Z2Nat.id by lia; lia ]).
  rewrite <- Hg in Hpre.
  destruct (map_nth_error_inv _ _ _ _ _ _ Hpre) as [g [Hg' Heq]].
  exists g. split; [exact Hg'|].
  rewrite <- Heq in Hmut, Hty.
  cbn [translate_globaltype tg_mut tg_t] in Hmut, Hty.
  split; [apply translate_mut_const; exact Hmut|].
  split; [apply translate_vt_v_inj; exact Hty | rewrite Hn; exact Hlt].
Qed.

Lemma const_ok_of_prefix : forall env gts more nimp t e,
  List.map translate_globaltype (vec_list env.(env_Env_global_types))
    = gts ++ more ->
  to_Z env.(env_Env_num_imported_globals) = nimp ->
  Z.of_nat (List.length gts) = nimp ->
  spec_const_ok gts nimp t e -> const_ok env t e.
Proof.
  intros env gts more nimp t e Hg Hn Hlen [ce [vt [He [Ht Hok]]]].
  exists ce, vt. split; [exact He|]. split; [exact Ht|].
  exact (const_expr_ok_of_prefix env gts more nimp vt ce Hg Hn Hlen Hok).
Qed.

(** [env_at]'s global clauses in the shape [const_ok] consumes. Every line from
    six on has the same two, since only the import and global sections write
    them. *)
Lemma env_at_globals : forall env es L, 6 <= L -> env_at env es L ->
  List.map translate_globaltype (vec_list env.(env_Env_global_types))
    = all_globtypes es
  /\ to_Z env.(env_Env_num_imported_globals) = spec_nimp_globals es.
Proof.
  intros env es L HL H.
  destruct H as [_ [_ [_ [_ [_ [_ [Hg [_ [_ [_ [_ Hn]]]]]]]]]]].
  rewrite (at_globtypes_full es L HL) in Hg.
  rewrite (at_imps_full es L (ltac:(lia))) in Hn.
  split; [exact Hg | exact Hn].
Qed.

(** Every [const_ok] in the module, from one clause of the invariant. *)
Lemma env_at_const_ok : forall env es L t e,
  2 <= L -> env_at env es L ->
  spec_const_ok (spec_imported_globals (es_imps es)) (spec_nimp_globals es) t e ->
  const_ok env t e.
Proof.
  intros env es L t e HL H Hs.
  destruct H as [_ [_ [_ [_ [_ [_ [Hg [_ [_ [_ [_ Hn]]]]]]]]]]].
  rewrite (at_imps_full es L HL) in Hn.
  unfold at_globtypes in Hg. rewrite (at_imps_full es L HL) in Hg.
  exact (const_ok_of_prefix env _ (List.map modglob_type (at_globs es L))
           (spec_nimp_globals es) t e Hg Hn (ltac:(reflexivity)) Hs).
Qed.

Lemma functype_wasm10_translate : forall ft,
  functype_wasm10 (translate_functype ft) -> Module_Sound.ft_wasm10 ft.
Proof.
  intros ft H. unfold functype_wasm10, translate_functype in H.
  unfold Module_Sound.ft_wasm10. rewrite <- List.map_length with (f := translate_vt_v).
  exact H.
Qed.

Lemma env_at_types_wasm10 : forall env es L,
  List.Forall functype_wasm10 (at_types es L) ->
  env_at env es L -> Module_Sound.types_wasm10 env.
Proof.
  intros env es L Hall H ft Hin.
  apply functype_wasm10_translate.
  rewrite List.Forall_forall in Hall. apply Hall.
  rewrite <- (proj1 H). apply List.in_map. exact Hin.
Qed.

Lemma forall_spec_resolve : forall (P : function_type -> Prop) tfs xs,
  List.Forall P tfs -> List.Forall P (spec_resolve tfs xs).
Proof.
  intros P tfs xs Hall. induction xs as [|x xs IH]; [apply List.Forall_nil|].
  cbn [spec_resolve List.flat_map].
  destruct (List.nth_error tfs (N.to_nat x)) as [ft|] eqn:Hn; [|exact IH].
  apply List.Forall_cons; [|exact IH].
  rewrite List.Forall_forall in Hall. apply Hall.
  exact (List.nth_error_In _ _ Hn).
Qed.

Lemma env_at_funcs_wasm10 : forall env es L,
  3 <= L ->
  List.Forall functype_wasm10 (es_types es) ->
  env_at env es L -> funcs_wasm10 env.
Proof.
  intros env es L HL Hall H ft Hin.
  apply functype_wasm10_translate.
  destruct H as [_ [_ [_ [Hf _]]]]. rewrite (at_funcs_full es L HL) in Hf.
  assert (Hr : List.Forall functype_wasm10 (all_funcs es))
    by (unfold all_funcs; apply forall_spec_resolve; exact Hall).
  rewrite List.Forall_forall in Hr. apply Hr.
  rewrite <- Hf. apply List.in_map. exact Hin.
Qed.

(** Lines 2 and 3 want the type index space's length and nothing else. *)
Lemma env_at_typeidx : forall env es L x,
  1 <= L ->
  (N.to_nat x < List.length (es_types es))%nat ->
  env_at env es L -> typeidx_in_range env x.
Proof.
  intros env es L x HL Hlt H. unfold typeidx_in_range.
  rewrite (map_length_eq _ _ _ _ _ (proj1 H)).
  rewrite (at_types_full es L HL). exact Hlt.
Qed.

Lemma env_at_importdesc : forall env es L d,
  1 <= L ->
  spec_importdesc_wasm10 (es_types es) d ->
  env_at env es L -> importdesc_wasm10 env d.
Proof.
  intros env es L d HL Hd H. destruct d as [x|t|m|g]; try exact Hd.
  exact (env_at_typeidx env es L x HL Hd H).
Qed.

(** The table and memory rooms. [env_at] pins the current length exactly, so
    the bound the loop has to carry is the module's own total. *)
Lemma env_at_table_len : forall env es L,
  4 <= L ->
  env_at env es L ->
  List.length (vec_list env.(env_Env_table_types))
    = List.length (all_tabtypes es).
Proof.
  intros env es L HL H.
  destruct H as [_ [_ [_ [_ [Ht _]]]]]. rewrite (at_tabtypes_full es L HL) in Ht.
  apply (map_length_eq _ _ _ _ _ Ht).
Qed.

Lemma env_at_mem_len : forall env es L,
  5 <= L ->
  env_at env es L ->
  List.length (vec_list env.(env_Env_mem_types))
    = List.length (all_memtypes es).
Proof.
  intros env es L HL H.
  destruct H as [_ [_ [_ [_ [_ [Hm _]]]]]].
  rewrite (at_memtypes_full es L HL) in Hm.
  apply (map_length_eq _ _ _ _ _ Hm).
Qed.

Lemma env_at_func_len : forall env es L,
  3 <= L ->
  env_at env es L ->
  List.length (vec_list env.(env_Env_func_types)) = List.length (all_funcs es).
Proof.
  intros env es L HL H.
  destruct H as [_ [_ [_ [Hf _]]]]. rewrite (at_funcs_full es L HL) in Hf.
  apply (map_length_eq _ _ _ _ _ Hf).
Qed.

Lemma env_at_globtype_len : forall env es L,
  6 <= L ->
  env_at env es L ->
  List.length (vec_list env.(env_Env_global_types))
    = List.length (all_globtypes es).
Proof.
  intros env es L HL H.
  apply (map_length_eq _ _ _ _ _ (proj1 (env_at_globals env es L HL H))).
Qed.

(** Line 7's uniqueness check. Before the export section runs the environment
    has no exports, so [exports_fresh]'s second clause is vacuous and what is
    left is a statement about the module. *)
Lemma env_at_exports_fresh : forall env es L vs,
  L < 7 ->
  List.NoDup (List.map (fun e => name_bytes e.(modexp_name)) vs) ->
  env_at env es L -> exports_fresh env vs.
Proof.
  intros env es L vs HL Hnd H. split; [exact Hnd|].
  destruct H as [_ [_ [_ [_ [_ [_ [_ [_ [He _]]]]]]]]].
  unfold at_exps, upto in He.
  rewrite (proj2 (Z.leb_gt 7 L) (ltac:(lia))) in He.
  rewrite (map_eq_nil_inv _ _ _ _ He). intros e0 [].
Qed.

Lemma env_at_exportdesc : forall env es L d,
  6 <= L ->
  spec_exportdesc_wasm10 es d ->
  env_at env es L -> exportdesc_wasm10 env d.
Proof.
  intros env es L d HL Hd H. destruct d as [x|x|x|x]; cbn [exportdesc_wasm10].
  - rewrite (env_at_func_len env es L (ltac:(lia)) H). exact Hd.
  - rewrite (env_at_table_len env es L (ltac:(lia)) H). exact Hd.
  - rewrite (env_at_mem_len env es L (ltac:(lia)) H). exact Hd.
  - rewrite (env_at_globtype_len env es L HL H). exact Hd.
Qed.

(** Spec 3.4.13's start function, whose type has to be [[] -> []] on the nose.
    That is the one place a condition needs the entry rather than the length. *)
Lemma env_at_start : forall env es L s,
  3 <= L ->
  List.nth_error (all_funcs es) (N.to_nat s.(modstart_func)) = Some (Tf [] []) ->
  env_at env es L -> start_wasm10 env s.
Proof.
  intros env es L s HL Hnth H.
  destruct H as [_ [_ [_ [Hf _]]]]. rewrite (at_funcs_full es L HL) in Hf.
  rewrite <- Hf in Hnth.
  destruct (map_nth_error_inv _ _ _ _ _ _ Hnth) as [ft [Hft Heq]].
  exists ft. split; [exact Hft|].
  unfold translate_functype in Heq. injection Heq as Hp Hr.
  split; [exact (map_eq_nil_inv _ _ _ _ Hp) | exact (map_eq_nil_inv _ _ _ _ Hr)].
Qed.

Lemma env_at_element : forall env es L el,
  6 <= L ->
  spec_element_wasm10 es el ->
  env_at env es L -> element_wasm10 env el.
Proof.
  intros env es L el HL Hspec H.
  unfold spec_element_wasm10 in Hspec. destruct Hspec as [Hmode Hinit].
  unfold element_wasm10. split; [|split].
  - destruct el.(modelem_mode) as [|x e|]; [exact Hmode| |exact Hmode].
    rewrite (env_at_table_len env es L (ltac:(lia)) H). exact (proj1 Hmode).
  - destruct el.(modelem_mode) as [|x e|]; [exact Hmode| |exact Hmode].
    exact (env_at_const_ok env es L _ _ (ltac:(lia)) H (proj2 Hmode)).
  - revert Hinit. apply List.Forall_impl. intros ie [x [-> Hx]].
    exists x. split; [reflexivity|]. unfold funcidx_in_range.
    rewrite (env_at_func_len env es L (ltac:(lia)) H). exact Hx.
Qed.

Lemma env_at_data : forall env es L d,
  6 <= L ->
  spec_data_wasm10 es d ->
  env_at env es L -> data_wasm10 env d.
Proof.
  intros env es L d HL Hd H.
  unfold spec_data_wasm10 in Hd. unfold data_wasm10. split.
  - destruct d.(moddata_mode) as [|x e]; [exact Hd|].
    rewrite (env_at_mem_len env es L (ltac:(lia)) H). exact (proj1 Hd).
  - destruct d.(moddata_mode) as [|x e]; [exact Hd|].
    exact (env_at_const_ok env es L _ _ (ltac:(lia)) H (proj2 Hd)).
Qed.

(** The import section's four index-space contributions, translated. Each is
    the same [flat_map] on both sides, so the [map] commutes with it. *)
Lemma spec_imported_tables_map : forall imps,
  spec_imported_tables (List.map translate_import imps)
    = List.map translate_tabletype (imported_tables imps).
Proof.
  unfold spec_imported_tables, imported_tables.
  induction imps as [|im imps IH]; [reflexivity|].
  destruct im as [md nm [x|t|m|g]];
    cbn [List.map List.flat_map List.app
         translate_import translate_importdesc imp_desc env_Import_desc];
    rewrite IH; reflexivity.
Qed.

Lemma spec_imported_mems_map : forall imps,
  spec_imported_mems (List.map translate_import imps)
    = List.map translate_memtype (imported_mems imps).
Proof.
  unfold spec_imported_mems, imported_mems.
  induction imps as [|im imps IH]; [reflexivity|].
  destruct im as [md nm [x|t|m|g]];
    cbn [List.map List.flat_map List.app
         translate_import translate_importdesc imp_desc env_Import_desc];
    rewrite IH; reflexivity.
Qed.

Lemma spec_imported_globals_map : forall imps,
  spec_imported_globals (List.map translate_import imps)
    = List.map translate_globaltype (imported_globals imps).
Proof.
  unfold spec_imported_globals, imported_globals.
  induction imps as [|im imps IH]; [reflexivity|].
  destruct im as [md nm [x|t|m|g]];
    cbn [List.map List.flat_map List.app
         translate_import translate_importdesc imp_desc env_Import_desc];
    rewrite IH; reflexivity.
Qed.

Lemma spec_imported_fidxs_map : forall imps,
  spec_imported_fidxs (List.map translate_import imps)
    = List.map translate_idx (imported_func_idxs imps).
Proof.
  unfold spec_imported_fidxs, imported_func_idxs.
  induction imps as [|im imps IH]; [reflexivity|].
  destruct im as [md nm [x|t|m|g]];
    cbn [List.map List.flat_map List.app
         translate_import translate_importdesc imp_desc env_Import_desc];
    rewrite IH; reflexivity.
Qed.


Lemma spec_resolve_nil : forall tfs, spec_resolve tfs [] = [].
Proof. reflexivity. Qed.

Lemma spec_resolve_app : forall tfs xs ys,
  spec_resolve tfs (xs ++ ys) = spec_resolve tfs xs ++ spec_resolve tfs ys.
Proof. intros tfs xs ys. apply List.flat_map_app. Qed.

Lemma spec_imported_tables_nil : spec_imported_tables [] = [].
Proof. reflexivity. Qed.
Lemma spec_imported_mems_nil : spec_imported_mems [] = [].
Proof. reflexivity. Qed.
Lemma spec_imported_globals_nil : spec_imported_globals [] = [].
Proof. reflexivity. Qed.
Lemma spec_imported_fidxs_nil : spec_imported_fidxs [] = [].
Proof. reflexivity. Qed.

Lemma modtab_type_translate : forall tts,
  List.map modtab_type (List.map translate_table tts)
    = List.map translate_tabletype tts.
Proof.
  induction tts as [|t tts IH]; [reflexivity|].
  cbn [List.map translate_table modtab_type]. rewrite IH. reflexivity.
Qed.

Lemma modmem_type_translate : forall mts,
  List.map modmem_type (List.map translate_mem mts)
    = List.map translate_memtype mts.
Proof.
  induction mts as [|m mts IH]; [reflexivity|].
  cbn [List.map translate_mem modmem_type]. rewrite IH. reflexivity.
Qed.

Lemma modglob_type_translate : forall gls,
  List.map modglob_type (List.map translate_global gls)
    = List.map translate_globaltype
        (List.map (fun g => g.(env_Global_gtype)) gls).
Proof.
  induction gls as [|g gls IH]; [reflexivity|].
  cbn [List.map translate_global modglob_type]. rewrite IH. reflexivity.
Qed.

(* ================================================================== *)
(** ** Carrying [env_at] across one section                            *)
(* ================================================================== *)

(** Each step is the same two moves: the field the line wrote is the old one
    with the section's list appended, and every other field is a projection of
    the record the section rebuilt, which closes by [reflexivity]. The [at_*]
    readings that do not mention the line's field are the same on both sides,
    and at a literal [L] that is a computation. *)
Ltac at_cbn :=
  cbv beta delta [at_funcs at_tabtypes at_memtypes at_globtypes at_types
                  at_imps at_tidxs at_tabs at_mems at_globs at_exps at_start
                  at_els upto];
  cbn [Z.leb Z.compare Pos.compare Pos.compare_cont].

(** The empty readings a low [L] leaves behind, cleared away so that [rewrite]
    can see the shape underneath. *)
Ltac at_simpl :=
  at_cbn;
  repeat first [ rewrite spec_imported_tables_nil
               | rewrite spec_imported_mems_nil
               | rewrite spec_imported_globals_nil
               | rewrite spec_imported_fidxs_nil
               | rewrite spec_resolve_nil
               | rewrite app_nil_r | rewrite app_nil_l
               | progress cbn [List.map List.length] ].

Ltac at_simpl_in H :=
  cbv beta delta [at_funcs at_tabtypes at_memtypes at_globtypes at_types
                  at_imps at_tidxs at_tabs at_mems at_globs at_exps at_start
                  at_els upto] in H;
  cbn [Z.leb Z.compare Pos.compare Pos.compare_cont] in H;
  repeat first [ rewrite spec_imported_tables_nil in H
               | rewrite spec_imported_mems_nil in H
               | rewrite spec_imported_globals_nil in H
               | rewrite spec_imported_fidxs_nil in H
               | rewrite spec_resolve_nil in H
               | rewrite app_nil_r in H | rewrite app_nil_l in H
               | progress cbn [List.map List.length] in H ].

Ltac env_at_open Hat :=
  destruct Hat as [E1 [E2 [E3 [E4 [E5 [E6 [E7 [E8 [E9 [E10 [E11 E12]]]]]]]]]]];
  at_simpl_in E1; at_simpl_in E2; at_simpl_in E3; at_simpl_in E4;
  at_simpl_in E5; at_simpl_in E6; at_simpl_in E7; at_simpl_in E8;
  at_simpl_in E9; at_simpl_in E10; at_simpl_in E11; at_simpl_in E12.

(** A field the section left alone: the record it rebuilt is a literal, so the
    projection reduces and the old clause is the new one. *)
Ltac at_keep Heq H := rewrite Heq; env_proj; exact H.

Lemma env_at_step_types : forall env env2 es tfs,
  env_at env es 0 ->
  vec_list env2.(env_Env_types) = vec_list env.(env_Env_types) ++ tfs ->
  env2 = env_with_types env env2.(env_Env_types) ->
  List.map translate_functype tfs = es_types es ->
  env_at env2 es 1.
Proof.
  intros env env2 es tfs Hat Hlist Heq Hid. env_at_open Hat.
  rewrite (map_eq_nil_inv _ _ _ _ E1) in Hlist. cbn [List.app] in Hlist.
  unfold env_at. at_simpl. repeat split.
  - rewrite Hlist. exact Hid.
  - at_keep Heq E2.
  - at_keep Heq E3.
  - at_keep Heq E4.
  - at_keep Heq E5.
  - at_keep Heq E6.
  - at_keep Heq E7.
  - at_keep Heq E8.
  - at_keep Heq E9.
  - at_keep Heq E10.
  - at_keep Heq E11.
  - at_keep Heq E12.
Qed.

Lemma env_at_step_imports : forall env env2 es imps,
  env_at env es 1 ->
  vec_list env2.(env_Env_imports) = vec_list env.(env_Env_imports) ++ imps ->
  env_imported env env2 ->
  import_spaces env env2 imps ->
  List.map translate_import imps = es_imps es ->
  env_at env2 es 2.
Proof.
  intros env env2 es imps Hat Hlist Heq Hsp Hid. env_at_open Hat.
  destruct Hsp as [Ht [Hm [Hg [Hty [[Hfs _] Hn]]]]].
  unfold env_imported in Heq.
  rewrite (map_eq_nil_inv _ _ _ _ E2) in Hlist. cbn [List.app] in Hlist.
  unfold env_at. at_simpl. repeat split.
  - rewrite Hty. exact E1.
  - rewrite Hlist. exact Hid.
  - at_keep Heq E3.
  - rewrite Hfs. rewrite E4. cbn [List.app].
    rewrite resolved_types_spec. rewrite E1.
    rewrite <- spec_imported_fidxs_map. rewrite Hid. reflexivity.
  - rewrite Ht. rewrite List.map_app. rewrite E5. cbn [List.app].
    rewrite <- spec_imported_tables_map. rewrite Hid. reflexivity.
  - rewrite Hm. rewrite List.map_app. rewrite E6. cbn [List.app].
    rewrite <- spec_imported_mems_map. rewrite Hid. reflexivity.
  - rewrite Hg. rewrite List.map_app. rewrite E7. cbn [List.app].
    rewrite <- spec_imported_globals_map. rewrite Hid. reflexivity.
  - at_keep Heq E8.
  - at_keep Heq E9.
  - at_keep Heq E10.
  - at_keep Heq E11.
  - rewrite Hn. rewrite E12. rewrite <- Hid.
    rewrite spec_imported_globals_map. rewrite List.map_length. lia.
Qed.

Lemma env_at_step_funcs : forall env env2 es xs,
  env_at env es 2 ->
  vec_list env2.(env_Env_func_type_indices)
    = vec_list env.(env_Env_func_type_indices) ++ xs ->
  env2 = env_with_func env env2.(env_Env_func_types)
                       env2.(env_Env_func_type_indices) ->
  func_space env env2 xs ->
  List.map translate_idx xs = es_tidxs es ->
  env_at env2 es 3.
Proof.
  intros env env2 es xs Hat Hlist Heq [Hfs _] Hid. env_at_open Hat.
  rewrite (map_eq_nil_inv _ _ _ _ E3) in Hlist. cbn [List.app] in Hlist.
  unfold env_at. at_simpl. repeat split.
  - at_keep Heq E1.
  - at_keep Heq E2.
  - rewrite Hlist. exact Hid.
  - rewrite Hfs. rewrite E4. rewrite resolved_types_spec. rewrite E1.
    rewrite Hid. rewrite spec_resolve_app. reflexivity.
  - at_keep Heq E5.
  - at_keep Heq E6.
  - at_keep Heq E7.
  - at_keep Heq E8.
  - at_keep Heq E9.
  - at_keep Heq E10.
  - at_keep Heq E11.
  - at_keep Heq E12.
Qed.

Lemma env_at_step_tables : forall env env2 es tts,
  env_at env es 3 ->
  vec_list env2.(env_Env_table_types)
    = vec_list env.(env_Env_table_types) ++ tts ->
  env2 = env_with_table env env2.(env_Env_table_types) ->
  List.map translate_table tts = es_tabs es ->
  env_at env2 es 4.
Proof.
  intros env env2 es tts Hat Hlist Heq Hid. env_at_open Hat.
  unfold env_at. at_simpl. repeat split.
  - at_keep Heq E1.
  - at_keep Heq E2.
  - at_keep Heq E3.
  - at_keep Heq E4.
  - rewrite Hlist. rewrite List.map_app. rewrite E5.
    rewrite <- Hid. rewrite modtab_type_translate. reflexivity.
  - at_keep Heq E6.
  - at_keep Heq E7.
  - at_keep Heq E8.
  - at_keep Heq E9.
  - at_keep Heq E10.
  - at_keep Heq E11.
  - at_keep Heq E12.
Qed.

Lemma env_at_step_mems : forall env env2 es mts,
  env_at env es 4 ->
  vec_list env2.(env_Env_mem_types) = vec_list env.(env_Env_mem_types) ++ mts ->
  env2 = env_with_mem env env2.(env_Env_mem_types) ->
  List.map translate_mem mts = es_mems es ->
  env_at env2 es 5.
Proof.
  intros env env2 es mts Hat Hlist Heq Hid. env_at_open Hat.
  unfold env_at. at_simpl. repeat split.
  - at_keep Heq E1.
  - at_keep Heq E2.
  - at_keep Heq E3.
  - at_keep Heq E4.
  - at_keep Heq E5.
  - rewrite Hlist. rewrite List.map_app. rewrite E6.
    rewrite <- Hid. rewrite modmem_type_translate. reflexivity.
  - at_keep Heq E7.
  - at_keep Heq E8.
  - at_keep Heq E9.
  - at_keep Heq E10.
  - at_keep Heq E11.
  - at_keep Heq E12.
Qed.

Lemma env_at_step_globals : forall env env2 es gls,
  env_at env es 5 ->
  vec_list env2.(env_Env_globals) = vec_list env.(env_Env_globals) ++ gls ->
  env2 = env_with_global env env2.(env_Env_globals)
                             env2.(env_Env_global_types) ->
  vec_list env2.(env_Env_global_types)
    = vec_list env.(env_Env_global_types)
      ++ List.map (fun g => g.(env_Global_gtype)) gls ->
  List.map translate_global gls = es_globs es ->
  env_at env2 es 6.
Proof.
  intros env env2 es gls Hat Hlist Heq Hgts Hid. env_at_open Hat.
  rewrite (map_eq_nil_inv _ _ _ _ E8) in Hlist. cbn [List.app] in Hlist.
  unfold env_at. at_simpl. repeat split.
  - at_keep Heq E1.
  - at_keep Heq E2.
  - at_keep Heq E3.
  - at_keep Heq E4.
  - at_keep Heq E5.
  - at_keep Heq E6.
  - rewrite Hgts. rewrite List.map_app. rewrite E7.
    rewrite <- modglob_type_translate. rewrite Hid. reflexivity.
  - rewrite Hlist. exact Hid.
  - at_keep Heq E9.
  - at_keep Heq E10.
  - at_keep Heq E11.
  - at_keep Heq E12.
Qed.

Lemma env_at_step_exports : forall env env2 es exs,
  env_at env es 6 ->
  vec_list env2.(env_Env_exports) = vec_list env.(env_Env_exports) ++ exs ->
  env2 = env_with_exports env env2.(env_Env_exports) ->
  List.map translate_export exs = es_exps es ->
  env_at env2 es 7.
Proof.
  intros env env2 es exs Hat Hlist Heq Hid. env_at_open Hat.
  rewrite (map_eq_nil_inv _ _ _ _ E9) in Hlist. cbn [List.app] in Hlist.
  unfold env_at. at_simpl. repeat split.
  - at_keep Heq E1.
  - at_keep Heq E2.
  - at_keep Heq E3.
  - at_keep Heq E4.
  - at_keep Heq E5.
  - at_keep Heq E6.
  - at_keep Heq E7.
  - at_keep Heq E8.
  - rewrite Hlist. exact Hid.
  - at_keep Heq E10.
  - at_keep Heq E11.
  - at_keep Heq E12.
Qed.

Lemma env_at_step_start : forall env env2 es,
  env_at env es 7 ->
  env2 = env_with_start env env2.(env_Env_start) ->
  translate_start env2.(env_Env_start) = es_start es ->
  env_at env2 es 8.
Proof.
  intros env env2 es Hat Heq Hid. env_at_open Hat.
  unfold env_at. at_simpl. repeat split.
  - at_keep Heq E1.
  - at_keep Heq E2.
  - at_keep Heq E3.
  - at_keep Heq E4.
  - at_keep Heq E5.
  - at_keep Heq E6.
  - at_keep Heq E7.
  - at_keep Heq E8.
  - at_keep Heq E9.
  - exact Hid.
  - at_keep Heq E11.
  - at_keep Heq E12.
Qed.

Lemma env_at_step_elements : forall env env2 es els,
  env_at env es 8 ->
  vec_list env2.(env_Env_elements) = vec_list env.(env_Env_elements) ++ els ->
  env2 = env_with_elements env env2.(env_Env_elements) ->
  List.map translate_element els = es_els es ->
  env_at env2 es 9.
Proof.
  intros env env2 es els Hat Hlist Heq Hid. env_at_open Hat.
  rewrite (map_eq_nil_inv _ _ _ _ E11) in Hlist. cbn [List.app] in Hlist.
  unfold env_at. at_simpl. repeat split.
  - at_keep Heq E1.
  - at_keep Heq E2.
  - at_keep Heq E3.
  - at_keep Heq E4.
  - at_keep Heq E5.
  - at_keep Heq E6.
  - at_keep Heq E7.
  - at_keep Heq E8.
  - at_keep Heq E9.
  - at_keep Heq E10.
  - rewrite Hlist. exact Hid.
  - at_keep Heq E12.
Qed.

(** The environment the run starts from holds nothing. *)
Lemma env_at_new : forall env0 es, env_Env_new = Ok env0 -> env_at env0 es 0.
Proof.
  intros env0 es H. unfold env_Env_new in H. injection H as <-.
  unfold env_at. at_simpl.
  cbn [vec_list alloc_vec_Vec_new proj1_sig List.map translate_start option_map
       env_Env_types env_Env_imports env_Env_globals env_Env_exports
       env_Env_elements env_Env_start env_Env_func_type_indices
       env_Env_func_types env_Env_table_types env_Env_mem_types
       env_Env_global_types env_Env_num_imported_globals].
  repeat split; reflexivity.
Qed.

(** A line the module does not have moves the invariant on for free: the only
    reading that changes is the one over that line's field, and the field is
    the line's absent value. *)
Lemma env_at_skip_1 : forall env es,
  es_types es = [] -> env_at env es 0 -> env_at env es 1.
Proof.
  intros env es Hnil Hat. env_at_open Hat.
  unfold env_at. at_simpl. rewrite Hnil. repeat split; assumption.
Qed.

Lemma env_at_skip_2 : forall env es,
  es_imps es = [] -> env_at env es 1 -> env_at env es 2.
Proof.
  intros env es Hnil Hat. env_at_open Hat.
  unfold env_at. at_simpl. rewrite Hnil. at_simpl. repeat split; assumption.
Qed.

Lemma env_at_skip_3 : forall env es,
  es_tidxs es = [] -> env_at env es 2 -> env_at env es 3.
Proof.
  intros env es Hnil Hat. env_at_open Hat.
  unfold env_at. at_simpl. rewrite Hnil. at_simpl. repeat split; assumption.
Qed.

Lemma env_at_skip_4 : forall env es,
  es_tabs es = [] -> env_at env es 3 -> env_at env es 4.
Proof.
  intros env es Hnil Hat. env_at_open Hat.
  unfold env_at. at_simpl. rewrite Hnil. at_simpl. repeat split; assumption.
Qed.

Lemma env_at_skip_5 : forall env es,
  es_mems es = [] -> env_at env es 4 -> env_at env es 5.
Proof.
  intros env es Hnil Hat. env_at_open Hat.
  unfold env_at. at_simpl. rewrite Hnil. at_simpl. repeat split; assumption.
Qed.

Lemma env_at_skip_6 : forall env es,
  es_globs es = [] -> env_at env es 5 -> env_at env es 6.
Proof.
  intros env es Hnil Hat. env_at_open Hat.
  unfold env_at. at_simpl. rewrite Hnil. at_simpl. repeat split; assumption.
Qed.

Lemma env_at_skip_7 : forall env es,
  es_exps es = [] -> env_at env es 6 -> env_at env es 7.
Proof.
  intros env es Hnil Hat. env_at_open Hat.
  unfold env_at. at_simpl. rewrite Hnil. repeat split; assumption.
Qed.

Lemma env_at_skip_8 : forall env es,
  es_start es = None -> env_at env es 7 -> env_at env es 8.
Proof.
  intros env es Hnil Hat. env_at_open Hat.
  unfold env_at. at_simpl. rewrite Hnil. repeat split; assumption.
Qed.

Lemma env_at_skip_9 : forall env es,
  es_els es = [] -> env_at env es 8 -> env_at env es 9.
Proof.
  intros env es Hnil Hat. env_at_open Hat.
  unfold env_at. at_simpl. rewrite Hnil. repeat split; assumption.
Qed.

(* ================================================================== *)
(** ** The chain, read on the specification's side                     *)
(* ================================================================== *)

(** Spec 5.5.16's environment lines as a statement about the nine values, from
    a cursor down to the place [validate_code] takes over. [Module_Sound]'s
    [chain_from] is the same shape with the extraction's values in it; this one
    has the module's, because completeness walks the chain rather than
    producing it. *)
Definition spec_chain_tail (es : env_secs) (bs rest : list Z) : Prop :=
  repr_customs bs rest.

Definition spec_chain_9 (es : env_secs) (bs rest : list Z) : Prop :=
  exists p, repr_padded 9 (repr_vec repr_elem) [] bs (es_els es) p
            /\ spec_chain_tail es p rest.

Definition spec_chain_8 (es : env_secs) (bs rest : list Z) : Prop :=
  exists p, repr_padded 8 repr_start None bs (es_start es) p
            /\ spec_chain_9 es p rest.

Definition spec_chain_7 (es : env_secs) (bs rest : list Z) : Prop :=
  exists p, repr_padded 7 (repr_vec repr_export) [] bs (es_exps es) p
            /\ spec_chain_8 es p rest.

Definition spec_chain_6 (es : env_secs) (bs rest : list Z) : Prop :=
  exists p, repr_padded 6 (repr_vec repr_global) [] bs (es_globs es) p
            /\ spec_chain_7 es p rest.

Definition spec_chain_5 (es : env_secs) (bs rest : list Z) : Prop :=
  exists p, repr_padded 5 (repr_vec repr_mem) [] bs (es_mems es) p
            /\ spec_chain_6 es p rest.

Definition spec_chain_4 (es : env_secs) (bs rest : list Z) : Prop :=
  exists p, repr_padded 4 (repr_vec repr_table) [] bs (es_tabs es) p
            /\ spec_chain_5 es p rest.

Definition spec_chain_3 (es : env_secs) (bs rest : list Z) : Prop :=
  exists p, repr_padded 3 (repr_vec repr_idx) [] bs (es_tidxs es) p
            /\ spec_chain_4 es p rest.

Definition spec_chain_2 (es : env_secs) (bs rest : list Z) : Prop :=
  exists p, repr_padded 2 (repr_vec repr_import) [] bs (es_imps es) p
            /\ spec_chain_3 es p rest.

Definition spec_chain_1 (es : env_secs) (bs rest : list Z) : Prop :=
  exists p, repr_padded 1 (repr_vec repr_functype) [] bs (es_types es) p
            /\ spec_chain_2 es p rest.

Definition spec_chain_from (L : Z) (es : env_secs) (bs rest : list Z) : Prop :=
  if Z.eqb L 0 then spec_chain_1 es bs rest
  else if Z.eqb L 1 then spec_chain_2 es bs rest
  else if Z.eqb L 2 then spec_chain_3 es bs rest
  else if Z.eqb L 3 then spec_chain_4 es bs rest
  else if Z.eqb L 4 then spec_chain_5 es bs rest
  else if Z.eqb L 5 then spec_chain_6 es bs rest
  else if Z.eqb L 6 then spec_chain_7 es bs rest
  else if Z.eqb L 7 then spec_chain_8 es bs rest
  else if Z.eqb L 8 then spec_chain_9 es bs rest
  else spec_chain_tail es bs rest.

(** *** Taking a [customs*] run apart

    Two facts, and every step of the chain is one of them: a custom section the
    loop consumed is the head of the run, and a cursor that does not begin with
    a custom section's id is where the run ended. *)
Lemma customs_here : forall bs m mid,
  repr_section 0 repr_custom bs tt m ->
  repr_customs bs mid -> repr_customs m mid.
Proof.
  intros bs m mid Hs Hc.
  destruct (repr_customs_inv _ _ Hc) as [[Hnb Hbs]|[m' [Hs' Hc']]].
  - exfalso. apply Hnb.
    destruct (repr_section_inv _ _ _ _ _ _ Hs) as [p0 [sz [content [Hbs' _]]]].
    exists p0. exact Hbs'.
  - destruct (repr_section_det _ 0 repr_custom repr_custom_det _ _ _ _ _ Hs Hs')
      as [_ <-]. exact Hc'.
Qed.

Lemma customs_none : forall bs mid,
  ~ begins_with 0 bs -> repr_customs bs mid -> mid = bs.
Proof.
  intros bs mid Hnb Hc.
  destruct (repr_customs_inv _ _ Hc) as [[_ Hbs]|[m' [Hs' _]]]; [exact Hbs|].
  exfalso. apply Hnb.
  destruct (repr_section_inv _ _ _ _ _ _ Hs') as [p0 [sz [content [Hbs' _]]]].
  exists p0. exact Hbs'.
Qed.

Lemma repr_padded_custom : forall A id (R : list Z -> A -> list Z -> Prop)
                                  absent bs m x rest,
  repr_section 0 repr_custom bs tt m ->
  repr_padded id R absent bs x rest -> repr_padded id R absent m x rest.
Proof.
  intros A id R absent bs m x rest Hs [mid [Hc Ho]].
  exists mid. split; [exact (customs_here bs m mid Hs Hc) | exact Ho].
Qed.

(** The section-level step: with no custom section here, the line is either the
    section itself or nothing at all. *)
Lemma repr_padded_split : forall A id (R : list Z -> A -> list Z -> Prop)
                                 absent bs x rest,
  ~ begins_with 0 bs ->
  repr_padded id R absent bs x rest ->
  repr_section id R bs x rest
  \/ (~ begins_with id bs /\ x = absent /\ rest = bs).
Proof.
  intros A id R absent bs x rest Hnb [mid [Hc Ho]].
  rewrite (customs_none _ _ Hnb Hc) in Ho.
  exact (repr_optsec_inv _ _ _ _ _ _ _ Ho).
Qed.

(** *** Prepending a custom section

    A custom section the loop consumed is the head of the [customs*] run of
    whatever line comes next, whichever that is. *)
Lemma spec_chain_tail_custom : forall es bs m rest,
  repr_section 0 repr_custom bs tt m ->
  spec_chain_tail es bs rest -> spec_chain_tail es m rest.
Proof. intros es bs m rest Hs Hc. exact (customs_here _ _ _ Hs Hc). Qed.

Lemma spec_chain_1_custom : forall es bs m rest,
  repr_section 0 repr_custom bs tt m ->
  spec_chain_1 es bs rest -> spec_chain_1 es m rest.
Proof.
  intros es bs m rest Hs [p [Hp Hrest]]. exists p.
  split; [exact (repr_padded_custom _ _ _ _ _ _ _ _ Hs Hp) | exact Hrest].
Qed.

Lemma spec_chain_2_custom : forall es bs m rest,
  repr_section 0 repr_custom bs tt m ->
  spec_chain_2 es bs rest -> spec_chain_2 es m rest.
Proof.
  intros es bs m rest Hs [p [Hp Hrest]]. exists p.
  split; [exact (repr_padded_custom _ _ _ _ _ _ _ _ Hs Hp) | exact Hrest].
Qed.

Lemma spec_chain_3_custom : forall es bs m rest,
  repr_section 0 repr_custom bs tt m ->
  spec_chain_3 es bs rest -> spec_chain_3 es m rest.
Proof.
  intros es bs m rest Hs [p [Hp Hrest]]. exists p.
  split; [exact (repr_padded_custom _ _ _ _ _ _ _ _ Hs Hp) | exact Hrest].
Qed.

Lemma spec_chain_4_custom : forall es bs m rest,
  repr_section 0 repr_custom bs tt m ->
  spec_chain_4 es bs rest -> spec_chain_4 es m rest.
Proof.
  intros es bs m rest Hs [p [Hp Hrest]]. exists p.
  split; [exact (repr_padded_custom _ _ _ _ _ _ _ _ Hs Hp) | exact Hrest].
Qed.

Lemma spec_chain_5_custom : forall es bs m rest,
  repr_section 0 repr_custom bs tt m ->
  spec_chain_5 es bs rest -> spec_chain_5 es m rest.
Proof.
  intros es bs m rest Hs [p [Hp Hrest]]. exists p.
  split; [exact (repr_padded_custom _ _ _ _ _ _ _ _ Hs Hp) | exact Hrest].
Qed.

Lemma spec_chain_6_custom : forall es bs m rest,
  repr_section 0 repr_custom bs tt m ->
  spec_chain_6 es bs rest -> spec_chain_6 es m rest.
Proof.
  intros es bs m rest Hs [p [Hp Hrest]]. exists p.
  split; [exact (repr_padded_custom _ _ _ _ _ _ _ _ Hs Hp) | exact Hrest].
Qed.

Lemma spec_chain_7_custom : forall es bs m rest,
  repr_section 0 repr_custom bs tt m ->
  spec_chain_7 es bs rest -> spec_chain_7 es m rest.
Proof.
  intros es bs m rest Hs [p [Hp Hrest]]. exists p.
  split; [exact (repr_padded_custom _ _ _ _ _ _ _ _ Hs Hp) | exact Hrest].
Qed.

Lemma spec_chain_8_custom : forall es bs m rest,
  repr_section 0 repr_custom bs tt m ->
  spec_chain_8 es bs rest -> spec_chain_8 es m rest.
Proof.
  intros es bs m rest Hs [p [Hp Hrest]]. exists p.
  split; [exact (repr_padded_custom _ _ _ _ _ _ _ _ Hs Hp) | exact Hrest].
Qed.

Lemma spec_chain_9_custom : forall es bs m rest,
  repr_section 0 repr_custom bs tt m ->
  spec_chain_9 es bs rest -> spec_chain_9 es m rest.
Proof.
  intros es bs m rest Hs [p [Hp Hrest]]. exists p.
  split; [exact (repr_padded_custom _ _ _ _ _ _ _ _ Hs Hp) | exact Hrest].
Qed.

Lemma spec_chain_custom : forall L es bs m rest,
  repr_section 0 repr_custom bs tt m ->
  spec_chain_from L es bs rest -> spec_chain_from L es m rest.
Proof.
  intros L es bs m rest Hs H. unfold spec_chain_from in H |- *.
  repeat (match goal with
          | [ |- context [Z.eqb L ?k] ] =>
              let E := fresh "E" in
              destruct (Z.eqb L k) eqn:E; cbn beta iota in H |- *
          end).
  all: first [ apply (spec_chain_1_custom _ bs) | apply (spec_chain_2_custom _ bs)
             | apply (spec_chain_3_custom _ bs) | apply (spec_chain_4_custom _ bs)
             | apply (spec_chain_5_custom _ bs) | apply (spec_chain_6_custom _ bs)
             | apply (spec_chain_7_custom _ bs) | apply (spec_chain_8_custom _ bs)
             | apply (spec_chain_9_custom _ bs) | apply (spec_chain_tail_custom _ bs) ];
       solve [ exact Hs | exact H ].
Qed.

(** *** The line at the cursor, present or absent

    One per line, and it is what both the skip and the read use: with no custom
    section here the [repr_optsec] has to decide, and the byte the header
    reports says which way. *)
Lemma spec_chain_1_split : forall es bs rest,
  ~ begins_with 0 bs ->
  spec_chain_1 es bs rest ->
  (exists mid, repr_section 1 (repr_vec repr_functype) bs (es_types es) mid /\ spec_chain_2 es mid rest)
  \/ (~ begins_with 1 bs /\ es_types es = [] /\ spec_chain_2 es bs rest).
Proof.
  intros es bs rest H0 [p [Hp Hrest]].
  destruct (repr_padded_split _ _ _ _ _ _ _ H0 Hp) as [Hpres|[Hnb [Hx Hr]]].
  - left. exists p. split; [exact Hpres | exact Hrest].
  - right. split; [exact Hnb|]. split; [exact Hx|]. rewrite <- Hr. exact Hrest.
Qed.

Lemma spec_chain_2_split : forall es bs rest,
  ~ begins_with 0 bs ->
  spec_chain_2 es bs rest ->
  (exists mid, repr_section 2 (repr_vec repr_import) bs (es_imps es) mid /\ spec_chain_3 es mid rest)
  \/ (~ begins_with 2 bs /\ es_imps es = [] /\ spec_chain_3 es bs rest).
Proof.
  intros es bs rest H0 [p [Hp Hrest]].
  destruct (repr_padded_split _ _ _ _ _ _ _ H0 Hp) as [Hpres|[Hnb [Hx Hr]]].
  - left. exists p. split; [exact Hpres | exact Hrest].
  - right. split; [exact Hnb|]. split; [exact Hx|]. rewrite <- Hr. exact Hrest.
Qed.

Lemma spec_chain_3_split : forall es bs rest,
  ~ begins_with 0 bs ->
  spec_chain_3 es bs rest ->
  (exists mid, repr_section 3 (repr_vec repr_idx) bs (es_tidxs es) mid /\ spec_chain_4 es mid rest)
  \/ (~ begins_with 3 bs /\ es_tidxs es = [] /\ spec_chain_4 es bs rest).
Proof.
  intros es bs rest H0 [p [Hp Hrest]].
  destruct (repr_padded_split _ _ _ _ _ _ _ H0 Hp) as [Hpres|[Hnb [Hx Hr]]].
  - left. exists p. split; [exact Hpres | exact Hrest].
  - right. split; [exact Hnb|]. split; [exact Hx|]. rewrite <- Hr. exact Hrest.
Qed.

Lemma spec_chain_4_split : forall es bs rest,
  ~ begins_with 0 bs ->
  spec_chain_4 es bs rest ->
  (exists mid, repr_section 4 (repr_vec repr_table) bs (es_tabs es) mid /\ spec_chain_5 es mid rest)
  \/ (~ begins_with 4 bs /\ es_tabs es = [] /\ spec_chain_5 es bs rest).
Proof.
  intros es bs rest H0 [p [Hp Hrest]].
  destruct (repr_padded_split _ _ _ _ _ _ _ H0 Hp) as [Hpres|[Hnb [Hx Hr]]].
  - left. exists p. split; [exact Hpres | exact Hrest].
  - right. split; [exact Hnb|]. split; [exact Hx|]. rewrite <- Hr. exact Hrest.
Qed.

Lemma spec_chain_5_split : forall es bs rest,
  ~ begins_with 0 bs ->
  spec_chain_5 es bs rest ->
  (exists mid, repr_section 5 (repr_vec repr_mem) bs (es_mems es) mid /\ spec_chain_6 es mid rest)
  \/ (~ begins_with 5 bs /\ es_mems es = [] /\ spec_chain_6 es bs rest).
Proof.
  intros es bs rest H0 [p [Hp Hrest]].
  destruct (repr_padded_split _ _ _ _ _ _ _ H0 Hp) as [Hpres|[Hnb [Hx Hr]]].
  - left. exists p. split; [exact Hpres | exact Hrest].
  - right. split; [exact Hnb|]. split; [exact Hx|]. rewrite <- Hr. exact Hrest.
Qed.

Lemma spec_chain_6_split : forall es bs rest,
  ~ begins_with 0 bs ->
  spec_chain_6 es bs rest ->
  (exists mid, repr_section 6 (repr_vec repr_global) bs (es_globs es) mid /\ spec_chain_7 es mid rest)
  \/ (~ begins_with 6 bs /\ es_globs es = [] /\ spec_chain_7 es bs rest).
Proof.
  intros es bs rest H0 [p [Hp Hrest]].
  destruct (repr_padded_split _ _ _ _ _ _ _ H0 Hp) as [Hpres|[Hnb [Hx Hr]]].
  - left. exists p. split; [exact Hpres | exact Hrest].
  - right. split; [exact Hnb|]. split; [exact Hx|]. rewrite <- Hr. exact Hrest.
Qed.

Lemma spec_chain_7_split : forall es bs rest,
  ~ begins_with 0 bs ->
  spec_chain_7 es bs rest ->
  (exists mid, repr_section 7 (repr_vec repr_export) bs (es_exps es) mid /\ spec_chain_8 es mid rest)
  \/ (~ begins_with 7 bs /\ es_exps es = [] /\ spec_chain_8 es bs rest).
Proof.
  intros es bs rest H0 [p [Hp Hrest]].
  destruct (repr_padded_split _ _ _ _ _ _ _ H0 Hp) as [Hpres|[Hnb [Hx Hr]]].
  - left. exists p. split; [exact Hpres | exact Hrest].
  - right. split; [exact Hnb|]. split; [exact Hx|]. rewrite <- Hr. exact Hrest.
Qed.

Lemma spec_chain_8_split : forall es bs rest,
  ~ begins_with 0 bs ->
  spec_chain_8 es bs rest ->
  (exists mid, repr_section 8 repr_start bs (es_start es) mid /\ spec_chain_9 es mid rest)
  \/ (~ begins_with 8 bs /\ es_start es = None /\ spec_chain_9 es bs rest).
Proof.
  intros es bs rest H0 [p [Hp Hrest]].
  destruct (repr_padded_split _ _ _ _ _ _ _ H0 Hp) as [Hpres|[Hnb [Hx Hr]]].
  - left. exists p. split; [exact Hpres | exact Hrest].
  - right. split; [exact Hnb|]. split; [exact Hx|]. rewrite <- Hr. exact Hrest.
Qed.

Lemma spec_chain_9_split : forall es bs rest,
  ~ begins_with 0 bs ->
  spec_chain_9 es bs rest ->
  (exists mid, repr_section 9 (repr_vec repr_elem) bs (es_els es) mid /\ spec_chain_tail es mid rest)
  \/ (~ begins_with 9 bs /\ es_els es = [] /\ spec_chain_tail es bs rest).
Proof.
  intros es bs rest H0 [p [Hp Hrest]].
  destruct (repr_padded_split _ _ _ _ _ _ _ H0 Hp) as [Hpres|[Hnb [Hx Hr]]].
  - left. exists p. split; [exact Hpres | exact Hrest].
  - right. split; [exact Hnb|]. split; [exact Hx|]. rewrite <- Hr. exact Hrest.
Qed.


(** The ten cases of [spec_chain_from], as equations, because a goal at a
    literal [L] has to be rewritten rather than computed: [Z.eqb] is not in any
    reduction list that leaves the rest of the goal alone. *)
Lemma chain_from_0 : forall es bs rest,
  spec_chain_from 0 es bs rest = spec_chain_1 es bs rest.
Proof. reflexivity. Qed.

Lemma chain_from_1 : forall es bs rest,
  spec_chain_from 1 es bs rest = spec_chain_2 es bs rest.
Proof. reflexivity. Qed.

Lemma chain_from_2 : forall es bs rest,
  spec_chain_from 2 es bs rest = spec_chain_3 es bs rest.
Proof. reflexivity. Qed.

Lemma chain_from_3 : forall es bs rest,
  spec_chain_from 3 es bs rest = spec_chain_4 es bs rest.
Proof. reflexivity. Qed.

Lemma chain_from_4 : forall es bs rest,
  spec_chain_from 4 es bs rest = spec_chain_5 es bs rest.
Proof. reflexivity. Qed.

Lemma chain_from_5 : forall es bs rest,
  spec_chain_from 5 es bs rest = spec_chain_6 es bs rest.
Proof. reflexivity. Qed.

Lemma chain_from_6 : forall es bs rest,
  spec_chain_from 6 es bs rest = spec_chain_7 es bs rest.
Proof. reflexivity. Qed.

Lemma chain_from_7 : forall es bs rest,
  spec_chain_from 7 es bs rest = spec_chain_8 es bs rest.
Proof. reflexivity. Qed.

Lemma chain_from_8 : forall es bs rest,
  spec_chain_from 8 es bs rest = spec_chain_9 es bs rest.
Proof. reflexivity. Qed.

Lemma chain_from_9 : forall es bs rest,
  spec_chain_from 9 es bs rest = spec_chain_tail es bs rest.
Proof. reflexivity. Qed.

(** One line skipped: the chain moves on and so does the invariant, because the
    line's own field is its absent value. *)
Lemma spec_chain_skip : forall L es bs rest env,
  0 <= L < 9 ->
  ~ begins_with 0 bs ->
  ~ begins_with (L + 1) bs ->
  spec_chain_from L es bs rest -> env_at env es L ->
  spec_chain_from (L + 1) es bs rest /\ env_at env es (L + 1).
Proof.
  intros L es bs rest env HL H0 Hj Hchain Hat.
  assert (Hc : L = 0 \/ L = 1 \/ L = 2 \/ L = 3 \/ L = 4 \/ L = 5 \/ L = 6
               \/ L = 7 \/ L = 8) by lia.
  destruct Hc as [->|Hc].
  { change (0 + 1) with 1 in Hj |- *.
    rewrite chain_from_0 in Hchain. rewrite chain_from_1.
    destruct (spec_chain_1_split _ _ _ H0 Hchain) as [[mid [Hpres _]]|[_ [Hx Hrest]]].
    - exfalso. apply Hj.
      destruct (repr_section_inv _ _ _ _ _ _ Hpres) as [p0 [sz [ct [Hbs _]]]].
      exists p0. exact Hbs.
    - split; [exact Hrest | exact (env_at_skip_1 env es Hx Hat)]. }
  destruct Hc as [->|Hc].
  { change (1 + 1) with 2 in Hj |- *.
    rewrite chain_from_1 in Hchain. rewrite chain_from_2.
    destruct (spec_chain_2_split _ _ _ H0 Hchain) as [[mid [Hpres _]]|[_ [Hx Hrest]]].
    - exfalso. apply Hj.
      destruct (repr_section_inv _ _ _ _ _ _ Hpres) as [p0 [sz [ct [Hbs _]]]].
      exists p0. exact Hbs.
    - split; [exact Hrest | exact (env_at_skip_2 env es Hx Hat)]. }
  destruct Hc as [->|Hc].
  { change (2 + 1) with 3 in Hj |- *.
    rewrite chain_from_2 in Hchain. rewrite chain_from_3.
    destruct (spec_chain_3_split _ _ _ H0 Hchain) as [[mid [Hpres _]]|[_ [Hx Hrest]]].
    - exfalso. apply Hj.
      destruct (repr_section_inv _ _ _ _ _ _ Hpres) as [p0 [sz [ct [Hbs _]]]].
      exists p0. exact Hbs.
    - split; [exact Hrest | exact (env_at_skip_3 env es Hx Hat)]. }
  destruct Hc as [->|Hc].
  { change (3 + 1) with 4 in Hj |- *.
    rewrite chain_from_3 in Hchain. rewrite chain_from_4.
    destruct (spec_chain_4_split _ _ _ H0 Hchain) as [[mid [Hpres _]]|[_ [Hx Hrest]]].
    - exfalso. apply Hj.
      destruct (repr_section_inv _ _ _ _ _ _ Hpres) as [p0 [sz [ct [Hbs _]]]].
      exists p0. exact Hbs.
    - split; [exact Hrest | exact (env_at_skip_4 env es Hx Hat)]. }
  destruct Hc as [->|Hc].
  { change (4 + 1) with 5 in Hj |- *.
    rewrite chain_from_4 in Hchain. rewrite chain_from_5.
    destruct (spec_chain_5_split _ _ _ H0 Hchain) as [[mid [Hpres _]]|[_ [Hx Hrest]]].
    - exfalso. apply Hj.
      destruct (repr_section_inv _ _ _ _ _ _ Hpres) as [p0 [sz [ct [Hbs _]]]].
      exists p0. exact Hbs.
    - split; [exact Hrest | exact (env_at_skip_5 env es Hx Hat)]. }
  destruct Hc as [->|Hc].
  { change (5 + 1) with 6 in Hj |- *.
    rewrite chain_from_5 in Hchain. rewrite chain_from_6.
    destruct (spec_chain_6_split _ _ _ H0 Hchain) as [[mid [Hpres _]]|[_ [Hx Hrest]]].
    - exfalso. apply Hj.
      destruct (repr_section_inv _ _ _ _ _ _ Hpres) as [p0 [sz [ct [Hbs _]]]].
      exists p0. exact Hbs.
    - split; [exact Hrest | exact (env_at_skip_6 env es Hx Hat)]. }
  destruct Hc as [->|Hc].
  { change (6 + 1) with 7 in Hj |- *.
    rewrite chain_from_6 in Hchain. rewrite chain_from_7.
    destruct (spec_chain_7_split _ _ _ H0 Hchain) as [[mid [Hpres _]]|[_ [Hx Hrest]]].
    - exfalso. apply Hj.
      destruct (repr_section_inv _ _ _ _ _ _ Hpres) as [p0 [sz [ct [Hbs _]]]].
      exists p0. exact Hbs.
    - split; [exact Hrest | exact (env_at_skip_7 env es Hx Hat)]. }
  destruct Hc as [->|Hc].
  { change (7 + 1) with 8 in Hj |- *.
    rewrite chain_from_7 in Hchain. rewrite chain_from_8.
    destruct (spec_chain_8_split _ _ _ H0 Hchain) as [[mid [Hpres _]]|[_ [Hx Hrest]]].
    - exfalso. apply Hj.
      destruct (repr_section_inv _ _ _ _ _ _ Hpres) as [p0 [sz [ct [Hbs _]]]].
      exists p0. exact Hbs.
    - split; [exact Hrest | exact (env_at_skip_8 env es Hx Hat)]. }
  subst L.
  { change (8 + 1) with 9 in Hj |- *.
    rewrite chain_from_8 in Hchain. rewrite chain_from_9.
    destruct (spec_chain_9_split _ _ _ H0 Hchain) as [[mid [Hpres _]]|[_ [Hx Hrest]]].
    - exfalso. apply Hj.
      destruct (repr_section_inv _ _ _ _ _ _ Hpres) as [p0 [sz [ct [Hbs _]]]].
      exists p0. exact Hbs.
    - split; [exact Hrest | exact (env_at_skip_9 env es Hx Hat)]. }
Qed.

Lemma spec_chain_skip_many : forall n L es bs rest env,
  0 <= L -> L + Z.of_nat n <= 9 ->
  ~ begins_with 0 bs ->
  (forall j, L < j <= L + Z.of_nat n -> ~ begins_with j bs) ->
  spec_chain_from L es bs rest -> env_at env es L ->
  spec_chain_from (L + Z.of_nat n) es bs rest /\ env_at env es (L + Z.of_nat n).
Proof.
  induction n as [|n IH]; intros L es bs rest env HL0 Hn H0 Hj Hchain Hat.
  - cbn [Z.of_nat]. rewrite Z.add_0_r. split; assumption.
  - rewrite Nat2Z.inj_succ in Hn, Hj |- *.
    pose proof (Nat2Z.is_nonneg n) as Hnn.
    destruct (spec_chain_skip L es bs rest env (ltac:(lia)) H0
                (Hj (L + 1) (ltac:(lia))) Hchain Hat) as [Hc' Hat'].
    destruct (IH (L + 1) es bs rest env (ltac:(lia)) (ltac:(lia)) H0
                (ltac:(intros j Hjr; apply Hj; lia)) Hc' Hat') as [Hc'' Hat''].
    replace (L + Z.succ (Z.of_nat n)) with (L + 1 + Z.of_nat n) by lia.
    split; assumption.
Qed.

(** The lines between the last id read and the one the loop is at, which is
    what the loop actually needs: the id it just read declares them all absent.
    Stated at the line reached rather than at the id, so that the caller passes
    a literal and no arithmetic is left in the goal. *)
Lemma spec_chain_upto : forall L k es bs rest env,
  0 <= L -> L <= k -> k <= 9 ->
  ~ begins_with 0 bs ->
  (forall j, L < j <= k -> ~ begins_with j bs) ->
  spec_chain_from L es bs rest -> env_at env es L ->
  spec_chain_from k es bs rest /\ env_at env es k.
Proof.
  intros L k es bs rest env HL0 HLk Hk H0 Hno Hchain Hat.
  destruct (spec_chain_skip_many (Z.to_nat (k - L)) L es bs rest env HL0
              (ltac:(rewrite Z2Nat.id; lia)) H0
              (ltac:(intros j Hjr; rewrite Z2Nat.id in Hjr by lia;
                     apply Hno; lia)) Hchain Hat) as [Hc Hat'].
  rewrite Z2Nat.id in Hc, Hat' by lia.
  replace (L + (k - L)) with k in Hc, Hat' by lia.
  split; assumption.
Qed.

(** Every line of the chain opens with a run of custom sections, which is what
    lets the loop take one apart without knowing which line it is at. *)
Lemma spec_chain_head : forall L es bs rest,
  spec_chain_from L es bs rest -> exists mid, repr_customs bs mid.
Proof.
  intros L es bs rest H. unfold spec_chain_from in H.
  (* no [eqn:], or the equation it names is itself a hypothesis mentioning
     [Z.eqb L k] and the walk never runs out of matches *)
  repeat (match goal with
          | [ H : context [Z.eqb L ?k] |- _ ] =>
              destruct (Z.eqb L k); cbn beta iota in H
          end).
  all: try (destruct H as [p [[mid [Hc _]] _]]; exists mid; exact Hc).
  all: exists rest; exact H.
Qed.

Lemma spec_chain_custom_here : forall L es bs rest,
  begins_with 0 bs -> spec_chain_from L es bs rest ->
  exists m, repr_section 0 repr_custom bs tt m.
Proof.
  intros L es bs rest Hbw H. destruct (spec_chain_head L es bs rest H) as [mid Hc].
  destruct (repr_customs_inv _ _ Hc) as [[Hnb _]|[m [Hs _]]].
  - exfalso. exact (Hnb Hbw).
  - exists m. exact Hs.
Qed.

(** The line at the cursor as the section decoder sees it: the header reads,
    its id is the line's, and the rule holds of the stream from the section's
    first content byte. [section_here] plus [section_lift], written once. *)
Lemma env_line_here : forall data (q : usize) A
                             (R : list Z -> A -> list Z -> Prop) idz x mid rh,
  reads_prefix R ->
  repr_section idz R (bytes_from data q) x mid ->
  module_read_section_header data q = Ok rh ->
  exists (id : u8) (start fin : usize),
    rh = Core_result_Result_Ok (id, start, fin)
    /\ to_Z id = idz
    /\ R (bytes_from data start) x (bytes_from data fin)
    /\ bytes_from data fin = mid
    /\ to_Z fin <= dlen data /\ to_Z start <= to_Z fin.
Proof.
  intros data q A R idz x mid rh Hpre Hsec Hrun.
  destruct (section_here data q idz A R x mid rh Hsec Hrun)
    as [id [start [fin [-> [Hid [HR [Hfineq [Hle Hsf]]]]]]]].
  exists id, start, fin. split; [reflexivity|]. split; [exact Hid|].
  split; [|split; [exact Hfineq | split; [exact Hle | exact Hsf]]].
  pose proof (section_lift _ R data start fin x [] Hpre HR Hsf) as Hlift.
  cbn [List.app] in Hlift. exact Hlift.
Qed.

Lemma bytes_from_head : forall data (q : usize),
  to_Z q < dlen data ->
  exists z bs', bytes_from data q = z :: bs' /\ 0 <= z <= 255.
Proof.
  intros data q Hlt. pose proof (usize_nonneg q).
  destruct (bytes_from data q) as [|z bs'] eqn:E.
  - exfalso.
    pose proof (bytes_at_nil_ge data (to_Z q) (ltac:(lia))
                  (ltac:(rewrite <- bytes_from_at; exact E))). lia.
  - exists z, bs'. split; [reflexivity|].
    (* the head is a byte the input holds, so it is one *)
    assert (Hin : List.In z (byte_list data)).
    { rewrite <- (List.firstn_skipn (Z.to_nat (to_Z q)) (byte_list data)).
      apply List.in_or_app. right.
      change (List.skipn (Z.to_nat (to_Z q)) (byte_list data))
        with (bytes_from data q).
      rewrite E. left. reflexivity. }
    unfold byte_list in Hin. apply List.in_map_iff in Hin.
    destruct Hin as [b [<- _]]. exact (u8_bounds b).
Qed.

(* ================================================================== *)
(** ** The nine conditions, as one statement about the module          *)
(* ================================================================== *)

(** What Wasm 1.0 asks of a module beyond the format, spec-side. These are the
    hypotheses the nine section lemmas take, moved off the environment and onto
    the values the chain carries: the loop turns each one into the environment
    form where the section that needs it runs. *)
Definition env_wasm10 (es : env_secs) : Prop :=
  List.Forall functype_wasm10 (es_types es)
  /\ List.Forall (fun im => spec_importdesc_wasm10 (es_types es) im.(imp_desc))
       (es_imps es)
  /\ List.Forall (fun x => (N.to_nat x < List.length (es_types es))%nat)
       (es_tidxs es)
  /\ List.Forall (fun t => tabletype_valid t.(modtab_type) = true) (es_tabs es)
  /\ List.Forall (fun m => memtype_valid m.(modmem_type) = true) (es_mems es)
  /\ Z.of_nat (List.length (spec_imported_tables (es_imps es)))
       + Z.of_nat (List.length (es_tabs es)) <= 1
  /\ Z.of_nat (List.length (spec_imported_mems (es_imps es)))
       + Z.of_nat (List.length (es_mems es)) <= 1
  /\ List.Forall (fun g => spec_const_ok (spec_imported_globals (es_imps es))
                             (spec_nimp_globals es) (tg_t g.(modglob_type))
                             g.(modglob_init)) (es_globs es)
  /\ List.NoDup (List.map (fun e => name_bytes e.(modexp_name)) (es_exps es))
  /\ List.Forall (fun e => spec_exportdesc_wasm10 es e.(modexp_desc))
       (es_exps es)
  /\ (forall s, es_start es = Some s ->
        List.nth_error (all_funcs es) (N.to_nat s.(modstart_func))
          = Some (Tf [] []))
  /\ List.Forall (spec_element_wasm10 es) (es_els es).

(** The two index spaces the room bounds are about, read off the invariant at
    the line that is about to write them. *)
Lemma env_at_1_tt : forall env es,
  env_at env es 1 -> vec_list env.(env_Env_table_types) = [].
Proof.
  intros env es H. destruct H as [_ [_ [_ [_ [Ht _]]]]]. at_simpl_in Ht.
  exact (map_eq_nil_inv _ _ _ _ Ht).
Qed.

Lemma env_at_1_mt : forall env es,
  env_at env es 1 -> vec_list env.(env_Env_mem_types) = [].
Proof.
  intros env es H. destruct H as [_ [_ [_ [_ [_ [Hm _]]]]]]. at_simpl_in Hm.
  exact (map_eq_nil_inv _ _ _ _ Hm).
Qed.

Lemma env_at_3_tt : forall env es,
  env_at env es 3 ->
  List.length (vec_list env.(env_Env_table_types))
    = List.length (spec_imported_tables (es_imps es)).
Proof.
  intros env es H. destruct H as [_ [_ [_ [_ [Ht _]]]]]. at_simpl_in Ht.
  exact (map_length_eq _ _ _ _ _ Ht).
Qed.

Lemma env_at_4_mt : forall env es,
  env_at env es 4 ->
  List.length (vec_list env.(env_Env_mem_types))
    = List.length (spec_imported_mems (es_imps es)).
Proof.
  intros env es H. destruct H as [_ [_ [_ [_ [_ [Hm _]]]]]]. at_simpl_in Hm.
  exact (map_length_eq _ _ _ _ _ Hm).
Qed.

(* ================================================================== *)
(** ** [decode_env]'s loop                                             *)
(* ================================================================== *)

(** The Rust runs one loop over sections with a [last_id] ordering check, and
    the specification is a fixed chain of eleven [customs* Xsec] lines. What
    lines them up:

    - the byte the header reports says which case the loop is in, and the same
      byte decides every [repr_optsec] between [last_id] and it: they are all
      absent, which is [spec_chain_upto];
    - the ordering check cannot fire, because an id at or below [last_id] would
      leave the chain exhausted at a cursor whose byte is an environment
      section's, and [no_env_id] says that is not where the chain ends;
    - a line the byte does name has to be present, because [repr_optsec]'s
      absent case forbids the id it is written at.

    [env_small] rides along for one reason: the section decoder's own cursor
    bound, which is what turns "the two positions have the same stream left"
    into the equality the [p != end] check compares. *)
Lemma decode_env_with_loop_complete :
  forall V (inst : module_ModuleVisitor_t V) m data es vis vis' env q last_id rest r,
  module_hooks_accept inst ->
  dlen data - to_Z q <= Z.of_nat m ->
  to_Z q <= dlen data ->
  dlen data <= module_bytes ->
  env_small env q ->
  0 <= to_Z last_id <= 9 ->
  env_wasm10 es ->
  spec_chain_from (to_Z last_id) es (bytes_from data q) rest ->
  env_at env es (to_Z last_id) ->
  no_env_id rest ->
  (rest = [] \/ framed rest) ->
  module_decode_env_with_loop inst data vis env q last_id = Ok (r, vis') ->
  exists envf qf, r = Core_result_Result_Ok (envf, qf)
                  /\ bytes_from data qf = rest
                  /\ to_Z qf <= dlen data
                  /\ env_at envf es 9
                  /\ env_small envf qf.
Proof.
  assert (Hc0 : to_Z module_section_custom = 0) by reflexivity.
  assert (Hc10 : to_Z module_section_code = 10) by reflexivity.
  intros V inst m. induction m as [|m IH];
    intros data es vis vis' env q last_id rest r Hacc Hmeas Hq Hmod Hsmall Hlid
           Hw10 Hchain Hat Hno Hfr Hw;
    pose proof Hw10 as HW;
    destruct HW as [W1 [W2 [W3 [W4 [W5 [W6 [W7 [W8 [W9 [W10 [W11 W12]]]]]]]]]]];
    unfold module_decode_env_with_loop in Hw; rewrite loop_unfold in Hw;
    cbn beta iota in Hw; destruct (q s>= slice_len data) eqn:Hge.
  1,3: injection Hw as <- <-;
       apply scalar_geb_true_ge in Hge; rewrite slice_len_spec in Hge;
       assert (Hnil : bytes_from data q = [])
         by (rewrite bytes_from_at; apply bytes_at_end; lia);
       assert (Hnb : forall j, ~ begins_with j (bytes_from data q))
         by (intros j [more Hm]; rewrite Hnil in Hm; discriminate);
       destruct (spec_chain_upto (to_Z last_id) 9 es (bytes_from data q) rest env
                   (proj1 Hlid) (proj2 Hlid) (ltac:(lia)) (Hnb 0)
                   (ltac:(intros j _; apply Hnb)) Hchain Hat) as [Hc9 Hat9];
       rewrite chain_from_9 in Hc9; unfold spec_chain_tail in Hc9;
       exists env, q;
       split; [reflexivity|];
       split; [symmetry; exact (customs_none _ _ (Hnb 0) Hc9)|];
       split; [exact Hq|]; split; [exact Hat9 | exact Hsmall].
  - exfalso. apply scalar_geb_false_lt in Hge. cbn [Z.of_nat] in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge. pose proof (usize_nonneg q).
    rewrite Nat2Z.inj_succ in Hmeas.
    destruct (module_read_section_header data q) as [rh|] eqn:Eh;
      cbn [bind] in Hw; [|discriminate].
    destruct (bytes_from_head data q (ltac:(lia))) as [z [bs' [Ehd Hzb]]].
    assert (Hbz : begins_with z (bytes_from data q)) by (exists bs'; exact Ehd).
    assert (Hbw : forall j, j <> z -> ~ begins_with j (bytes_from data q))
      by (intros j Hj [more Hm]; rewrite Ehd in Hm; injection Hm as Hjz;
          apply Hj; symmetry; exact Hjz).
    destruct (Z.eq_dec z 0) as [Hz0|Hz0].
    { (* a custom section, which the run of customs at the head absorbs *)
      subst z.
      destruct (spec_chain_custom_here (to_Z last_id) es (bytes_from data q)
                  rest Hbz Hchain) as [m0' Hsec].
      destruct (custom_here data q m0' rh Hsec Eh)
        as [id [start [fin [nm [m1 [-> [Hid [Hfineq [Hle [Hsf Hnm]]]]]]]]]].
      destruct (read_section_header_step _ _ _ _ _ Eh) as [Hqs [_ _]].
      rewrite branch_ok in Hw. cbn [bind] in Hw.
      guard_true_in Hw Hid.
      destruct (module_decode_custom_section data start fin) as [rc|] eqn:Ec;
        cbn [bind] in Hw; [|discriminate].
      destruct (decode_custom_section_complete data start fin rc nm m1 Hmod Hsf
                  Hle Hnm Ec) as [c ->].
      rewrite branch_ok in Hw. cbn [bind] in Hw.
      destruct (Hacc vis c) as [vis1 Hh]. rewrite Hh in Hw. cbn [bind] in Hw.
      cbn beta iota in Hw.
      exact (IH data es vis1 vis' env fin last_id rest r Hacc (ltac:(lia)) Hle Hmod
               (env_small_mono env q fin Hsmall (ltac:(lia))) Hlid Hw10
               (ltac:(rewrite Hfineq;
                      exact (spec_chain_custom _ es _ _ _ Hsec Hchain)))
               Hat Hno Hfr Hw). }
    assert (Hnb0 : ~ begins_with 0 (bytes_from data q)) by (apply Hbw; lia).
    destruct (Z_le_gt_dec 10 z) as [Hz10|Hz10].
    { (* the code section or later: the environment is finished *)
      destruct (spec_chain_upto (to_Z last_id) 9 es (bytes_from data q) rest env
                  (proj1 Hlid) (proj2 Hlid) (ltac:(lia)) Hnb0
                  (ltac:(intros j Hj; apply Hbw; lia)) Hchain Hat)
        as [Hc9 Hat9].
      rewrite chain_from_9 in Hc9. unfold spec_chain_tail in Hc9.
      pose proof (customs_none _ _ Hnb0 Hc9) as Hrest.
      assert (Hframed : framed (bytes_from data q)).
      { destruct Hfr as [Hnil|Hf];
          [ exfalso; rewrite Hrest in Hnil; rewrite Hnil in Ehd; discriminate
          | rewrite <- Hrest; exact Hf ]. }
      destruct (framed_here data q rh Hframed Eh) as [id [start [fin [-> Hidb]]]].
      assert (Hid : to_Z id = z)
        by (rewrite Ehd in Hidb; injection Hidb as Hjz; lia).
      rewrite branch_ok in Hw. cbn [bind] in Hw.
      rewrite (scalar_eqb_of_ne id module_section_custom) in Hw by lia.
      rewrite (scalar_ge_geb_true id module_section_code) in Hw by lia.
      injection Hw as <-. exists env, q. split; [reflexivity|].
      split; [symmetry; exact Hrest|]. split; [exact Hq|].
      split; [exact Hat9 | exact Hsmall]. }
    (* an environment section, and its id has to be past [last_id] *)
    assert (HLz : to_Z last_id < z).
    { destruct (Z_lt_ge_dec (to_Z last_id) z) as [Hlt|Hge']; [exact Hlt|].
      exfalso.
      destruct (spec_chain_upto (to_Z last_id) 9 es (bytes_from data q) rest env
                  (proj1 Hlid) (proj2 Hlid) (ltac:(lia)) Hnb0
                  (ltac:(intros j Hj; apply Hbw; lia)) Hchain Hat) as [Hc9 _].
      rewrite chain_from_9 in Hc9. unfold spec_chain_tail in Hc9.
      rewrite <- (customs_none _ _ Hnb0 Hc9) in Hbz.
      exact (Hno z (ltac:(lia)) Hbz). }
    assert (Hcases : z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6
                     \/ z = 7 \/ z = 8 \/ z = 9) by lia.
    destruct Hcases as [->|Hcases].
  { destruct (spec_chain_upto (to_Z last_id) 0 es (bytes_from data q) rest env
                (proj1 Hlid) (ltac:(lia)) (ltac:(lia)) Hnb0
                (ltac:(intros j Hj; apply Hbw; lia)) Hchain Hat) as [Hc' Hat'].
    rewrite chain_from_0 in Hc'.
    destruct (spec_chain_1_split _ _ _ Hnb0 Hc')
      as [[mid [Hpres Hnext]]|[Hab _]]; [|exfalso; exact (Hab Hbz)].
    destruct (env_line_here data q _ _ _ _ mid rh (repr_vec_prefix _ _ repr_functype_prefix) Hpres Eh)
      as [id [start [fin [-> [Hid [HR [Hfineq [Hfle Hsf]]]]]]]].
    destruct (read_section_header_step _ _ _ _ _ Eh) as [Hqs [_ _]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    rewrite (scalar_eqb_of_ne id module_section_custom) in Hw by lia.
    rewrite (scalar_lt_geb_false id module_section_code) in Hw by lia.
    rewrite (scalar_leb_of_gt id last_id) in Hw by lia.
    cbn beta iota in Hw.
    destruct (decode_env_section_ok data start id env
                (env_small_mono env q start Hsmall (ltac:(lia))) (ltac:(lia))
                Hmod) as [r0 [e0 [Hr0 Hpost0]]].
    rewrite Hr0 in Hw. cbn [bind] in Hw.
    rewrite (env_section_eq_type data start id env Hid) in Hr0.
    destruct (decode_type_section_complete data start env r0 e0 (es_types es) (bytes_from data fin)
                Hr0 HR W1) as [q' [-> Hq']].
    destruct (Hpost0 q' (ltac:(reflexivity))) as [_ [Hq'le Hsmall']].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    assert (Hqf : to_Z q' = to_Z fin)
      by (apply (bytes_from_pos_eq data q' fin Hq'le Hfle);
          rewrite Hq'; reflexivity).
    rewrite (scalar_neqb_of_eq q' fin Hqf) in Hw. cbn beta iota in Hw.
    destruct (decode_type_section_sound data start env q' e0 Hr0) as [vs [Hlist [Henv [_ Hrepv]]]].
    assert (Hidn : List.map translate_functype vs = es_types es)
      by (destruct ((repr_vec_det _ _ repr_functype_det) _ _ _ _ _ Hrepv HR) as [Ha _]; exact Ha).
    assert (Hchain2 : spec_chain_from (to_Z id) es (bytes_from data fin) rest)
      by (rewrite Hid; rewrite chain_from_1; rewrite Hfineq; exact Hnext).
    assert (Hat2 : env_at e0 es (to_Z id)) by (rewrite Hid; exact (env_at_step_types env e0 es vs Hat' Hlist Henv Hidn)).
    exact (IH data es vis vis' e0 fin id rest r Hacc (ltac:(lia)) Hfle Hmod
             (env_small_mono e0 q' fin Hsmall' (ltac:(lia)))
             (ltac:(lia)) Hw10 Hchain2 Hat2 Hno Hfr Hw). }
    destruct Hcases as [->|Hcases].
  { destruct (spec_chain_upto (to_Z last_id) 1 es (bytes_from data q) rest env
                (proj1 Hlid) (ltac:(lia)) (ltac:(lia)) Hnb0
                (ltac:(intros j Hj; apply Hbw; lia)) Hchain Hat) as [Hc' Hat'].
    rewrite chain_from_1 in Hc'.
    destruct (spec_chain_2_split _ _ _ Hnb0 Hc')
      as [[mid [Hpres Hnext]]|[Hab _]]; [|exfalso; exact (Hab Hbz)].
    destruct (env_line_here data q _ _ _ _ mid rh (repr_vec_prefix _ _ repr_import_prefix) Hpres Eh)
      as [id [start [fin [-> [Hid [HR [Hfineq [Hfle Hsf]]]]]]]].
    destruct (read_section_header_step _ _ _ _ _ Eh) as [Hqs [_ _]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    rewrite (scalar_eqb_of_ne id module_section_custom) in Hw by lia.
    rewrite (scalar_lt_geb_false id module_section_code) in Hw by lia.
    rewrite (scalar_leb_of_gt id last_id) in Hw by lia.
    cbn beta iota in Hw.
    destruct (decode_env_section_ok data start id env
                (env_small_mono env q start Hsmall (ltac:(lia))) (ltac:(lia))
                Hmod) as [r0 [e0 [Hr0 Hpost0]]].
    rewrite Hr0 in Hw. cbn [bind] in Hw.
    rewrite (env_section_eq_import data start id env Hid) in Hr0.
  assert (Hall : List.Forall
                   (fun im => importdesc_wasm10 env im.(imp_desc)) (es_imps es)).
  { revert W2. apply List.Forall_impl. intros im Hd.
    exact (env_at_importdesc env es 1 _ (ltac:(lia)) Hd Hat'). }
  assert (Htab : Z.of_nat (List.length (vec_list env.(env_Env_table_types)))
                 + Z.of_nat (List.length (spec_imported_tables (es_imps es)))
                 <= 1)
    by (rewrite (env_at_1_tt env es Hat'); cbn [List.length]; lia).
  assert (Hmem : Z.of_nat (List.length (vec_list env.(env_Env_mem_types)))
                 + Z.of_nat (List.length (spec_imported_mems (es_imps es)))
                 <= 1)
    by (rewrite (env_at_1_mt env es Hat'); cbn [List.length]; lia).
    destruct (decode_import_section_complete data start env r0 e0 (es_imps es) (bytes_from data fin)
                Hr0 HR Hmod Hall Htab Hmem) as [q' [-> Hq']].
    destruct (Hpost0 q' (ltac:(reflexivity))) as [_ [Hq'le Hsmall']].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    assert (Hqf : to_Z q' = to_Z fin)
      by (apply (bytes_from_pos_eq data q' fin Hq'le Hfle);
          rewrite Hq'; reflexivity).
    rewrite (scalar_neqb_of_eq q' fin Hqf) in Hw. cbn beta iota in Hw.
    destruct (decode_import_section_sound data start env q' e0 Hr0) as [vs [Hlist [Henv [Hrepv [_ Hsp]]]]].
    assert (Hidn : List.map translate_import vs = es_imps es)
      by (destruct ((repr_vec_det _ _ repr_import_det) _ _ _ _ _ Hrepv HR) as [Ha _]; exact Ha).
    assert (Hchain2 : spec_chain_from (to_Z id) es (bytes_from data fin) rest)
      by (rewrite Hid; rewrite chain_from_2; rewrite Hfineq; exact Hnext).
    assert (Hat2 : env_at e0 es (to_Z id)) by (rewrite Hid; exact (env_at_step_imports env e0 es vs Hat' Hlist Henv Hsp Hidn)).
    exact (IH data es vis vis' e0 fin id rest r Hacc (ltac:(lia)) Hfle Hmod
             (env_small_mono e0 q' fin Hsmall' (ltac:(lia)))
             (ltac:(lia)) Hw10 Hchain2 Hat2 Hno Hfr Hw). }
    destruct Hcases as [->|Hcases].
  { destruct (spec_chain_upto (to_Z last_id) 2 es (bytes_from data q) rest env
                (proj1 Hlid) (ltac:(lia)) (ltac:(lia)) Hnb0
                (ltac:(intros j Hj; apply Hbw; lia)) Hchain Hat) as [Hc' Hat'].
    rewrite chain_from_2 in Hc'.
    destruct (spec_chain_3_split _ _ _ Hnb0 Hc')
      as [[mid [Hpres Hnext]]|[Hab _]]; [|exfalso; exact (Hab Hbz)].
    destruct (env_line_here data q _ _ _ _ mid rh (repr_vec_prefix _ _ repr_idx_prefix) Hpres Eh)
      as [id [start [fin [-> [Hid [HR [Hfineq [Hfle Hsf]]]]]]]].
    destruct (read_section_header_step _ _ _ _ _ Eh) as [Hqs [_ _]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    rewrite (scalar_eqb_of_ne id module_section_custom) in Hw by lia.
    rewrite (scalar_lt_geb_false id module_section_code) in Hw by lia.
    rewrite (scalar_leb_of_gt id last_id) in Hw by lia.
    cbn beta iota in Hw.
    destruct (decode_env_section_ok data start id env
                (env_small_mono env q start Hsmall (ltac:(lia))) (ltac:(lia))
                Hmod) as [r0 [e0 [Hr0 Hpost0]]].
    rewrite Hr0 in Hw. cbn [bind] in Hw.
    rewrite (env_section_eq_function data start id env Hid) in Hr0.
  assert (Hall : List.Forall (typeidx_in_range env) (es_tidxs es)).
  { revert W3. apply List.Forall_impl. intros x Hx.
    exact (env_at_typeidx env es 2 x (ltac:(lia)) Hx Hat'). }
    destruct (decode_function_section_complete data start env r0 e0 (es_tidxs es) (bytes_from data fin)
                Hr0 HR Hall) as [q' [-> Hq']].
    destruct (Hpost0 q' (ltac:(reflexivity))) as [_ [Hq'le Hsmall']].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    assert (Hqf : to_Z q' = to_Z fin)
      by (apply (bytes_from_pos_eq data q' fin Hq'le Hfle);
          rewrite Hq'; reflexivity).
    rewrite (scalar_neqb_of_eq q' fin Hqf) in Hw. cbn beta iota in Hw.
    destruct (decode_function_section_sound data start env q' e0 Hr0) as [vs [Hlist [Henv [Hrepv Hfs]]]].
    assert (Hidn : List.map translate_idx vs = es_tidxs es)
      by (destruct ((repr_vec_det _ _ repr_idx_det) _ _ _ _ _ Hrepv HR) as [Ha _]; exact Ha).
    assert (Hchain2 : spec_chain_from (to_Z id) es (bytes_from data fin) rest)
      by (rewrite Hid; rewrite chain_from_3; rewrite Hfineq; exact Hnext).
    assert (Hat2 : env_at e0 es (to_Z id)) by (rewrite Hid; exact (env_at_step_funcs env e0 es vs Hat' Hlist Henv Hfs Hidn)).
    exact (IH data es vis vis' e0 fin id rest r Hacc (ltac:(lia)) Hfle Hmod
             (env_small_mono e0 q' fin Hsmall' (ltac:(lia)))
             (ltac:(lia)) Hw10 Hchain2 Hat2 Hno Hfr Hw). }
    destruct Hcases as [->|Hcases].
  { destruct (spec_chain_upto (to_Z last_id) 3 es (bytes_from data q) rest env
                (proj1 Hlid) (ltac:(lia)) (ltac:(lia)) Hnb0
                (ltac:(intros j Hj; apply Hbw; lia)) Hchain Hat) as [Hc' Hat'].
    rewrite chain_from_3 in Hc'.
    destruct (spec_chain_4_split _ _ _ Hnb0 Hc')
      as [[mid [Hpres Hnext]]|[Hab _]]; [|exfalso; exact (Hab Hbz)].
    destruct (env_line_here data q _ _ _ _ mid rh (repr_vec_prefix _ _ repr_table_prefix) Hpres Eh)
      as [id [start [fin [-> [Hid [HR [Hfineq [Hfle Hsf]]]]]]]].
    destruct (read_section_header_step _ _ _ _ _ Eh) as [Hqs [_ _]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    rewrite (scalar_eqb_of_ne id module_section_custom) in Hw by lia.
    rewrite (scalar_lt_geb_false id module_section_code) in Hw by lia.
    rewrite (scalar_leb_of_gt id last_id) in Hw by lia.
    cbn beta iota in Hw.
    destruct (decode_env_section_ok data start id env
                (env_small_mono env q start Hsmall (ltac:(lia))) (ltac:(lia))
                Hmod) as [r0 [e0 [Hr0 Hpost0]]].
    rewrite Hr0 in Hw. cbn [bind] in Hw.
    rewrite (env_section_eq_table data start id env Hid) in Hr0.
  assert (Hroom : Z.of_nat (List.length (vec_list env.(env_Env_table_types)))
                  + Z.of_nat (List.length (es_tabs es)) <= 1)
    by (rewrite (env_at_3_tt env es Hat'); lia).
    destruct (decode_table_section_complete data start env r0 e0 (es_tabs es) (bytes_from data fin)
                Hr0 HR W4 Hroom) as [q' [-> Hq']].
    destruct (Hpost0 q' (ltac:(reflexivity))) as [_ [Hq'le Hsmall']].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    assert (Hqf : to_Z q' = to_Z fin)
      by (apply (bytes_from_pos_eq data q' fin Hq'le Hfle);
          rewrite Hq'; reflexivity).
    rewrite (scalar_neqb_of_eq q' fin Hqf) in Hw. cbn beta iota in Hw.
    destruct (decode_table_section_sound data start env q' e0 Hr0) as [vs [Hlist [Henv [Hrepv _]]]].
    assert (Hidn : List.map translate_table vs = es_tabs es)
      by (destruct ((repr_vec_det _ _ repr_table_det) _ _ _ _ _ Hrepv HR) as [Ha _]; exact Ha).
    assert (Hchain2 : spec_chain_from (to_Z id) es (bytes_from data fin) rest)
      by (rewrite Hid; rewrite chain_from_4; rewrite Hfineq; exact Hnext).
    assert (Hat2 : env_at e0 es (to_Z id)) by (rewrite Hid; exact (env_at_step_tables env e0 es vs Hat' Hlist Henv Hidn)).
    exact (IH data es vis vis' e0 fin id rest r Hacc (ltac:(lia)) Hfle Hmod
             (env_small_mono e0 q' fin Hsmall' (ltac:(lia)))
             (ltac:(lia)) Hw10 Hchain2 Hat2 Hno Hfr Hw). }
    destruct Hcases as [->|Hcases].
  { destruct (spec_chain_upto (to_Z last_id) 4 es (bytes_from data q) rest env
                (proj1 Hlid) (ltac:(lia)) (ltac:(lia)) Hnb0
                (ltac:(intros j Hj; apply Hbw; lia)) Hchain Hat) as [Hc' Hat'].
    rewrite chain_from_4 in Hc'.
    destruct (spec_chain_5_split _ _ _ Hnb0 Hc')
      as [[mid [Hpres Hnext]]|[Hab _]]; [|exfalso; exact (Hab Hbz)].
    destruct (env_line_here data q _ _ _ _ mid rh (repr_vec_prefix _ _ repr_mem_prefix) Hpres Eh)
      as [id [start [fin [-> [Hid [HR [Hfineq [Hfle Hsf]]]]]]]].
    destruct (read_section_header_step _ _ _ _ _ Eh) as [Hqs [_ _]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    rewrite (scalar_eqb_of_ne id module_section_custom) in Hw by lia.
    rewrite (scalar_lt_geb_false id module_section_code) in Hw by lia.
    rewrite (scalar_leb_of_gt id last_id) in Hw by lia.
    cbn beta iota in Hw.
    destruct (decode_env_section_ok data start id env
                (env_small_mono env q start Hsmall (ltac:(lia))) (ltac:(lia))
                Hmod) as [r0 [e0 [Hr0 Hpost0]]].
    rewrite Hr0 in Hw. cbn [bind] in Hw.
    rewrite (env_section_eq_memory data start id env Hid) in Hr0.
  assert (Hroom : Z.of_nat (List.length (vec_list env.(env_Env_mem_types)))
                  + Z.of_nat (List.length (es_mems es)) <= 1)
    by (rewrite (env_at_4_mt env es Hat'); lia).
    destruct (decode_memory_section_complete data start env r0 e0 (es_mems es) (bytes_from data fin)
                Hr0 HR W5 Hroom) as [q' [-> Hq']].
    destruct (Hpost0 q' (ltac:(reflexivity))) as [_ [Hq'le Hsmall']].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    assert (Hqf : to_Z q' = to_Z fin)
      by (apply (bytes_from_pos_eq data q' fin Hq'le Hfle);
          rewrite Hq'; reflexivity).
    rewrite (scalar_neqb_of_eq q' fin Hqf) in Hw. cbn beta iota in Hw.
    destruct (decode_memory_section_sound data start env q' e0 Hr0) as [vs [Hlist [Henv [Hrepv _]]]].
    assert (Hidn : List.map translate_mem vs = es_mems es)
      by (destruct ((repr_vec_det _ _ repr_mem_det) _ _ _ _ _ Hrepv HR) as [Ha _]; exact Ha).
    assert (Hchain2 : spec_chain_from (to_Z id) es (bytes_from data fin) rest)
      by (rewrite Hid; rewrite chain_from_5; rewrite Hfineq; exact Hnext).
    assert (Hat2 : env_at e0 es (to_Z id)) by (rewrite Hid; exact (env_at_step_mems env e0 es vs Hat' Hlist Henv Hidn)).
    exact (IH data es vis vis' e0 fin id rest r Hacc (ltac:(lia)) Hfle Hmod
             (env_small_mono e0 q' fin Hsmall' (ltac:(lia)))
             (ltac:(lia)) Hw10 Hchain2 Hat2 Hno Hfr Hw). }
    destruct Hcases as [->|Hcases].
  { destruct (spec_chain_upto (to_Z last_id) 5 es (bytes_from data q) rest env
                (proj1 Hlid) (ltac:(lia)) (ltac:(lia)) Hnb0
                (ltac:(intros j Hj; apply Hbw; lia)) Hchain Hat) as [Hc' Hat'].
    rewrite chain_from_5 in Hc'.
    destruct (spec_chain_6_split _ _ _ Hnb0 Hc')
      as [[mid [Hpres Hnext]]|[Hab _]]; [|exfalso; exact (Hab Hbz)].
    destruct (env_line_here data q _ _ _ _ mid rh (repr_vec_prefix _ _ repr_global_prefix) Hpres Eh)
      as [id [start [fin [-> [Hid [HR [Hfineq [Hfle Hsf]]]]]]]].
    destruct (read_section_header_step _ _ _ _ _ Eh) as [Hqs [_ _]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    rewrite (scalar_eqb_of_ne id module_section_custom) in Hw by lia.
    rewrite (scalar_lt_geb_false id module_section_code) in Hw by lia.
    rewrite (scalar_leb_of_gt id last_id) in Hw by lia.
    cbn beta iota in Hw.
    destruct (decode_env_section_ok data start id env
                (env_small_mono env q start Hsmall (ltac:(lia))) (ltac:(lia))
                Hmod) as [r0 [e0 [Hr0 Hpost0]]].
    rewrite Hr0 in Hw. cbn [bind] in Hw.
    rewrite (env_section_eq_global data start id env Hid) in Hr0.
  assert (Hall : List.Forall
                   (fun g => const_ok env (tg_t g.(modglob_type))
                               g.(modglob_init)) (es_globs es)).
  { revert W8. apply List.Forall_impl. intros g Hg.
    exact (env_at_const_ok env es 5 _ _ (ltac:(lia)) Hat' Hg). }
    destruct (decode_global_section_complete data start env r0 e0 (es_globs es) (bytes_from data fin)
                Hr0 HR Hall) as [q' [-> Hq']].
    destruct (Hpost0 q' (ltac:(reflexivity))) as [_ [Hq'le Hsmall']].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    assert (Hqf : to_Z q' = to_Z fin)
      by (apply (bytes_from_pos_eq data q' fin Hq'le Hfle);
          rewrite Hq'; reflexivity).
    rewrite (scalar_neqb_of_eq q' fin Hqf) in Hw. cbn beta iota in Hw.
    destruct (decode_global_section_sound data start env q' e0 Hr0) as [vs [Hlist [Henv [Hrepv [Hgts _]]]]].
    assert (Hidn : List.map translate_global vs = es_globs es)
      by (destruct ((repr_vec_det _ _ repr_global_det) _ _ _ _ _ Hrepv HR) as [Ha _]; exact Ha).
    assert (Hchain2 : spec_chain_from (to_Z id) es (bytes_from data fin) rest)
      by (rewrite Hid; rewrite chain_from_6; rewrite Hfineq; exact Hnext).
    assert (Hat2 : env_at e0 es (to_Z id)) by (rewrite Hid; exact (env_at_step_globals env e0 es vs Hat' Hlist Henv Hgts Hidn)).
    exact (IH data es vis vis' e0 fin id rest r Hacc (ltac:(lia)) Hfle Hmod
             (env_small_mono e0 q' fin Hsmall' (ltac:(lia)))
             (ltac:(lia)) Hw10 Hchain2 Hat2 Hno Hfr Hw). }
    destruct Hcases as [->|Hcases].
  { destruct (spec_chain_upto (to_Z last_id) 6 es (bytes_from data q) rest env
                (proj1 Hlid) (ltac:(lia)) (ltac:(lia)) Hnb0
                (ltac:(intros j Hj; apply Hbw; lia)) Hchain Hat) as [Hc' Hat'].
    rewrite chain_from_6 in Hc'.
    destruct (spec_chain_7_split _ _ _ Hnb0 Hc')
      as [[mid [Hpres Hnext]]|[Hab _]]; [|exfalso; exact (Hab Hbz)].
    destruct (env_line_here data q _ _ _ _ mid rh (repr_vec_prefix _ _ repr_export_prefix) Hpres Eh)
      as [id [start [fin [-> [Hid [HR [Hfineq [Hfle Hsf]]]]]]]].
    destruct (read_section_header_step _ _ _ _ _ Eh) as [Hqs [_ _]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    rewrite (scalar_eqb_of_ne id module_section_custom) in Hw by lia.
    rewrite (scalar_lt_geb_false id module_section_code) in Hw by lia.
    rewrite (scalar_leb_of_gt id last_id) in Hw by lia.
    cbn beta iota in Hw.
    destruct (decode_env_section_ok data start id env
                (env_small_mono env q start Hsmall (ltac:(lia))) (ltac:(lia))
                Hmod) as [r0 [e0 [Hr0 Hpost0]]].
    rewrite Hr0 in Hw. cbn [bind] in Hw.
    rewrite (env_section_eq_export data start id env Hid) in Hr0.
  assert (Hfresh : exports_fresh env (es_exps es))
    by exact (env_at_exports_fresh env es 6 (es_exps es) (ltac:(lia)) W9 Hat').
  assert (Hall : List.Forall
                   (fun e => exportdesc_wasm10 env e.(modexp_desc)) (es_exps es)).
  { revert W10. apply List.Forall_impl. intros e He.
    exact (env_at_exportdesc env es 6 _ (ltac:(lia)) He Hat'). }
    destruct (decode_export_section_complete data start env r0 e0 (es_exps es) (bytes_from data fin)
                Hr0 HR Hmod Hfresh Hall) as [q' [-> Hq']].
    destruct (Hpost0 q' (ltac:(reflexivity))) as [_ [Hq'le Hsmall']].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    assert (Hqf : to_Z q' = to_Z fin)
      by (apply (bytes_from_pos_eq data q' fin Hq'le Hfle);
          rewrite Hq'; reflexivity).
    rewrite (scalar_neqb_of_eq q' fin Hqf) in Hw. cbn beta iota in Hw.
    destruct (decode_export_section_sound data start env q' e0 Hr0) as [vs [Hlist [Henv [Hrepv [_ _]]]]].
    assert (Hidn : List.map translate_export vs = es_exps es)
      by (destruct ((repr_vec_det _ _ repr_export_det) _ _ _ _ _ Hrepv HR) as [Ha _]; exact Ha).
    assert (Hchain2 : spec_chain_from (to_Z id) es (bytes_from data fin) rest)
      by (rewrite Hid; rewrite chain_from_7; rewrite Hfineq; exact Hnext).
    assert (Hat2 : env_at e0 es (to_Z id)) by (rewrite Hid; exact (env_at_step_exports env e0 es vs Hat' Hlist Henv Hidn)).
    exact (IH data es vis vis' e0 fin id rest r Hacc (ltac:(lia)) Hfle Hmod
             (env_small_mono e0 q' fin Hsmall' (ltac:(lia)))
             (ltac:(lia)) Hw10 Hchain2 Hat2 Hno Hfr Hw). }
    destruct Hcases as [->|Hcases].
  { destruct (spec_chain_upto (to_Z last_id) 7 es (bytes_from data q) rest env
                (proj1 Hlid) (ltac:(lia)) (ltac:(lia)) Hnb0
                (ltac:(intros j Hj; apply Hbw; lia)) Hchain Hat) as [Hc' Hat'].
    rewrite chain_from_7 in Hc'.
    destruct (spec_chain_8_split _ _ _ Hnb0 Hc')
      as [[mid [Hpres Hnext]]|[Hab _]]; [|exfalso; exact (Hab Hbz)].
    destruct (env_line_here data q _ _ _ _ mid rh repr_start_prefix Hpres Eh)
      as [id [start [fin [-> [Hid [HR [Hfineq [Hfle Hsf]]]]]]]].
    destruct (read_section_header_step _ _ _ _ _ Eh) as [Hqs [_ _]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    rewrite (scalar_eqb_of_ne id module_section_custom) in Hw by lia.
    rewrite (scalar_lt_geb_false id module_section_code) in Hw by lia.
    rewrite (scalar_leb_of_gt id last_id) in Hw by lia.
    cbn beta iota in Hw.
    destruct (decode_env_section_ok data start id env
                (env_small_mono env q start Hsmall (ltac:(lia))) (ltac:(lia))
                Hmod) as [r0 [e0 [Hr0 Hpost0]]].
    rewrite Hr0 in Hw. cbn [bind] in Hw.
    rewrite (env_section_eq_start data start id env Hid) in Hr0.
  assert (Hst : forall s, es_start es = Some s -> start_wasm10 env s)
    by (intros s Hs; exact (env_at_start env es 7 s (ltac:(lia)) (W11 s Hs) Hat')).
    destruct (decode_start_section_complete data start env r0 e0 (es_start es) (bytes_from data fin)
                Hr0 HR Hst) as [q' [-> Hq']].
    destruct (Hpost0 q' (ltac:(reflexivity))) as [_ [Hq'le Hsmall']].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    assert (Hqf : to_Z q' = to_Z fin)
      by (apply (bytes_from_pos_eq data q' fin Hq'le Hfle);
          rewrite Hq'; reflexivity).
    rewrite (scalar_neqb_of_eq q' fin Hqf) in Hw. cbn beta iota in Hw.
    destruct (decode_start_section_sound data start env q' e0 Hr0) as [Henv [Hrepv _]].
    assert (Hidn : translate_start e0.(env_Env_start) = es_start es)
      by (destruct (repr_start_det _ _ _ _ _ Hrepv HR) as [Ha _]; exact Ha).
    assert (Hchain2 : spec_chain_from (to_Z id) es (bytes_from data fin) rest)
      by (rewrite Hid; rewrite chain_from_8; rewrite Hfineq; exact Hnext).
    assert (Hat2 : env_at e0 es (to_Z id)) by (rewrite Hid; exact (env_at_step_start env e0 es Hat' Henv Hidn)).
    exact (IH data es vis vis' e0 fin id rest r Hacc (ltac:(lia)) Hfle Hmod
             (env_small_mono e0 q' fin Hsmall' (ltac:(lia)))
             (ltac:(lia)) Hw10 Hchain2 Hat2 Hno Hfr Hw). }
    subst z.
  { destruct (spec_chain_upto (to_Z last_id) 8 es (bytes_from data q) rest env
                (proj1 Hlid) (ltac:(lia)) (ltac:(lia)) Hnb0
                (ltac:(intros j Hj; apply Hbw; lia)) Hchain Hat) as [Hc' Hat'].
    rewrite chain_from_8 in Hc'.
    destruct (spec_chain_9_split _ _ _ Hnb0 Hc')
      as [[mid [Hpres Hnext]]|[Hab _]]; [|exfalso; exact (Hab Hbz)].
    destruct (env_line_here data q _ _ _ _ mid rh (repr_vec_prefix _ _ repr_elem_prefix) Hpres Eh)
      as [id [start [fin [-> [Hid [HR [Hfineq [Hfle Hsf]]]]]]]].
    destruct (read_section_header_step _ _ _ _ _ Eh) as [Hqs [_ _]].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    rewrite (scalar_eqb_of_ne id module_section_custom) in Hw by lia.
    rewrite (scalar_lt_geb_false id module_section_code) in Hw by lia.
    rewrite (scalar_leb_of_gt id last_id) in Hw by lia.
    cbn beta iota in Hw.
    destruct (decode_env_section_ok data start id env
                (env_small_mono env q start Hsmall (ltac:(lia))) (ltac:(lia))
                Hmod) as [r0 [e0 [Hr0 Hpost0]]].
    rewrite Hr0 in Hw. cbn [bind] in Hw.
    rewrite (env_section_eq_element data start id env Hid) in Hr0.
  assert (Hall : List.Forall (element_wasm10 env) (es_els es)).
  { revert W12. apply List.Forall_impl. intros el Hel.
    exact (env_at_element env es 8 el (ltac:(lia)) Hel Hat'). }
    destruct (decode_element_section_complete data start env r0 e0 (es_els es) (bytes_from data fin)
                Hr0 HR Hall) as [q' [-> Hq']].
    destruct (Hpost0 q' (ltac:(reflexivity))) as [_ [Hq'le Hsmall']].
    rewrite branch_ok in Hw. cbn [bind] in Hw.
    assert (Hqf : to_Z q' = to_Z fin)
      by (apply (bytes_from_pos_eq data q' fin Hq'le Hfle);
          rewrite Hq'; reflexivity).
    rewrite (scalar_neqb_of_eq q' fin Hqf) in Hw. cbn beta iota in Hw.
    destruct (decode_element_section_sound data start env q' e0 Hr0) as [vs [Hlist [Henv [Hrepv _]]]].
    assert (Hidn : List.map translate_element vs = es_els es)
      by (destruct ((repr_vec_det _ _ repr_elem_det) _ _ _ _ _ Hrepv HR) as [Ha _]; exact Ha).
    assert (Hchain2 : spec_chain_from (to_Z id) es (bytes_from data fin) rest)
      by (rewrite Hid; rewrite chain_from_9; rewrite Hfineq; exact Hnext).
    assert (Hat2 : env_at e0 es (to_Z id)) by (rewrite Hid; exact (env_at_step_elements env e0 es vs Hat' Hlist Henv Hidn)).
    exact (IH data es vis vis' e0 fin id rest r Hacc (ltac:(lia)) Hfle Hmod
             (env_small_mono e0 q' fin Hsmall' (ltac:(lia)))
             (ltac:(lia)) Hw10 Hchain2 Hat2 Hno Hfr Hw). }
Qed.

Lemma decode_env_complete : forall data es p0 rest r,
  dlen data <= module_bytes ->
  env_wasm10 es ->
  repr_magic_version (byte_list data) p0 ->
  spec_chain_from 0 es p0 rest ->
  no_env_id rest ->
  (rest = [] \/ framed rest) ->
  module_decode_env data = Ok r ->
  exists envf qf, r = Core_result_Result_Ok (envf, qf)
                  /\ bytes_from data qf = rest
                  /\ to_Z qf <= dlen data
                  /\ env_at envf es 9
                  /\ env_small envf qf.
Proof.
  intros data es p0 rest r Hmod Hw10 Hmagic Hchain Hno Hfr Hrun.
  pose proof (Module_Sound.decode_env_nop_inv _ _ Hrun) as Hw.
  unfold module_decode_env_with in Hw.
  destruct env_Env_new as [env0|] eqn:Hnew; cbn [bind] in Hw; [|discriminate].
  destruct (module_read_header data) as [rh|] eqn:Eh; cbn [bind] in Hw;
    [|discriminate].
  destruct (read_header_complete data rh p0 Eh Hmagic) as [p [-> [Hp Hple]]].
  rewrite branch_ok in Hw. cbn [bind] in Hw.
  assert (Hz : to_Z 0%u8 = 0) by reflexivity.
  apply (decode_env_with_loop_complete _
           module_NopModuleVisitor_Insts_VeriwasmModuleModuleVisitor
           (Z.to_nat (dlen data)) data es tt tt env0 p 0%u8 rest r);
    [ exact nop_module_hooks_accept
    | pose proof (usize_nonneg p);
      rewrite Z2Nat.id by (pose proof (usize_nonneg (slice_len data)); lia); lia
    | exact Hple | exact Hmod | exact (env_small_new p env0 Hnew)
    | rewrite Hz; lia | exact Hw10
    | rewrite Hz; rewrite Hp; exact Hchain
    | rewrite Hz; exact (env_at_new env0 es Hnew)
    | exact Hno | exact Hfr | exact Hw ].
Qed.

(* ================================================================== *)
(** ** The module, with the code section's two size bounds             *)
(* ================================================================== *)

(** Spec 5.5.16 again, with the code line strengthened to [repr_vec_fit]: each
    entry within [MAX_FUNCTION_BYTES] and each function's locals within
    [MAX_LOCALS]. Those are Wasm 1.0 restrictions with no format rule behind
    them, and the byte-extent one cannot be said about the module alone, so it
    rides on the derivation. Everything else is [repr_module] line for line,
    which [repr_module_fit_module] states. *)
Inductive repr_module_fit : list Z -> module -> Prop :=
| repr_module_fit_intro : forall bs
    p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11
    tfs imps tidxs tabs mems globs exps st els codes datas fs,
    repr_magic_version bs p0 ->
    repr_padded 1  (repr_vec repr_functype) [] p0  tfs   p1  ->
    repr_padded 2  (repr_vec repr_import)   [] p1  imps  p2  ->
    repr_padded 3  (repr_vec repr_idx)      [] p2  tidxs p3  ->
    repr_padded 4  (repr_vec repr_table)    [] p3  tabs  p4  ->
    repr_padded 5  (repr_vec repr_mem)      [] p4  mems  p5  ->
    repr_padded 6  (repr_vec repr_global)   [] p5  globs p6  ->
    repr_padded 7  (repr_vec repr_export)   [] p6  exps  p7  ->
    repr_padded 8  repr_start             None p7  st    p8  ->
    repr_padded 9  (repr_vec repr_elem)     [] p8  els   p9  ->
    repr_padded 10 repr_vec_fit             [] p9  codes p10 ->
    repr_padded 11 (repr_vec repr_data)     [] p10 datas p11 ->
    repr_customs p11 [] ->
    funcs_of tidxs codes fs ->
    repr_module_fit bs
      {| mod_types   := tfs;
         mod_funcs   := fs;
         mod_tables  := tabs;
         mod_mems    := mems;
         mod_globals := globs;
         mod_elems   := els;
         mod_datas   := datas;
         mod_start   := st;
         mod_imports := imps;
         mod_exports := exps |}.

Lemma repr_padded_weaken : forall A id (R S : list Z -> A -> list Z -> Prop)
                                  absent bs x rest,
  (forall b y r, R b y r -> S b y r) ->
  repr_padded id R absent bs x rest -> repr_padded id S absent bs x rest.
Proof.
  intros A id R S absent bs x rest Himp [mid [Hc Ho]].
  exists mid. split; [exact Hc|].
  inversion Ho as [b0 y0 r0 Hs|b0 Hnb]; subst.
  - apply repr_optsec_present.
    inversion Hs as [q0 sz ct y1 r1 Hn Hl HR]; subst.
    econstructor;
      [ exact Hn | first [reflexivity | exact Hl] | apply Himp; exact HR ].
  - apply repr_optsec_absent. exact Hnb.
Qed.

Lemma repr_module_fit_module : forall bs m,
  repr_module_fit bs m -> repr_module bs m.
Proof.
  intros bs m H. inversion H; subst.
  econstructor; try eassumption.
  apply (repr_padded_weaken _ _ repr_vec_fit); [|assumption].
  intros b y r. apply repr_vec_fit_vec.
Qed.

(* ================================================================== *)
(** ** The code entries, typed on the specification's side             *)
(* ================================================================== *)

(** [func_body_context] reads five index spaces off the environment and nothing
    else, and [env_at] pins all five, so the context a body checks in is a
    function of the module. The three fields no Wasm 1.0 instruction reads stay
    quantified, exactly as they are in [code_typed]. *)
Definition spec_func_context (elems : list reference_type) (datas : list ok)
                             (refs : list funcidx) (es : env_secs)
                             (ft : function_type)
                             (t_locs : list value_type) : t_context :=
  {| tc_types := es_types es;
     tc_funcs := all_funcs es;
     tc_tables := all_tabtypes es;
     tc_mems := all_memtypes es;
     tc_globals := all_globtypes es;
     tc_elems := elems;
     tc_datas := datas;
     tc_locals := match ft with Tf tn _ => tn end ++ t_locs;
     tc_labels := [match ft with Tf _ tm => tm end];
     tc_return := Some (match ft with Tf _ tm => tm end);
     tc_refs := refs |}.

(** The three fields are parameters rather than quantified: no Wasm 1.0
    instruction reads them, so which triple the entries check against does not
    matter, and taking them as given is what lets the module's own element,
    data and ref index spaces be the answer. *)
Definition spec_code_typed (elems : list reference_type) (datas : list ok)
                           (refs : list funcidx) (es : env_secs)
                           (tidx : typeidx) (c : list value_type * expr)
  : Prop :=
  exists ft,
    List.nth_error (es_types es) (N.to_nat tidx) = Some ft
    /\ (exists ds, fst c = List.map translate_vt_v ds)
    /\ b_e_type_checker (spec_func_context elems datas refs es ft (fst c))
         (snd c) (Tf [] (match ft with Tf _ tm => tm end)) = true.

Lemma func_body_context_spec : forall elems datas refs env es ft t_locs,
  env_at env es 9 ->
  func_body_context elems datas refs env ft t_locs
    = spec_func_context elems datas refs es (translate_functype ft) t_locs.
Proof.
  intros elems datas refs env es ft t_locs H.
  destruct H as [H1 [_ [_ [H4 [H5 [H6 [H7 _]]]]]]].
  rewrite (at_types_full es 9 (ltac:(lia))) in H1.
  rewrite (at_funcs_full es 9 (ltac:(lia))) in H4.
  rewrite (at_tabtypes_full es 9 (ltac:(lia))) in H5.
  rewrite (at_memtypes_full es 9 (ltac:(lia))) in H6.
  rewrite (at_globtypes_full es 9 (ltac:(lia))) in H7.
  unfold func_body_context, spec_func_context.
  rewrite H1. rewrite H4. rewrite H5. rewrite H6. rewrite H7.
  cbn [translate_functype]. reflexivity.
Qed.

Lemma translate_functype_results : forall ft tn tm,
  translate_functype ft = Tf tn tm ->
  List.map translate_vt_v (vec_list ft.(types_FuncType_results)) = tm.
Proof.
  intros ft tn tm H. unfold translate_functype in H. injection H as _ H.
  unfold vec_list. exact H.
Qed.

Lemma code_typed_of_spec : forall elems datas refs env es tidx c,
  env_at env es 9 ->
  spec_code_typed elems datas refs es (translate_idx tidx) c ->
  code_typed_at elems datas refs env tidx c.
Proof.
  intros elems datas refs env es tidx c Hat [ft [Hnth [Hds Hchk]]].
  pose proof Hat as Hat'. destruct Hat' as [H1 _].
  rewrite (at_types_full es 9 (ltac:(lia))) in H1.
  rewrite <- H1 in Hnth. unfold translate_idx in Hnth.
  rewrite N_to_nat_Z_to_N in Hnth.
  destruct (map_nth_error_inv _ _ _ _ _ _ Hnth) as [ft' [Hft' Heq]].
  exists ft'. split; [exact Hft'|]. split; [exact Hds|].
  rewrite (func_body_context_spec elems datas refs env es ft' (fst c) Hat).
  destruct ft as [tn tm].
  rewrite (translate_functype_results ft' tn tm Heq). rewrite Heq. exact Hchk.
Qed.

(* ================================================================== *)
(** ** The module's sections, read off the module                      *)
(* ================================================================== *)

Definition es_of (m : module) : env_secs :=
  {| es_types := mod_types m;
     es_imps  := mod_imports m;
     es_tidxs := List.map modfunc_type (mod_funcs m);
     es_tabs  := mod_tables m;
     es_mems  := mod_mems m;
     es_globs := mod_globals m;
     es_exps  := mod_exports m;
     es_start := mod_start m;
     es_els   := mod_elems m |}.

Definition codes_of (m : module) : list (list value_type * expr) :=
  List.map (fun f => (f.(modfunc_locals), f.(modfunc_body))) (mod_funcs m).

(** [funcs_of] pairs the function section's indices with the code section's
    bodies, so both are recoverable from the module's functions. *)
Lemma funcs_of_parts : forall tidxs codes fs,
  funcs_of tidxs codes fs ->
  tidxs = List.map modfunc_type fs
  /\ codes = List.map (fun f => (f.(modfunc_locals), f.(modfunc_body))) fs.
Proof.
  intros tidxs codes fs H.
  induction H as [|x xs lcls e cs fs' H IH]; [split; reflexivity|].
  destruct IH as [IH1 IH2]. cbn [List.map modfunc_type modfunc_locals
                                 modfunc_body].
  split; f_equal; assumption.
Qed.

Lemma forall2_code_typed : forall elems datas refs env es xs codes,
  env_at env es 9 ->
  List.Forall2 (spec_code_typed elems datas refs es) (List.map translate_idx xs)
    codes ->
  List.Forall2 (code_typed_at elems datas refs env) xs codes.
Proof.
  intros elems datas refs env es xs.
  induction xs as [|x xs IH]; intros codes Hat H.
  - inversion H; subst. apply Forall2_nil.
  - cbn [List.map] in H. inversion H as [|a b l1 l2 Hab Hrest]; subst.
    apply Forall2_cons;
      [exact (code_typed_of_spec elems datas refs env es x b Hat Hab)
      | exact (IH l2 Hat Hrest)].
Qed.

(** Everything Wasm 1.0 asks of a module that the format does not: the nine
    environment lines' conditions, the data segments', and the code section's
    typing, all against the module. *)
Definition module_wasm10 (m : module) : Prop :=
  env_wasm10 (es_of m)
  /\ List.Forall (spec_data_wasm10 (es_of m)) (mod_datas m)
  /\ exists elems datas refs,
       List.Forall2 (spec_code_typed elems datas refs (es_of m))
         (List.map modfunc_type (mod_funcs m)) (codes_of m).

(** Where the environment hands over, nothing an environment section could
    start with is there, and either the input is over or a section is framed:
    the two things [validate_code]'s absent case and the loop's exit need. *)
Lemma code_line_head : forall mid codes p10 datas p11,
  ~ begins_with 0 mid ->
  repr_optsec 10 repr_vec_fit [] mid codes p10 ->
  repr_padded 11 (repr_vec repr_data) [] p10 datas p11 ->
  repr_customs p11 [] ->
  no_env_id mid /\ (mid = [] \/ framed mid).
Proof.
  intros mid codes p10 datas p11 Hnb Ho10 Hp11 Htr.
  destruct (repr_optsec_inv _ _ _ _ _ _ _ Ho10) as [Hpres|[_ [_ Hr]]].
  - destruct (repr_section_inv _ _ _ _ _ _ Hpres) as [b0 [sz [ct [Hbs _]]]].
    split.
    + intros j Hj [more Hm]. rewrite Hbs in Hm. injection Hm as Hj10. lia.
    + right. exact (framed_of_section _ _ _ _ _ _ Hpres).
  - subst p10. destruct Hp11 as [mid11 [Hc11 Ho11]].
    rewrite (customs_none _ _ Hnb Hc11) in Ho11.
    destruct (repr_optsec_inv _ _ _ _ _ _ _ Ho11) as [Hpres|[_ [_ Hr2]]].
    + destruct (repr_section_inv _ _ _ _ _ _ Hpres) as [b0 [sz [ct [Hbs _]]]].
      split.
      * intros j Hj [more Hm]. rewrite Hbs in Hm. injection Hm as Hj11. lia.
      * right. exact (framed_of_section _ _ _ _ _ _ Hpres).
    + subst p11. rewrite <- (customs_none _ _ Hnb Htr).
      split; [intros j Hj [more Hm]; discriminate | left; reflexivity].
Qed.

(** A run of custom sections ends where none begins. *)
Lemma repr_customs_end : forall bs rest,
  repr_customs bs rest -> ~ begins_with 0 rest.
Proof. intros bs rest H. induction H; assumption. Qed.

(* ================================================================== *)
(** ** No false rejects, for the module                                *)
(* ================================================================== *)

(** The converse of [validate_module_repr]: bytes that encode a Wasm 1.0 module
    the type system accepts are bytes the validator accepts.

    The three parts meet here the way they do on the soundness side, in the
    other direction. [decode_env] consumes the magic number, the nine
    environment lines and the run of custom sections that pads the code line;
    [validate_code] consumes that line, and [funcs_of] is what makes its count
    check pass, since it pairs the two lists by construction; [decode_tail]
    consumes the data line and the run that closes the module. *)
Lemma validate_module_no_reject : forall data m r,
  dlen data <= module_bytes ->
  repr_module_fit (byte_list data) m ->
  module_wasm10 m ->
  module_validate_module data = Ok r ->
  exists vm, r = Core_result_Result_Ok vm.
Proof.
  intros data m r Hmod Hrepr Hwm Hrun.
  destruct Hwm as [Hw10 [Hdata [elems [dts [refs Hcode]]]]].
  set (es := es_of m) in *.
  remember (byte_list data) as bs eqn:Ebs.
  destruct Hrepr as [bs0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
                     tfs imps tidxs tabs mems globs exps st els codes datas fs
                     Hmagic L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 Htr Hfuncs].
  subst bs0.
  destruct (funcs_of_parts _ _ _ Hfuncs) as [Htidx Hcodes].
  subst tidxs. subst codes. unfold codes_of in Hcode. cbn [mod_funcs] in Hcode.
  (* the code line: the run of customs the environment ends in, then the
     section itself *)
  destruct L10 as [mid10 [Hc10 Ho10]].
  destruct (code_line_head mid10 _ q10 datas q11 (repr_customs_end _ _ Hc10)
              Ho10 L11 Htr) as [Hno Hfr].
  assert (Hchain : spec_chain_from 0 es q0 mid10).
  { rewrite chain_from_0.
    exists q1. split; [exact L1|]. exists q2. split; [exact L2|].
    exists q3. split; [exact L3|]. exists q4. split; [exact L4|].
    exists q5. split; [exact L5|]. exists q6. split; [exact L6|].
    exists q7. split; [exact L7|]. exists q8. split; [exact L8|].
    exists q9. split; [exact L9|]. exact Hc10. }
  (* the module is not too large *)
  pose proof Hrun as Hw. unfold module_validate_module in Hw.
  destruct (slice_len data s> limits_max_module_bytes) eqn:Hbig.
  { exfalso. apply scalar_gtb_true in Hbig.
    rewrite max_module_bytes_val in Hbig. lia. }
  cbn beta zeta in Hw.
  (* the environment *)
  destruct (module_decode_env data) as [re|] eqn:Ee; cbn [bind] in Hw;
    [|discriminate].
  destruct (decode_env_complete data es q0 mid10 re Hmod Hw10 Hmagic Hchain
              Hno Hfr Ee) as [envf [cp [-> [Hcp [Hcple [Hat9 Hsm]]]]]].
  rewrite branch_ok in Hw. cbn [bind] in Hw.
  (* the code section *)
  destruct (validate_code_ok data cp envf Hsm Hcple Hmod) as [rc [Hrc Hpostc]].
  rewrite Hrc in Hw. cbn [bind] in Hw.
  assert (Hf2 : List.Forall2 (code_typed_at elems dts refs envf)
                  (vec_list envf.(env_Env_func_type_indices))
                  (List.map (fun f => (f.(modfunc_locals), f.(modfunc_body)))
                     fs)).
  { apply (forall2_code_typed elems dts refs envf es); [exact Hat9|].
    destruct Hat9 as [_ [_ [Hti _]]].
    rewrite Hti. unfold at_tidxs, upto.
    cbn [Z.leb Z.compare Pos.compare Pos.compare_cont]. exact Hcode. }
  destruct (validate_code_complete elems dts refs data cp envf rc _ q10 Hmod
              Hcple Hsm
              (env_at_types_wasm10 envf es 9
                 (ltac:(rewrite (at_types_full es 9 (ltac:(lia)));
                        exact (proj1 Hw10))) Hat9)
              (env_at_funcs_wasm10 envf es 9 (ltac:(lia)) (proj1 Hw10) Hat9)
              (ltac:(rewrite Hcp; exact Ho10)) (ltac:(rewrite Hcp; exact Hfr))
              Hf2 Hrc) as [tp [-> Htp]].
  destruct (Hpostc tp (ltac:(reflexivity))) as [_ Htple].
  rewrite branch_ok in Hw. cbn [bind] in Hw.
  (* the tail *)
  destruct L11 as [mid11 [Hc11 Ho11]].
  destruct (module_decode_tail data tp envf) as [rt|] eqn:Et; cbn [bind] in Hw;
    [|discriminate].
  assert (Hdw : List.Forall (data_wasm10 envf) datas).
  { revert Hdata. apply List.Forall_impl. intros d Hd.
    exact (env_at_data envf es 9 d (ltac:(lia)) Hd Hat9). }
  destruct (decode_tail_complete data tp envf rt datas mid11 q11 Htple Hmod
              (ltac:(rewrite Htp; exact Hc11)) Ho11 Htr Hdw Et) as [t ->].
  rewrite branch_ok in Hw. cbn [bind] in Hw.
  injection Hw as <-. eexists. reflexivity.
Qed.

(** The same with the run supplied by [validate_module_no_panic], which is the
    form the soundness theorems are stated against. *)
Theorem validate_module_complete : forall data m,
  dlen data <= module_bytes ->
  repr_module_fit (byte_list data) m ->
  module_wasm10 m ->
  exists vm, module_validate_module data = Ok (Core_result_Result_Ok vm).
Proof.
  intros data m Hmod Hrepr Hwm.
  destruct (validate_module_no_panic data) as [r Hr].
  destruct (validate_module_no_reject data m r Hmod Hrepr Hwm Hr) as [vm ->].
  exists vm. exact Hr.
Qed.
