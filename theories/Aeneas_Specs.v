(** * Specifications for Aeneas primitives

    Aeneas emits Rust stdlib operations as axioms without specs. This file
    states what they do in terms of the underlying list or integer, plus the
    scalar and list arithmetic facts the proofs need on top.

    These are trust items, but shallow ones: each mirrors the obvious semantics
    of the Rust function it stands for. See TRUST.md.
 *)

Require Import Primitives.
Import Primitives.
Require Import Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.Nnat.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Sumbool.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Import Itasca_Types.
Include Itasca_Types.
Require Import Itasca_FunsExternal.
Include Itasca_FunsExternal.
Require Import Itasca_Funs.
Include Itasca_Funs.

(** Vec is a bounded list; specs are stated over the underlying list. *)
Definition vec_list {T} (v : alloc_vec_Vec T) : list T := proj1_sig v.

Lemma vec_push_spec : forall {T} (v : alloc_vec_Vec T) (x : T) v',
  alloc_vec_Vec_push v x = Ok v' ->
  vec_list v' = vec_list v ++ [x].
Proof.
  intros T v x v' H.
  unfold alloc_vec_Vec_push, alloc_vec_Vec_bind, bind, alloc_vec_Vec_to_list, vec_list in *.
  simpl in H.
  match type of H with
  | context [sumbool_of_bool ?b] => destruct (sumbool_of_bool b) as [Hle|Hlt]
  end; simpl in H.
  - inversion H; subst. reflexivity.
  - discriminate.
Qed.

Axiom vec_pop_last : forall {T} (A : Type) (v : alloc_vec_Vec T) o v',
  alloc_vec_Vec_pop A v = Ok (o, v') ->
  match List.rev (vec_list v) with
  | [] => o = None /\ vec_list v' = []
  | x :: rest => o = Some x /\ vec_list v' = List.rev rest
  end.

(** [Vec::pop] cannot fail in Rust; Aeneas models it as an opaque function whose
    result type admits [Fail_], and [vec_pop_last] constrains only the [Ok] case.
    Panic-freedom needs the totality separately. *)
Axiom vec_pop_ok : forall {T} (A : Type) (v : alloc_vec_Vec T),
  exists o v', alloc_vec_Vec_pop A v = Ok (o, v').

(** [Vec::push] is a real definition rather than an axiom, so its one failure
    condition -- the length reaching [usize_max] -- is visible and this is a
    lemma. It is the only place the function body size limit is load-bearing. *)
Lemma vec_push_ok : forall {T} (v : alloc_vec_Vec T) (x : T),
  Z.of_nat (List.length (vec_list v)) + 1 <= usize_max ->
  exists v', alloc_vec_Vec_push v x = Ok v'.
Proof.
  intros T v x Hle.
  unfold alloc_vec_Vec_push, alloc_vec_Vec_bind, alloc_vec_Vec_to_list,
         vec_list in *.
  cbn [bind].
  (* the [sumbool] is dependent, so destruct it rather than abstracting *)
  destruct (sumbool_of_bool
              (scalar_le_max Usize (Z.of_nat (length (proj1_sig v ++ [x])))))
    as [Hok|Hbad].
  - eexists. reflexivity.
  - exfalso. unfold scalar_le_max in Hbad.
    apply Bool.orb_false_iff in Hbad as [_ Hbad2].
    apply Z.leb_gt in Hbad2.
    rewrite List.app_length in Hbad2. cbn [length] in Hbad2.
    unfold scalar_max in Hbad2. lia.
Qed.

Axiom vec_is_empty_spec : forall {T} (A : Type) (v : alloc_vec_Vec T),
  alloc_vec_Vec_is_empty A v =
    Ok (match vec_list v with [] => true | _ => false end).

Axiom vec_deref_spec : forall {T} (v : alloc_vec_Vec T),
  alloc_vec_Vec_deref v = v.

Axiom vec_index_spec : forall {T} (v : alloc_vec_Vec T) (i : usize),
  alloc_vec_Vec_index (core_slice_index_SliceIndexUsizeSliceInst T) v i =
    match List.nth_error (vec_list v) (Z.to_nat (to_Z i)) with
    | Some x => Ok x
    | None => Fail_ Failure
    end.

Axiom slice_index_usize_spec : forall {T} (s : slice T) (i : usize),
  slice_index_usize s i =
    match List.nth_error (vec_list s) (Z.to_nat (to_Z i)) with
    | Some x => Ok x
    | None => Fail_ Failure
    end.

Axiom slice_len_spec : forall {T} (s : slice T),
  to_Z (slice_len s) = Z.of_nat (List.length (vec_list s)).

(** [alloc_vec_Vec_len] is a real definition, not an axiom, so this needs no
    trust. *)
Lemma vec_len_spec : forall {T} (v : alloc_vec_Vec T),
  to_Z (alloc_vec_Vec_len v) = Z.of_nat (List.length (vec_list v)).
Proof. intros T v. reflexivity. Qed.

(** A sub-slice. [core_slice_index_Slice_index] fails when [get] returns [None],
    so this is where "the range is inside the slice" turns into panic-freedom,
    and it is the only place the module decoder takes a sub-slice: the bytes of
    one function body. *)
Axiom slice_range_get_spec : forall {T} (s : slice T) (a b : usize),
  to_Z a <= to_Z b ->
  to_Z b <= Z.of_nat (List.length (vec_list s)) ->
  exists sub,
    core_slice_index_SliceIndexRangeUsizeSlice_get
      {| core_ops_range_Range_start := a; core_ops_range_Range_end_ := b |} s
      = Ok (Some sub)
    /\ vec_list sub = List.firstn (Z.to_nat (to_Z b - to_Z a))
                        (List.skipn (Z.to_nat (to_Z a)) (vec_list s)).

Lemma slice_range_ok : forall {T} (s : slice T) (a b : usize),
  to_Z a <= to_Z b ->
  to_Z b <= Z.of_nat (List.length (vec_list s)) ->
  exists sub,
    core_slice_index_Slice_index (core_slice_index_SliceIndexRangeUsizeSliceInst T)
      s {| core_ops_range_Range_start := a; core_ops_range_Range_end_ := b |}
      = Ok sub
    /\ vec_list sub = List.firstn (Z.to_nat (to_Z b - to_Z a))
                        (List.skipn (Z.to_nat (to_Z a)) (vec_list s)).
Proof.
  intros T s a b Hab Hb.
  destruct (slice_range_get_spec s a b Hab Hb) as [sub [Hget Hlist]].
  exists sub. split; [|exact Hlist].
  unfold core_slice_index_Slice_index. cbn [core_slice_index_SliceIndex_get
    core_slice_index_SliceIndexRangeUsizeSliceInst].
  rewrite Hget. reflexivity.
Qed.

(** Scalar arithmetic helpers used in loop proofs. *)

Lemma usize_nonneg : forall (i : usize), 0 <= to_Z i.
Proof.
  intros [z [Hlo Hhi]]. unfold scalar_min, usize_min in Hlo. exact Hlo.
Qed.

Lemma u32_nonneg : forall (i : scalar U32), (0 <= to_Z i)%Z.
Proof.
  intros [z [Hlo Hhi]]. unfold scalar_min, u32_min in Hlo. exact Hlo.
Qed.

Lemma usize_le_max : forall (i : usize), to_Z i <= usize_max.
Proof.
  intros [z [Hlo Hhi]]. unfold scalar_max in Hhi. simpl in Hhi. exact Hhi.
Qed.

Lemma scalar_geb_false_lt : forall {ty} (x y : scalar ty),
  (x s>= y) = false -> to_Z x < to_Z y.
Proof.
  intros ty x y H. unfold scalar_geb in H.
  destruct x as [xz Hx], y as [yz Hy].
  unfold Z.geb, to_Z in H; simpl in H.
  unfold to_Z; simpl.
  destruct (xz ?= yz) eqn:Ecmp; try discriminate.
  apply Z.compare_lt_iff in Ecmp. exact Ecmp.
Qed.

Lemma scalar_eqb_zero_true : forall (i : usize),
  to_Z i = 0 -> (i s= 0%usize) = true.
Proof.
  intros i H. unfold scalar_eqb. simpl. apply Z.eqb_eq. exact H.
Qed.

Lemma scalar_eqb_zero_false : forall (i : usize),
  to_Z i <> 0 -> (i s= 0%usize) = false.
Proof.
  intros i H. unfold scalar_eqb. simpl. apply Z.eqb_neq. exact H.
Qed.

Lemma mk_scalar_ok_to_Z : forall ty x (s : scalar ty),
  mk_scalar ty x = Ok s -> to_Z s = x.
Proof.
  intros ty x s H. unfold mk_scalar in H.
  destruct (sumbool_of_bool (scalar_in_bounds ty x)) as [Hok|Hfail]; [|discriminate].
  injection H as <-. reflexivity.
Qed.

Lemma usize_add_1_lt_max : forall (i : usize) {T} (s : slice T),
  (i s>= slice_len s) = false ->
  to_Z i + 1 <= usize_max.
Proof.
  intros i T s Hlt.
  apply scalar_geb_false_lt in Hlt.
  rewrite slice_len_spec in Hlt.
  pose proof (usize_le_max (slice_len s)).
  rewrite slice_len_spec in H. lia.
Qed.

Lemma usize_sub_1_ok : forall (i : usize),
  to_Z i >= 1 ->
  exists i', usize_sub i 1%usize = Ok i' /\ to_Z i' = to_Z i - 1.
Proof.
  intros i Hge. unfold usize_sub, scalar_sub.
  assert (H1 : to_Z 1%usize = 1) by reflexivity.
  rewrite H1. unfold mk_scalar.
  destruct (sumbool_of_bool (scalar_in_bounds Usize (to_Z i - 1))) as [Hok|Hfail].
  - eexists. split; reflexivity.
  - exfalso. assert (scalar_in_bounds Usize (to_Z i - 1) = true).
    { unfold scalar_in_bounds. apply Bool.andb_true_iff. split.
      - unfold scalar_ge_min. apply Bool.orb_true_iff. left.
        unfold scalar_min_cons. simpl. unfold u32_min. apply Z.leb_le. lia.
      - unfold scalar_le_max. apply Bool.orb_true_iff. right.
        simpl. apply Z.leb_le. pose proof (usize_le_max i). lia. }
    congruence.
Qed.

Lemma usize_sub_ok : forall (a b : usize),
  to_Z a >= to_Z b ->
  exists c, usize_sub a b = Ok c /\ to_Z c = to_Z a - to_Z b.
Proof.
  intros a b H. unfold usize_sub, scalar_sub.
  unfold mk_scalar.
  destruct (sumbool_of_bool (scalar_in_bounds Usize (to_Z a - to_Z b))) as [Hok|Hfail].
  - cbv iota. eexists. split; reflexivity.
  - exfalso. assert (scalar_in_bounds Usize (to_Z a - to_Z b) = true).
    { unfold scalar_in_bounds. apply Bool.andb_true_iff. split.
      - unfold scalar_ge_min. apply Bool.orb_true_iff. left.
        unfold scalar_min_cons. simpl. unfold u32_min. apply Z.leb_le.
        pose proof (usize_nonneg b). lia.
      - unfold scalar_le_max. apply Bool.orb_true_iff. right.
        simpl. apply Z.leb_le.
        pose proof (usize_le_max a). pose proof (usize_nonneg b). lia. }
    congruence.
Qed.

(** The converse of [scalar_geb_false_lt], for the completeness direction: a
    bounds check that ought to pass does pass. *)
Lemma scalar_geb_of_lt : forall {ty} (x y : scalar ty),
  to_Z x < to_Z y -> (x s>= y) = false.
Proof.
  intros ty x y H. unfold scalar_geb. rewrite Z.geb_leb.
  apply Z.leb_gt. exact H.
Qed.

Lemma scalar_geb_true_ge : forall {ty} (x y : scalar ty),
  (x s>= y) = true -> to_Z x >= to_Z y.
Proof.
  intros ty x y H. unfold scalar_geb in H.
  destruct x as [xz Hx], y as [yz Hy].
  unfold Z.geb, to_Z in *; simpl in *.
  destruct (xz ?= yz) eqn:Ecmp; try discriminate.
  - apply Z.compare_eq_iff in Ecmp. lia.
  - apply Z.compare_gt_iff in Ecmp. lia.
Qed.

Lemma N_to_nat_Z_to_N : forall (z : Z), N.to_nat (Z.to_N z) = Z.to_nat z.
Proof. intros z. destruct z as [|p|p]; reflexivity. Qed.

Lemma Z_to_nat_of_nat : forall (n : nat), Z.to_nat (Z.of_nat n) = n.
Proof.
  intro n. apply Nat2Z.inj.
  rewrite Z2Nat.id.
  - reflexivity.
  - apply Nat2Z.is_nonneg.
Qed.

(** The two directions a slice loop moves in. [pop_types] counts down, so it
    grows a [firstn] at the end; [push_types] counts up, so it uncons's a
    [skipn]. Both are indexed by the element the code just read. *)
Lemma firstn_nth_error_snoc : forall {T} k (l : list T) x,
  List.nth_error l k = Some x ->
  List.firstn (S k) l = List.firstn k l ++ [x].
Proof.
  induction k as [|k IH]; intros l x H; destruct l as [|h t];
    cbn [List.nth_error] in H; try discriminate.
  - injection H as <-. reflexivity.
  - assert (Hs : List.firstn (S (S k)) (h :: t) = h :: List.firstn (S k) t)
      by reflexivity.
    rewrite Hs. rewrite (IH t x H). reflexivity.
Qed.

Lemma skipn_nth_error : forall {T} k (l : list T) x,
  List.nth_error l k = Some x ->
  List.skipn k l = x :: List.skipn (S k) l.
Proof.
  induction k as [|k IH]; intros l x H; destruct l as [|h t];
    cbn [List.nth_error] in H; try discriminate.
  - injection H as <-. reflexivity.
  - exact (IH t x H).
Qed.

(** Uncons a [skipn] of a [map] in one step, giving the source element rather
    than its image. Stated directly rather than via [nth_error_map] because
    rewriting with that lemma's [option_map] form does not fire on the result. *)
Lemma skipn_map_cons_inv : forall {A B} (f : A -> B) k (l : list A) y rest,
  List.skipn k (List.map f l) = y :: rest ->
  exists x, List.nth_error l k = Some x
            /\ f x = y
            /\ (k < List.length l)%nat
            /\ List.skipn (S k) (List.map f l) = rest.
Proof.
  induction k as [|k IH]; intros l y rest H; destruct l as [|h t]; simpl in H.
  - discriminate.
  - injection H as <- <-. exists h. split; [reflexivity|].
    split; [reflexivity|]. split; [simpl; lia | reflexivity].
  - discriminate.
  - destruct (IH t y rest H) as [x [Hn [Hf [Hlt Hs]]]].
    exists x. split; [exact Hn|]. split; [exact Hf|].
    split; [simpl; lia | exact Hs].
Qed.

Lemma usize_add_ok : forall (a b : usize),
  to_Z a + to_Z b <= usize_max ->
  exists c, usize_add a b = Ok c /\ to_Z c = to_Z a + to_Z b.
Proof.
  intros a b Hmax. unfold usize_add, scalar_add, mk_scalar.
  destruct (sumbool_of_bool (scalar_in_bounds Usize (to_Z a + to_Z b)))
    as [Hok|Hfail].
  - eexists. split; reflexivity.
  - exfalso. assert (scalar_in_bounds Usize (to_Z a + to_Z b) = true).
    { unfold scalar_in_bounds. apply Bool.andb_true_iff. split.
      - unfold scalar_ge_min. apply Bool.orb_true_iff. left.
        unfold scalar_min_cons. simpl. unfold u32_min. apply Z.leb_le.
        pose proof (usize_nonneg a). pose proof (usize_nonneg b). lia.
      - unfold scalar_le_max. apply Bool.orb_true_iff. right.
        simpl. apply Z.leb_le. exact Hmax. }
    congruence.
Qed.

(** A successful addition, as a fact about [to_Z], with the literal's value
    carried across the same way the comparison lemmas do it. Stated over
    [scalar_add] so that the cursor and the loop counter share it. *)
Lemma scalar_add_val : forall {ty} (i j k : scalar ty) v,
  scalar_add i k = Ok j -> to_Z k = v -> to_Z j = to_Z i + v.
Proof.
  intros ty i j k v H <-. unfold scalar_add in H.
  apply mk_scalar_ok_to_Z in H. exact H.
Qed.

Lemma usize_add_1_ok : forall (i : usize),
  to_Z i + 1 <= usize_max ->
  exists i', usize_add i 1%usize = Ok i' /\ to_Z i' = to_Z i + 1.
Proof.
  intros i Hmax. unfold usize_add, scalar_add.
  assert (H1 : to_Z 1%usize = 1) by reflexivity.
  rewrite H1. unfold mk_scalar.
  destruct (sumbool_of_bool (scalar_in_bounds Usize (to_Z i + 1))) as [Hok|Hfail].
  - eexists. split; reflexivity.
  - exfalso. assert (scalar_in_bounds Usize (to_Z i + 1) = true).
    { unfold scalar_in_bounds. apply Bool.andb_true_iff. split.
      - unfold scalar_ge_min. apply Bool.orb_true_iff. left.
        unfold scalar_min_cons. simpl. unfold u32_min. apply Z.leb_le.
        pose proof (usize_nonneg i). lia.
      - unfold scalar_le_max. apply Bool.orb_true_iff. right.
        simpl. apply Z.leb_le. exact Hmax. }
    congruence.
Qed.

Lemma scalar_ge_geb_true : forall {ty} (x y : scalar ty),
  to_Z x >= to_Z y -> (x s>= y) = true.
Proof.
  intros ty x y H.
  destruct x as [xz Hx], y as [yz Hy].
  unfold scalar_geb, Z.geb, to_Z in *; simpl in *.
  destruct (Z.compare_spec xz yz) as [Heq|Hlt|Hgt]; simpl; try reflexivity.
  exfalso. lia.
Qed.

Lemma scalar_lt_geb_false : forall {ty} (x y : scalar ty),
  to_Z x < to_Z y -> (x s>= y) = false.
Proof.
  intros ty x y H.
  destruct x as [xz Hx], y as [yz Hy].
  unfold scalar_geb, Z.geb, to_Z in *; simpl in *.
  destruct (Z.compare_spec xz yz) as [Heq|Hlt|Hgt]; simpl;
    try reflexivity; exfalso; lia.
Qed.

Lemma Z_to_nat_add1 : forall z, 0 <= z -> Z.to_nat (z + 1) = S (Z.to_nat z).
Proof.
  intros z Hz. rewrite Z.add_1_r. apply Z2Nat.inj_succ. exact Hz.
Qed.

(** Monad plumbing: the ? operator compiles to branch + match ControlFlow. *)

Axiom branch_ok : forall {T E} (x : T),
  core_result_Result_Insts_CoreOpsTry_traitTryTResultInfallibleE_branch
    (@Core_result_Result_Ok T E x) =
  Ok (Core_ops_control_flow_ControlFlow_Continue x).

Axiom branch_err : forall {T E} (e : E),
  core_result_Result_Insts_CoreOpsTry_traitTryTResultInfallibleE_branch
    (@Core_result_Result_Err T E e) =
  Ok (@Core_ops_control_flow_ControlFlow_Break
        (core_result_Result_t core_convert_Infallible_t E) T
        (Core_result_Result_Err e)).

Axiom from_residual_err : forall (T : Type) {E : Type} (e : E),
  core_result_Result_Insts_CoreOpsTry_traitFromResidualResultInfallibleE_from_residual
    T (core_convert_From_Blanket E) (Core_result_Result_Err e) =
  Ok (Core_result_Result_Err e).

(** The same, for the conversion from a reader error to a module error. The
    two are separate axioms because [core_convert_From_Blanket_from] is itself
    an unspecified axiom, so the identity case cannot be derived from a general
    rule; [error_Error_Insts_CoreConvertFromOpError_from] is a real definition,
    and this says [from_residual] applies it. *)
Axiom from_residual_op_err : forall (T : Type) (e : error_OpError_t),
  core_result_Result_Insts_CoreOpsTry_traitFromResidualResultInfallibleE_from_residual
    T error_Error_Insts_CoreConvertFromOpError (Core_result_Result_Err e) =
  Ok (Core_result_Result_Err (Error_Error_Read e)).

(** The whole of the ? operator's error arm: branch, then whichever of the two
    conversions applies. Every walk over a decoder needs it, in the goal or in
    a hypothesis. *)
Ltac try_err_rw :=
  rewrite branch_err; cbn [bind];
  first [rewrite from_residual_err | rewrite from_residual_op_err]; cbn [bind].

Ltac try_err_rw_in H :=
  rewrite branch_err in H; cbn [bind] in H;
  first [rewrite from_residual_err in H | rewrite from_residual_op_err in H];
  cbn [bind] in H.

(** Clone returns an equal value for all our types. *)
Definition types_ValueType_t_beq (a b : types_ValueType_t) : bool :=
  match a, b with
  | Types_ValueType_I32, Types_ValueType_I32 => true
  | Types_ValueType_I64, Types_ValueType_I64 => true
  | Types_ValueType_F32, Types_ValueType_F32 => true
  | Types_ValueType_F64, Types_ValueType_F64 => true
  | _, _ => false
  end.

(** ValueType PartialEq *)
Lemma vt_eq_spec : forall a b,
  types_ValueType_Insts_CoreCmpPartialEqValueType_eq a b =
    Ok (types_ValueType_t_beq a b).
Proof. intros a b. destruct a, b; reflexivity. Qed.

Definition code_BlockType_t_beq (a b : code_BlockType_t) : bool :=
  match a, b with
  | Code_BlockType_Empty, Code_BlockType_Empty => true
  | Code_BlockType_Value x, Code_BlockType_Value y => types_ValueType_t_beq x y
  | _, _ => false
  end.

(** BlockType PartialEq. A lemma rather than an axiom: the derived [ne] is what
    costs one, and [br_table] only ever compares. *)
Lemma bt_eq_spec : forall a b,
  code_BlockType_Insts_CoreCmpPartialEqBlockType_eq a b =
    Ok (code_BlockType_t_beq a b).
Proof.
  intros a b. destruct a as [|x]; destruct b as [|y];
    [reflexivity | reflexivity | reflexivity | apply vt_eq_spec].
Qed.

(** The derived [ne]s. Aeneas emits these as axioms rather than as the
    negation of the [eq] it does translate, so each needs saying. *)
Axiom vt_ne_spec : forall a b,
  types_ValueType_Insts_CoreCmpPartialEqValueType_ne a b =
    Ok (negb (types_ValueType_t_beq a b)).

Definition types_Mut_t_beq (a b : types_Mut_t) : bool :=
  match a, b with
  | Types_Mut_Const, Types_Mut_Const => true
  | Types_Mut_Var, Types_Mut_Var => true
  | _, _ => false
  end.

Axiom mut_ne_spec : forall a b,
  types_Mut_Insts_CoreCmpPartialEqMut_ne a b =
    Ok (negb (types_Mut_t_beq a b)).

(** Scalar cast u32 <-> usize: succeeds and preserves the underlying Z. *)
Lemma scalar_cast_u32_usize : forall (x : scalar U32),
  exists y : scalar Usize, scalar_cast U32 Usize x = Ok y /\ to_Z y = to_Z x.
Proof.
  intros [z [Hlo Hhi]].
  unfold scalar_cast, mk_scalar, to_Z. simpl.
  unfold scalar_min, u32_min in Hlo.
  unfold scalar_max, u32_max in Hhi.
  destruct (sumbool_of_bool (scalar_in_bounds Usize z)) as [Hok|Hfail].
  - eexists. split; reflexivity.
  - exfalso. assert (H : scalar_in_bounds Usize z = true).
    { unfold scalar_in_bounds. apply Bool.andb_true_iff. split.
      - unfold scalar_ge_min. apply Bool.orb_true_iff. left.
        unfold scalar_min_cons. simpl. unfold u32_min. apply Z.leb_le. lia.
      - unfold scalar_le_max. apply Bool.orb_true_iff. left.
        unfold scalar_max_cons. simpl. unfold u32_max. apply Z.leb_le. lia. }
    congruence.
Qed.

(** Loop combinator: iterates body until Done. *)
Axiom loop_unfold : forall {A B}
  (f : A -> Primitives.result (LoopControl A B)) (a : A),
  loop f a =
    match f a with
    | Ok (Cont a') => loop f a'
    | Ok (Done b) => Ok b
    | Fail_ e => Fail_ e
    end.

(** array_to_slice/mk_array: the underlying list matches the given list. *)
(** ** Constructing scalars from bounds

    [mk_scalar_ok_to_Z] reads a successful construction; these go the other way,
    which is what the no-overflow side conditions need. *)

Lemma mk_scalar_ok_of_bounds : forall ty x,
  scalar_min ty <= x <= scalar_max ty ->
  exists s, mk_scalar ty x = Ok s /\ to_Z s = x.
Proof.
  intros ty x [Hlo Hhi]. unfold mk_scalar.
  assert (Hb : scalar_in_bounds ty x = true).
  { unfold scalar_in_bounds. apply Bool.andb_true_iff. split.
    - unfold scalar_ge_min. apply Bool.orb_true_iff. right.
      apply Z.leb_le. exact Hlo.
    - unfold scalar_le_max. apply Bool.orb_true_iff. right.
      apply Z.leb_le. exact Hhi. }
  destruct (sumbool_of_bool (scalar_in_bounds ty x)) as [Hok|Hfail].
  - eexists. split; reflexivity.
  - rewrite Hb in Hfail. discriminate.
Qed.

Lemma u8_bounds : forall (b : u8), 0 <= to_Z b <= 255.
Proof.
  intros [bz [Hlo Hhi]].
  unfold scalar_min, u8_min in Hlo. unfold scalar_max, u8_max in Hhi.
  unfold to_Z. simpl. lia.
Qed.

Lemma u32_bounds : forall (x : u32), 0 <= to_Z x <= u32_max.
Proof.
  intros [xz [Hlo Hhi]].
  unfold scalar_min, u32_min in Hlo. unfold scalar_max in Hhi.
  unfold to_Z. simpl. lia.
Qed.

(** Indexing succeeds inside the bounds. The panic-freedom proof needs this
    direction; [slice_index_usize_spec] gives the value once it does. *)
Lemma slice_index_usize_ok : forall {T} (s : slice T) (i : usize),
  to_Z i < Z.of_nat (List.length (vec_list s)) ->
  exists x, slice_index_usize s i = Ok x.
Proof.
  intros T s i Hlt. rewrite slice_index_usize_spec.
  destruct (List.nth_error (vec_list s) (Z.to_nat (to_Z i))) as [x|] eqn:Hnth.
  - exists x. reflexivity.
  - exfalso. apply List.nth_error_None in Hnth.
    pose proof (usize_nonneg i). lia.
Qed.

(** The converse of [slice_index_usize_ok]: a successful index was in bounds.
    Panic-freedom for the module decoder reads bounds back out of reads that
    already happened, rather than checking them again. *)
Lemma slice_index_usize_lt : forall {T} (s : slice T) (i : usize) x,
  slice_index_usize s i = Ok x -> to_Z i < to_Z (slice_len s).
Proof.
  intros T s i x H. rewrite slice_index_usize_spec in H.
  destruct (List.nth_error (vec_list s) (Z.to_nat (to_Z i))) eqn:Hnth;
    [|discriminate].
  assert (Hlt : (Z.to_nat (to_Z i) < List.length (vec_list s))%nat).
  { apply List.nth_error_Some. rewrite Hnth. discriminate. }
  rewrite slice_len_spec. pose proof (usize_nonneg i). lia.
Qed.

Lemma u8_rem_128_ok : forall (b : u8),
  exists low, u8_rem b 128%u8 = Ok low
              /\ to_Z low = Z.rem (to_Z b) 128
              /\ 0 <= to_Z low < 128.
Proof.
  intros b. pose proof (u8_bounds b) as [Hlo Hhi].
  assert (H128 : to_Z 128%u8 = 128) by reflexivity.
  assert (Hrem : 0 <= Z.rem (to_Z b) 128 < 128)
    by (apply Z.rem_bound_pos; lia).
  unfold u8_rem, scalar_rem. rewrite H128.
  destruct (mk_scalar_ok_of_bounds U8 (Z.rem (to_Z b) 128)) as [low [Hmk Hval]].
  { unfold scalar_min, scalar_max, u8_min, u8_max. simpl. lia. }
  exists low. rewrite Hmk. split; [reflexivity|]. split; [exact Hval|]. lia.
Qed.

Lemma cast_u8_u32_ok : forall (x : u8),
  exists y : u32, scalar_cast U8 U32 x = Ok y /\ to_Z y = to_Z x.
Proof.
  intros x. pose proof (u8_bounds x) as [Hlo Hhi].
  unfold scalar_cast.
  destruct (mk_scalar_ok_of_bounds U32 (to_Z x)) as [y [Hmk Hval]].
  { unfold scalar_min, scalar_max, u32_min, u32_max. simpl. lia. }
  exists y. rewrite Hmk. split; [reflexivity | exact Hval].
Qed.

(** A [u32] always fits a [usize], by [usize_max_bound]. *)
Lemma cast_u32_usize_ok : forall (x : u32),
  exists y : usize, scalar_cast U32 Usize x = Ok y /\ to_Z y = to_Z x.
Proof.
  intros x. pose proof (u32_bounds x) as [Hlo Hhi].
  pose proof usize_max_bound as Hb. unfold scalar_cast.
  destruct (mk_scalar_ok_of_bounds Usize (to_Z x)) as [y [Hmk Hval]].
  { unfold scalar_min, scalar_max, usize_min. simpl. lia. }
  exists y. rewrite Hmk. split; [reflexivity | exact Hval].
Qed.

Lemma u32_mul_ok : forall (x y : u32),
  to_Z x * to_Z y <= u32_max ->
  exists z, u32_mul x y = Ok z /\ to_Z z = to_Z x * to_Z y.
Proof.
  intros x y Hle. pose proof (u32_bounds x) as [Hx _].
  pose proof (u32_bounds y) as [Hy _].
  unfold u32_mul, scalar_mul.
  destruct (mk_scalar_ok_of_bounds U32 (to_Z x * to_Z y)) as [z [Hmk Hval]].
  { unfold scalar_min, scalar_max, u32_min. simpl.
    split; [apply Z.mul_nonneg_nonneg; lia | exact Hle]. }
  exists z. rewrite Hmk. split; [reflexivity | exact Hval].
Qed.

Lemma u32_add_ok : forall (x y : u32),
  to_Z x + to_Z y <= u32_max ->
  exists z, u32_add x y = Ok z /\ to_Z z = to_Z x + to_Z y.
Proof.
  intros x y Hle. pose proof (u32_bounds x) as [Hx _].
  pose proof (u32_bounds y) as [Hy _].
  unfold u32_add, scalar_add.
  destruct (mk_scalar_ok_of_bounds U32 (to_Z x + to_Z y)) as [z [Hmk Hval]].
  { unfold scalar_min, scalar_max, u32_min. simpl. lia. }
  exists z. rewrite Hmk. split; [reflexivity | exact Hval].
Qed.

(** Reflect the scalar comparison booleans into [Z] facts. [scalar_geb] already
    has [scalar_geb_true_ge] and [scalar_geb_false_lt] above; these cover the
    rest. *)

Lemma scalar_eqb_true : forall {ty} (x y : scalar ty),
  (x s= y) = true -> to_Z x = to_Z y.
Proof.
  intros ty x y H. unfold scalar_eqb in H. apply Z.eqb_eq. exact H.
Qed.

Lemma scalar_eqb_false : forall {ty} (x y : scalar ty),
  (x s= y) = false -> to_Z x <> to_Z y.
Proof.
  intros ty x y H. unfold scalar_eqb in H. apply Z.eqb_neq. exact H.
Qed.

Lemma scalar_neqb_false : forall {ty} (x y : scalar ty),
  (x s<> y) = false -> to_Z x = to_Z y.
Proof.
  intros ty x y H. unfold scalar_neqb in H.
  apply Bool.negb_false_iff in H. apply Z.eqb_eq. exact H.
Qed.

Lemma scalar_neqb_true : forall {ty} (x y : scalar ty),
  (x s<> y) = true -> to_Z x <> to_Z y.
Proof.
  intros ty x y H. unfold scalar_neqb in H.
  apply Bool.negb_true_iff in H. apply Z.eqb_neq. exact H.
Qed.

Lemma scalar_ltb_true : forall {ty} (x y : scalar ty),
  (x s< y) = true -> to_Z x < to_Z y.
Proof.
  intros ty x y H. unfold scalar_ltb in H. apply Z.ltb_lt. exact H.
Qed.

Lemma scalar_ltb_false : forall {ty} (x y : scalar ty),
  (x s< y) = false -> to_Z y <= to_Z x.
Proof.
  intros ty x y H. unfold scalar_ltb in H.
  apply Z.ltb_ge in H. exact H.
Qed.

Lemma scalar_gtb_true : forall {ty} (x y : scalar ty),
  (x s> y) = true -> to_Z y < to_Z x.
Proof.
  intros ty x y H. unfold scalar_gtb in H.
  apply Z.gtb_lt in H. exact H.
Qed.

Lemma scalar_gtb_false : forall {ty} (x y : scalar ty),
  (x s> y) = false -> to_Z x <= to_Z y.
Proof.
  intros ty x y H. unfold scalar_gtb in H.
  rewrite Z.gtb_ltb in H. apply Z.ltb_ge in H. exact H.
Qed.

Lemma scalar_gtb_of_le : forall {ty} (x y : scalar ty),
  to_Z x <= to_Z y -> (x s> y) = false.
Proof.
  intros ty x y H. unfold scalar_gtb. rewrite Z.gtb_ltb. apply Z.ltb_ge.
  exact H.
Qed.

(** [Include]ing the extracted modules shadows some Primitives constants with
    opaque copies, so [unfold u32_max] fails downstream even though conversion
    still works. Expose the bound as a rewritable equation instead. *)
Lemma u32_max_val : u32_max = 4294967295.
Proof. reflexivity. Qed.

Lemma scalar_neqb_of_neq : forall {ty} (x y : scalar ty),
  to_Z x <> to_Z y -> (x s<> y) = true.
Proof.
  intros ty x y H. unfold scalar_neqb, scalar_eqb.
  apply Bool.negb_true_iff. apply Z.eqb_neq. exact H.
Qed.

Lemma scalar_leb_true : forall {ty} (x y : scalar ty),
  (x s<= y) = true -> to_Z x <= to_Z y.
Proof.
  intros ty x y H. unfold scalar_leb in H. apply Z.leb_le. exact H.
Qed.

Lemma scalar_leb_false : forall {ty} (x y : scalar ty),
  (x s<= y) = false -> to_Z y < to_Z x.
Proof.
  intros ty x y H. unfold scalar_leb in H. apply Z.leb_gt in H. exact H.
Qed.

(** The constructors that were missing, for the completeness direction: a guard
    whose value is known has to be *computed*, not read off. *)
Lemma scalar_leb_of_le : forall {ty} (x y : scalar ty),
  to_Z x <= to_Z y -> (x s<= y) = true.
Proof. intros ty x y H. unfold scalar_leb. apply Z.leb_le. exact H. Qed.

Lemma scalar_leb_of_gt : forall {ty} (x y : scalar ty),
  to_Z y < to_Z x -> (x s<= y) = false.
Proof. intros ty x y H. unfold scalar_leb. apply Z.leb_gt. exact H. Qed.

Lemma scalar_ltb_of_ge : forall {ty} (x y : scalar ty),
  to_Z y <= to_Z x -> (x s< y) = false.
Proof. intros ty x y H. unfold scalar_ltb. apply Z.ltb_ge. exact H. Qed.

(** The same five again, delivering the literal's *value* rather than its
    [to_Z]. Every guard in the decoder compares against a literal, and
    [to_Z 127%u8] is convertible to [127] but not syntactically equal, which is
    the difference between [lia] closing and not. The comparison comes first so
    that the literal is resolved before [eq_refl] is checked. *)

Lemma scalar_leb_val : forall {ty} (x y : scalar ty) k,
  (x s<= y) = true -> to_Z y = k -> to_Z x <= k.
Proof. intros ty x y k H <-. apply scalar_leb_true. exact H. Qed.

Lemma scalar_geb_val : forall {ty} (x y : scalar ty) k,
  (x s>= y) = true -> to_Z y = k -> k <= to_Z x.
Proof. intros ty x y k H <-. apply Z.ge_le, scalar_geb_true_ge. exact H. Qed.

Lemma scalar_eqb_val : forall {ty} (x y : scalar ty) k,
  (x s= y) = true -> to_Z y = k -> to_Z x = k.
Proof. intros ty x y k H <-. apply scalar_eqb_true. exact H. Qed.

Lemma scalar_gtb_false_val : forall {ty} (x y : scalar ty) k,
  (x s> y) = false -> to_Z y = k -> to_Z x <= k.
Proof. intros ty x y k H <-. apply scalar_gtb_false. exact H. Qed.

(** Not in the standard library, which only has [rev_nth] for the
    default-valued [nth]. Proved here rather than in a file that imports
    ssreflect, to avoid the notation clash. *)
Lemma nth_error_rev : forall {A} (l : list A) n,
  (n < List.length l)%nat ->
  List.nth_error (List.rev l) n = List.nth_error l (List.length l - S n).
Proof.
  intros A l. induction l as [|a l IH]; intros n Hn; simpl in *; [lia|].
  destruct (Nat.lt_ge_cases n (List.length l)) as [Hlt|Hge].
  - rewrite List.nth_error_app1.
    2: { rewrite List.rev_length. exact Hlt. }
    rewrite IH by exact Hlt.
    destruct (List.length l - n)%nat eqn:Hd; [lia|].
    simpl. f_equal. lia.
  - assert (Hn' : n = List.length l) by lia. subst n.
    rewrite List.nth_error_app2.
    2: { rewrite List.rev_length. lia. }
    rewrite List.rev_length.
    replace (List.length l - List.length l)%nat with 0%nat by lia.
    replace (List.length l - List.length l)%nat with 0%nat by lia.
    reflexivity.
Qed.

(** ** Signed scalar helpers, for the signed LEB128 reader

    Same shape as the u32 family above. The rewritable bound equations exist for
    the same reason as [u32_max_val]: [Include]ing the extracted modules blocks
    [unfold] on Primitives constants while leaving conversion intact. *)

Lemma i64_max_val : i64_max = 9223372036854775807.
Proof. reflexivity. Qed.

Lemma i64_min_val : i64_min = -9223372036854775808.
Proof. reflexivity. Qed.

Lemma i32_max_val : i32_max = 2147483647.
Proof. reflexivity. Qed.

Lemma i32_min_val : i32_min = -2147483648.
Proof. reflexivity. Qed.

(** The narrow step of the signed LEB128 reader: the two range checks in front of
    the cast to [i32] are exactly the cast's precondition. *)
(** ** u64, for the little-endian float immediate reader

    Spec 5.2.3's [fN] is [N/8] raw bytes, so the reader assembles up to eight of
    them into a [u64]. Same shape as the u32 family above. *)

Lemma u64_max_val : u64_max = 18446744073709551615.
Proof. reflexivity. Qed.

Lemma u64_bounds : forall (x : u64), 0 <= to_Z x <= u64_max.
Proof.
  intros [xz [Hlo Hhi]]. unfold scalar_min, scalar_max, u64_min in *.
  unfold to_Z. simpl. lia.
Qed.

Lemma cast_u8_u64_ok : forall (x : u8),
  exists y : u64, scalar_cast U8 U64 x = Ok y /\ to_Z y = to_Z x.
Proof.
  intros x. pose proof (u8_bounds x) as [Hlo Hhi].
  unfold scalar_cast.
  destruct (mk_scalar_ok_of_bounds U64 (to_Z x)) as [y [Hmk Hval]].
  { unfold scalar_min, scalar_max, u64_min, u64_max. simpl. lia. }
  exists y. rewrite Hmk. split; [reflexivity | exact Hval].
Qed.

Lemma cast_u64_u32_ok : forall (x : u64),
  to_Z x <= u32_max ->
  exists y : u32, scalar_cast U64 U32 x = Ok y /\ to_Z y = to_Z x.
Proof.
  intros x Hle. pose proof (u64_bounds x) as [Hlo _]. unfold scalar_cast.
  destruct (mk_scalar_ok_of_bounds U32 (to_Z x)) as [y [Hmk Hval]].
  { unfold scalar_min, scalar_max, u32_min. simpl. split; [lia | exact Hle]. }
  exists y. rewrite Hmk. split; [reflexivity | exact Hval].
Qed.

Lemma u64_mul_ok : forall (x y : u64),
  to_Z x * to_Z y <= u64_max ->
  exists z, u64_mul x y = Ok z /\ to_Z z = to_Z x * to_Z y.
Proof.
  intros x y Hle. pose proof (u64_bounds x) as [Hx _].
  pose proof (u64_bounds y) as [Hy _].
  unfold u64_mul, scalar_mul.
  destruct (mk_scalar_ok_of_bounds U64 (to_Z x * to_Z y)) as [z [Hmk Hval]].
  { unfold scalar_min, scalar_max, u64_min. simpl.
    split; [apply Z.mul_nonneg_nonneg; lia | exact Hle]. }
  exists z. rewrite Hmk. split; [reflexivity | exact Hval].
Qed.

Lemma u64_add_ok : forall (x y : u64),
  to_Z x + to_Z y <= u64_max ->
  exists z, u64_add x y = Ok z /\ to_Z z = to_Z x + to_Z y.
Proof.
  intros x y Hle. pose proof (u64_bounds x) as [Hx _].
  pose proof (u64_bounds y) as [Hy _].
  unfold u64_add, scalar_add.
  destruct (mk_scalar_ok_of_bounds U64 (to_Z x + to_Z y)) as [z [Hmk Hval]].
  { unfold scalar_min, scalar_max, u64_min. simpl. split; [lia | exact Hle]. }
  exists z. rewrite Hmk. split; [reflexivity | exact Hval].
Qed.

(** ** i128, for the signed LEB128 reader's accumulator

    The signed reader accumulates in [i128] because its place value reaches
    [128 ^ 9 = 2 ^ 63], which a 64-bit accumulator cannot multiply a byte into.
    Same shape as the i64 family above. *)

Lemma i128_max_val : i128_max = 170141183460469231731687303715884105727.
Proof. reflexivity. Qed.

Lemma i128_min_val : i128_min = -170141183460469231731687303715884105728.
Proof. reflexivity. Qed.

Lemma cast_u8_i128_ok : forall (x : u8),
  exists y : i128, scalar_cast U8 I128 x = Ok y /\ to_Z y = to_Z x.
Proof.
  intros x. pose proof (u8_bounds x) as [Hlo Hhi].
  unfold scalar_cast.
  destruct (mk_scalar_ok_of_bounds I128 (to_Z x)) as [y [Hmk Hval]].
  { unfold scalar_min, scalar_max, i128_min, i128_max. simpl. lia. }
  exists y. rewrite Hmk. split; [reflexivity | exact Hval].
Qed.

Lemma cast_i128_i32_ok : forall (x : i128),
  i32_min <= to_Z x <= i32_max ->
  exists y : i32, scalar_cast I128 I32 x = Ok y /\ to_Z y = to_Z x.
Proof.
  intros x Hb. unfold scalar_cast.
  destruct (mk_scalar_ok_of_bounds I32 (to_Z x)) as [y [Hmk Hval]].
  { unfold scalar_min, scalar_max. simpl. exact Hb. }
  exists y. rewrite Hmk. split; [reflexivity | exact Hval].
Qed.

Lemma cast_i128_i64_ok : forall (x : i128),
  i64_min <= to_Z x <= i64_max ->
  exists y : i64, scalar_cast I128 I64 x = Ok y /\ to_Z y = to_Z x.
Proof.
  intros x Hb. unfold scalar_cast.
  destruct (mk_scalar_ok_of_bounds I64 (to_Z x)) as [y [Hmk Hval]].
  { unfold scalar_min, scalar_max. simpl. exact Hb. }
  exists y. rewrite Hmk. split; [reflexivity | exact Hval].
Qed.

Lemma i128_mul_ok : forall (x y : i128),
  i128_min <= to_Z x * to_Z y <= i128_max ->
  exists z, i128_mul x y = Ok z /\ to_Z z = to_Z x * to_Z y.
Proof.
  intros x y Hb. unfold i128_mul, scalar_mul.
  destruct (mk_scalar_ok_of_bounds I128 (to_Z x * to_Z y)) as [z [Hmk Hval]].
  { unfold scalar_min, scalar_max. simpl. exact Hb. }
  exists z. rewrite Hmk. split; [reflexivity | exact Hval].
Qed.

Lemma i128_add_ok : forall (x y : i128),
  i128_min <= to_Z x + to_Z y <= i128_max ->
  exists z, i128_add x y = Ok z /\ to_Z z = to_Z x + to_Z y.
Proof.
  intros x y Hb. unfold i128_add, scalar_add.
  destruct (mk_scalar_ok_of_bounds I128 (to_Z x + to_Z y)) as [z [Hmk Hval]].
  { unfold scalar_min, scalar_max. simpl. exact Hb. }
  exists z. rewrite Hmk. split; [reflexivity | exact Hval].
Qed.

Lemma i128_sub_ok : forall (x y : i128),
  i128_min <= to_Z x - to_Z y <= i128_max ->
  exists z, i128_sub x y = Ok z /\ to_Z z = to_Z x - to_Z y.
Proof.
  intros x y Hb. unfold i128_sub, scalar_sub.
  destruct (mk_scalar_ok_of_bounds I128 (to_Z x - to_Z y)) as [z [Hmk Hval]].
  { unfold scalar_min, scalar_max. simpl. exact Hb. }
  exists z. rewrite Hmk. split; [reflexivity | exact Hval].
Qed.

Lemma nth_error_snoc : forall {A} (cs : list A) (c : A),
  List.nth_error (cs ++ [c]) (List.length cs) = Some c.
Proof.
  intros A cs c. induction cs as [|a cs IH]; simpl; [reflexivity | exact IH].
Qed.

(** ** Vec update and index_mut

    Both are axioms in Primitives.v with no specs. These mirror
    [alloc_vec_Vec_index_mut_usize] (Primitives.v:866), which *is* defined, as
    index-then-update; the pair below says the trait-dispatched version agrees.
    Auditable against that definition by eye. *)

Fixpoint list_update {T} (l : list T) (n : nat) (x : T) : list T :=
  match l, n with
  | [], _ => []
  | _ :: t, O => x :: t
  | h :: t, S n' => h :: list_update t n' x
  end.

Axiom vec_update_spec : forall {T} (v : alloc_vec_Vec T) (i : usize) (x : T),
  vec_list (alloc_vec_Vec_update v i x)
    = list_update (vec_list v) (Z.to_nat (to_Z i)) x.

Axiom vec_index_mut_spec : forall {T} (v : alloc_vec_Vec T) (i : usize),
  alloc_vec_Vec_index_mut (core_slice_index_SliceIndexUsizeSliceInst T) v i
    = match List.nth_error (vec_list v) (Z.to_nat (to_Z i)) with
      | Some x => Ok (x, alloc_vec_Vec_update v i)
      | None => Fail_ Failure
      end.

Lemma list_update_snoc : forall {T} (cs : list T) (c x : T),
  list_update (cs ++ [c]) (List.length cs) x = cs ++ [x].
Proof.
  intros T cs c x. induction cs as [|h cs IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

(** A successful pop that yielded an element exposes the vector as a snoc. *)
Lemma vec_pop_snoc : forall {T} (v : alloc_vec_Vec T) x v',
  alloc_vec_Vec_pop alloc_alloc_Global v = Ok (Some x, v') ->
  vec_list v = vec_list v' ++ [x].
Proof.
  intros T v x v' H.
  pose proof (vec_pop_last alloc_alloc_Global v (Some x) v' H) as Hspec.
  destruct (List.rev (vec_list v)) as [|y rest] eqn:Hrev.
  - destruct Hspec as [Ho _]. discriminate Ho.
  - destruct Hspec as [Ho Hv]. injection Ho as <-. rewrite Hv.
    apply (f_equal (@List.rev _)) in Hrev.
    rewrite List.rev_involutive in Hrev. rewrite Hrev. reflexivity.
Qed.

(** A pop never lengthens the vector, whatever it returned. The panic-freedom
    argument needs only this much about it. *)
Lemma vec_pop_size : forall {T} (v : alloc_vec_Vec T) o v',
  alloc_vec_Vec_pop alloc_alloc_Global v = Ok (o, v') ->
  (List.length (vec_list v') <= List.length (vec_list v))%nat.
Proof.
  intros T v o v' H.
  pose proof (vec_pop_last alloc_alloc_Global v o v' H) as Hspec.
  destruct (List.rev (vec_list v)) as [|x rest] eqn:Hrev.
  - destruct Hspec as [_ Hv]. rewrite Hv. apply Nat.le_0_l.
  - destruct Hspec as [_ Hv]. rewrite Hv. rewrite List.rev_length.
    apply (f_equal (@List.length _)) in Hrev.
    rewrite List.rev_length in Hrev. rewrite Hrev. simpl. lia.
Qed.

Lemma list_update_length : forall {T} (l : list T) n x,
  List.length (list_update l n x) = List.length l.
Proof.
  intros T l. induction l as [|h l IH]; intros n x; [reflexivity|].
  destruct n as [|n]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

(** The other direction: a vector already known to be a snoc pops its last
    element, whatever the caller does with the returned option. *)
Lemma vec_pop_of_snoc : forall {T} (v : alloc_vec_Vec T) cs c o v',
  vec_list v = cs ++ [c] ->
  alloc_vec_Vec_pop alloc_alloc_Global v = Ok (o, v') ->
  o = Some c /\ vec_list v' = cs.
Proof.
  intros T v cs c o v' Hsnoc H.
  pose proof (vec_pop_last alloc_alloc_Global v o v' H) as Hspec.
  rewrite Hsnoc in Hspec. rewrite List.rev_app_distr in Hspec.
  simpl in Hspec. destruct Hspec as [Ho Hv].
  split; [exact Ho|]. rewrite Hv. apply List.rev_involutive.
Qed.
