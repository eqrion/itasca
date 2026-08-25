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
Require Import Coq.Logic.ProofIrrelevance.
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

Lemma scalar_to_Z_inj : forall {ty} (x y : scalar ty),
  to_Z x = to_Z y -> x = y.
Proof.
  intros ty [x Hx] [y Hy] H. cbn in H. subst y.
  f_equal. apply proof_irrelevance.
Qed.

Lemma vec_new_list : forall T, vec_list (alloc_vec_Vec_new T) = [].
Proof. reflexivity. Qed.

(** Logical list views of Aeneas arrays and the allocation-free stacks.  The
    prefix lives in a fixed array and any suffix in the overflow vector. *)
Definition array_list {T n} (a : array T n) : list T := proj1_sig a.

Definition vals_inline_list (v : array code_StackType_t 32%usize) :
  list code_StackType_t := array_list v.

Definition ctrls_inline_list (v : array code_Ctrl_t 16%usize) :
  list code_Ctrl_t := array_list v.

Definition locals_inline_list (v : array types_ValueType_t 32%usize) :
  list types_ValueType_t := array_list v.

Definition vals_list (v : code_ValsStack_t) : list code_StackType_t :=
  if v.(code_ValsStack_inline_len) s>= 32%usize
  then vals_inline_list v.(code_ValsStack_inline)
       ++ vec_list v.(code_ValsStack_overflow)
  else List.firstn (Z.to_nat (to_Z v.(code_ValsStack_inline_len)))
                   (vals_inline_list v.(code_ValsStack_inline)).

Definition ctrls_list (v : code_CtrlsStack_t) : list code_Ctrl_t :=
  if v.(code_CtrlsStack_inline_len) s>= 16%usize
  then ctrls_inline_list v.(code_CtrlsStack_inline)
       ++ vec_list v.(code_CtrlsStack_overflow)
  else List.firstn (Z.to_nat (to_Z v.(code_CtrlsStack_inline_len)))
                   (ctrls_inline_list v.(code_CtrlsStack_inline)).

Definition locals_list (v : code_LocalsStack_t) : list types_ValueType_t :=
  if v.(code_LocalsStack_inline_len) s>= 32%usize
  then locals_inline_list v.(code_LocalsStack_inline)
       ++ vec_list v.(code_LocalsStack_overflow)
  else List.firstn (Z.to_nat (to_Z v.(code_LocalsStack_inline_len)))
                   (locals_inline_list v.(code_LocalsStack_inline)).
Lemma vals_stack_new_spec : forall v,
  code_ValsStack_new = Ok v -> vals_list v = [].
Proof.
  intros v H. unfold code_ValsStack_new in H.
  cbn [bind] in H. injection H as <-. reflexivity.
Qed.

Lemma ctrls_stack_new_spec : forall v,
  code_CtrlsStack_new = Ok v -> ctrls_list v = [].
Proof.
  intros v H. unfold code_CtrlsStack_new in H.
  cbn [bind] in H. injection H as <-. reflexivity.
Qed.

Lemma locals_stack_new_spec : forall v,
  code_LocalsStack_new = Ok v -> locals_list v = [].
Proof.
  intros v H. unfold code_LocalsStack_new in H.
  cbn [bind] in H. injection H as <-. reflexivity.
Qed.

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

(** Aeneas leaves array operations opaque, just as it does several [Vec]
    operations above.  These assumptions state their ordinary Rust list
    semantics.  The array length itself is not assumed: it follows from the
    subtype used by [Primitives.array]. *)
Lemma array_list_length : forall {T n} (a : array T n),
  Z.of_nat (List.length (array_list a)) = to_Z n.
Proof. intros T n [l Hl]. exact Hl. Qed.

Lemma vals_inline_list_length : forall a,
  List.length (vals_inline_list a) = 32%nat.
Proof.
  intros a. unfold vals_inline_list.
  pose proof (array_list_length a) as H. apply Nat2Z.inj. cbn. exact H.
Qed.

Lemma ctrls_inline_list_length : forall a,
  List.length (ctrls_inline_list a) = 16%nat.
Proof.
  intros a. unfold ctrls_inline_list.
  pose proof (array_list_length a) as H. apply Nat2Z.inj. cbn. exact H.
Qed.

Lemma locals_inline_list_length : forall a,
  List.length (locals_inline_list a) = 32%nat.
Proof.
  intros a. unfold locals_inline_list.
  pose proof (array_list_length a) as H. apply Nat2Z.inj. cbn. exact H.
Qed.

Axiom array_index_usize_spec : forall {T n} (a : array T n) i,
  array_index_usize a i =
    match List.nth_error (array_list a) (Z.to_nat (to_Z i)) with
    | Some x => Ok x
    | None => Fail_ Failure
    end.

Axiom array_update_spec : forall {T n} (a : array T n) i (x : T),
  array_list (array_update a i x) =
    list_update (array_list a) (Z.to_nat (to_Z i)) x.

Axiom array_update_usize_spec : forall {T n} (a : array T n) i (x : T),
  0 <= to_Z i < to_Z n ->
  exists a', array_update_usize a i x = Ok a' /\
    array_list a' = list_update (array_list a) (Z.to_nat (to_Z i)) x.

Lemma array_index_usize_total : forall {T n} (a : array T n) i,
  0 <= to_Z i < to_Z n -> exists x, array_index_usize a i = Ok x.
Proof.
  intros T n a i Hrange. rewrite array_index_usize_spec.
  destruct (List.nth_error (array_list a) (Z.to_nat (to_Z i))) eqn:Hnth.
  - eauto.
  - apply List.nth_error_None in Hnth.
    pose proof (array_list_length a) as Hlen.
    pose proof (usize_nonneg i) as Hi.
    apply Nat2Z.inj_le in Hnth.
    rewrite Z2Nat.id in Hnth by exact Hi. lia.
Qed.

Lemma vals_inline_get_spec : forall (a : array code_StackType_t 32%usize) i x,
  0 <= to_Z i < 32 ->
  array_index_usize a i = Ok x ->
  List.nth_error (vals_inline_list a) (Z.to_nat (to_Z i)) = Some x.
Proof.
  intros a i x _ Hget. rewrite array_index_usize_spec in Hget.
  destruct (List.nth_error (array_list a) (Z.to_nat (to_Z i)))
    eqn:Hnth.
  - injection Hget as <-. exact Hnth.
  - discriminate.
Qed.

Lemma vals_inline_get_total : forall (a : array code_StackType_t 32%usize) i,
  0 <= to_Z i < 32 -> exists x, array_index_usize a i = Ok x.
Proof. intros. apply array_index_usize_total. cbn. exact H. Qed.

Lemma vals_inline_set_spec : forall (a : array code_StackType_t 32%usize) i x,
  vals_inline_list (array_update a i x) =
    list_update (vals_inline_list a) (Z.to_nat (to_Z i)) x.
Proof. intros. apply array_update_spec. Qed.

Lemma locals_inline_get_spec : forall (a : array types_ValueType_t 32%usize) i x,
  0 <= to_Z i < 32 ->
  array_index_usize a i = Ok x ->
  List.nth_error (locals_inline_list a) (Z.to_nat (to_Z i)) = Some x.
Proof.
  intros a i x _ Hget. rewrite array_index_usize_spec in Hget.
  destruct (List.nth_error (array_list a) (Z.to_nat (to_Z i)))
    eqn:Hnth.
  - injection Hget as <-. exact Hnth.
  - discriminate.
Qed.

Lemma locals_inline_get_total : forall (a : array types_ValueType_t 32%usize) i,
  0 <= to_Z i < 32 -> exists x, array_index_usize a i = Ok x.
Proof. intros. apply array_index_usize_total. cbn. exact H. Qed.

Lemma locals_inline_set_spec : forall (a : array types_ValueType_t 32%usize) i x,
  locals_inline_list (array_update a i x) =
    list_update (locals_inline_list a) (Z.to_nat (to_Z i)) x.
Proof. intros. apply array_update_spec. Qed.

Lemma ctrls_inline_get_spec : forall (a : array code_Ctrl_t 16%usize) i x,
  0 <= to_Z i < 16 ->
  array_index_usize a i = Ok x ->
  List.nth_error (ctrls_inline_list a) (Z.to_nat (to_Z i)) = Some x.
Proof.
  intros a i x _ Hget. rewrite array_index_usize_spec in Hget.
  destruct (List.nth_error (array_list a) (Z.to_nat (to_Z i)))
    eqn:Hnth.
  - injection Hget as <-. exact Hnth.
  - discriminate.
Qed.

Lemma ctrls_inline_get_total : forall (a : array code_Ctrl_t 16%usize) i,
  0 <= to_Z i < 16 -> exists x, array_index_usize a i = Ok x.
Proof. intros. apply array_index_usize_total. cbn. exact H. Qed.

Lemma ctrls_inline_set_spec : forall (a : array code_Ctrl_t 16%usize) i x,
  ctrls_inline_list (array_update a i x) =
    list_update (ctrls_inline_list a) (Z.to_nat (to_Z i)) x.
Proof. intros. apply array_update_spec. Qed.

Lemma ctrls_inline_update_spec : forall (a : array code_Ctrl_t 16%usize) i x a',
  0 <= to_Z i < 16 -> array_update_usize a i x = Ok a' ->
  ctrls_inline_list a' =
    list_update (ctrls_inline_list a) (Z.to_nat (to_Z i)) x.
Proof.
  intros a i x a' Hrange Hupdate.
  destruct (array_update_usize_spec a i x Hrange) as [a'' [Heq Hlist]].
  rewrite Hupdate in Heq. injection Heq as <-. exact Hlist.
Qed.

Lemma ctrls_inline_set_total : forall (a : array code_Ctrl_t 16%usize) i x,
  0 <= to_Z i < 16 -> exists a', array_update_usize a i x = Ok a'.
Proof.
  intros. destruct (array_update_usize_spec a i x H) as [a' [Heq _]].
  eauto.
Qed.

Lemma firstn_list_update_snoc : forall {T} (l : list T) n x,
  (n < List.length l)%nat ->
  List.firstn (S n) (list_update l n x) = List.firstn n l ++ [x].
Proof.
  intros T l. induction l as [|h l IH]; intros [|n] x Hlt; cbn in *;
    try lia; [reflexivity|].
  rewrite IH by lia. reflexivity.
Qed.

Lemma list_update_last_snoc : forall {T} (l : list T) n x,
  List.length l = S n ->
  list_update l n x = List.firstn n l ++ [x].
Proof.
  intros T l. induction l as [|h l IH]; intros [|n] x Hlen.
  - discriminate.
  - discriminate.
  - cbn in Hlen. destruct l; [reflexivity|discriminate].
  - cbn in Hlen.
    change (h :: list_update l n x = h :: (List.firstn n l ++ [x])).
    f_equal. apply IH. lia.
Qed.

(** The storage split is fully abstract: every finite inline-length constructor
    denotes a prefix, while overflow mode denotes all inline slots followed by
    the vector.  These operation lemmas are the bridge used by the validator
    proof; they are derived from the definitions above, not assumptions. *)
Lemma vals_stack_push_spec : forall v x v',
  code_ValsStack_push v x = Ok v' ->
  vals_list v' = vals_list v ++ [x].
Proof.
  intros [a ov l] x v' H.
  unfold code_ValsStack_push in H.
  unfold code_vals_inline_capacity in H.
  cbn [code_ValsStack_inline_len code_ValsStack_inline
       code_ValsStack_overflow] in H.
  destruct (l s>= 32%usize) eqn:Hge.
  - destruct (alloc_vec_Vec_push ov x) as [ov'|e] eqn:Hpush;
      cbn [bind] in H.
    2: inversion H.
    inversion H; subst; clear H. apply vec_push_spec in Hpush.
    unfold vals_list. cbn [code_ValsStack_inline_len code_ValsStack_inline
      code_ValsStack_overflow]. rewrite Hge, Hpush, List.app_assoc.
    reflexivity.
  - pose proof (scalar_geb_false_lt _ _ Hge) as Hlt.
    unfold array_index_mut_usize in H.
    destruct (vals_inline_get_total a l ltac:(pose proof (usize_nonneg l);
      assert (to_Z 32%usize = 32) by reflexivity; lia)) as [old Hget].
    rewrite Hget in H. cbn [bind] in H.
    change (usize_sub 32%usize 1%usize) with (Ok 31%usize) in H.
    cbn [bind] in H.
    destruct (l s= 31%usize) eqn:Hlast.
    + apply scalar_eqb_true in Hlast.
      assert (l = 31%usize) by
        (apply scalar_to_Z_inj; cbn [to_Z] in *; lia).
      subst l. cbn [bind] in H. injection H as <-.
      unfold vals_list. cbn [code_ValsStack_inline_len
        code_ValsStack_inline code_ValsStack_overflow].
      rewrite vals_inline_set_spec, vec_new_list, List.app_nil_r.
      apply list_update_last_snoc. apply vals_inline_list_length.
    + apply scalar_eqb_false in Hlast.
      cbn [to_Z] in Hlt, Hlast.
      destruct (usize_add_ok l 1%usize ltac:(
        pose proof (usize_le_max l);
        assert (to_Z 1%usize = 1) by reflexivity;
        assert (to_Z 31%usize = 31) by reflexivity;
        assert (to_Z 32%usize = 32) by reflexivity;
        pose proof usize_max_bound; rewrite u32_max_val in *; lia))
        as [l' [Hadd Hl']].
      rewrite Hadd in H. cbn [bind] in H. injection H as <-.
      unfold vals_list. cbn [code_ValsStack_inline_len
        code_ValsStack_inline code_ValsStack_overflow].
      rewrite Hge.
      rewrite (scalar_geb_of_lt l' 32%usize) by
        (assert (to_Z 1%usize = 1) by reflexivity;
         assert (to_Z 31%usize = 31) by reflexivity;
         assert (to_Z 32%usize = 32) by reflexivity; lia).
      rewrite vals_inline_set_spec.
      assert (Hnat : Z.to_nat (to_Z l') = S (Z.to_nat (to_Z l))).
      { rewrite Hl'. change (Z.to_nat (to_Z l + 1) = S (Z.to_nat (to_Z l))).
        rewrite Z2Nat.inj_add by (pose proof (usize_nonneg l); lia).
        cbn. lia. }
      rewrite Hnat.
      rewrite firstn_list_update_snoc by
        (rewrite vals_inline_list_length;
         change (Z.to_nat (to_Z l) < Z.to_nat 32)%nat;
         exact ((proj1 (Z2Nat.inj_lt (to_Z l) 32
           (usize_nonneg l) ltac:(lia))) Hlt)).
      reflexivity.
Qed.

Lemma ctrls_stack_push_spec : forall v x v',
  code_CtrlsStack_push v x = Ok v' ->
  ctrls_list v' = ctrls_list v ++ [x].
Proof.
  intros [a ov l] x v' H.
  unfold code_CtrlsStack_push in H.
  unfold code_ctrls_inline_capacity in H.
  cbn [code_CtrlsStack_inline_len code_CtrlsStack_inline
       code_CtrlsStack_overflow] in H.
  destruct (l s>= 16%usize) eqn:Hge.
  - destruct (alloc_vec_Vec_push ov x) as [ov'|e] eqn:Hpush;
      cbn [bind] in H.
    2: inversion H.
    inversion H; subst; clear H. apply vec_push_spec in Hpush.
    unfold ctrls_list. cbn [code_CtrlsStack_inline_len code_CtrlsStack_inline
      code_CtrlsStack_overflow]. rewrite Hge, Hpush, List.app_assoc.
    reflexivity.
  - pose proof (scalar_geb_false_lt _ _ Hge) as Hlt.
    unfold array_index_mut_usize in H.
    destruct (ctrls_inline_get_total a l ltac:(pose proof (usize_nonneg l);
      assert (to_Z 16%usize = 16) by reflexivity; lia)) as [old Hget].
    rewrite Hget in H. cbn [bind] in H.
    change (usize_sub 16%usize 1%usize) with (Ok 15%usize) in H.
    cbn [bind] in H.
    destruct (l s= 15%usize) eqn:Hlast.
    + apply scalar_eqb_true in Hlast.
      assert (l = 15%usize) by
        (apply scalar_to_Z_inj; cbn [to_Z] in *; lia).
      subst l. cbn [bind] in H. injection H as <-.
      unfold ctrls_list. cbn [code_CtrlsStack_inline_len
        code_CtrlsStack_inline code_CtrlsStack_overflow].
      rewrite ctrls_inline_set_spec, vec_new_list, List.app_nil_r.
      apply list_update_last_snoc. apply ctrls_inline_list_length.
    + apply scalar_eqb_false in Hlast.
      cbn [to_Z] in Hlt, Hlast.
      destruct (usize_add_ok l 1%usize ltac:(
        pose proof (usize_le_max l);
        assert (to_Z 1%usize = 1) by reflexivity;
        assert (to_Z 15%usize = 15) by reflexivity;
        assert (to_Z 16%usize = 16) by reflexivity;
        pose proof usize_max_bound; rewrite u32_max_val in *; lia))
        as [l' [Hadd Hl']].
      rewrite Hadd in H. cbn [bind] in H. injection H as <-.
      unfold ctrls_list. cbn [code_CtrlsStack_inline_len
        code_CtrlsStack_inline code_CtrlsStack_overflow].
      rewrite Hge.
      rewrite (scalar_geb_of_lt l' 16%usize) by
        (assert (to_Z 1%usize = 1) by reflexivity;
         assert (to_Z 15%usize = 15) by reflexivity;
         assert (to_Z 16%usize = 16) by reflexivity; lia).
      rewrite ctrls_inline_set_spec.
      assert (Hnat : Z.to_nat (to_Z l') = S (Z.to_nat (to_Z l))).
      { rewrite Hl'. change (Z.to_nat (to_Z l + 1) = S (Z.to_nat (to_Z l))).
        rewrite Z2Nat.inj_add by (pose proof (usize_nonneg l); lia).
        cbn. lia. }
      rewrite Hnat.
      rewrite firstn_list_update_snoc by
        (rewrite ctrls_inline_list_length;
         change (Z.to_nat (to_Z l) < Z.to_nat 16)%nat;
         exact ((proj1 (Z2Nat.inj_lt (to_Z l) 16
           (usize_nonneg l) ltac:(lia))) Hlt)).
      reflexivity.
Qed.

Lemma locals_stack_push_spec : forall v x v',
  code_LocalsStack_push v x = Ok v' ->
  locals_list v' = locals_list v ++ [x].
Proof.
  intros [a ov l] x v' H.
  unfold code_LocalsStack_push in H.
  unfold code_locals_inline_capacity in H.
  cbn [code_LocalsStack_inline_len code_LocalsStack_inline
       code_LocalsStack_overflow] in H.
  destruct (l s>= 32%usize) eqn:Hge.
  - destruct (alloc_vec_Vec_push ov x) as [ov'|e] eqn:Hpush;
      cbn [bind] in H.
    2: inversion H.
    inversion H; subst; clear H. apply vec_push_spec in Hpush.
    unfold locals_list. cbn [code_LocalsStack_inline_len code_LocalsStack_inline
      code_LocalsStack_overflow]. rewrite Hge, Hpush, List.app_assoc.
    reflexivity.
  - pose proof (scalar_geb_false_lt _ _ Hge) as Hlt.
    unfold array_index_mut_usize in H.
    destruct (locals_inline_get_total a l ltac:(pose proof (usize_nonneg l);
      assert (to_Z 32%usize = 32) by reflexivity; lia)) as [old Hget].
    rewrite Hget in H. cbn [bind] in H.
    change (usize_sub 32%usize 1%usize) with (Ok 31%usize) in H.
    cbn [bind] in H.
    destruct (l s= 31%usize) eqn:Hlast.
    + apply scalar_eqb_true in Hlast.
      assert (l = 31%usize) by
        (apply scalar_to_Z_inj; cbn [to_Z] in *; lia).
      subst l. cbn [bind] in H. injection H as <-.
      unfold locals_list. cbn [code_LocalsStack_inline_len
        code_LocalsStack_inline code_LocalsStack_overflow].
      rewrite locals_inline_set_spec, vec_new_list, List.app_nil_r.
      apply list_update_last_snoc. apply locals_inline_list_length.
    + apply scalar_eqb_false in Hlast.
      cbn [to_Z] in Hlt, Hlast.
      destruct (usize_add_ok l 1%usize ltac:(
        pose proof (usize_le_max l);
        assert (to_Z 1%usize = 1) by reflexivity;
        assert (to_Z 31%usize = 31) by reflexivity;
        assert (to_Z 32%usize = 32) by reflexivity;
        pose proof usize_max_bound; rewrite u32_max_val in *; lia))
        as [l' [Hadd Hl']].
      rewrite Hadd in H. cbn [bind] in H. injection H as <-.
      unfold locals_list. cbn [code_LocalsStack_inline_len
        code_LocalsStack_inline code_LocalsStack_overflow].
      rewrite Hge.
      rewrite (scalar_geb_of_lt l' 32%usize) by
        (assert (to_Z 1%usize = 1) by reflexivity;
         assert (to_Z 31%usize = 31) by reflexivity;
         assert (to_Z 32%usize = 32) by reflexivity; lia).
      rewrite locals_inline_set_spec.
      assert (Hnat : Z.to_nat (to_Z l') = S (Z.to_nat (to_Z l))).
      { rewrite Hl'. change (Z.to_nat (to_Z l + 1) = S (Z.to_nat (to_Z l))).
        rewrite Z2Nat.inj_add by (pose proof (usize_nonneg l); lia).
        cbn. lia. }
      rewrite Hnat.
      rewrite firstn_list_update_snoc by
        (rewrite locals_inline_list_length;
         change (Z.to_nat (to_Z l) < Z.to_nat 32)%nat;
         exact ((proj1 (Z2Nat.inj_lt (to_Z l) 32
           (usize_nonneg l) ltac:(lia))) Hlt)).
      reflexivity.
Qed.

Lemma vals_stack_push_total : forall v x,
  Z.of_nat (List.length (vals_list v)) + 1 <= usize_max ->
  exists v', code_ValsStack_push v x = Ok v'.
Proof.
  intros [a ov l] x Hmax.
  unfold code_ValsStack_push, code_vals_inline_capacity.
  cbn [code_ValsStack_inline_len code_ValsStack_inline
       code_ValsStack_overflow].
  destruct (l s>= 32%usize) eqn:Hge.
  - unfold vals_list in Hmax.
    cbn [code_ValsStack_inline_len code_ValsStack_inline
      code_ValsStack_overflow] in Hmax.
    rewrite Hge, List.app_length, vals_inline_list_length in Hmax.
    destruct (vec_push_ok ov x ltac:(lia)) as [ov' Hpush].
    rewrite Hpush. cbn [bind]. eexists. reflexivity.
  - pose proof (scalar_geb_false_lt _ _ Hge) as Hlt.
    destruct (vals_inline_get_total a l ltac:(
      pose proof (usize_nonneg l);
      assert (to_Z 32%usize = 32) by reflexivity; lia)) as [old Hget].
    unfold array_index_mut_usize. rewrite Hget. cbn [bind].
    change (usize_sub 32%usize 1%usize) with (Ok 31%usize).
    cbn [bind]. destruct (l s= 31%usize) eqn:Hlast.
    + eexists. reflexivity.
    + apply scalar_eqb_false in Hlast. cbn [to_Z] in Hlt, Hlast.
      destruct (usize_add_ok l 1%usize ltac:(
        assert (to_Z 1%usize = 1) by reflexivity;
        assert (to_Z 31%usize = 31) by reflexivity;
        assert (to_Z 32%usize = 32) by reflexivity;
        pose proof usize_max_bound; rewrite u32_max_val in *; lia))
        as [l' [Hadd _]].
      rewrite Hadd. cbn [bind]. eexists. reflexivity.
Qed.

Lemma ctrls_stack_push_total : forall v x,
  Z.of_nat (List.length (ctrls_list v)) + 1 <= usize_max ->
  exists v', code_CtrlsStack_push v x = Ok v'.
Proof.
  intros [a ov l] x Hmax.
  unfold code_CtrlsStack_push, code_ctrls_inline_capacity.
  cbn [code_CtrlsStack_inline_len code_CtrlsStack_inline
       code_CtrlsStack_overflow].
  destruct (l s>= 16%usize) eqn:Hge.
  - unfold ctrls_list in Hmax.
    cbn [code_CtrlsStack_inline_len code_CtrlsStack_inline
      code_CtrlsStack_overflow] in Hmax.
    rewrite Hge, List.app_length, ctrls_inline_list_length in Hmax.
    destruct (vec_push_ok ov x ltac:(lia)) as [ov' Hpush].
    rewrite Hpush. cbn [bind]. eexists. reflexivity.
  - pose proof (scalar_geb_false_lt _ _ Hge) as Hlt.
    destruct (ctrls_inline_get_total a l ltac:(
      pose proof (usize_nonneg l);
      assert (to_Z 16%usize = 16) by reflexivity; lia)) as [old Hget].
    unfold array_index_mut_usize. rewrite Hget. cbn [bind].
    change (usize_sub 16%usize 1%usize) with (Ok 15%usize).
    cbn [bind]. destruct (l s= 15%usize) eqn:Hlast.
    + eexists. reflexivity.
    + apply scalar_eqb_false in Hlast. cbn [to_Z] in Hlt, Hlast.
      destruct (usize_add_ok l 1%usize ltac:(
        assert (to_Z 1%usize = 1) by reflexivity;
        assert (to_Z 15%usize = 15) by reflexivity;
        assert (to_Z 16%usize = 16) by reflexivity;
        pose proof usize_max_bound; rewrite u32_max_val in *; lia))
        as [l' [Hadd _]].
      rewrite Hadd. cbn [bind]. eexists. reflexivity.
Qed.

Lemma locals_stack_push_total : forall v x,
  Z.of_nat (List.length (locals_list v)) + 1 <= usize_max ->
  exists v', code_LocalsStack_push v x = Ok v'.
Proof.
  intros [a ov l] x Hmax.
  unfold code_LocalsStack_push, code_locals_inline_capacity.
  cbn [code_LocalsStack_inline_len code_LocalsStack_inline
       code_LocalsStack_overflow].
  destruct (l s>= 32%usize) eqn:Hge.
  - unfold locals_list in Hmax.
    cbn [code_LocalsStack_inline_len code_LocalsStack_inline
      code_LocalsStack_overflow] in Hmax.
    rewrite Hge, List.app_length, locals_inline_list_length in Hmax.
    destruct (vec_push_ok ov x ltac:(lia)) as [ov' Hpush].
    rewrite Hpush. cbn [bind]. eexists. reflexivity.
  - pose proof (scalar_geb_false_lt _ _ Hge) as Hlt.
    destruct (locals_inline_get_total a l ltac:(
      pose proof (usize_nonneg l);
      assert (to_Z 32%usize = 32) by reflexivity; lia)) as [old Hget].
    unfold array_index_mut_usize. rewrite Hget. cbn [bind].
    change (usize_sub 32%usize 1%usize) with (Ok 31%usize).
    cbn [bind]. destruct (l s= 31%usize) eqn:Hlast.
    + eexists. reflexivity.
    + apply scalar_eqb_false in Hlast. cbn [to_Z] in Hlt, Hlast.
      destruct (usize_add_ok l 1%usize ltac:(
        assert (to_Z 1%usize = 1) by reflexivity;
        assert (to_Z 31%usize = 31) by reflexivity;
        assert (to_Z 32%usize = 32) by reflexivity;
        pose proof usize_max_bound; rewrite u32_max_val in *; lia))
        as [l' [Hadd _]].
      rewrite Hadd. cbn [bind]. eexists. reflexivity.
Qed.

Lemma vals_stack_len_spec : forall v n,
  code_ValsStack_len v = Ok n ->
  to_Z n = Z.of_nat (List.length (vals_list v)).
Proof.
  intros [a ov l] n H.
  unfold code_ValsStack_len, code_vals_inline_capacity in H.
  cbn [code_ValsStack_inline_len code_ValsStack_inline
       code_ValsStack_overflow] in H.
  destruct (l s>= 32%usize) eqn:Hge.
  - pose proof (scalar_add_val 32%usize n (alloc_vec_Vec_len ov)
      (to_Z (alloc_vec_Vec_len ov)) H eq_refl) as Hn.
    unfold vals_list. cbn [code_ValsStack_inline_len
      code_ValsStack_inline code_ValsStack_overflow].
    rewrite Hge, List.app_length, vals_inline_list_length.
    rewrite vec_len_spec in Hn.
    assert (to_Z 32%usize = 32) by reflexivity. lia.
  - injection H as <-.
    pose proof Hge as Hlt. apply scalar_geb_false_lt in Hlt.
    cbn [to_Z] in Hlt.
    unfold vals_list. cbn [code_ValsStack_inline_len
      code_ValsStack_inline code_ValsStack_overflow].
    rewrite Hge, List.firstn_length, vals_inline_list_length.
    rewrite Nat.min_l.
    + rewrite Z2Nat.id by apply usize_nonneg. reflexivity.
    + apply Nat.lt_le_incl.
      change (Z.to_nat (to_Z l) < Z.to_nat 32)%nat.
      exact ((proj1 (Z2Nat.inj_lt (to_Z l) 32
        (usize_nonneg l) ltac:(lia))) Hlt).
Qed.

Lemma ctrls_stack_len_spec : forall v n,
  code_CtrlsStack_len v = Ok n ->
  to_Z n = Z.of_nat (List.length (ctrls_list v)).
Proof.
  intros [a ov l] n H.
  unfold code_CtrlsStack_len, code_ctrls_inline_capacity in H.
  cbn [code_CtrlsStack_inline_len code_CtrlsStack_inline
       code_CtrlsStack_overflow] in H.
  destruct (l s>= 16%usize) eqn:Hge.
  - pose proof (scalar_add_val 16%usize n (alloc_vec_Vec_len ov)
      (to_Z (alloc_vec_Vec_len ov)) H eq_refl) as Hn.
    unfold ctrls_list. cbn [code_CtrlsStack_inline_len
      code_CtrlsStack_inline code_CtrlsStack_overflow].
    rewrite Hge, List.app_length, ctrls_inline_list_length.
    rewrite vec_len_spec in Hn.
    assert (to_Z 16%usize = 16) by reflexivity. lia.
  - injection H as <-.
    pose proof Hge as Hlt. apply scalar_geb_false_lt in Hlt.
    cbn [to_Z] in Hlt.
    unfold ctrls_list. cbn [code_CtrlsStack_inline_len
      code_CtrlsStack_inline code_CtrlsStack_overflow].
    rewrite Hge, List.firstn_length, ctrls_inline_list_length.
    rewrite Nat.min_l.
    + rewrite Z2Nat.id by apply usize_nonneg. reflexivity.
    + apply Nat.lt_le_incl.
      change (Z.to_nat (to_Z l) < Z.to_nat 16)%nat.
      exact ((proj1 (Z2Nat.inj_lt (to_Z l) 16
        (usize_nonneg l) ltac:(lia))) Hlt).
Qed.

Lemma locals_stack_len_spec : forall v n,
  code_LocalsStack_len v = Ok n ->
  to_Z n = Z.of_nat (List.length (locals_list v)).
Proof.
  intros [a ov l] n H.
  unfold code_LocalsStack_len, code_locals_inline_capacity in H.
  cbn [code_LocalsStack_inline_len code_LocalsStack_inline
       code_LocalsStack_overflow] in H.
  destruct (l s>= 32%usize) eqn:Hge.
  - pose proof (scalar_add_val 32%usize n (alloc_vec_Vec_len ov)
      (to_Z (alloc_vec_Vec_len ov)) H eq_refl) as Hn.
    unfold locals_list. cbn [code_LocalsStack_inline_len
      code_LocalsStack_inline code_LocalsStack_overflow].
    rewrite Hge, List.app_length, locals_inline_list_length.
    rewrite vec_len_spec in Hn.
    assert (to_Z 32%usize = 32) by reflexivity. lia.
  - injection H as <-.
    pose proof Hge as Hlt. apply scalar_geb_false_lt in Hlt.
    cbn [to_Z] in Hlt.
    unfold locals_list. cbn [code_LocalsStack_inline_len
      code_LocalsStack_inline code_LocalsStack_overflow].
    rewrite Hge, List.firstn_length, locals_inline_list_length.
    rewrite Nat.min_l.
    + rewrite Z2Nat.id by apply usize_nonneg. reflexivity.
    + apply Nat.lt_le_incl.
      change (Z.to_nat (to_Z l) < Z.to_nat 32)%nat.
      exact ((proj1 (Z2Nat.inj_lt (to_Z l) 32
        (usize_nonneg l) ltac:(lia))) Hlt).
Qed.

Lemma vals_stack_len_total : forall v,
  Z.of_nat (List.length (vals_list v)) <= usize_max ->
  exists n, code_ValsStack_len v = Ok n.
Proof.
  intros [a ov l] Hmax.
  unfold code_ValsStack_len, code_vals_inline_capacity.
  cbn [code_ValsStack_inline_len code_ValsStack_inline
       code_ValsStack_overflow].
  destruct (l s>= 32%usize) eqn:Hge.
  - unfold vals_list in Hmax.
    cbn [code_ValsStack_inline_len code_ValsStack_inline
      code_ValsStack_overflow] in Hmax.
    rewrite Hge, List.app_length, vals_inline_list_length in Hmax.
    destruct (usize_add_ok 32%usize (alloc_vec_Vec_len ov)) as [n [Hadd _]].
    { rewrite vec_len_spec. assert (to_Z 32%usize = 32) by reflexivity.
      lia. }
    rewrite Hadd. eauto.
  - eauto.
Qed.

Lemma ctrls_stack_len_total : forall v,
  Z.of_nat (List.length (ctrls_list v)) <= usize_max ->
  exists n, code_CtrlsStack_len v = Ok n.
Proof.
  intros [a ov l] Hmax.
  unfold code_CtrlsStack_len, code_ctrls_inline_capacity.
  cbn [code_CtrlsStack_inline_len code_CtrlsStack_inline
       code_CtrlsStack_overflow].
  destruct (l s>= 16%usize) eqn:Hge.
  - unfold ctrls_list in Hmax.
    cbn [code_CtrlsStack_inline_len code_CtrlsStack_inline
      code_CtrlsStack_overflow] in Hmax.
    rewrite Hge, List.app_length, ctrls_inline_list_length in Hmax.
    destruct (usize_add_ok 16%usize (alloc_vec_Vec_len ov)) as [n [Hadd _]].
    { rewrite vec_len_spec. assert (to_Z 16%usize = 16) by reflexivity.
      lia. }
    rewrite Hadd. eauto.
  - eauto.
Qed.

Lemma locals_stack_len_total : forall v,
  Z.of_nat (List.length (locals_list v)) <= usize_max ->
  exists n, code_LocalsStack_len v = Ok n.
Proof.
  intros [a ov l] Hmax.
  unfold code_LocalsStack_len, code_locals_inline_capacity.
  cbn [code_LocalsStack_inline_len code_LocalsStack_inline
       code_LocalsStack_overflow].
  destruct (l s>= 32%usize) eqn:Hge.
  - unfold locals_list in Hmax.
    cbn [code_LocalsStack_inline_len code_LocalsStack_inline
      code_LocalsStack_overflow] in Hmax.
    rewrite Hge, List.app_length, locals_inline_list_length in Hmax.
    destruct (usize_add_ok 32%usize (alloc_vec_Vec_len ov)) as [n [Hadd _]].
    { rewrite vec_len_spec. assert (to_Z 32%usize = 32) by reflexivity.
      lia. }
    rewrite Hadd. eauto.
  - eauto.
Qed.

Lemma vals_stack_pop_spec : forall v o v',
  code_ValsStack_pop v = Ok (o, v') ->
  match List.rev (vals_list v) with
  | [] => o = None /\ vals_list v' = []
  | x :: rest => o = Some x /\ vals_list v' = List.rev rest
  end.
Proof.
  intros [a ov l] o v' H.
  unfold code_ValsStack_pop, code_vals_inline_capacity in H.
  cbn [code_ValsStack_inline_len code_ValsStack_inline
       code_ValsStack_overflow] in H.
  destruct (l s>= 32%usize) eqn:Hge.
  - destruct (alloc_vec_Vec_len ov s<> 0%usize) eqn:Hne.
    + destruct (alloc_vec_Vec_pop alloc_alloc_Global ov)
        as [[o0 ov']|e] eqn:Hpop; cbn [bind] in H.
      2: inversion H.
      injection H as <- <-.
      pose proof (vec_pop_last _ ov o0 ov' Hpop) as Hp.
      apply scalar_neqb_true in Hne. rewrite vec_len_spec in Hne.
      assert (H0 : to_Z 0%usize = 0) by reflexivity. rewrite H0 in Hne.
      destruct (List.rev (vec_list ov)) as [|x rest] eqn:Hrev.
      * exfalso. apply (f_equal (@List.length code_StackType_t)) in Hrev.
        rewrite List.rev_length in Hrev. cbn in Hrev. lia.
      * destruct Hp as [Ho Hov]. rewrite Ho. unfold vals_list.
        cbn [code_ValsStack_inline_len code_ValsStack_inline
          code_ValsStack_overflow]. rewrite Hge.
        rewrite List.rev_app_distr, Hrev. cbn.
        rewrite List.rev_app_distr, Hov.
        split; [reflexivity|]. rewrite List.rev_involutive. reflexivity.
    + change (usize_sub 32%usize 1%usize) with (Ok 31%usize) in H.
      cbn [bind] in H.
      destruct (array_index_usize a 31%usize) as [x|e] eqn:Hget;
        cbn [bind] in H.
      2: inversion H.
      injection H as <- <-.
      apply scalar_neqb_false in Hne. rewrite vec_len_spec in Hne.
      assert (H0 : to_Z 0%usize = 0) by reflexivity. rewrite H0 in Hne.
      assert (Hov : vec_list ov = []).
      { destruct (vec_list ov); [reflexivity|]. cbn in Hne. lia. }
      pose proof (vals_inline_get_spec a 31%usize x
        ltac:(assert (to_Z 31%usize = 31) by reflexivity; lia) Hget) as Hnth.
      pose proof (firstn_nth_error_snoc 31 (vals_inline_list a) x Hnth)
        as Hsnoc.
      assert (Hfull : List.firstn 32 (vals_inline_list a) =
                      vals_inline_list a).
      { apply List.firstn_all2. rewrite vals_inline_list_length. lia. }
      assert (Hfull_snoc : vals_inline_list a =
        List.firstn 31 (vals_inline_list a) ++ [x]).
      { exact (eq_trans (eq_sym Hfull) Hsnoc). }
      unfold vals_list. cbn [code_ValsStack_inline_len
        code_ValsStack_inline code_ValsStack_overflow].
      rewrite Hge, Hov, List.app_nil_r.
      replace (List.rev (vals_inline_list a)) with
        (x :: List.rev (List.firstn 31 (vals_inline_list a))).
      2: { pose proof (f_equal (@List.rev _) Hfull_snoc) as Hr.
           rewrite List.rev_app_distr in Hr.
           cbn [List.rev List.app] in Hr. exact (eq_sym Hr). }
      cbn. split; [reflexivity|]. symmetry. apply List.rev_involutive.
  - destruct (l s= 0%usize) eqn:Hz.
    + injection H as <- <-. apply scalar_eqb_true in Hz.
      assert (l = 0%usize) by (apply scalar_to_Z_inj; exact Hz).
      subst l. unfold vals_list.
      cbn [code_ValsStack_inline_len code_ValsStack_inline
        code_ValsStack_overflow]. split; reflexivity.
    + apply scalar_eqb_false in Hz.
      destruct (usize_sub l 1%usize) as [l'|e] eqn:Hsub;
        cbn [bind] in H.
      2: inversion H.
      destruct (array_index_usize a l') as [x|e] eqn:Hget;
        cbn [bind] in H.
      2: inversion H.
      injection H as <- <-.
      unfold usize_sub, scalar_sub in Hsub. apply mk_scalar_ok_to_Z in Hsub.
      pose proof (scalar_geb_false_lt _ _ Hge) as Hlt.
      assert (Hrange : 0 <= to_Z l' < 32).
      { pose proof (usize_nonneg l). pose proof (usize_nonneg l').
        assert (to_Z 0%usize = 0) by reflexivity.
        assert (to_Z 1%usize = 1) by reflexivity.
        assert (to_Z 32%usize = 32) by reflexivity. lia. }
      pose proof (vals_inline_get_spec a l' x Hrange Hget) as Hnth.
      pose proof (firstn_nth_error_snoc
        (Z.to_nat (to_Z l')) (vals_inline_list a) x Hnth) as Hsnoc.
      assert (Hnat : Z.to_nat (to_Z l) = S (Z.to_nat (to_Z l'))).
      { assert (to_Z 1%usize = 1) by reflexivity.
        assert (Hsum : to_Z l = to_Z l' + 1) by lia. rewrite Hsum.
        rewrite Z2Nat.inj_add by
          (pose proof (usize_nonneg l'); lia). cbn. lia. }
      unfold vals_list. cbn [code_ValsStack_inline_len
        code_ValsStack_inline code_ValsStack_overflow].
      rewrite Hge.
      rewrite (scalar_geb_of_lt l' 32%usize) by
        (assert (to_Z 32%usize = 32) by reflexivity; lia).
      rewrite Hnat, Hsnoc, List.rev_app_distr. cbn.
      split; [reflexivity|]. symmetry. apply List.rev_involutive.
Qed.

Lemma ctrls_stack_pop_spec : forall v o v',
  code_CtrlsStack_pop v = Ok (o, v') ->
  match List.rev (ctrls_list v) with
  | [] => o = None /\ ctrls_list v' = []
  | x :: rest => o = Some x /\ ctrls_list v' = List.rev rest
  end.
Proof.
  intros [a ov l] o v' H.
  unfold code_CtrlsStack_pop, code_ctrls_inline_capacity in H.
  cbn [code_CtrlsStack_inline_len code_CtrlsStack_inline
       code_CtrlsStack_overflow] in H.
  destruct (l s>= 16%usize) eqn:Hge.
  - destruct (alloc_vec_Vec_len ov s<> 0%usize) eqn:Hne.
    + destruct (alloc_vec_Vec_pop alloc_alloc_Global ov)
        as [[o0 ov']|e] eqn:Hpop; cbn [bind] in H.
      2: inversion H.
      injection H as <- <-.
      pose proof (vec_pop_last _ ov o0 ov' Hpop) as Hp.
      apply scalar_neqb_true in Hne. rewrite vec_len_spec in Hne.
      assert (H0 : to_Z 0%usize = 0) by reflexivity. rewrite H0 in Hne.
      destruct (List.rev (vec_list ov)) as [|x rest] eqn:Hrev.
      * exfalso. apply (f_equal (@List.length code_Ctrl_t)) in Hrev.
        rewrite List.rev_length in Hrev. cbn in Hrev. lia.
      * destruct Hp as [Ho Hov]. rewrite Ho. unfold ctrls_list.
        cbn [code_CtrlsStack_inline_len code_CtrlsStack_inline
          code_CtrlsStack_overflow]. rewrite Hge.
        rewrite List.rev_app_distr, Hrev. cbn.
        rewrite List.rev_app_distr, Hov.
        split; [reflexivity|]. rewrite List.rev_involutive. reflexivity.
    + change (usize_sub 16%usize 1%usize) with (Ok 15%usize) in H.
      cbn [bind] in H.
      destruct (array_index_usize a 15%usize) as [x|e] eqn:Hget;
        cbn [bind] in H.
      2: inversion H.
      injection H as <- <-.
      apply scalar_neqb_false in Hne. rewrite vec_len_spec in Hne.
      assert (H0 : to_Z 0%usize = 0) by reflexivity. rewrite H0 in Hne.
      assert (Hov : vec_list ov = []).
      { destruct (vec_list ov); [reflexivity|]. cbn in Hne. lia. }
      pose proof (ctrls_inline_get_spec a 15%usize x
        ltac:(assert (to_Z 15%usize = 15) by reflexivity; lia) Hget) as Hnth.
      pose proof (firstn_nth_error_snoc 15 (ctrls_inline_list a) x Hnth)
        as Hsnoc.
      assert (Hfull : List.firstn 16 (ctrls_inline_list a) =
                      ctrls_inline_list a).
      { apply List.firstn_all2. rewrite ctrls_inline_list_length. lia. }
      assert (Hfull_snoc : ctrls_inline_list a =
        List.firstn 15 (ctrls_inline_list a) ++ [x]).
      { exact (eq_trans (eq_sym Hfull) Hsnoc). }
      unfold ctrls_list. cbn [code_CtrlsStack_inline_len
        code_CtrlsStack_inline code_CtrlsStack_overflow].
      rewrite Hge, Hov, List.app_nil_r.
      replace (List.rev (ctrls_inline_list a)) with
        (x :: List.rev (List.firstn 15 (ctrls_inline_list a))).
      2: { pose proof (f_equal (@List.rev _) Hfull_snoc) as Hr.
           rewrite List.rev_app_distr in Hr.
           cbn [List.rev List.app] in Hr. exact (eq_sym Hr). }
      cbn. split; [reflexivity|]. symmetry. apply List.rev_involutive.
  - destruct (l s= 0%usize) eqn:Hz.
    + injection H as <- <-. apply scalar_eqb_true in Hz.
      assert (l = 0%usize) by (apply scalar_to_Z_inj; exact Hz).
      subst l. unfold ctrls_list.
      cbn [code_CtrlsStack_inline_len code_CtrlsStack_inline
        code_CtrlsStack_overflow]. split; reflexivity.
    + apply scalar_eqb_false in Hz.
      destruct (usize_sub l 1%usize) as [l'|e] eqn:Hsub;
        cbn [bind] in H.
      2: inversion H.
      destruct (array_index_usize a l') as [x|e] eqn:Hget;
        cbn [bind] in H.
      2: inversion H.
      injection H as <- <-.
      unfold usize_sub, scalar_sub in Hsub. apply mk_scalar_ok_to_Z in Hsub.
      pose proof (scalar_geb_false_lt _ _ Hge) as Hlt.
      assert (Hrange : 0 <= to_Z l' < 16).
      { pose proof (usize_nonneg l). pose proof (usize_nonneg l').
        assert (to_Z 0%usize = 0) by reflexivity.
        assert (to_Z 1%usize = 1) by reflexivity.
        assert (to_Z 16%usize = 16) by reflexivity. lia. }
      pose proof (ctrls_inline_get_spec a l' x Hrange Hget) as Hnth.
      pose proof (firstn_nth_error_snoc
        (Z.to_nat (to_Z l')) (ctrls_inline_list a) x Hnth) as Hsnoc.
      assert (Hnat : Z.to_nat (to_Z l) = S (Z.to_nat (to_Z l'))).
      { assert (to_Z 1%usize = 1) by reflexivity.
        assert (Hsum : to_Z l = to_Z l' + 1) by lia. rewrite Hsum.
        rewrite Z2Nat.inj_add by
          (pose proof (usize_nonneg l'); lia). cbn. lia. }
      unfold ctrls_list. cbn [code_CtrlsStack_inline_len
        code_CtrlsStack_inline code_CtrlsStack_overflow].
      rewrite Hge.
      rewrite (scalar_geb_of_lt l' 16%usize) by
        (assert (to_Z 16%usize = 16) by reflexivity; lia).
      rewrite Hnat, Hsnoc, List.rev_app_distr. cbn.
      split; [reflexivity|]. symmetry. apply List.rev_involutive.
Qed.

Lemma ctrls_stack_pop_of_snoc : forall v pre c o v',
  ctrls_list v = pre ++ [c] ->
  code_CtrlsStack_pop v = Ok (o, v') ->
  o = Some c /\ ctrls_list v' = pre.
Proof.
  intros v pre c o v' Hsnoc Hpop.
  pose proof (ctrls_stack_pop_spec v o v' Hpop) as Hspec.
  rewrite Hsnoc, List.rev_app_distr in Hspec. cbn in Hspec.
  destruct Hspec as [Ho Hv]. split; [exact Ho|].
  rewrite Hv. apply List.rev_involutive.
Qed.

Lemma vals_stack_pop_len : forall v o v',
  code_ValsStack_pop v = Ok (o, v') ->
  vals_list v <> [] ->
  (List.length (vals_list v') < List.length (vals_list v))%nat.
Proof.
  intros v o v' Hpop Hne.
  pose proof (vals_stack_pop_spec v o v' Hpop) as Hspec.
  destruct (List.rev (vals_list v)) as [|x rest] eqn:Hrev.
  - exfalso. apply Hne. apply (f_equal (@List.rev code_StackType_t)) in Hrev.
    rewrite List.rev_involutive in Hrev. cbn in Hrev. exact Hrev.
  - destruct Hspec as [_ Hv']. rewrite Hv'. rewrite List.rev_length.
    apply (f_equal (@List.length code_StackType_t)) in Hrev.
    rewrite List.rev_length in Hrev. rewrite Hrev. cbn. lia.
Qed.

Lemma vals_stack_pop_size : forall v o v',
  code_ValsStack_pop v = Ok (o, v') ->
  (List.length (vals_list v') <= List.length (vals_list v))%nat.
Proof.
  intros v o v' Hpop. pose proof (vals_stack_pop_spec v o v' Hpop) as Hspec.
  destruct (List.rev (vals_list v)) as [|x rest] eqn:Hrev.
  - destruct Hspec as [_ Hv]. rewrite Hv. apply Nat.le_0_l.
  - destruct Hspec as [_ Hv]. rewrite Hv, List.rev_length.
    apply (f_equal (@List.length _)) in Hrev.
    rewrite List.rev_length in Hrev. rewrite Hrev. cbn. lia.
Qed.

Lemma vals_stack_pop_total : forall v,
  exists o v', code_ValsStack_pop v = Ok (o, v').
Proof.
  intros [a ov l].
  unfold code_ValsStack_pop, code_vals_inline_capacity.
  cbn [code_ValsStack_inline_len code_ValsStack_inline
       code_ValsStack_overflow].
  destruct (l s>= 32%usize) eqn:Hge.
  - destruct (alloc_vec_Vec_len ov s<> 0%usize).
    + destruct (vec_pop_ok alloc_alloc_Global ov) as [o [ov' Hpop]].
      rewrite Hpop. cbn [bind]. eexists; eexists; reflexivity.
    + change (usize_sub 32%usize 1%usize) with (Ok 31%usize).
      cbn [bind].
      destruct (vals_inline_get_total a 31%usize ltac:(
        assert (to_Z 31%usize = 31) by reflexivity; lia)) as [x Hget].
      rewrite Hget. cbn [bind]. eexists; eexists; reflexivity.
  - destruct (l s= 0%usize) eqn:Hz.
    + eexists; eexists; reflexivity.
    + apply scalar_eqb_false in Hz.
      pose proof (scalar_geb_false_lt _ _ Hge) as Hlt.
      destruct (usize_sub_ok l 1%usize ltac:(
        pose proof (usize_nonneg l);
        assert (to_Z 0%usize = 0) by reflexivity;
        assert (to_Z 1%usize = 1) by reflexivity; lia))
        as [l' [Hsub Hl']].
      rewrite Hsub. cbn [bind].
      destruct (vals_inline_get_total a l' ltac:(
        pose proof (usize_nonneg l');
        assert (to_Z 1%usize = 1) by reflexivity;
        assert (to_Z 32%usize = 32) by reflexivity; lia))
        as [x Hget].
      rewrite Hget. cbn [bind]. eexists; eexists; reflexivity.
Qed.

Lemma nth_error_firstn_lt : forall {T} (l : list T) n i,
  (i < n)%nat -> List.nth_error (List.firstn n l) i = List.nth_error l i.
Proof.
  intros T l n. revert l. induction n as [|n IH]; intros l i Hlt;
    [lia|]. destruct l as [|x xs]; destruct i; cbn; try reflexivity.
  apply IH. lia.
Qed.

Lemma locals_stack_get_spec : forall v i x,
  (Z.to_nat (to_Z i) < List.length (locals_list v))%nat ->
  code_LocalsStack_get v i = Ok x ->
  List.nth_error (locals_list v) (Z.to_nat (to_Z i)) = Some x.
Proof.
  intros [a ov l] i x Hbound Hget.
  unfold locals_list in Hbound.
  cbn [code_LocalsStack_inline_len code_LocalsStack_inline
       code_LocalsStack_overflow] in Hbound.
  destruct (l s>= 32%usize) eqn:Hge.
  - unfold code_LocalsStack_get, code_locals_inline_capacity in Hget.
    cbn [code_LocalsStack_inline code_LocalsStack_overflow] in Hget.
    destruct (i s< 32%usize) eqn:Hi.
    + apply scalar_ltb_true in Hi.
      pose proof (locals_inline_get_spec a i x ltac:(
        pose proof (usize_nonneg i);
        assert (to_Z 32%usize = 32) by reflexivity; lia) Hget) as Hin.
      unfold locals_list. cbn [code_LocalsStack_inline_len
        code_LocalsStack_inline code_LocalsStack_overflow].
      rewrite Hge, List.nth_error_app1; [exact Hin|].
      rewrite locals_inline_list_length.
      change (Z.to_nat (to_Z i) < Z.to_nat 32)%nat.
      exact ((proj1 (Z2Nat.inj_lt (to_Z i) 32
        (usize_nonneg i) ltac:(lia))) ltac:(
          assert (to_Z 32%usize = 32) by reflexivity; lia)).
    + apply scalar_ltb_false in Hi.
      destruct (usize_sub i 32%usize) as [j|e] eqn:Hsub;
        cbn [bind] in Hget.
      2: inversion Hget.
      unfold usize_sub, scalar_sub in Hsub. apply mk_scalar_ok_to_Z in Hsub.
      rewrite vec_index_spec in Hget.
      destruct (List.nth_error (vec_list ov) (Z.to_nat (to_Z j)))
        as [y|] eqn:Hnth; [injection Hget as <-|inversion Hget].
      unfold locals_list. cbn [code_LocalsStack_inline_len
        code_LocalsStack_inline code_LocalsStack_overflow].
      rewrite Hge, List.nth_error_app2.
      * rewrite locals_inline_list_length.
        rewrite Hsub in Hnth. rewrite Z2Nat.inj_sub in Hnth by
          (pose proof (usize_nonneg i);
           assert (to_Z 32%usize = 32) by reflexivity; lia).
        cbn in Hnth. exact Hnth.
      * rewrite locals_inline_list_length.
        change (Z.to_nat 32 <= Z.to_nat (to_Z i))%nat.
        apply (proj1 (Z2Nat.inj_le 32 (to_Z i) ltac:(lia)
          (usize_nonneg i))). assert (to_Z 32%usize = 32) by reflexivity.
        lia.
  - pose proof (scalar_geb_false_lt _ _ Hge) as Hl.
    unfold code_LocalsStack_get, code_locals_inline_capacity in Hget.
    cbn [code_LocalsStack_inline code_LocalsStack_overflow] in Hget.
    assert (Hrange : 0 <= to_Z i < 32).
    { pose proof (usize_nonneg i).
      rewrite List.firstn_length, locals_inline_list_length in Hbound.
      assert (Hnat : (Z.to_nat (to_Z i) < Z.to_nat (to_Z l))%nat) by lia.
      apply (proj2 (Z2Nat.inj_lt (to_Z i) (to_Z l)
        (usize_nonneg i) (usize_nonneg l))) in Hnat.
      assert (to_Z 32%usize = 32) by reflexivity. lia. }
    assert (Hi : (i s< 32%usize) = true).
    { unfold scalar_ltb. apply Z.ltb_lt.
      assert (to_Z 32%usize = 32) by reflexivity. lia. }
    rewrite Hi in Hget.
    pose proof (locals_inline_get_spec a i x Hrange Hget) as Hin.
    unfold locals_list. cbn [code_LocalsStack_inline_len
      code_LocalsStack_inline code_LocalsStack_overflow].
    rewrite Hge, nth_error_firstn_lt; [exact Hin|].
    rewrite List.firstn_length, locals_inline_list_length in Hbound.
    lia.
Qed.

Lemma locals_stack_get_total : forall v i,
  (Z.to_nat (to_Z i) < List.length (locals_list v))%nat ->
  exists x, code_LocalsStack_get v i = Ok x.
Proof.
  intros [a ov l] i Hbound.
  unfold locals_list in Hbound.
  cbn [code_LocalsStack_inline_len code_LocalsStack_inline
       code_LocalsStack_overflow] in Hbound.
  destruct (l s>= 32%usize) eqn:Hge.
  - unfold code_LocalsStack_get, code_locals_inline_capacity.
    cbn [code_LocalsStack_inline code_LocalsStack_overflow].
    destruct (i s< 32%usize) eqn:Hi.
    + apply scalar_ltb_true in Hi.
      apply locals_inline_get_total.
      pose proof (usize_nonneg i).
      assert (to_Z 32%usize = 32) by reflexivity. lia.
    + apply scalar_ltb_false in Hi.
      destruct (usize_sub_ok i 32%usize ltac:(lia)) as [j [Hsub Hj]].
      rewrite Hsub. cbn [bind]. rewrite vec_index_spec.
      assert (Hjbound :
        (Z.to_nat (to_Z j) < List.length (vec_list ov))%nat).
      { rewrite List.app_length, locals_inline_list_length in Hbound.
        assert (H32 : to_Z 32%usize = 32) by reflexivity.
        rewrite Hj, H32, Z2Nat.inj_sub by
          (pose proof (usize_nonneg i); lia). lia. }
      destruct (List.nth_error (vec_list ov) (Z.to_nat (to_Z j)))
        as [x|] eqn:Hnth; [exists x; reflexivity|].
      apply List.nth_error_None in Hnth. lia.
  - pose proof (scalar_geb_false_lt _ _ Hge) as Hl.
    assert (Hrange : 0 <= to_Z i < 32).
    { pose proof (usize_nonneg i).
      rewrite List.firstn_length, locals_inline_list_length in Hbound.
      assert (Hnat : (Z.to_nat (to_Z i) < Z.to_nat (to_Z l))%nat) by lia.
      apply (proj2 (Z2Nat.inj_lt (to_Z i) (to_Z l)
        (usize_nonneg i) (usize_nonneg l))) in Hnat.
      assert (to_Z 32%usize = 32) by reflexivity. lia. }
    unfold code_LocalsStack_get, code_locals_inline_capacity.
    cbn [code_LocalsStack_inline code_LocalsStack_overflow].
    assert (Hi : (i s< 32%usize) = true).
    { unfold scalar_ltb. apply Z.ltb_lt.
      assert (to_Z 32%usize = 32) by reflexivity. lia. }
    rewrite Hi. apply locals_inline_get_total. exact Hrange.
Qed.

Lemma locals_stack_get_checked_total : forall v i,
  exists o, code_LocalsStack_get_checked v i = Ok o.
Proof.
  intros [a ov l] i.
  unfold code_LocalsStack_get_checked, code_locals_inline_capacity.
  cbn [code_LocalsStack_inline_len code_LocalsStack_inline
       code_LocalsStack_overflow].
  destruct (l s>= 32%usize) eqn:Hl.
  - destruct (i s< 32%usize) eqn:Hi.
    + apply scalar_ltb_true in Hi.
      destruct (locals_inline_get_total a i ltac:(
        pose proof (usize_nonneg i);
        assert (to_Z 32%usize = 32) by reflexivity; lia)) as [x Hget].
      rewrite Hget. cbn [bind]. eauto.
    + apply scalar_ltb_false in Hi.
      destruct (usize_sub_ok i 32%usize ltac:(lia)) as [j [Hsub Hj]].
      rewrite Hsub. cbn [bind].
      destruct (j s>= alloc_vec_Vec_len ov) eqn:Hge.
      * eauto.
      * apply scalar_geb_false_lt in Hge. rewrite vec_len_spec in Hge.
        rewrite vec_index_spec.
        destruct (List.nth_error (vec_list ov) (Z.to_nat (to_Z j)))
          as [x|] eqn:Hnth.
        -- eexists. reflexivity.
        -- apply List.nth_error_None in Hnth. apply Nat2Z.inj_le in Hnth.
           pose proof (usize_nonneg j). rewrite Z2Nat.id in Hnth by lia. lia.
  - pose proof (scalar_geb_false_lt _ _ Hl) as Hllen.
    destruct (i s>= l) eqn:Hge.
    + eauto.
    + apply scalar_geb_false_lt in Hge.
      destruct (locals_inline_get_total a i ltac:(
        pose proof (usize_nonneg i);
        assert (to_Z 32%usize = 32) by reflexivity; lia)) as [x Hget].
      rewrite Hget. cbn [bind]. eauto.
Qed.

Lemma locals_stack_get_checked_spec : forall v i o,
  code_LocalsStack_get_checked v i = Ok o ->
  o = List.nth_error (locals_list v) (Z.to_nat (to_Z i)).
Proof.
  intros [a ov l] i o H.
  unfold code_LocalsStack_get_checked, code_locals_inline_capacity in H.
  cbn [code_LocalsStack_inline_len code_LocalsStack_inline
       code_LocalsStack_overflow] in H.
  destruct (l s>= 32%usize) eqn:Hl.
  - destruct (i s< 32%usize) eqn:Hi.
    + apply scalar_ltb_true in Hi.
      destruct (array_index_usize a i) as [vt|e] eqn:Hget;
        cbn [bind] in H.
      2: inversion H.
      injection H as <-. unfold locals_list.
      cbn [code_LocalsStack_inline_len code_LocalsStack_inline
        code_LocalsStack_overflow]. rewrite Hl. symmetry.
      rewrite List.nth_error_app1.
      * apply locals_inline_get_spec; [|exact Hget].
        pose proof (usize_nonneg i).
        assert (to_Z 32%usize = 32) by reflexivity. lia.
      * rewrite locals_inline_list_length.
        change (Z.to_nat (to_Z i) < Z.to_nat 32)%nat.
        exact ((proj1 (Z2Nat.inj_lt (to_Z i) 32
          (usize_nonneg i) ltac:(lia))) ltac:(
            assert (to_Z 32%usize = 32) by reflexivity; lia)).
    + apply scalar_ltb_false in Hi.
      destruct (usize_sub i 32%usize) as [j|e] eqn:Hsub;
        cbn [bind] in H.
      2: inversion H.
      unfold usize_sub, scalar_sub in Hsub. apply mk_scalar_ok_to_Z in Hsub.
      assert (H32 : to_Z 32%usize = 32) by reflexivity.
      rewrite H32 in Hsub.
      destruct (j s>= alloc_vec_Vec_len ov) eqn:Hge.
      * injection H as <-. symmetry. unfold locals_list.
        cbn [code_LocalsStack_inline_len code_LocalsStack_inline
          code_LocalsStack_overflow]. rewrite Hl, List.nth_error_app2.
        -- rewrite locals_inline_list_length. cbn.
           change (List.nth_error (vec_list ov)
             (Z.to_nat (to_Z i) - Z.to_nat 32) = None).
           rewrite <- Z2Nat.inj_sub by
             (pose proof (usize_nonneg i);
              assert (to_Z 32%usize = 32) by reflexivity; lia).
           rewrite <- Hsub. apply List.nth_error_None.
           apply (proj2 (Nat2Z.inj_le _ _)).
           apply scalar_geb_true_ge in Hge. rewrite vec_len_spec in Hge.
           rewrite Z2Nat.id by apply usize_nonneg. lia.
        -- rewrite locals_inline_list_length.
           change (Z.to_nat 32 <= Z.to_nat (to_Z i))%nat.
           apply (proj1 (Z2Nat.inj_le 32 (to_Z i) ltac:(lia)
             (usize_nonneg i))). assert (to_Z 32%usize = 32) by reflexivity.
           lia.
      * apply scalar_geb_false_lt in Hge. rewrite vec_index_spec in H.
        destruct (List.nth_error (vec_list ov) (Z.to_nat (to_Z j)))
          as [vt|] eqn:Hnth; cbn [bind] in H.
        2: inversion H.
        injection H as <-. symmetry. unfold locals_list.
        cbn [code_LocalsStack_inline_len code_LocalsStack_inline
          code_LocalsStack_overflow]. rewrite Hl, List.nth_error_app2.
        -- rewrite locals_inline_list_length. cbn.
           change (List.nth_error (vec_list ov)
             (Z.to_nat (to_Z i) - Z.to_nat 32) = Some vt).
           rewrite <- Z2Nat.inj_sub by
             (pose proof (usize_nonneg i);
              assert (to_Z 32%usize = 32) by reflexivity; lia).
           rewrite <- Hsub. exact Hnth.
        -- rewrite locals_inline_list_length.
           change (Z.to_nat 32 <= Z.to_nat (to_Z i))%nat.
           apply (proj1 (Z2Nat.inj_le 32 (to_Z i) ltac:(lia)
             (usize_nonneg i))). assert (to_Z 32%usize = 32) by reflexivity.
           lia.
  - pose proof (scalar_geb_false_lt _ _ Hl) as Hllen.
    destruct (i s>= l) eqn:Hge.
    + injection H as <-. symmetry. apply List.nth_error_None.
      unfold locals_list. cbn [code_LocalsStack_inline_len
        code_LocalsStack_inline code_LocalsStack_overflow].
      rewrite Hl, List.firstn_length, locals_inline_list_length.
      apply scalar_geb_true_ge in Hge.
      assert (Hnat : (Z.to_nat (to_Z l) <= Z.to_nat (to_Z i))%nat).
      { apply (proj1 (Z2Nat.inj_le (to_Z l) (to_Z i)
          (usize_nonneg l) (usize_nonneg i))). lia. }
      lia.
    + apply scalar_geb_false_lt in Hge.
      destruct (array_index_usize a i) as [vt|e] eqn:Hget;
        cbn [bind] in H.
      2: inversion H.
      injection H as <-. symmetry. unfold locals_list.
      cbn [code_LocalsStack_inline_len code_LocalsStack_inline
        code_LocalsStack_overflow]. rewrite Hl, nth_error_firstn_lt.
      * apply locals_inline_get_spec; [|exact Hget].
        pose proof (usize_nonneg i).
        assert (to_Z 32%usize = 32) by reflexivity. lia.
      * apply (proj1 (Z2Nat.inj_lt (to_Z i) (to_Z l)
          (usize_nonneg i) (usize_nonneg l))). exact Hge.
Qed.

Lemma ctrls_stack_get_spec : forall v i x,
  (Z.to_nat (to_Z i) < List.length (ctrls_list v))%nat ->
  code_CtrlsStack_get v i = Ok x ->
  List.nth_error (ctrls_list v) (Z.to_nat (to_Z i)) = Some x.
Proof.
  intros [a ov l] i x Hbound Hget.
  unfold ctrls_list in Hbound.
  cbn [code_CtrlsStack_inline_len code_CtrlsStack_inline
       code_CtrlsStack_overflow] in Hbound.
  destruct (l s>= 16%usize) eqn:Hge.
  - unfold code_CtrlsStack_get, code_ctrls_inline_capacity in Hget.
    cbn [code_CtrlsStack_inline code_CtrlsStack_overflow] in Hget.
    destruct (i s< 16%usize) eqn:Hi.
    + apply scalar_ltb_true in Hi.
      pose proof (ctrls_inline_get_spec a i x ltac:(
        pose proof (usize_nonneg i);
        assert (to_Z 16%usize = 16) by reflexivity; lia) Hget) as Hin.
      unfold ctrls_list. cbn [code_CtrlsStack_inline_len
        code_CtrlsStack_inline code_CtrlsStack_overflow].
      rewrite Hge, List.nth_error_app1; [exact Hin|].
      rewrite ctrls_inline_list_length.
      change (Z.to_nat (to_Z i) < Z.to_nat 16)%nat.
      exact ((proj1 (Z2Nat.inj_lt (to_Z i) 16
        (usize_nonneg i) ltac:(lia))) ltac:(
          assert (to_Z 16%usize = 16) by reflexivity; lia)).
    + apply scalar_ltb_false in Hi.
      destruct (usize_sub i 16%usize) as [j|e] eqn:Hsub;
        cbn [bind] in Hget.
      2: inversion Hget.
      unfold usize_sub, scalar_sub in Hsub. apply mk_scalar_ok_to_Z in Hsub.
      rewrite vec_index_spec in Hget.
      destruct (List.nth_error (vec_list ov) (Z.to_nat (to_Z j)))
        as [y|] eqn:Hnth; [injection Hget as <-|inversion Hget].
      unfold ctrls_list. cbn [code_CtrlsStack_inline_len
        code_CtrlsStack_inline code_CtrlsStack_overflow].
      rewrite Hge, List.nth_error_app2.
      * rewrite ctrls_inline_list_length.
        rewrite Hsub in Hnth. rewrite Z2Nat.inj_sub in Hnth by
          (pose proof (usize_nonneg i);
           assert (to_Z 16%usize = 16) by reflexivity; lia).
        cbn in Hnth. exact Hnth.
      * rewrite ctrls_inline_list_length.
        change (Z.to_nat 16 <= Z.to_nat (to_Z i))%nat.
        apply (proj1 (Z2Nat.inj_le 16 (to_Z i) ltac:(lia)
          (usize_nonneg i))). assert (to_Z 16%usize = 16) by reflexivity.
        lia.
  - pose proof (scalar_geb_false_lt _ _ Hge) as Hl.
    unfold code_CtrlsStack_get, code_ctrls_inline_capacity in Hget.
    cbn [code_CtrlsStack_inline code_CtrlsStack_overflow] in Hget.
    assert (Hrange : 0 <= to_Z i < 16).
    { pose proof (usize_nonneg i).
      rewrite List.firstn_length, ctrls_inline_list_length in Hbound.
      assert (Hnat : (Z.to_nat (to_Z i) < Z.to_nat (to_Z l))%nat) by lia.
      apply (proj2 (Z2Nat.inj_lt (to_Z i) (to_Z l)
        (usize_nonneg i) (usize_nonneg l))) in Hnat.
      assert (to_Z 16%usize = 16) by reflexivity. lia. }
    assert (Hi : (i s< 16%usize) = true).
    { unfold scalar_ltb. apply Z.ltb_lt.
      assert (to_Z 16%usize = 16) by reflexivity. lia. }
    rewrite Hi in Hget.
    pose proof (ctrls_inline_get_spec a i x Hrange Hget) as Hin.
    unfold ctrls_list. cbn [code_CtrlsStack_inline_len
      code_CtrlsStack_inline code_CtrlsStack_overflow].
    rewrite Hge, nth_error_firstn_lt; [exact Hin|].
    rewrite List.firstn_length, ctrls_inline_list_length in Hbound.
    lia.
Qed.

Lemma ctrls_stack_get_total : forall v i,
  (Z.to_nat (to_Z i) < List.length (ctrls_list v))%nat ->
  exists x, code_CtrlsStack_get v i = Ok x.
Proof.
  intros [a ov l] i Hbound.
  unfold ctrls_list in Hbound.
  cbn [code_CtrlsStack_inline_len code_CtrlsStack_inline
       code_CtrlsStack_overflow] in Hbound.
  destruct (l s>= 16%usize) eqn:Hge.
  - unfold code_CtrlsStack_get, code_ctrls_inline_capacity.
    cbn [code_CtrlsStack_inline code_CtrlsStack_overflow].
    destruct (i s< 16%usize) eqn:Hi.
    + apply scalar_ltb_true in Hi.
      apply ctrls_inline_get_total.
      pose proof (usize_nonneg i).
      assert (to_Z 16%usize = 16) by reflexivity. lia.
    + apply scalar_ltb_false in Hi.
      destruct (usize_sub_ok i 16%usize ltac:(lia)) as [j [Hsub Hj]].
      rewrite Hsub. cbn [bind]. rewrite vec_index_spec.
      assert (Hjbound :
        (Z.to_nat (to_Z j) < List.length (vec_list ov))%nat).
      { rewrite List.app_length, ctrls_inline_list_length in Hbound.
        assert (H16 : to_Z 16%usize = 16) by reflexivity.
        rewrite Hj, H16, Z2Nat.inj_sub by
          (pose proof (usize_nonneg i); lia). lia. }
      destruct (List.nth_error (vec_list ov) (Z.to_nat (to_Z j)))
        as [x|] eqn:Hnth; [exists x; reflexivity|].
      apply List.nth_error_None in Hnth. lia.
  - pose proof (scalar_geb_false_lt _ _ Hge) as Hl.
    assert (Hrange : 0 <= to_Z i < 16).
    { pose proof (usize_nonneg i).
      rewrite List.firstn_length, ctrls_inline_list_length in Hbound.
      assert (Hnat : (Z.to_nat (to_Z i) < Z.to_nat (to_Z l))%nat) by lia.
      apply (proj2 (Z2Nat.inj_lt (to_Z i) (to_Z l)
        (usize_nonneg i) (usize_nonneg l))) in Hnat.
      assert (to_Z 16%usize = 16) by reflexivity. lia. }
    unfold code_CtrlsStack_get, code_ctrls_inline_capacity.
    cbn [code_CtrlsStack_inline code_CtrlsStack_overflow].
    assert (Hi : (i s< 16%usize) = true).
    { unfold scalar_ltb. apply Z.ltb_lt.
      assert (to_Z 16%usize = 16) by reflexivity. lia. }
    rewrite Hi. apply ctrls_inline_get_total. exact Hrange.
Qed.

Axiom vec_update_spec : forall {T} (v : alloc_vec_Vec T) (i : usize) (x : T),
  vec_list (alloc_vec_Vec_update v i x)
    = list_update (vec_list v) (Z.to_nat (to_Z i)) x.

Axiom vec_index_mut_spec : forall {T} (v : alloc_vec_Vec T) (i : usize),
  alloc_vec_Vec_index_mut (core_slice_index_SliceIndexUsizeSliceInst T) v i
    = match List.nth_error (vec_list v) (Z.to_nat (to_Z i)) with
      | Some x => Ok (x, alloc_vec_Vec_update v i)
      | None => Fail_ Failure
      end.

Lemma ctrls_stack_set_total : forall v i x,
  (Z.to_nat (to_Z i) < List.length (ctrls_list v))%nat ->
  exists v', code_CtrlsStack_set v i x = Ok v'.
Proof.
  intros [a ov l] i x Hbound.
  unfold ctrls_list in Hbound.
  cbn [code_CtrlsStack_inline_len code_CtrlsStack_inline
       code_CtrlsStack_overflow] in Hbound.
  destruct (l s>= 16%usize) eqn:Hl.
  - unfold code_CtrlsStack_set, code_ctrls_inline_capacity.
    cbn [code_CtrlsStack_inline code_CtrlsStack_overflow].
    destruct (i s< 16%usize) eqn:Hi.
    + apply scalar_ltb_true in Hi.
      destruct (ctrls_inline_set_total a i x ltac:(
        pose proof (usize_nonneg i);
        assert (to_Z 16%usize = 16) by reflexivity; lia)) as [a' Hset].
      rewrite Hset. cbn [bind]. eauto.
    + apply scalar_ltb_false in Hi.
      destruct (usize_sub_ok i 16%usize ltac:(lia)) as [j [Hsub Hj]].
      rewrite Hsub. cbn [bind]. rewrite vec_index_mut_spec.
      assert (Hjbound :
        (Z.to_nat (to_Z j) < List.length (vec_list ov))%nat).
      { rewrite List.app_length, ctrls_inline_list_length in Hbound.
        assert (H16 : to_Z 16%usize = 16) by reflexivity.
        rewrite Hj, H16, Z2Nat.inj_sub by
          (pose proof (usize_nonneg i); lia). lia. }
      destruct (List.nth_error (vec_list ov) (Z.to_nat (to_Z j)))
        as [old|] eqn:Hnth; [cbn [bind]; eauto|].
      apply List.nth_error_None in Hnth. lia.
  - pose proof (scalar_geb_false_lt _ _ Hl) as Hllen.
    assert (Hrange : 0 <= to_Z i < 16).
    { pose proof (usize_nonneg i).
      rewrite List.firstn_length, ctrls_inline_list_length in Hbound.
      assert (Hnat : (Z.to_nat (to_Z i) < Z.to_nat (to_Z l))%nat) by lia.
      apply (proj2 (Z2Nat.inj_lt (to_Z i) (to_Z l)
        (usize_nonneg i) (usize_nonneg l))) in Hnat.
      assert (to_Z 16%usize = 16) by reflexivity. lia. }
    unfold code_CtrlsStack_set, code_ctrls_inline_capacity.
    cbn [code_CtrlsStack_inline code_CtrlsStack_overflow].
    assert (Hi : (i s< 16%usize) = true).
    { unfold scalar_ltb. apply Z.ltb_lt.
      assert (to_Z 16%usize = 16) by reflexivity. lia. }
    rewrite Hi.
    destruct (ctrls_inline_set_total a i x Hrange) as [a' Hset].
    rewrite Hset. cbn [bind]. eauto.
Qed.

Lemma list_update_app_left : forall {T} (l r : list T) n x,
  (n < List.length l)%nat ->
  list_update (l ++ r) n x = list_update l n x ++ r.
Proof.
  intros T l. induction l as [|h l IH]; intros r n x Hlt; [cbn in Hlt; lia|].
  destruct n; [reflexivity|]. cbn [list_update List.app].
  f_equal. apply IH. apply (proj2 (Nat.succ_lt_mono _ _)). exact Hlt.
Qed.

Lemma list_update_app_right : forall {T} (l r : list T) n x,
  (List.length l <= n)%nat ->
  list_update (l ++ r) n x = l ++ list_update r (n - List.length l) x.
Proof.
  intros T l. induction l as [|h l IH]; intros r n x Hle.
  - cbn [list_update List.app List.length]. rewrite Nat.sub_0_r. reflexivity.
  - destruct n; [cbn in Hle; lia|].
    change (h :: list_update (l ++ r) n x =
      h :: (l ++ list_update r (n - List.length l) x)).
    f_equal. apply IH. apply (proj2 (Nat.succ_le_mono _ _)). exact Hle.
Qed.

Lemma firstn_list_update : forall {T} (l : list T) k n x,
  (n < k)%nat ->
  List.firstn k (list_update l n x) =
    list_update (List.firstn k l) n x.
Proof.
  intros T l. induction l as [|h l IH]; intros k n x Hlt.
  - destruct k, n; cbn [list_update]; reflexivity.
  - destruct k; [lia|]. destruct n; [reflexivity|].
    change (h :: List.firstn k (list_update l n x) =
      h :: list_update (List.firstn k l) n x).
    f_equal. apply IH. apply (proj2 (Nat.succ_lt_mono _ _)). exact Hlt.
Qed.

Lemma ctrls_stack_set_spec : forall v i x v',
  (Z.to_nat (to_Z i) < List.length (ctrls_list v))%nat ->
  code_CtrlsStack_set v i x = Ok v' ->
  ctrls_list v' = list_update (ctrls_list v) (Z.to_nat (to_Z i)) x.
Proof.
  intros [a ov l] i x v' Hbound Hset.
  unfold ctrls_list in Hbound.
  cbn [code_CtrlsStack_inline_len code_CtrlsStack_inline
       code_CtrlsStack_overflow] in Hbound.
  destruct (l s>= 16%usize) eqn:Hl.
  - unfold code_CtrlsStack_set, code_ctrls_inline_capacity in Hset.
    cbn [code_CtrlsStack_inline code_CtrlsStack_overflow] in Hset.
    destruct (i s< 16%usize) eqn:Hi.
    + apply scalar_ltb_true in Hi.
      destruct (array_update_usize a i x) as [a'|e]
        eqn:Hinline in Hset; cbn [bind] in Hset.
      2: inversion Hset.
      injection Hset as <-. unfold ctrls_list.
      cbn [code_CtrlsStack_inline_len code_CtrlsStack_inline
        code_CtrlsStack_overflow]. rewrite Hl.
      assert (Hrange : 0 <= to_Z i < 16).
      { pose proof (usize_nonneg i).
        assert (to_Z 16%usize = 16) by reflexivity. lia. }
      rewrite (ctrls_inline_update_spec _ _ _ _ Hrange Hinline).
      symmetry. apply list_update_app_left.
      rewrite ctrls_inline_list_length.
      change (Z.to_nat (to_Z i) < Z.to_nat 16)%nat.
      exact ((proj1 (Z2Nat.inj_lt (to_Z i) 16
        (proj1 Hrange) ltac:(lia))) (proj2 Hrange)).
    + apply scalar_ltb_false in Hi.
      destruct (usize_sub i 16%usize) as [j|e] eqn:Hsub;
        cbn [bind] in Hset.
      2: inversion Hset.
      rewrite vec_index_mut_spec in Hset.
      destruct (List.nth_error (vec_list ov) (Z.to_nat (to_Z j)))
        as [old|] eqn:Hnth in Hset.
      2: inversion Hset.
      cbn [bind] in Hset. injection Hset as <-.
      unfold ctrls_list. cbn [code_CtrlsStack_inline_len
        code_CtrlsStack_inline code_CtrlsStack_overflow]. rewrite Hl.
      rewrite vec_update_spec. symmetry. rewrite list_update_app_right.
      * f_equal. unfold usize_sub, scalar_sub in Hsub.
        apply mk_scalar_ok_to_Z in Hsub.
        assert (H16 : to_Z 16%usize = 16) by reflexivity. rewrite H16 in Hsub.
        rewrite Hsub, Z2Nat.inj_sub by
          (pose proof (usize_nonneg i); lia).
        rewrite ctrls_inline_list_length. reflexivity.
      * rewrite ctrls_inline_list_length.
        change (Z.to_nat 16 <= Z.to_nat (to_Z i))%nat.
        apply (proj1 (Z2Nat.inj_le 16 (to_Z i) ltac:(lia)
          (usize_nonneg i))). assert (to_Z 16%usize = 16) by reflexivity.
        lia.
  - pose proof (scalar_geb_false_lt _ _ Hl) as Hllen.
    assert (Hlt : (Z.to_nat (to_Z i) < Z.to_nat (to_Z l))%nat).
    { rewrite List.firstn_length, ctrls_inline_list_length in Hbound. lia. }
    assert (Hzlt : to_Z i < to_Z l).
    { apply (proj2 (Z2Nat.inj_lt (to_Z i) (to_Z l)
        (usize_nonneg i) (usize_nonneg l))). exact Hlt. }
    assert (Hrange : 0 <= to_Z i < 16).
    { pose proof (usize_nonneg i).
      assert (to_Z 16%usize = 16) by reflexivity. lia. }
    unfold code_CtrlsStack_set, code_ctrls_inline_capacity in Hset.
    cbn [code_CtrlsStack_inline code_CtrlsStack_overflow] in Hset.
    assert (Hi : (i s< 16%usize) = true).
    { unfold scalar_ltb. apply Z.ltb_lt.
      assert (to_Z 16%usize = 16) by reflexivity. lia. }
    rewrite Hi in Hset.
    destruct (array_update_usize a i x) as [a'|e]
      eqn:Hinline in Hset; cbn [bind] in Hset.
    2: inversion Hset.
    injection Hset as <-. unfold ctrls_list.
    cbn [code_CtrlsStack_inline_len code_CtrlsStack_inline
      code_CtrlsStack_overflow]. rewrite Hl.
    rewrite (ctrls_inline_update_spec _ _ _ _ Hrange Hinline).
    apply firstn_list_update. exact Hlt.
Qed.

Lemma list_update_length : forall {T} (l : list T) n x,
  List.length (list_update l n x) = List.length l.
Proof.
  intros T l. induction l as [|h l IH]; intros n x; [reflexivity|].
  destruct n as [|n]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma ctrls_stack_set_length : forall v i x v',
  code_CtrlsStack_set v i x = Ok v' ->
  List.length (ctrls_list v') = List.length (ctrls_list v).
Proof.
  intros [a ov l] i x v' Hset.
  unfold code_CtrlsStack_set, code_ctrls_inline_capacity in Hset.
  cbn [code_CtrlsStack_inline_len code_CtrlsStack_inline
       code_CtrlsStack_overflow] in Hset.
  destruct (i s< 16%usize) eqn:Hi.
  - destruct (array_update_usize a i x) as [a'|e]
      eqn:Hinline in Hset; cbn [bind] in Hset.
    2: inversion Hset.
    injection Hset as <-. unfold ctrls_list.
    cbn [code_CtrlsStack_inline_len code_CtrlsStack_inline
      code_CtrlsStack_overflow].
    destruct (l s>= 16%usize).
    + repeat rewrite List.app_length.
      repeat rewrite ctrls_inline_list_length. reflexivity.
    + repeat rewrite List.firstn_length.
      repeat rewrite ctrls_inline_list_length. reflexivity.
  - destruct (usize_sub i 16%usize) as [j|e] eqn:Hsub;
      cbn [bind] in Hset.
    2: inversion Hset.
    rewrite vec_index_mut_spec in Hset.
    destruct (List.nth_error (vec_list ov) (Z.to_nat (to_Z j)))
      as [old|] eqn:Hnth in Hset.
    2: inversion Hset.
    cbn [bind] in Hset. injection Hset as <-.
    unfold ctrls_list. cbn [code_CtrlsStack_inline_len
      code_CtrlsStack_inline code_CtrlsStack_overflow].
    destruct (l s>= 16%usize).
    + repeat rewrite List.app_length.
      rewrite vec_update_spec, list_update_length. reflexivity.
    + reflexivity.
Qed.

Lemma ctrls_stack_pop_size : forall v o v',
  code_CtrlsStack_pop v = Ok (o, v') ->
  (List.length (ctrls_list v') <= List.length (ctrls_list v))%nat.
Proof.
  intros v o v' Hpop.
  pose proof (ctrls_stack_pop_spec v o v' Hpop) as Hspec.
  destruct (List.rev (ctrls_list v)) as [|x rest] eqn:Hrev.
  - destruct Hspec as [_ Hv]. rewrite Hv. apply Nat.le_0_l.
  - destruct Hspec as [_ Hv]. rewrite Hv, List.rev_length.
    apply (f_equal (@List.length _)) in Hrev.
    rewrite List.rev_length in Hrev. rewrite Hrev. cbn. lia.
Qed.

Lemma ctrls_stack_pop_total : forall v,
  exists o v', code_CtrlsStack_pop v = Ok (o, v').
Proof.
  intros [a ov l].
  unfold code_CtrlsStack_pop, code_ctrls_inline_capacity.
  cbn [code_CtrlsStack_inline_len code_CtrlsStack_inline
       code_CtrlsStack_overflow].
  destruct (l s>= 16%usize) eqn:Hge.
  - destruct (alloc_vec_Vec_len ov s<> 0%usize).
    + destruct (vec_pop_ok alloc_alloc_Global ov) as [o [ov' Hpop]].
      rewrite Hpop. cbn [bind]. eexists; eexists; reflexivity.
    + change (usize_sub 16%usize 1%usize) with (Ok 15%usize).
      cbn [bind].
      destruct (ctrls_inline_get_total a 15%usize ltac:(
        assert (to_Z 15%usize = 15) by reflexivity; lia)) as [x Hget].
      rewrite Hget. cbn [bind]. eexists; eexists; reflexivity.
  - destruct (l s= 0%usize) eqn:Hz.
    + eexists; eexists; reflexivity.
    + apply scalar_eqb_false in Hz.
      pose proof (scalar_geb_false_lt _ _ Hge) as Hlt.
      destruct (usize_sub_ok l 1%usize ltac:(
        pose proof (usize_nonneg l);
        assert (to_Z 0%usize = 0) by reflexivity;
        assert (to_Z 1%usize = 1) by reflexivity; lia))
        as [l' [Hsub Hl']].
      rewrite Hsub. cbn [bind].
      destruct (ctrls_inline_get_total a l' ltac:(
        pose proof (usize_nonneg l');
        assert (to_Z 1%usize = 1) by reflexivity;
        assert (to_Z 16%usize = 16) by reflexivity; lia))
        as [x Hget].
      rewrite Hget. cbn [bind]. eexists; eexists; reflexivity.
Qed.

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
