(** * Bridges into mathcomp's boolean vocabulary

    WasmCert's checkers are booleans over mathcomp's [seq], and several of the
    facts below cannot be *stated* without its notations: membership in a [seq]
    over an [eqType], its [all], and decidable equality. Everything else in
    [Module_Typing.v] and [Module_Wasm10.v] is said in plain [List] terms, so
    this file is where the notations are imported and the statements live. Each
    is used by [rewrite] or [apply], which needs the term to match the one the
    checker produced, so stating them here rather than unfolding [in_mem] by
    hand is what makes them fire.

    The first group is what soundness needs, producing a boolean the checker
    will read; the second is what completeness needs, reading one it produced. *)

From mathcomp Require Import ssreflect ssrbool eqtype seq.
Require Import Coq.Lists.List.

Lemma mem_of_In : forall (T : eqType) (x : T) (l : list T),
  List.In x l -> (x \in l).
Proof.
  intros T x l. induction l as [|y l IH]; intros Hin; [destruct Hin|].
  rewrite seq.in_cons. destruct Hin as [Heq|Hin].
  - by rewrite Heq eqxx.
  - by rewrite (IH Hin) orbT.
Qed.

Lemma all_of_Forall : forall (T : Type) (p : T -> bool) (l : list T),
  List.Forall (fun x => p x = true) l -> all p l.
Proof.
  intros T p l. induction l as [|x l IH]; intros Hall; [reflexivity|].
  inversion Hall; subst. cbn [all].
  by rewrite (IH ltac:(assumption)) andbT.
Qed.

Lemma eqb_refl_true : forall (T : eqType) (x : T), (x == x) = true.
Proof. intros T x. by rewrite eqxx. Qed.

Lemma neq_true : forall (T : eqType) (x y : T), x <> y -> (x != y) = true.
Proof. intros T x y H. by apply /eqP. Qed.

(** Reading a boolean the checker produced. *)
Lemma eqb_eq : forall (T : eqType) (x y : T), (x == y) = true -> x = y.
Proof. intros T x y H. by apply /eqP. Qed.

Lemma Forall_of_all : forall (T : Type) (p : T -> bool) (l : list T),
  all p l = true -> List.Forall (fun x => p x = true) l.
Proof.
  intros T p l. induction l as [|x l IH]; intros Hall; [apply List.Forall_nil|].
  move: Hall => /andP [Hx Hl].
  apply List.Forall_cons; [exact Hx | exact (IH Hl)].
Qed.

(** [all2] pairs the two lists off one by one, so it can only hold of lists of
    the same length. That is what turns "the operand stack agrees with the
    result type" into a count. *)
(* [Coq.Lists.List] shadows mathcomp's [seq] with its own [seq : nat -> nat ->
   list nat], so the lists are spelt [list]. *)
Lemma all2_length : forall (T U : Type) (r : T -> U -> bool) (l1 : list T)
                           (l2 : list U),
  all2 r l1 l2 = true -> List.length l1 = List.length l2.
Proof.
  intros T U r l1. induction l1 as [|x l1 IH]; intros [|y l2] H;
    try discriminate; [reflexivity|].
  move: H => /andP [_ H]. cbn [List.length]. by rewrite (IH l2 H).
Qed.
