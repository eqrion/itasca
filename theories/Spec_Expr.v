(** * Structuring a flat operator stream into an instruction tree

    [Spec_Binary.v] decodes one operator at a time, because that is what a
    streaming validator can do: when [0x02] arrives its body is not yet known,
    so [FO_block] carries only the block type and [FO_end] is an operator in its
    own right. WasmCert's [basic_instruction], on the other hand, is a tree.

    This file supplies the missing half, in the direction that makes it a
    function: [flat_of] flattens a tree into the operator stream that encodes it,
    and [repr_expr] says a byte range encodes a given instruction sequence
    followed by the closing [end]. That mirrors spec 5.4.1

      blockinstr ::= 0x02 bt:blocktype (in:instr)* 0x0B
                   | 0x03 bt:blocktype (in:instr)* 0x0B

    and 5.4.9

      expr ::= (in:instr)* 0x0B

    read right to left. Flattening is injective, so the byte range determines the
    tree: [repr_expr_det] at the end of this file.

    THIS FILE IS A TRUST ITEM, for the same reason [Spec_Binary.v] is. Spec
    5.4.1 has two productions for [if] that decode to the identical WasmCert
    instruction, so the operator stream is not a function of the tree, and
    [else_sugar] is where that one ambiguity is written down. Putting it in
    [Spec_Binary.v] instead would have made the byte format itself ambiguous.

    It depends on nothing but [Spec_Binary.v] and WasmCert. Reading the flat
    operator stream *off a frame list*, which is what the simulation invariant
    needs, is [OpIter_Expr.v]; that half touches the extraction and this one
    deliberately does not. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
From Wasm Require Import datatypes numerics.
Require Import Veriwasm.Spec_Binary.

Open Scope Z_scope.

(* ================================================================== *)
(** ** Flattening an instruction tree                                  *)
(* ================================================================== *)

(** The operator stream that encodes an instruction, and a sequence of them.

    [flat_of] is [concat . map flat_of_one] rather than a fixpoint of its own so
    that both equations hold by conversion. A mutual pair does not work here:
    [basic_instruction] carries its body as a [list basic_instruction], and the
    two types are not in one mutual inductive block, so the guard checker will not
    accept a cross call. Recursing through [map] inside [flat_of_one] it does
    accept, which is the same shape WasmCert's [check_single] uses.

    Only [BI_block], [BI_loop] and [BI_if] have bodies in the covered subset, so
    everything else is one [FO_plain]. [BI_if] has two: the then-branch stops at
    [FO_else] rather than [FO_end], which is exactly the boundary [stops] and
    [frame_open] (an [Else] frame's opener) both know about. *)
Fixpoint flat_of_one (be : basic_instruction) : list flat_op :=
  match be with
  | BI_block bt inner =>
      FO_block bt :: List.concat (List.map flat_of_one inner) ++ [FO_end]
  | BI_loop bt inner =>
      FO_loop bt :: List.concat (List.map flat_of_one inner) ++ [FO_end]
  | BI_if bt es1 es2 =>
      FO_if bt :: List.concat (List.map flat_of_one es1)
                ++ FO_else :: List.concat (List.map flat_of_one es2) ++ [FO_end]
  | _ => [FO_plain be]
  end.

Definition flat_of (es : list basic_instruction) : list flat_op :=
  List.concat (List.map flat_of_one es).

Lemma flat_of_nil : flat_of [] = [].
Proof. reflexivity. Qed.

Lemma flat_of_cons : forall be es,
  flat_of (be :: es) = flat_of_one be ++ flat_of es.
Proof. intros be es. reflexivity. Qed.

Lemma flat_of_one_block : forall bt inner,
  flat_of_one (BI_block bt inner) = FO_block bt :: flat_of inner ++ [FO_end].
Proof. intros bt inner. reflexivity. Qed.

Lemma flat_of_one_loop : forall bt inner,
  flat_of_one (BI_loop bt inner) = FO_loop bt :: flat_of inner ++ [FO_end].
Proof. intros bt inner. reflexivity. Qed.

Lemma flat_of_one_if : forall bt es1 es2,
  flat_of_one (BI_if bt es1 es2)
    = FO_if bt :: flat_of es1 ++ FO_else :: flat_of es2 ++ [FO_end].
Proof. intros bt es1 es2. reflexivity. Qed.

(* ================================================================== *)
(** ** The [else] a bare [if] does not write                           *)
(* ================================================================== *)

(** Spec 5.4.1 gives [if] two productions:

      0x04 bt:blocktype (in:instr)*                0x0B => if bt in* else e end
      0x04 bt:blocktype (in1:instr)* 0x05 (in2:instr)* 0x0B => if bt in1* else in2* end

    The first is sugar for the second with an empty else-branch, and both yield
    the *same* abstract instruction: WasmCert's AST, like the specification's,
    has only [BI_if bt es1 es2], so [if bt in* end] and [if bt in* else end]
    decode to the identical [BI_if bt in* [::]].

    That is why [flat_of] alone cannot say which byte stream an instruction
    tree came from. [flat_of_one_if] always writes the [FO_else], because that
    is the boundary the then-branch stops at, so an [if] with an empty
    else-branch flattens to [... FO_else; FO_end], and the sugared form's bytes
    carry no [0x05] for that [FO_else] to represent.

    [else_sugar full lean] is the missing degree of freedom: [lean] is [full]
    with any number of empty else-branches written in the sugared form. It is a
    relation and not a function because the choice is the encoder's, and the
    bytes record it -- one [FO_else] elided is one [0x05] absent. *)
Inductive else_sugar : list flat_op -> list flat_op -> Prop :=
| else_sugar_nil : else_sugar [] []
| else_sugar_keep : forall op ops lean,
    else_sugar ops lean -> else_sugar (op :: ops) (op :: lean)
| else_sugar_drop : forall ops lean,
    else_sugar (FO_end :: ops) lean -> else_sugar (FO_else :: FO_end :: ops) lean.

(** Spec 5.4.9: [expr ::= (in:instr)* 0x0B]. A whole function body is
    [repr_expr bs es []], which is what [validate_body]'s "the cursor reached the
    end" check corresponds to.

    The operator stream the bytes encode is the instruction sequence's
    flattening up to that one freedom: [repr_expr_det] below is what says the
    freedom is visible in the bytes, so the tree is still determined. *)
Definition repr_expr (bs : list Z) (es : list basic_instruction)
                     (rest : list Z) : Prop :=
  exists ops,
    else_sugar (flat_of es ++ [FO_end]) ops /\ repr_ops bs ops rest.

(** Sugaring never empties a non-empty stream: the [FO_else] it may drop is
    always followed by the [FO_end] it kept. *)
Lemma else_sugar_nil_out : forall ops lean,
  else_sugar ops lean -> lean = [] -> ops = [].
Proof.
  intros ops lean H. induction H as [| op ops0 lean0 H IH | ops0 lean0 H IH];
    intros Hnil; [reflexivity | discriminate Hnil |].
  exfalso. pose proof (IH Hnil) as Hbad. discriminate Hbad.
Qed.

Lemma else_sugar_refl : forall ops, else_sugar ops ops.
Proof.
  induction ops as [|op ops IH]; [apply else_sugar_nil|].
  apply else_sugar_keep. exact IH.
Qed.

(** The validator grows its stream at the end, so both rules are needed in
    snoc form: one operator read is one operator appended, and the [end] that
    closes a bare [if] appends the elided [FO_else] along with it. *)
Lemma else_sugar_snoc : forall ops lean op,
  else_sugar ops lean -> else_sugar (ops ++ [op]) (lean ++ [op]).
Proof.
  intros ops lean op H. induction H as [| op0 ops0 lean0 H IH | ops0 lean0 H IH];
    cbn [app].
  - apply else_sugar_keep. apply else_sugar_nil.
  - apply else_sugar_keep. exact IH.
  - apply else_sugar_drop. cbn [app] in IH. exact IH.
Qed.

Lemma else_sugar_snoc_else_end : forall ops lean,
  else_sugar ops lean -> else_sugar (ops ++ [FO_else; FO_end]) (lean ++ [FO_end]).
Proof.
  intros ops lean H. induction H as [| op0 ops0 lean0 H IH | ops0 lean0 H IH];
    cbn [app].
  - apply else_sugar_drop. apply else_sugar_keep. apply else_sugar_nil.
  - apply else_sugar_keep. exact IH.
  - apply else_sugar_drop. cbn [app] in IH. exact IH.
Qed.

(* ================================================================== *)
(** ** The shape of one flattened instruction                           *)
(* ================================================================== *)

(** [flat_of_one] has a case per constructor and [basic_instruction] has forty.
    This is the one case analysis; every proof below goes through it rather than
    enumerating constructors again. *)
(** The same three, with every operator written as a one-element list. Both
    forms are the same term up to conversion; this one is what the list algebra
    of [OpIter_Complete.v]'s operator stream needs, since [rewrite] cannot
    reassociate an append past a [cons]. *)
Lemma flat_of_one_block_app : forall bt inner,
  flat_of_one (BI_block bt inner) = [FO_block bt] ++ flat_of inner ++ [FO_end].
Proof. intros bt inner. reflexivity. Qed.

Lemma flat_of_one_loop_app : forall bt inner,
  flat_of_one (BI_loop bt inner) = [FO_loop bt] ++ flat_of inner ++ [FO_end].
Proof. intros bt inner. reflexivity. Qed.

Lemma flat_of_one_if_app : forall bt es1 es2,
  flat_of_one (BI_if bt es1 es2)
    = [FO_if bt] ++ flat_of es1 ++ [FO_else] ++ flat_of es2 ++ [FO_end].
Proof. intros bt es1 es2. reflexivity. Qed.

Lemma flat_of_one_cases : forall be,
  (exists bt inner, be = BI_block bt inner
     /\ flat_of_one be = FO_block bt :: flat_of inner ++ [FO_end])
  \/ (exists bt inner, be = BI_loop bt inner
     /\ flat_of_one be = FO_loop bt :: flat_of inner ++ [FO_end])
  \/ (exists bt es1 es2, be = BI_if bt es1 es2
     /\ flat_of_one be
        = FO_if bt :: flat_of es1 ++ FO_else :: flat_of es2 ++ [FO_end])
  \/ flat_of_one be = [FO_plain be].
Proof.
  intros be. destruct be.
  all: try (right; right; right; reflexivity).
  all: try (left; eexists; eexists; split; reflexivity).
  all: try (right; left; eexists; eexists; split; reflexivity).
  all: try (right; right; left; eexists; eexists; eexists; split; reflexivity).
Qed.

Lemma flat_of_one_nonnil : forall be, flat_of_one be <> [].
Proof.
  intros be.
  destruct (flat_of_one_cases be) as [[bt [inner [_ Ho]]]
                                     |[[bt [inner [_ Ho]]]
                                     |[[bt [es1 [es2 [_ Ho]]]] | Ho]]];
    rewrite Ho; discriminate.
Qed.

Lemma flat_of_nil_inv : forall es, flat_of es = [] -> es = [].
Proof.
  intros es H. destruct es as [|be es']; [reflexivity|].
  exfalso. rewrite flat_of_cons in H. apply app_eq_nil in H as [H1 _].
  apply (flat_of_one_nonnil be). exact H1.
Qed.

(** Flattening is concatenative, which is what lets a step lemma reason about the
    single instruction it appends without unfolding the whole ghost list. *)
Lemma flat_of_app : forall es1 es2,
  flat_of (es1 ++ es2) = flat_of es1 ++ flat_of es2.
Proof.
  induction es1 as [|be es1 IH]; intros es2; [reflexivity|].
  cbn [app]. rewrite flat_of_cons. rewrite flat_of_cons. rewrite IH.
  rewrite app_assoc. reflexivity.
Qed.

Lemma flat_of_single : forall be, flat_of [be] = flat_of_one be.
Proof. intros be. rewrite flat_of_cons. rewrite flat_of_nil. apply app_nil_r. Qed.

(* ================================================================== *)
(** ** Flattening is injective                                         *)
(* ================================================================== *)

(** A remainder a flattened sequence may be followed by: the stream has run out,
    the next operator closes an enclosing block, or (a then-branch only) the
    next operator is that [if]'s [else]. Those are the only three places an
    instruction sequence can stop, which is what lets the statement below be
    applied to a nested body -- then-branch included -- as well as to a whole
    one. *)
Definition stops (ops : list flat_op) : Prop :=
  ops = [] \/ (exists rest, ops = FO_end :: rest)
  \/ (exists rest, ops = FO_else :: rest).

Lemma stops_nil : stops [].
Proof. left. reflexivity. Qed.

Lemma stops_end : forall rest, stops (FO_end :: rest).
Proof. intros rest. right. left. exists rest. reflexivity. Qed.

Lemma stops_else : forall rest, stops (FO_else :: rest).
Proof. intros rest. right. right. exists rest. reflexivity. Qed.

(** Nothing flattens to a stream that a stopped remainder could match: a
    flattened instruction starts with [FO_plain], [FO_block] or [FO_loop], never
    with [FO_end]. This is where the matching [end] of a block becomes
    unambiguous. *)
Lemma flat_of_inj_nil : forall es r1 r2,
  stops r1 -> r1 = flat_of es ++ r2 -> es = [] /\ r1 = r2.
Proof.
  intros es r1 r2 Hs1 Heq.
  destruct es as [|be es']; [split; [reflexivity | exact Heq]|].
  exfalso. rewrite flat_of_cons in Heq.
  destruct (flat_of_one_cases be) as [[bt [inner [_ Ho]]]
                                     |[[bt [inner [_ Ho]]]
                                     |[[bt [es1 [es2 [_ Ho]]]] | Ho]]];
    rewrite Ho in Heq; cbn [app] in Heq;
    destruct Hs1 as [-> | [[rest ->] | [rest ->]]]; discriminate Heq.
Qed.

(** Re-associating the operator that closes a body onto the remainder, which is
    the form the body's sub-derivation is applied at: an [if]'s then-branch
    stops at [FO_else] rather than at an [FO_end]. *)
Lemma app_mid_reassoc : forall (A : list flat_op) (x : flat_op) (B C : list flat_op),
  (A ++ x :: B) ++ C = A ++ x :: (B ++ C).
Proof. intros A x B C. rewrite <- app_assoc. reflexivity. Qed.

(** Taking an [else_sugar] derivation apart. Only an [FO_else] can be elided,
    so every other leading operator is passed through, and the sugared stream's
    head settles it. *)
Lemma else_sugar_nil_inv : forall lean, else_sugar [] lean -> lean = [].
Proof. intros lean H. inversion H. reflexivity. Qed.

(** The disequality comes *after* the derivation in both of these, so that
    [ltac:(discriminate)] can discharge it: the operator is an evar until the
    derivation is elaborated. *)
Lemma else_sugar_keep_inv : forall op ops lean,
  else_sugar (op :: ops) lean -> op <> FO_else ->
  exists lean', lean = op :: lean' /\ else_sugar ops lean'.
Proof.
  intros op ops lean H Hne. inversion H as [|op0 ops0 lean0 Hsub|ops0 lean0 Hsub];
    subst.
  - eexists. split; [reflexivity | exact Hsub].
  - exfalso. apply Hne. reflexivity.
Qed.

Lemma else_sugar_else_inv : forall ops lean,
  else_sugar (FO_else :: ops) lean ->
  (exists lean', lean = FO_else :: lean' /\ else_sugar ops lean')
  \/ (exists ops', ops = FO_end :: ops' /\ else_sugar ops lean).
Proof.
  intros ops lean H. inversion H as [|op0 ops0 lean0 Hsub|ops0 lean0 Hsub]; subst.
  - left. eexists. split; [reflexivity | exact Hsub].
  - right. eexists. split; [reflexivity | exact Hsub].
Qed.

(** A stopped stream stays stopped: whether or not its leading [FO_else] was
    elided, what is left starts with an [FO_else] or an [FO_end]. *)
Lemma else_sugar_stops : forall r lean, stops r -> else_sugar r lean -> stops lean.
Proof.
  intros r lean Hs H. destruct Hs as [-> | [[rest ->] | [rest ->]]].
  - rewrite (else_sugar_nil_inv lean H). apply stops_nil.
  - destruct (else_sugar_keep_inv _ _ _ H (ltac:(discriminate)))
      as [lean' [-> _]].
    apply stops_end.
  - destruct (else_sugar_else_inv _ _ H) as [[lean' [-> _]] | [ops' [-> Hd]]].
    + apply stops_else.
    + destruct (else_sugar_keep_inv _ _ _ Hd (ltac:(discriminate)))
        as [lean' [-> _]].
      apply stops_end.
Qed.

(** Two streams that sugar to the same thing lead with the same operator, as
    long as neither leading operator is the one that may go missing. *)
Lemma else_sugar_hd : forall op1 ops1 op2 ops2 lean,
  else_sugar (op1 :: ops1) lean -> else_sugar (op2 :: ops2) lean ->
  op1 <> FO_else -> op2 <> FO_else ->
  op1 = op2 /\ exists lean', else_sugar ops1 lean' /\ else_sugar ops2 lean'.
Proof.
  intros op1 ops1 op2 ops2 lean H1 H2 Hne1 Hne2.
  destruct (else_sugar_keep_inv _ _ _ H1 Hne1) as [l1 [Hl1 H1']].
  destruct (else_sugar_keep_inv _ _ _ H2 Hne2) as [l2 [Hl2 H2']].
  rewrite Hl1 in Hl2. injection Hl2 as Hop Hl.
  split; [exact Hop|]. exists l1. split; [exact H1'|].
  rewrite Hl. exact H2'.
Qed.

(** The leading operator of a flattened non-empty sequence, which is what makes
    [else_sugar_hd] applicable: it is never the elidable [FO_else], and never
    the [FO_end] a stopped remainder starts with. *)
Lemma flat_of_hd : forall be es r,
  exists op rest,
    flat_of (be :: es) ++ r = op :: rest /\ op <> FO_else /\ op <> FO_end.
Proof.
  intros be es r. rewrite flat_of_cons. rewrite <- app_assoc.
  destruct (flat_of_one_cases be) as [[bt [inner [_ Ho]]]
                                     |[[bt [inner [_ Ho]]]
                                     |[[bt [es1 [es2 [_ Ho]]]] | Ho]]];
    rewrite Ho; cbn [app]; eexists; eexists;
    repeat split; try reflexivity; discriminate.
Qed.

(** An empty sequence's sugaring cannot be a non-empty one's: the second leads
    with a real operator and the first with what stops it. *)
Lemma flat_sugar_nil : forall es r1 r2 lean,
  stops r1 -> else_sugar r1 lean -> else_sugar (flat_of es ++ r2) lean -> es = [].
Proof.
  intros es r1 r2 lean Hs1 H1 H2. destruct es as [|be es']; [reflexivity|].
  exfalso.
  destruct (flat_of_hd be es' r2) as [op [rest [Heq [Hne Hnd]]]].
  rewrite Heq in H2.
  destruct (else_sugar_keep_inv _ _ _ H2 Hne) as [lean' [Hlean _]].
  pose proof (else_sugar_stops r1 lean Hs1 H1) as Hst.
  rewrite Hlean in Hst.
  destruct Hst as [Hbad | [[rest' Hbad] | [rest' Hbad]]];
    [discriminate Hbad
    | injection Hbad as Hbad'; apply Hnd; exact Hbad'
    | injection Hbad as Hbad'; apply Hne; exact Hbad'].
Qed.

(** Induction is on the length of the flattened stream, not on the sequence: the
    block case recurses into the body, which [list basic_instruction]'s own
    induction principle does not reach.

    Stated over the *sugared* stream rather than over [flat_of] itself, since
    that is the one the bytes pin down. Where the two sides disagree about
    eliding an [else], the disagreement is visible: one sugaring leads with
    [FO_else] and the other with the [FO_end] it hid. *)
Lemma flat_sugar_inj_gen : forall n es1 r1 es2 r2 lean,
  (List.length (flat_of es1) <= n)%nat ->
  stops r1 -> stops r2 ->
  else_sugar (flat_of es1 ++ r1) lean ->
  else_sugar (flat_of es2 ++ r2) lean ->
  es1 = es2 /\ exists lean', else_sugar r1 lean' /\ else_sugar r2 lean'.
Proof.
  induction n as [|n IH]; intros es1 r1 es2 r2 lean Hn Hs1 Hs2 H1 H2.
  - (* an empty flattening forces an empty sequence *)
    assert (Hes1 : es1 = []).
    { apply flat_of_nil_inv. destruct (flat_of es1); [reflexivity|].
      cbn [List.length] in Hn. lia. }
    subst es1. rewrite flat_of_nil in H1. cbn [app] in H1.
    assert (Hes2 : es2 = []) by (apply (flat_sugar_nil es2 r1 r2 lean Hs1 H1 H2)).
    subst es2. rewrite flat_of_nil in H2. cbn [app] in H2.
    split; [reflexivity | exists lean; split; [exact H1 | exact H2]].
  - destruct es1 as [|be1 es1'].
    { rewrite flat_of_nil in H1. cbn [app] in H1.
      assert (Hes2 : es2 = []) by (apply (flat_sugar_nil es2 r1 r2 lean Hs1 H1 H2)).
      subst es2. rewrite flat_of_nil in H2. cbn [app] in H2.
      split; [reflexivity | exists lean; split; [exact H1 | exact H2]]. }
    destruct es2 as [|be2 es2'].
    { rewrite flat_of_nil in H2. cbn [app] in H2.
      assert (Hbad : be1 :: es1' = [])
        by (apply (flat_sugar_nil (be1 :: es1') r2 r1 lean Hs2 H2 H1)).
      discriminate Hbad. }
    (* peel one instruction off each side and let the leading operator decide *)
    rewrite flat_of_cons in H1. rewrite <- app_assoc in H1.
    rewrite flat_of_cons in H2. rewrite <- app_assoc in H2.
    rewrite flat_of_cons in Hn. rewrite app_length in Hn.
    destruct (flat_of_one_cases be1) as [[bt1 [in1 [Hb1 Ho1]]]
                                        |[[bt1 [in1 [Hb1 Ho1]]]
                                        |[[bt1 [es1a [es1b [Hb1 Ho1]]]] | Ho1]]];
    destruct (flat_of_one_cases be2) as [[bt2 [in2 [Hb2 Ho2]]]
                                        |[[bt2 [in2 [Hb2 Ho2]]]
                                        |[[bt2 [es2a [es2b [Hb2 Ho2]]]] | Ho2]]];
      rewrite Ho1 in H1; rewrite Ho2 in H2;
      cbn [app] in H1; cbn [app] in H2;
      repeat rewrite app_mid_reassoc in H1;
      repeat rewrite app_mid_reassoc in H2;
      cbn [app] in H1; cbn [app] in H2;
      rewrite Ho1 in Hn; cbn [List.length] in Hn;
      destruct (else_sugar_hd _ _ _ _ _ H1 H2
                  (ltac:(discriminate)) (ltac:(discriminate)))
        as [Hhd [lean1 [H1' H2']]];
      try discriminate Hhd.
    + (* block against block: the bodies match, then the tails *)
      rewrite app_length in Hn. cbn [List.length] in Hn.
      assert (Hin : (List.length (flat_of in1) <= n)%nat) by lia.
      destruct (IH in1 (FO_end :: (flat_of es1' ++ r1))
                   in2 (FO_end :: (flat_of es2' ++ r2)) lean1
                   Hin (stops_end _) (stops_end _) H1' H2') as [Hinner [l2 [Ha Hb]]].
      destruct (else_sugar_hd _ _ _ _ _ Ha Hb
                  (ltac:(discriminate)) (ltac:(discriminate)))
        as [_ [l3 [Ha' Hb']]].
      assert (Htail : (List.length (flat_of es1') <= n)%nat) by lia.
      destruct (IH es1' r1 es2' r2 l3 Htail Hs1 Hs2 Ha' Hb') as [Htl2 Hr].
      subst be1 be2. injection Hhd as Hbt. rewrite Hbt. rewrite Hinner.
      rewrite Htl2. split; [reflexivity | exact Hr].
    + (* loop against loop *)
      rewrite app_length in Hn. cbn [List.length] in Hn.
      assert (Hin : (List.length (flat_of in1) <= n)%nat) by lia.
      destruct (IH in1 (FO_end :: (flat_of es1' ++ r1))
                   in2 (FO_end :: (flat_of es2' ++ r2)) lean1
                   Hin (stops_end _) (stops_end _) H1' H2') as [Hinner [l2 [Ha Hb]]].
      destruct (else_sugar_hd _ _ _ _ _ Ha Hb
                  (ltac:(discriminate)) (ltac:(discriminate)))
        as [_ [l3 [Ha' Hb']]].
      assert (Htail : (List.length (flat_of es1') <= n)%nat) by lia.
      destruct (IH es1' r1 es2' r2 l3 Htail Hs1 Hs2 Ha' Hb') as [Htl2 Hr].
      subst be1 be2. injection Hhd as Hbt. rewrite Hbt. rewrite Hinner.
      rewrite Htl2. split; [reflexivity | exact Hr].
    + (* if against if. The then-bodies match at the [FO_else] boundary, and
         that is where the sugaring can differ: an empty else-body may have
         been written without its [0x05]. Either both sides elided it, in
         which case both else-bodies are empty, or neither did; a disagreement
         shows up as [FO_else] against the [FO_end] it hid. *)
      repeat rewrite app_length in Hn. cbn [List.length] in Hn.
      repeat rewrite app_length in Hn. cbn [List.length] in Hn.
      assert (Hina : (List.length (flat_of es1a) <= n)%nat) by lia.
      destruct (IH es1a
                   (FO_else :: (flat_of es1b ++ FO_end :: (flat_of es1' ++ r1)))
                   es2a
                   (FO_else :: (flat_of es2b ++ FO_end :: (flat_of es2' ++ r2)))
                   lean1 Hina (stops_else _) (stops_else _) H1' H2')
        as [Hthen [l2 [Ha Hb]]].
      assert (Hboth : es1b = es2b
                      /\ exists l3, else_sugar (flat_of es1' ++ r1) l3
                                    /\ else_sugar (flat_of es2' ++ r2) l3).
      { destruct (else_sugar_else_inv _ _ Ha) as [[la [Hla Ha']] | [opsa [Hea Ha']]];
        destruct (else_sugar_else_inv _ _ Hb) as [[lb [Hlb Hb']] | [opsb [Heb Hb']]].
        - (* neither elided: the else-bodies match at the closing [end] *)
          rewrite Hla in Hlb. injection Hlb as Hl. rewrite <- Hl in Hb'.
          assert (Hinb : (List.length (flat_of es1b) <= n)%nat) by lia.
          destruct (IH es1b (FO_end :: (flat_of es1' ++ r1))
                       es2b (FO_end :: (flat_of es2' ++ r2)) la
                       Hinb (stops_end _) (stops_end _) Ha' Hb')
            as [Helse [l3 [Hc Hd]]].
          destruct (else_sugar_hd _ _ _ _ _ Hc Hd
                      (ltac:(discriminate)) (ltac:(discriminate)))
            as [_ [l4 [Hc' Hd']]].
          split; [exact Helse | exists l4; split; [exact Hc' | exact Hd']].
        - (* one elided, the other did not: [FO_else] against [FO_end] *)
          exfalso. rewrite Heb in Hb'.
          destruct (else_sugar_keep_inv _ _ _ Hb' (ltac:(discriminate)))
            as [lb [Hlb _]].
          rewrite Hla in Hlb. discriminate Hlb.
        - exfalso. rewrite Hea in Ha'.
          destruct (else_sugar_keep_inv _ _ _ Ha' (ltac:(discriminate)))
            as [la [Hla _]].
          rewrite Hlb in Hla. discriminate Hla.
        - (* both elided: an else-body whose flattening starts with [FO_end] is
             empty, so the two agree *)
          assert (Hn1 : es1b = [] /\ FO_end :: opsa = FO_end :: (flat_of es1' ++ r1)).
          { apply (flat_of_inj_nil es1b (FO_end :: opsa)
                     (FO_end :: (flat_of es1' ++ r1)) (stops_end _)).
            rewrite <- Hea. reflexivity. }
          assert (Hn2 : es2b = [] /\ FO_end :: opsb = FO_end :: (flat_of es2' ++ r2)).
          { apply (flat_of_inj_nil es2b (FO_end :: opsb)
                     (FO_end :: (flat_of es2' ++ r2)) (stops_end _)).
            rewrite <- Heb. reflexivity. }
          destruct Hn1 as [Hb1n Hoa]. destruct Hn2 as [Hb2n Hob].
          rewrite Hea in Ha'. rewrite Hoa in Ha'.
          rewrite Heb in Hb'. rewrite Hob in Hb'.
          destruct (else_sugar_hd _ _ _ _ _ Ha' Hb'
                      (ltac:(discriminate)) (ltac:(discriminate)))
            as [_ [l3 [Hc Hd]]].
          split; [rewrite Hb1n; rewrite Hb2n; reflexivity
                 | exists l3; split; [exact Hc | exact Hd]]. }
      destruct Hboth as [Helse [l3 [Hc Hd]]].
      assert (Htail : (List.length (flat_of es1') <= n)%nat) by lia.
      destruct (IH es1' r1 es2' r2 l3 Htail Hs1 Hs2 Hc Hd) as [Htl2 Hr].
      subst be1 be2. injection Hhd as Hbt. rewrite Hbt. rewrite Hthen.
      rewrite Helse. rewrite Htl2. split; [reflexivity | exact Hr].
    + (* plain against plain *)
      assert (Htail : (List.length (flat_of es1') <= n)%nat) by lia.
      destruct (IH es1' r1 es2' r2 lean1 Htail Hs1 Hs2 H1' H2') as [Htl2 Hr].
      injection Hhd as Hbe. rewrite Hbe. rewrite Htl2.
      split; [reflexivity | exact Hr].
Qed.

(** The bytes of a body determine the instruction sequence. [repr_ops_det]
    settles the operator stream and [flat_sugar_inj_gen] settles the tree, so the
    validator's run cannot have structured the stream any other way -- and in
    particular a missing [0x05] is not a second reading of the same bytes, it is
    the only reading of different ones. This is what the completeness direction
    of the top-level theorem will need. *)
Theorem repr_expr_det : forall bs es1 es2,
  repr_expr bs es1 [] -> repr_expr bs es2 [] -> es1 = es2.
Proof.
  intros bs es1 es2 [ops1 [Hsug1 Hr1]] [ops2 [Hsug2 Hr2]].
  pose proof (repr_ops_det bs ops1 [] ops2 [] Hr1 Hr2 (eq_refl _) (eq_refl _))
    as Hops.
  subst ops2.
  destruct (flat_sugar_inj_gen (List.length (flat_of es1)) es1 [FO_end]
              es2 [FO_end] ops1 (Nat.le_refl _) (stops_end _) (stops_end _)
              Hsug1 Hsug2) as [Hes _].
  exact Hes.
Qed.

(* ================================================================== *)
(** ** An expression delimits itself                                   *)
(* ================================================================== *)

(** [repr_expr_det] above needs the expression to be the whole of the input,
    because [repr_ops] on its own is ambiguous: the empty operator sequence
    consumes nothing from anything. A function body is the whole of its input,
    so that was enough for the body theorems. A global's initialiser and an
    element or data segment's offset are not: bytes follow them, and the module
    format spec needs to know that the reader stops in only one place.

    It does, and the reason is that an expression's operator stream is
    self-delimiting. Nesting depth starts at zero, stays non-negative through
    the body, and the terminating [end] is the first operator that takes it
    below zero. Two readings of the same bytes agree operator by operator
    ([repr_op] is deterministic), so one stream is a prefix of the other, and a
    stream whose only negative depth is at its very end has no proper prefix
    with the same property. *)

(** Reading one operator is deterministic, so of two operator streams read from
    the same bytes, one is a prefix of the other and the shorter one's
    remainder carries the difference. *)
Lemma repr_ops_prefix : forall bs ops1 r1 ops2 r2,
  repr_ops bs ops1 r1 -> repr_ops bs ops2 r2 ->
  (exists tl, ops2 = ops1 ++ tl /\ repr_ops r1 tl r2)
  \/ (exists tl, ops1 = ops2 ++ tl /\ repr_ops r2 tl r1).
Proof.
  intros bs ops1 r1 ops2 r2 H1. revert ops2 r2.
  induction H1 as [bs1 | bs1 op1 mid1 ops1' r1' Hop1 Hops1 IH];
    intros ops2 r2 H2.
  - left. exists ops2. split; [reflexivity | exact H2].
  - inversion H2 as [bs2 | bs2 op2 mid2 ops2' r2' Hop2 Hops2]; subst.
    + right. exists (op1 :: ops1'). split; [reflexivity|].
      eapply repr_ops_cons; eassumption.
    + destruct (repr_op_det _ _ _ _ _ Hop1 Hop2) as [-> ->].
      destruct (IH _ _ Hops2) as [[tl [-> Htl]] | [tl [-> Htl]]].
      * left. exists tl. split; [reflexivity | exact Htl].
      * right. exists tl. split; [reflexivity | exact Htl].
Qed.

(** How one operator changes the nesting depth. [FO_else] does not: it closes
    no frame and opens none, it switches between the two halves of one. *)
Definition op_delta (op : flat_op) : Z :=
  match op with
  | FO_block _ | FO_loop _ | FO_if _ => 1
  | FO_end => -1
  | FO_else => 0
  | FO_plain _ => 0
  end.

Fixpoint depth (d : Z) (ops : list flat_op) : Z :=
  match ops with
  | [] => d
  | op :: rest => depth (d + op_delta op) rest
  end.

Lemma depth_app : forall ops1 ops2 d,
  depth d (ops1 ++ ops2) = depth (depth d ops1) ops2.
Proof.
  induction ops1 as [|op ops1 IH]; intros ops2 d; [reflexivity|].
  cbn. apply IH.
Qed.

(** Depth is a running total, so shifting the start shifts every reading. *)
Lemma depth_shift : forall ops d k, depth (d + k) ops = depth d ops + k.
Proof.
  induction ops as [|op ops IH]; intros d k; [reflexivity|].
  cbn. replace (d + k + op_delta op) with (d + op_delta op + k) by lia.
  apply IH.
Qed.

(** An operator stream that opens and closes every frame it mentions, and never
    closes one it did not open. *)
Definition balanced (ops : list flat_op) : Prop :=
  depth 0 ops = 0 /\ forall pre suf, ops = pre ++ suf -> 0 <= depth 0 pre.

Lemma balanced_nil : balanced [].
Proof.
  split; [reflexivity|].
  intros pre suf H. symmetry in H. apply app_eq_nil in H as [-> _].
  cbn. lia.
Qed.

Lemma balanced_flat : forall op, op_delta op = 0 -> balanced [op].
Proof.
  intros op Hd. split.
  - cbn. rewrite Hd. reflexivity.
  - intros pre suf H.
    destruct pre as [|o [|o' pre']]; cbn in *; try discriminate; try lia.
    injection H as -> _. rewrite Hd. lia.
Qed.

Lemma balanced_app : forall a b, balanced a -> balanced b -> balanced (a ++ b).
Proof.
  intros a b [Ha0 Hap] [Hb0 Hbp]. split.
  - rewrite depth_app, Ha0. exact Hb0.
  - intros pre suf Hsplit.
    destruct (app_eq_app _ _ _ _ Hsplit) as [l [[H1 H2] | [H1 H2]]].
    + (* the prefix stops inside [a] *)
      exact (Hap _ _ H1).
    + (* the prefix covers [a] and part of [b] *)
      subst pre. rewrite depth_app, Ha0. exact (Hbp _ _ H2).
Qed.

(** [cbn] turns [0 + x] into [x], so a reading that starts one frame deep is
    [depth 1] with no addition left for [depth_shift] to match on. *)
Lemma depth_one : forall ops, depth 1 ops = depth 0 ops + 1.
Proof.
  intros ops. pose proof (depth_shift ops 0 1) as H.
  replace (0 + 1) with 1 in H by lia. exact H.
Qed.

Lemma balanced_wrap : forall op inner,
  op_delta op = 1 -> balanced inner -> balanced (op :: inner ++ [FO_end]).
Proof.
  intros op inner Hd [Hi0 Hip]. split.
  - cbn. rewrite Hd, depth_app, depth_one, Hi0. cbn. lia.
  - intros pre suf Hsplit.
    destruct pre as [|o pre']; [cbn; lia|].
    cbn in Hsplit. injection Hsplit as -> Hsplit.
    cbn. rewrite Hd.
    destruct (app_eq_app _ _ _ _ Hsplit) as [l [[H1 H2] | [H1 H2]]].
    + (* stops inside the body: one deeper than the body's own reading *)
      rewrite depth_one. pose proof (Hip _ _ H1). lia.
    + (* covers the body, and then either stops or takes the closing end *)
      subst pre'. rewrite depth_app, depth_one, Hi0.
      destruct l as [|o' l']; [cbn; lia|].
      cbn in H2. injection H2 as <- H2.
      symmetry in H2. apply app_eq_nil in H2 as [-> ->].
      cbn. lia.
Qed.

(** Pull a bound on a sub-flattening out of a bound on the whole. Two rounds,
    because [if]'s flattening nests an append inside a cons inside an append. *)
Ltac crunch_len H :=
  cbn in H; rewrite ?List.app_length in H; cbn in H;
  rewrite ?List.app_length in H; cbn in H.

Lemma flat_of_balanced_gen : forall n es,
  (List.length (flat_of es) <= n)%nat -> balanced (flat_of es).
Proof.
  induction n as [|n IH]; intros es Hn.
  - destruct es as [|be es']; [rewrite flat_of_nil; apply balanced_nil|].
    exfalso. rewrite flat_of_cons, List.app_length in Hn.
    pose proof (flat_of_one_nonnil be) as Hnn.
    destruct (flat_of_one be) as [|o os]; [contradiction|]. cbn in Hn. lia.
  - destruct es as [|be es']; [rewrite flat_of_nil; apply balanced_nil|].
    rewrite flat_of_cons in *. rewrite List.app_length in Hn.
    assert (Hrest : (List.length (flat_of es') <= n)%nat).
    { pose proof (flat_of_one_nonnil be) as Hnn.
      destruct (flat_of_one be) as [|o os]; [contradiction|]. cbn in Hn. lia. }
    apply balanced_app; [|exact (IH _ Hrest)].
    destruct (flat_of_one_cases be)
      as [[bt [inner [_ Hbe]]] | [[bt [inner [_ Hbe]]]
         | [[bt [es1 [es2 [_ Hbe]]]] | Hbe]]]; rewrite Hbe in *.
    + apply balanced_wrap; [reflexivity|].
      apply IH. crunch_len Hn. lia.
    + apply balanced_wrap; [reflexivity|].
      apply IH. crunch_len Hn. lia.
    + (* the two halves and the [else] between them are each balanced *)
      assert (Hshape :
        FO_if bt :: flat_of es1 ++ FO_else :: flat_of es2 ++ [FO_end]
        = FO_if bt :: (flat_of es1 ++ [FO_else] ++ flat_of es2) ++ [FO_end]).
      { f_equal. rewrite <- !app_assoc. reflexivity. }
      rewrite Hshape.
      assert (Hlen : (List.length (flat_of es1) + List.length (flat_of es2)
                      <= n)%nat).
      { crunch_len Hn. lia. }
      apply balanced_wrap; [reflexivity|].
      apply balanced_app; [apply IH; lia|].
      apply balanced_app; [apply balanced_flat; reflexivity | apply IH; lia].
    + apply balanced_flat. reflexivity.
Qed.

Lemma flat_of_balanced : forall es, balanced (flat_of es).
Proof.
  intros es. exact (flat_of_balanced_gen (List.length (flat_of es)) es (le_n _)).
Qed.

(** Sugaring drops [FO_else]s, whose delta is zero, so it leaves depth alone. *)
Lemma else_sugar_depth : forall full lean,
  else_sugar full lean -> forall d, depth d lean = depth d full.
Proof.
  intros full lean H.
  induction H as [| op ops lean0 H IH | ops lean0 H IH]; intros d.
  - reflexivity.
  - cbn. apply IH.
  - rewrite (IH d). cbn. f_equal. lia.
Qed.

(** A split of the sugared stream comes from a split of the full one. *)
Lemma else_sugar_split : forall full lean pre suf,
  else_sugar full lean -> lean = pre ++ suf ->
  exists fpre fsuf,
    full = fpre ++ fsuf /\ else_sugar fpre pre /\ else_sugar fsuf suf.
Proof.
  intros full lean pre suf H. revert pre suf.
  induction H as [| op ops lean0 H IH | ops lean0 H IH]; intros pre suf Hsplit.
  - symmetry in Hsplit. apply app_eq_nil in Hsplit as [-> ->].
    exists [], []. split; [reflexivity|]. split; apply else_sugar_nil.
  - destruct pre as [|p pre'].
    + cbn in Hsplit. subst suf.
      exists [], (op :: ops). split; [reflexivity|].
      split; [apply else_sugar_nil | apply else_sugar_keep; exact H].
    + cbn in Hsplit. injection Hsplit as <- Hsplit.
      destruct (IH _ _ Hsplit) as [fpre [fsuf [-> [Hp Hs]]]].
      exists (op :: fpre), fsuf. split; [reflexivity|].
      split; [apply else_sugar_keep; exact Hp | exact Hs].
  - destruct (IH _ _ Hsplit) as [fpre [fsuf [Heq [Hp Hs]]]].
    (* the dropped [FO_else] sits with the [FO_end] it hid, so it goes
       wherever that [FO_end] went *)
    destruct fpre as [|f fpre'].
    + cbn in Heq. subst fsuf.
      exists [], (FO_else :: FO_end :: ops). split; [reflexivity|].
      split; [exact Hp | apply else_sugar_drop; exact Hs].
    + cbn in Heq. injection Heq as <- Heq. subst ops.
      exists (FO_else :: FO_end :: fpre'), fsuf. split; [reflexivity|].
      split; [apply else_sugar_drop; exact Hp | exact Hs].
Qed.

(** The converse of [else_sugar_nil_out]: nothing sugars to something. *)
Lemma else_sugar_nil_in : forall lean, else_sugar [] lean -> lean = [].
Proof. intros lean H. inversion H. reflexivity. Qed.

(** An expression's operator stream reaches depth -1, and only at its very end.
    That is what makes it self-delimiting: the terminating [end] is the first
    operator to close a frame that was never opened. *)
Lemma expr_ops_depth : forall es ops,
  else_sugar (flat_of es ++ [FO_end]) ops -> depth 0 ops = -1.
Proof.
  intros es ops Hsug.
  rewrite (else_sugar_depth _ _ Hsug 0), depth_app.
  destruct (flat_of_balanced es) as [Hb _]. rewrite Hb. cbn. lia.
Qed.

Lemma expr_ops_prefix_nonneg : forall es ops pre suf,
  else_sugar (flat_of es ++ [FO_end]) ops ->
  ops = pre ++ suf -> suf <> [] -> 0 <= depth 0 pre.
Proof.
  intros es ops pre suf Hsug Hsplit Hne.
  destruct (else_sugar_split _ _ _ _ Hsug Hsplit)
    as [fpre [fsuf [Heq [Hp Hs]]]].
  rewrite (else_sugar_depth _ _ Hp 0).
  (* a non-empty sugared suffix comes from a non-empty full one, so [fpre]
     stops before the closing [end] and lies inside the flattening *)
  assert (Hfs : fsuf <> []).
  { intros ->. apply Hne. exact (else_sugar_nil_in _ Hs). }
  destruct (flat_of_balanced es) as [_ Hbp].
  destruct (app_eq_app _ _ _ _ Heq) as [l [[H1 H2] | [H1 H2]]].
  - (* [fpre] stops inside the flattening *)
    exact (Hbp _ _ H1).
  - (* [fpre] covers the flattening; taking the [end] too would leave
       nothing for the suffix *)
    destruct l as [|o l'].
    + rewrite app_nil_r in H1. rewrite H1.
      exact (Hbp _ [] (eq_sym (app_nil_r _))).
    + exfalso. cbn in H2. injection H2 as _ H2.
      symmetry in H2. apply app_eq_nil in H2 as [_ ->]. apply Hfs. reflexivity.
Qed.

(** [repr_expr] with a remainder. [Spec_Expr.repr_expr_det] is the case where
    the remainder is empty; this is what a global's initialiser and a segment's
    offset need, since bytes follow them. *)
Theorem repr_expr_det_rest : forall bs es1 r1 es2 r2,
  repr_expr bs es1 r1 -> repr_expr bs es2 r2 -> es1 = es2 /\ r1 = r2.
Proof.
  intros bs es1 r1 es2 r2 [ops1 [Hsug1 Hr1]] [ops2 [Hsug2 Hr2]].
  assert (Hsame : ops1 = ops2 /\ r1 = r2).
  { destruct (repr_ops_prefix _ _ _ _ _ Hr1 Hr2)
      as [[tl [-> Htl]] | [tl [-> Htl]]].
    - destruct tl as [|t tl'].
      + rewrite app_nil_r. inversion Htl; subst. split; reflexivity.
      + exfalso.
        pose proof (expr_ops_prefix_nonneg _ _ ops1 (t :: tl') Hsug2
                      eq_refl ltac:(discriminate)) as Hnn.
        pose proof (expr_ops_depth _ _ Hsug1) as Hm. lia.
    - destruct tl as [|t tl'].
      + rewrite app_nil_r. inversion Htl; subst. split; reflexivity.
      + exfalso.
        pose proof (expr_ops_prefix_nonneg _ _ ops2 (t :: tl') Hsug1
                      eq_refl ltac:(discriminate)) as Hnn.
        pose proof (expr_ops_depth _ _ Hsug2) as Hm. lia. }
  destruct Hsame as [-> ->]. split; [|reflexivity].
  destruct (flat_sugar_inj_gen (List.length (flat_of es1)) es1 [FO_end]
              es2 [FO_end] ops2 (Nat.le_refl _) (stops_end _) (stops_end _)
              Hsug1 Hsug2) as [Hes _].
  exact Hes.
Qed.

(* ================================================================== *)
(** ** Reading a prefix                                                *)
(* ================================================================== *)

(** An expression reads a prefix and does not look past it, for the same
    reason its operator stream does: the sugaring is a fact about the stream
    alone, and [repr_ops] is where the bytes are read. A global's initialiser
    and a segment's offset both sit inside a section, so this is what lets
    them be read out of the module and then be an expression on their own. *)
Lemma repr_expr_prefix : reads_prefix repr_expr.
Proof.
  intros bs es rest [ops [Hsug Hops]].
  destruct (repr_ops_prefix_read _ _ _ Hops) as [pre [Heq Hall]].
  exists pre. split; [exact Heq|].
  intros rest'. exists ops. split; [exact Hsug | apply Hall].
Qed.
