(** * Reading the consumed operator stream off a frame list

    [Spec_Expr.v] defines [flat_of], which flattens an instruction tree into the
    operator stream encoding it, and [repr_expr], which ties that stream to the
    bytes. Both are facts about the specification alone.

    Recovering the tree from the stream is what the simulation invariant's ghost
    lists already do: [step_block] pushes a frame, [step_end_block] appends
    [BI_block bt (fv_done g)] to the frame below. This file makes that precise.
    [frames_flat] reads the operators consumed so far straight off the frame
    list, and each step lemma of [OpIter_Sim.v] gets a corollary saying it
    extends that stream by exactly the operator it consumed.

    These are facts about the step lemmas' conclusions, not about the byte
    format, which is why they live here rather than in [Spec_Expr.v]. *)

Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
From Wasm Require Import datatypes numerics type_checker operations typing.
(* [Aeneas_Specs] is what brings the extracted types into scope; never [Include]
   the extracted modules again, which would shadow Primitives constants with
   opaque copies. *)
Require Import Itasca.Aeneas_Specs.
Require Import Itasca.Spec_Binary.
(* [Export], not [Import]: [flat_of], [else_sugar] and [repr_expr] used to be
   defined here and moved to [Spec_Expr.v] so that the module format spec could
   depend on them without dragging in the extraction. Consumers of this file
   should not have to care which half a name came from. *)
Require Export Itasca.Spec_Expr.
Require Import Itasca.Translate.
Require Import Itasca.OpIter_State.
Require Import Itasca.OpIter_Sim.

(* Mathcomp is not imported here, so [++] is [List.app] and the ordinary
   [rewrite] applies, including [rewrite <-]. Binding the type keeps it that way
   even if a dependency's [Bind Scope seq_scope with list] is in force. *)
Local Open Scope list_scope.
Local Bind Scope list_scope with list.


(* ================================================================== *)
(** ** The operator stream a frame list accounts for                    *)
(* ================================================================== *)

(** The operator(s) that opened a frame. The outermost frame is opened by
    entering the function rather than by an operator, so it contributes
    nothing.

    A function of the [fview], not just the [Ctrl]: an [Else] frame's opener
    has to include the then-branch, which only the ghost list still
    remembers -- [fv_done] holds the *else*-branch's progress by the time the
    frame is [Else], since that is what [step_switch_else] stashed [fv_then]
    for. A [Then] frame's opener is just the [if], since its own [fv_done] is
    the then-branch in progress. *)
Definition frame_open (f : fview) : list flat_op :=
  match (fv_ctrl f).(code_Ctrl_kind) with
  | Code_LabelKind_Block =>
      [FO_block (translate_bt (fv_ctrl f).(code_Ctrl_block_type))]
  | Code_LabelKind_Loop =>
      [FO_loop (translate_bt (fv_ctrl f).(code_Ctrl_block_type))]
  | Code_LabelKind_Then =>
      [FO_if (translate_bt (fv_ctrl f).(code_Ctrl_block_type))]
  | Code_LabelKind_Else =>
      FO_if (translate_bt (fv_ctrl f).(code_Ctrl_block_type))
        :: flat_of (fv_then f) ++ [FO_else]
  | _ => []
  end.

Lemma frame_open_block : forall f bt,
  (fv_ctrl f).(code_Ctrl_kind) = Code_LabelKind_Block ->
  (fv_ctrl f).(code_Ctrl_block_type) = bt ->
  frame_open f = [FO_block (translate_bt bt)].
Proof.
  intros f bt Hk Hb. unfold frame_open. rewrite Hk. rewrite Hb. reflexivity.
Qed.

Lemma frame_open_loop : forall f bt,
  (fv_ctrl f).(code_Ctrl_kind) = Code_LabelKind_Loop ->
  (fv_ctrl f).(code_Ctrl_block_type) = bt ->
  frame_open f = [FO_loop (translate_bt bt)].
Proof.
  intros f bt Hk Hb. unfold frame_open. rewrite Hk. rewrite Hb. reflexivity.
Qed.

Lemma frame_open_body : forall f,
  (fv_ctrl f).(code_Ctrl_kind) = Code_LabelKind_Body -> frame_open f = [].
Proof. intros f Hk. unfold frame_open. rewrite Hk. reflexivity. Qed.

Lemma frame_open_then : forall f bt,
  (fv_ctrl f).(code_Ctrl_kind) = Code_LabelKind_Then ->
  (fv_ctrl f).(code_Ctrl_block_type) = bt ->
  frame_open f = [FO_if (translate_bt bt)].
Proof.
  intros f bt Hk Hb. unfold frame_open. rewrite Hk. rewrite Hb. reflexivity.
Qed.

Lemma frame_open_else : forall f bt,
  (fv_ctrl f).(code_Ctrl_kind) = Code_LabelKind_Else ->
  (fv_ctrl f).(code_Ctrl_block_type) = bt ->
  frame_open f = FO_if (translate_bt bt) :: flat_of (fv_then f) ++ [FO_else].
Proof.
  intros f bt Hk Hb. unfold frame_open. rewrite Hk. rewrite Hb. reflexivity.
Qed.

(** The operators consumed so far, read off the frames. Each frame contributes
    the operator that opened it followed by the flattening of what it has
    consumed. Frames are outermost-first, and an enclosing frame consumes nothing
    while a nested one is open, so this is exactly stream order. *)
Fixpoint frames_flat (fs : list fview) : list flat_op :=
  match fs with
  | [] => []
  | f :: rest =>
      frame_open f ++ flat_of (fv_done f) ++ frames_flat rest
  end.

Lemma frames_flat_app : forall fs gs,
  frames_flat (fs ++ gs) = frames_flat fs ++ frames_flat gs.
Proof.
  induction fs as [|f fs IH]; intros gs; [reflexivity|].
  cbn [frames_flat app]. rewrite IH.
  rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
Qed.

(* ================================================================== *)
(** ** Every step extends the stream by the operator it consumed        *)
(* ================================================================== *)

(** The frame the plain steps produce: the same control frame up to fields
    [frame_open] does not read, a new operand segment, and one instruction
    appended. The [Ctrl] is left free so [unreachable], the one step that
    rewrites the frame, is covered too. *)
Lemma frames_flat_plain : forall pre f c' seg' be,
  frame_open {| fv_ctrl := c'; fv_seg := seg'; fv_done := fv_done f ++ [be];
                fv_then := fv_then f |}
    = frame_open f ->
  flat_of_one be = [FO_plain be] ->
  frames_flat (pre ++ [{| fv_ctrl := c';
                          fv_seg := seg';
                          fv_done := fv_done f ++ [be];
                          fv_then := fv_then f |}])
    = frames_flat (pre ++ [f]) ++ [FO_plain be].
Proof.
  intros pre f c' seg' be Hopen Hbe.
  rewrite frames_flat_app. rewrite frames_flat_app.
  cbn [frames_flat]. rewrite Hopen.
  cbn [fv_done]. rewrite flat_of_app. rewrite flat_of_single. rewrite Hbe.
  rewrite app_nil_r. rewrite app_nil_r.
  rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
Qed.

(** [frames_flat_plain]'s side condition, for every instruction the covered
    readers append. All are single [FO_plain]s; [block] and [loop] are the only
    exceptions and they push a frame rather than appending. *)
Lemma flat_of_one_nop : flat_of_one BI_nop = [FO_plain BI_nop].
Proof. reflexivity. Qed.

Lemma flat_of_one_unreachable :
  flat_of_one BI_unreachable = [FO_plain BI_unreachable].
Proof. reflexivity. Qed.

Lemma flat_of_one_drop : flat_of_one BI_drop = [FO_plain BI_drop].
Proof. reflexivity. Qed.

Lemma flat_of_one_select : forall ot,
  flat_of_one (BI_select ot) = [FO_plain (BI_select ot)].
Proof. intros ot. reflexivity. Qed.

Lemma flat_of_one_const_num : forall v,
  flat_of_one (BI_const_num v) = [FO_plain (BI_const_num v)].
Proof. intros v. reflexivity. Qed.

Lemma flat_of_one_load : forall nt tp a o,
  flat_of_one (BI_load nt tp a o) = [FO_plain (BI_load nt tp a o)].
Proof. intros nt tp a o. reflexivity. Qed.

Lemma flat_of_one_store : forall nt tp a o,
  flat_of_one (BI_store nt tp a o) = [FO_plain (BI_store nt tp a o)].
Proof. intros nt tp a o. reflexivity. Qed.

Lemma flat_of_one_br : forall i, flat_of_one (BI_br i) = [FO_plain (BI_br i)].
Proof. intros i. reflexivity. Qed.

Lemma flat_of_one_br_if : forall i,
  flat_of_one (BI_br_if i) = [FO_plain (BI_br_if i)].
Proof. intros i. reflexivity. Qed.

Lemma flat_of_one_br_table : forall iss i,
  flat_of_one (BI_br_table iss i) = [FO_plain (BI_br_table iss i)].
Proof. intros iss i. reflexivity. Qed.

Lemma flat_of_one_return : flat_of_one BI_return = [FO_plain BI_return].
Proof. reflexivity. Qed.

Lemma flat_of_one_call : forall i,
  flat_of_one (BI_call i) = [FO_plain (BI_call i)].
Proof. intros i. reflexivity. Qed.

Lemma flat_of_one_call_indirect : forall x y,
  flat_of_one (BI_call_indirect x y) = [FO_plain (BI_call_indirect x y)].
Proof. intros x y. reflexivity. Qed.

(** [block] and [loop]: a fresh frame contributes just its opener, having
    consumed nothing yet. *)
Lemma frames_flat_push : forall fs kind bt base,
  frames_flat (fs ++ [{| fv_ctrl :=
                           {| code_Ctrl_kind := kind;
                              code_Ctrl_block_type := bt;
                              code_Ctrl_value_stack_base := base;
                              code_Ctrl_polymorphic_base := false |};
                         fv_seg := [];
                         fv_done := [];
                         fv_then := [] |}])
    = frames_flat fs
      ++ frame_open {| fv_ctrl :=
                          {| code_Ctrl_kind := kind;
                             code_Ctrl_block_type := bt;
                             code_Ctrl_value_stack_base := base;
                             code_Ctrl_polymorphic_base := false |};
                        fv_seg := [];
                        fv_done := [];
                        fv_then := [] |}.
Proof.
  intros fs kind bt base. rewrite frames_flat_app.
  cbn [frames_flat fv_done]. rewrite flat_of_nil.
  cbn [app]. rewrite app_nil_r. reflexivity.
Qed.

(** [end]: the closed frame's opener and contents become the enclosing frame's
    [BI_block], and the stream grows by the single [FO_end] that closed it. The
    nesting cancels exactly, which is what the ghost lists exist to deliver. *)
Lemma frames_flat_end_block : forall pre f g seg' bt,
  (fv_ctrl g).(code_Ctrl_kind) = Code_LabelKind_Block ->
  (fv_ctrl g).(code_Ctrl_block_type) = bt ->
  frames_flat (pre ++ [{| fv_ctrl := fv_ctrl f;
                          fv_seg := seg';
                          fv_done := fv_done f
                                     ++ [BI_block (translate_bt bt)
                                                  (fv_done g)];
                                                  fv_then := fv_then f |}])
    = frames_flat (pre ++ [f] ++ [g]) ++ [FO_end].
Proof.
  intros pre f g seg' bt Hkind Hbt.
  (* [[f] ++ [g]] has to become a cons list before [frames_flat] can reduce *)
  cbn [app].
  rewrite frames_flat_app. rewrite frames_flat_app.
  cbn [frames_flat fv_ctrl fv_seg fv_done].
  rewrite (frame_open_block g bt Hkind Hbt).
  rewrite flat_of_app. rewrite flat_of_single. rewrite flat_of_one_block.
  repeat rewrite app_nil_r. repeat rewrite <- app_assoc. reflexivity.
Qed.

Lemma frames_flat_end_loop : forall pre f g seg' bt,
  (fv_ctrl g).(code_Ctrl_kind) = Code_LabelKind_Loop ->
  (fv_ctrl g).(code_Ctrl_block_type) = bt ->
  frames_flat (pre ++ [{| fv_ctrl := fv_ctrl f;
                          fv_seg := seg';
                          fv_done := fv_done f
                                     ++ [BI_loop (translate_bt bt)
                                                 (fv_done g)];
                                                 fv_then := fv_then f |}])
    = frames_flat (pre ++ [f] ++ [g]) ++ [FO_end].
Proof.
  intros pre f g seg' bt Hkind Hbt.
  (* [[f] ++ [g]] has to become a cons list before [frames_flat] can reduce *)
  cbn [app].
  rewrite frames_flat_app. rewrite frames_flat_app.
  cbn [frames_flat fv_ctrl fv_seg fv_done].
  rewrite (frame_open_loop g bt Hkind Hbt).
  rewrite flat_of_app. rewrite flat_of_single. rewrite flat_of_one_loop.
  repeat rewrite app_nil_r. repeat rewrite <- app_assoc. reflexivity.
Qed.

(** [else] rewrites the innermost frame rather than pushing one: the [Then]'s
    ghost list moves to [fv_then], which is where the [Else] frame's opener
    reads it, so the stream grows by the one [FO_else] the byte encoded. *)
Lemma frames_flat_switch_else : forall pre g c' bt,
  (fv_ctrl g).(code_Ctrl_kind) = Code_LabelKind_Then ->
  (fv_ctrl g).(code_Ctrl_block_type) = bt ->
  c'.(code_Ctrl_kind) = Code_LabelKind_Else ->
  c'.(code_Ctrl_block_type) = bt ->
  frames_flat (pre ++ [{| fv_ctrl := c';
                          fv_seg := [];
                          fv_done := [];
                          fv_then := fv_done g |}])
    = frames_flat (pre ++ [g]) ++ [FO_else].
Proof.
  intros pre g c' bt Hkind Hbt Hkind' Hbt'.
  rewrite frames_flat_app. rewrite frames_flat_app.
  cbn [frames_flat fv_done].
  rewrite (frame_open_then g bt Hkind Hbt).
  rewrite (frame_open_else {| fv_ctrl := c'; fv_seg := []; fv_done := [];
                              fv_then := fv_done g |} bt Hkind' Hbt').
  cbn [fv_then]. rewrite flat_of_nil.
  repeat rewrite app_nil_r. repeat rewrite <- app_assoc. cbn [app].
  repeat rewrite app_mid_reassoc. cbn [app].
  repeat rewrite <- app_assoc. reflexivity.
Qed.

(** [end] closing an [Else]: the two ghost lists are the two bodies, and the
    opener already accounts for the [FO_else] between them. One operator, as
    for a block. *)
Lemma frames_flat_end_else : forall pre f g seg' bt,
  (fv_ctrl g).(code_Ctrl_kind) = Code_LabelKind_Else ->
  (fv_ctrl g).(code_Ctrl_block_type) = bt ->
  frames_flat (pre ++ [{| fv_ctrl := fv_ctrl f;
                          fv_seg := seg';
                          fv_done := fv_done f
                                     ++ [BI_if (translate_bt bt)
                                               (fv_then g) (fv_done g)];
                          fv_then := fv_then f |}])
    = frames_flat (pre ++ [f] ++ [g]) ++ [FO_end].
Proof.
  intros pre f g seg' bt Hkind Hbt.
  cbn [app].
  rewrite frames_flat_app. rewrite frames_flat_app.
  cbn [frames_flat fv_ctrl fv_seg fv_done].
  rewrite (frame_open_else g bt Hkind Hbt).
  rewrite flat_of_app. rewrite flat_of_single. rewrite flat_of_one_if.
  repeat rewrite app_nil_r. repeat rewrite <- app_assoc. cbn [app].
  repeat rewrite app_mid_reassoc. cbn [app].
  repeat rewrite <- app_assoc. reflexivity.
Qed.

(** [end] closing a bare [Then]: the [if] had no [else] byte at all, and this is
    the one step whose stream grows by *two* operators. The closed frame becomes
    [BI_if bt es [::]], whose flattening writes the [FO_else] that separates the
    two bodies -- spec 5.4.1's second production -- but the bytes only carried
    the [0x0B]. [else_sugar] is what reconciles the two: the phantom [FO_else]
    is immediately followed by the [FO_end], which is exactly the pair it
    permits eliding. *)
Lemma frames_flat_end_then : forall pre f g seg' bt,
  (fv_ctrl g).(code_Ctrl_kind) = Code_LabelKind_Then ->
  (fv_ctrl g).(code_Ctrl_block_type) = bt ->
  frames_flat (pre ++ [{| fv_ctrl := fv_ctrl f;
                          fv_seg := seg';
                          fv_done := fv_done f
                                     ++ [BI_if (translate_bt bt)
                                               (fv_done g) []];
                          fv_then := fv_then f |}])
    = frames_flat (pre ++ [f] ++ [g]) ++ [FO_else; FO_end].
Proof.
  intros pre f g seg' bt Hkind Hbt.
  cbn [app].
  rewrite frames_flat_app. rewrite frames_flat_app.
  cbn [frames_flat fv_ctrl fv_seg fv_done].
  rewrite (frame_open_then g bt Hkind Hbt).
  rewrite flat_of_app. rewrite flat_of_single. rewrite flat_of_one_if.
  rewrite flat_of_nil.
  repeat rewrite app_nil_r. repeat rewrite <- app_assoc. cbn [app].
  repeat rewrite app_mid_reassoc. cbn [app].
  repeat rewrite <- app_assoc. reflexivity.
Qed.

(** The operand segment is not part of the stream, so a step that only moves
    operands leaves it alone. [if] pops its condition from the enclosing frame
    before pushing, which is the one push that needs this. *)
Lemma frames_flat_seg : forall pre f seg',
  frames_flat (pre ++ [{| fv_ctrl := fv_ctrl f; fv_seg := seg';
                          fv_done := fv_done f; fv_then := fv_then f |}])
    = frames_flat (pre ++ [f]).
Proof.
  intros pre f seg'. rewrite frames_flat_app. rewrite frames_flat_app.
  cbn [frames_flat fv_done]. unfold frame_open. cbn [fv_ctrl fv_then].
  reflexivity.
Qed.

(** The starting point: the [Body] frame has no opener and has consumed nothing,
    so the stream is empty. *)
Lemma frames_flat_start : forall bt, frames_flat [body_fview bt] = [].
Proof. intros bt. reflexivity. Qed.

(** And the finish. When the body's [end] closes the outermost frame, the stream
    consumed is the flattening of what that frame accumulated followed by the
    closing [end] -- which is exactly the operator stream [repr_expr] asks for. *)
Lemma frames_flat_body : forall f,
  (fv_ctrl f).(code_Ctrl_kind) = Code_LabelKind_Body ->
  frames_flat [f] ++ [FO_end] = flat_of (fv_done f) ++ [FO_end].
Proof.
  intros f Hkind. cbn [frames_flat]. rewrite (frame_open_body _ Hkind).
  rewrite app_nil_r. reflexivity.
Qed.

(* ================================================================== *)
(** ** Which frame is which                                           *)
(* ================================================================== *)

(** [Inv] does not say which frame is which, and for the step lemmas it does not
    need to. The dispatch does, in three ways. When [end] reports it closed a
    [Block] or [Loop] frame, [step_end_block_op] wants the frame list as
    [pre ++ [f] ++ [g]], so the closed frame must not have been the only one. When
    it reports the [Body] frame, the top-level case wants [fs = [f]], so there must
    have been nothing below it either. And there must be no third possibility:
    [Inv] permits a [Then] or [Else] frame, for which there is no step lemma at
    all.

    So the predicate is what the design actually guarantees, and what
    [start_function] plus [push_ctrl]'s three call sites establish: the bottom
    frame is the body's, and every frame above it is a block or a loop. Kept as a
    companion rather than a conjunct of [Inv], so no existing lemma changes: it is
    a property of the frame list alone, and every step lemma states its new frame
    list explicitly. *)
Definition kind_ok (c : code_Ctrl_t) : Prop :=
  c.(code_Ctrl_kind) = Code_LabelKind_Block
  \/ c.(code_Ctrl_kind) = Code_LabelKind_Loop
  \/ c.(code_Ctrl_kind) = Code_LabelKind_Then
  \/ c.(code_Ctrl_kind) = Code_LabelKind_Else.

Fixpoint inner_kinds (fs : list fview) : Prop :=
  match fs with
  | [] => True
  | f :: rest => kind_ok (fv_ctrl f) /\ inner_kinds rest
  end.

(** Parameterised by the body frame's block type as well as pinning its kind: the
    top-level theorem has to relate the finished instruction sequence to the
    function's declared results, and every step preserves both fields. *)
Definition body_first (bt : code_BlockType_t) (fs : list fview) : Prop :=
  match fs with
  | [] => False
  | f :: rest =>
      (fv_ctrl f).(code_Ctrl_kind) = Code_LabelKind_Body
      /\ (fv_ctrl f).(code_Ctrl_block_type) = bt
      /\ inner_kinds rest
  end.

Lemma inner_kinds_last : forall pre f g,
  (fv_ctrl g).(code_Ctrl_kind) = (fv_ctrl f).(code_Ctrl_kind) ->
  inner_kinds (pre ++ [f]) -> inner_kinds (pre ++ [g]).
Proof.
  intros pre f g Hk. induction pre as [|h pre IH]; cbn [app inner_kinds];
    intros [H1 H2].
  - split; [unfold kind_ok in H1 |- *; rewrite Hk; exact H1 | exact H2].
  - split; [exact H1 | apply IH; exact H2].
Qed.

Lemma inner_kinds_push : forall fs g,
  kind_ok (fv_ctrl g) -> inner_kinds fs -> inner_kinds (fs ++ [g]).
Proof.
  intros fs g Hg. induction fs as [|h fs IH]; cbn [app inner_kinds]; intros H.
  - split; [exact Hg | exact I].
  - destruct H as [H1 H2]. split; [exact H1 | apply IH; exact H2].
Qed.

Lemma inner_kinds_prefix : forall fs g, inner_kinds (fs ++ [g]) -> inner_kinds fs.
Proof.
  induction fs as [|h fs IH]; cbn [app inner_kinds]; intros g H; [exact I|].
  destruct H as [H1 H2]. split; [exact H1 | apply (IH g); exact H2].
Qed.

(** [step_switch_else] rewrites the innermost frame's kind ([Then] to [Else]),
    unlike [body_first_last]'s steps, which keep it fixed. All [body_first]
    asks of a non-head frame is [kind_ok], so any [kind_ok] replacement works,
    regardless of whether the kind itself changed. *)
Lemma body_first_switch : forall bt h pre g g',
  kind_ok (fv_ctrl g') -> body_first bt (h :: pre ++ [g]) ->
  body_first bt (h :: pre ++ [g']).
Proof.
  intros bt h pre g g' Hg' Hbf. cbn [body_first] in Hbf |- *.
  destruct Hbf as [H1 [H2 H3]]. split; [exact H1|]. split; [exact H2|].
  apply inner_kinds_push; [exact Hg'|]. apply (inner_kinds_prefix pre g).
  exact H3.
Qed.

Lemma inner_kinds_last_kind : forall fs f,
  inner_kinds (fs ++ [f]) -> kind_ok (fv_ctrl f).
Proof.
  induction fs as [|h fs IH]; cbn [app inner_kinds]; intros f [H1 H2];
    [exact H1 | apply IH; exact H2].
Qed.

Lemma body_first_start : forall bt, body_first bt [body_fview bt].
Proof. intros bt. split; [reflexivity|]. split; [reflexivity | exact I]. Qed.

(** Rewriting the innermost frame keeps it, as long as the frame's kind survives.
    Every non-control step and [unreachable] and [br] are of this shape. *)
Lemma body_first_last : forall bt pre f g,
  (fv_ctrl g).(code_Ctrl_kind) = (fv_ctrl f).(code_Ctrl_kind) ->
  (fv_ctrl g).(code_Ctrl_block_type) = (fv_ctrl f).(code_Ctrl_block_type) ->
  body_first bt (pre ++ [f]) -> body_first bt (pre ++ [g]).
Proof.
  intros bt pre f g Hk Hb. destruct pre as [|h pre]; cbn [app body_first];
    intros [H1 [H2 H3]].
  - split; [rewrite Hk; exact H1|].
    split; [rewrite Hb; exact H2 | exact H3].
  - split; [exact H1|].
    split; [exact H2 | apply (inner_kinds_last pre f g Hk); exact H3].
Qed.

(** [block] and [loop] are the only pushes, and both push a frame of a kind this
    permits. *)
Lemma body_first_push : forall bt fs g,
  kind_ok (fv_ctrl g) -> body_first bt fs -> body_first bt (fs ++ [g]).
Proof.
  intros bt fs g Hg. destruct fs as [|h fs]; cbn [app body_first]; intros H;
    [contradiction|].
  destruct H as [H1 [H2 H3]]. split; [exact H1|].
  split; [exact H2 | apply inner_kinds_push; assumption].
Qed.

Lemma body_first_prefix : forall bt fs g,
  fs <> [] -> body_first bt (fs ++ [g]) -> body_first bt fs.
Proof.
  intros bt fs g Hne H. destruct fs as [|h fs]; [contradiction|].
  cbn [app body_first] in H |- *. destruct H as [H1 [H2 H3]].
  split; [exact H1|].
  split; [exact H2 | apply (inner_kinds_prefix fs g); exact H3].
Qed.

(** Closing a frame keeps it: either the head is some earlier frame, or the frame
    below the closed one *is* the head and its kind is carried over. *)
Lemma body_first_end : forall bt pre f f' g,
  (fv_ctrl f').(code_Ctrl_kind) = (fv_ctrl f).(code_Ctrl_kind) ->
  (fv_ctrl f').(code_Ctrl_block_type) = (fv_ctrl f).(code_Ctrl_block_type) ->
  body_first bt (pre ++ [f] ++ [g]) -> body_first bt (pre ++ [f']).
Proof.
  intros bt pre f f' g Hk Hb H.
  assert (Hre : pre ++ [f] ++ [g] = (pre ++ [f]) ++ [g])
    by (rewrite app_assoc; reflexivity).
  rewrite Hre in H.
  apply (body_first_last bt pre f f' Hk Hb).
  apply (body_first_prefix bt (pre ++ [f]) g); [|exact H].
  intros Hnil. destruct pre; discriminate.
Qed.

Lemma body_first_snoc : forall bt fs,
  body_first bt fs -> exists pre f, fs = pre ++ [f].
Proof.
  intros bt fs H. destruct fs as [|h t]; [contradiction|].
  assert (Hne : h :: t <> []) by discriminate.
  destruct (List.exists_last Hne) as [pre [f Hp]].
  exists pre, f. exact Hp.
Qed.

(** The payoff, and the whole reason the predicate exists: the innermost frame is
    either the body's, alone, or a block or a loop with something below it. There
    is no fourth case, which is what [end]'s dispatch needs. *)
Lemma body_first_innermost : forall bt fs pre f,
  body_first bt fs -> fs = pre ++ [f] ->
  (pre = [] /\ (fv_ctrl f).(code_Ctrl_kind) = Code_LabelKind_Body
   /\ (fv_ctrl f).(code_Ctrl_block_type) = bt)
  \/ (exists pre2 f2, fs = pre2 ++ [f2] ++ [f] /\ kind_ok (fv_ctrl f)).
Proof.
  intros bt fs pre f Hbf Hfs. destruct pre as [|h pre].
  - left. split; [reflexivity|].
    rewrite Hfs in Hbf. cbn [app body_first] in Hbf.
    destruct Hbf as [Hk [Hb _]]. split; [exact Hk | exact Hb].
  - right.
    assert (Hkind : kind_ok (fv_ctrl f)).
    { rewrite Hfs in Hbf. cbn [app body_first] in Hbf.
      destruct Hbf as [_ [_ Hik]]. apply (inner_kinds_last_kind pre f). exact Hik. }
    assert (Hne : h :: pre <> []) by discriminate.
    destruct (List.exists_last Hne) as [pre2 [f2 Hpre]].
    exists pre2, f2. split; [|exact Hkind].
    rewrite Hfs. rewrite Hpre. rewrite <- app_assoc. reflexivity.
Qed.

(* ================================================================== *)
(** ** One operator per step                                           *)
(* ================================================================== *)

(** Each simulation step, restated as "the state still satisfies the invariant,
    the frame list is still headed by the body's frame, and the consumed operator
    stream grew by exactly one operator".

    This is the shape the dispatch consumes. The operator named on the right is
    the one [repr_op] is asked to produce from the bytes the reader consumed, so
    the two halves of the correspondence meet here.

    They are also the standing check that the bridge lemmas still match the step
    lemmas' frame shapes. Nothing but a mismatch can make one of these fail, and a
    mismatch is silent otherwise: [frames_flat] ignores [fv_seg], so a step that
    changed the segment differently than expected would go unnoticed. *)

Corollary step_nop_op : forall C0 bt0 st fs pre f,
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  exists fs', Inv C0 st fs' /\ body_first bt0 fs'
              /\ frames_flat fs' = frames_flat fs ++ [FO_plain BI_nop].
Proof.
  intros C0 bt0 st fs pre f Hinv Hbf Hfs.
  eexists. split; [apply (step_nop C0 st fs pre f Hinv Hfs)|].
  subst fs. split.
  - apply (body_first_last bt0 pre f _); [reflexivity | reflexivity | exact Hbf].
  - apply (frames_flat_plain pre f (fv_ctrl f) (fv_seg f) BI_nop);
      [reflexivity | apply flat_of_one_nop].
Qed.

Corollary step_unreachable_op : forall C0 bt0 st fs pre f st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  code_read_unreachable st = Ok (Core_result_Result_Ok tt, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs' = frames_flat fs ++ [FO_plain BI_unreachable].
Proof.
  intros C0 bt0 st fs pre f st' Hinv Hbf Hfs H.
  eexists. split; [apply (step_unreachable C0 st fs pre f st' Hinv Hfs H)|].
  subst fs. split.
  - apply (body_first_last bt0 pre f _); [reflexivity | reflexivity | exact Hbf].
  - apply (frames_flat_plain pre f
             {| code_Ctrl_kind := (fv_ctrl f).(code_Ctrl_kind);
                code_Ctrl_block_type := (fv_ctrl f).(code_Ctrl_block_type);
                code_Ctrl_value_stack_base :=
                  (fv_ctrl f).(code_Ctrl_value_stack_base);
                code_Ctrl_polymorphic_base := true |}
             [] BI_unreachable);
      [reflexivity | apply flat_of_one_unreachable].
Qed.

Corollary step_drop_op : forall C0 bt0 st fs pre f t st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  code_read_drop st = Ok (Core_result_Result_Ok t, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs' = frames_flat fs ++ [FO_plain BI_drop].
Proof.
  intros C0 bt0 st fs pre f t st' Hinv Hbf Hfs H.
  destruct (step_drop C0 st fs pre f t st' Hinv Hfs H) as [seg' Hinv'].
  eexists. split; [exact Hinv'|]. subst fs. split.
  - apply (body_first_last bt0 pre f _); [reflexivity | reflexivity | exact Hbf].
  - apply (frames_flat_plain pre f (fv_ctrl f) seg' BI_drop);
      [reflexivity | apply flat_of_one_drop].
Qed.

Corollary step_select_op : forall C0 bt0 st fs pre f t st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  code_read_select st = Ok (Core_result_Result_Ok t, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs' = frames_flat fs ++ [FO_plain (BI_select None)].
Proof.
  intros C0 bt0 st fs pre f t st' Hinv Hbf Hfs H.
  destruct (step_select C0 st fs pre f t st' Hinv Hfs H) as [seg' Hinv'].
  eexists. split; [exact Hinv'|]. subst fs. split.
  - apply (body_first_last bt0 pre f _); [reflexivity | reflexivity | exact Hbf].
  - apply (frames_flat_plain pre f (fv_ctrl f) seg' (BI_select None));
      [reflexivity | apply flat_of_one_select].
Qed.

Corollary step_i32_const_op : forall C0 bt0 st fs pre f data v st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  code_read_i32_const st data = Ok (Core_result_Result_Ok v, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs'
                 = frames_flat fs
                   ++ [FO_plain (BI_const_num
                                   (VAL_int32 (Wasm_int.Int32.repr (to_Z v))))].
Proof.
  intros C0 bt0 st fs pre f data v st' Hinv Hbf Hfs H.
  eexists.
  split; [apply (step_i32_const C0 st fs pre f data v st' Hinv Hfs H)|].
  subst fs. split.
  - apply (body_first_last bt0 pre f _); [reflexivity | reflexivity | exact Hbf].
  - apply (frames_flat_plain pre f (fv_ctrl f)
             (fv_seg f ++ [Code_StackType_Val Types_ValueType_I32]) _);
      [reflexivity | apply flat_of_one_const_num].
Qed.

Corollary step_f32_const_op : forall C0 bt0 st fs pre f data v st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  code_read_f32_const st data = Ok (Core_result_Result_Ok v, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs'
                 = frames_flat fs
                   ++ [FO_plain (BI_const_num (fconst_val T_f32 (to_Z v)))].
Proof.
  intros C0 bt0 st fs pre f data v st' Hinv Hbf Hfs H.
  eexists.
  split; [apply (step_f32_const C0 st fs pre f data v st' Hinv Hfs H)|].
  subst fs. split.
  - apply (body_first_last bt0 pre f _); [reflexivity | reflexivity | exact Hbf].
  - apply (frames_flat_plain pre f (fv_ctrl f)
             (fv_seg f ++ [Code_StackType_Val Types_ValueType_F32]) _);
      [reflexivity | apply flat_of_one_const_num].
Qed.

Corollary step_f64_const_op : forall C0 bt0 st fs pre f data v st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  code_read_f64_const st data = Ok (Core_result_Result_Ok v, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs'
                 = frames_flat fs
                   ++ [FO_plain (BI_const_num (fconst_val T_f64 (to_Z v)))].
Proof.
  intros C0 bt0 st fs pre f data v st' Hinv Hbf Hfs H.
  eexists.
  split; [apply (step_f64_const C0 st fs pre f data v st' Hinv Hfs H)|].
  subst fs. split.
  - apply (body_first_last bt0 pre f _); [reflexivity | reflexivity | exact Hbf].
  - apply (frames_flat_plain pre f (fv_ctrl f)
             (fv_seg f ++ [Code_StackType_Val Types_ValueType_F64]) _);
      [reflexivity | apply flat_of_one_const_num].
Qed.

Corollary step_i64_const_op : forall C0 bt0 st fs pre f data v st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  code_read_i64_const st data = Ok (Core_result_Result_Ok v, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs'
                 = frames_flat fs
                   ++ [FO_plain (BI_const_num
                                   (VAL_int64 (Wasm_int.Int64.repr (to_Z v))))].
Proof.
  intros C0 bt0 st fs pre f data v st' Hinv Hbf Hfs H.
  eexists.
  split; [apply (step_i64_const C0 st fs pre f data v st' Hinv Hfs H)|].
  subst fs. split.
  - apply (body_first_last bt0 pre f _); [reflexivity | reflexivity | exact Hbf].
  - apply (frames_flat_plain pre f (fv_ctrl f)
             (fv_seg f ++ [Code_StackType_Val Types_ValueType_I64]) _);
      [reflexivity | apply flat_of_one_const_num].
Qed.

(** The shared tail of every step that rewrites the innermost frame with one
    more instruction: the frame list still starts with the body's frame, and the
    operator stream grew by that instruction. The side condition is the one
    [frames_flat_plain] needs, and it holds by computation for every instruction
    the readers append, none of which carries a body. *)
Corollary step_plain_op : forall C0 bt0 st' fs pre f be seg',
  Inv C0 st' (pre ++ [{| fv_ctrl := fv_ctrl f;
                         fv_seg := seg';
                         fv_done := fv_done f ++ [be];
                         fv_then := fv_then f |}]) ->
  body_first bt0 fs -> fs = pre ++ [f] ->
  flat_of_one be = [FO_plain be] ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs' = frames_flat fs ++ [FO_plain be].
Proof.
  intros C0 bt0 st' fs pre f be seg' Hinv' Hbf Hfs Hflat.
  eexists. split; [exact Hinv'|]. subst fs. split.
  - apply (body_first_last bt0 pre f _); [reflexivity | reflexivity | exact Hbf].
  - apply (frames_flat_plain pre f (fv_ctrl f) seg' be);
      [reflexivity | exact Hflat].
Qed.

(** The binary shape, generic in the instruction, as [step_conversion_op] is for
    the one-operand shape. *)
Corollary step_binary_op : forall C0 bt0 st fs pre f ty res be st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  effect_in C0 be [translate_vt_v ty; translate_vt_v ty] [translate_vt_v res] ->
  flat_of_one be = [FO_plain be] ->
  code_read_binary st ty res = Ok (Core_result_Result_Ok tt, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs' = frames_flat fs ++ [FO_plain be].
Proof.
  intros C0 bt0 st fs pre f ty res be st' Hinv Hbf Hfs Heff Hflat H.
  destruct (step_binary C0 st fs pre f ty res be st' Hinv Hfs Heff H)
    as [seg' Hinv'].
  apply (step_plain_op C0 bt0 st' fs pre f be seg' Hinv' Hbf Hfs Hflat).
Qed.

(** The conversion shape, generic in the instruction: the operator stream grows
    by whatever [FO_plain] the opcode table named. The side condition is the one
    [frames_flat_plain] needs, and it holds by computation for every instruction
    the table can produce, none of which carries a body. *)
Corollary step_conversion_op :
  forall C0 bt0 st fs pre f from to be st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  effect_in C0 be [translate_vt_v from] [translate_vt_v to] ->
  flat_of_one be = [FO_plain be] ->
  code_read_conversion st from to
    = Ok (Core_result_Result_Ok tt, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs' = frames_flat fs ++ [FO_plain be].
Proof.
  intros C0 bt0 st fs pre f from to be st' Hinv Hbf Hfs Heff Hflat H.
  destruct (step_conversion C0 st fs pre f from to be st'
              Hinv Hfs Heff H) as [seg' Hinv'].
  apply (step_plain_op C0 bt0 st' fs pre f be seg' Hinv' Hbf Hfs Hflat).
Qed.

(** The three local operators. Each is the shared prologue followed by one of
    the shapes above, so each is its step lemma plus [step_plain_op]. *)
Corollary step_local_get_op : forall C0 bt0 ctx st fs pre f data idx st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  locals_agree ctx C0 ->
  code_read_local_get st data ctx = Ok (Core_result_Result_Ok idx, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs'
                 = frames_flat fs
                   ++ [FO_plain (BI_local_get (Z.to_N (to_Z idx)))].
Proof.
  intros C0 bt0 ctx st fs pre f data idx st' Hinv Hbf Hfs Hag H.
  destruct (step_local_get C0 ctx st fs pre f data idx st' Hinv Hfs Hag H)
    as [t Hinv'].
  apply (step_plain_op C0 bt0 st' fs pre f _ _ Hinv' Hbf Hfs (eq_refl _)).
Qed.

Corollary step_local_set_op : forall C0 bt0 ctx st fs pre f data idx st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  locals_agree ctx C0 ->
  code_read_local_set st data ctx = Ok (Core_result_Result_Ok idx, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs'
                 = frames_flat fs
                   ++ [FO_plain (BI_local_set (Z.to_N (to_Z idx)))].
Proof.
  intros C0 bt0 ctx st fs pre f data idx st' Hinv Hbf Hfs Hag H.
  destruct (step_local_set C0 ctx st fs pre f data idx st' Hinv Hfs Hag H)
    as [seg' Hinv'].
  apply (step_plain_op C0 bt0 st' fs pre f _ _ Hinv' Hbf Hfs (eq_refl _)).
Qed.

Corollary step_local_tee_op : forall C0 bt0 ctx st fs pre f data idx st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  locals_agree ctx C0 ->
  code_read_local_tee st data ctx = Ok (Core_result_Result_Ok idx, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs'
                 = frames_flat fs
                   ++ [FO_plain (BI_local_tee (Z.to_N (to_Z idx)))].
Proof.
  intros C0 bt0 ctx st fs pre f data idx st' Hinv Hbf Hfs Hag H.
  destruct (step_local_tee C0 ctx st fs pre f data idx st' Hinv Hfs Hag H)
    as [seg' [t Hinv']].
  apply (step_plain_op C0 bt0 st' fs pre f _ _ Hinv' Hbf Hfs (eq_refl _)).
Qed.

(** The two global operators, the same way. *)
Corollary step_global_get_op : forall C0 bt0 module st fs pre f data idx st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  globals_agree module C0 ->
  code_read_global_get st data module = Ok (Core_result_Result_Ok idx, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs'
                 = frames_flat fs
                   ++ [FO_plain (BI_global_get (Z.to_N (to_Z idx)))].
Proof.
  intros C0 bt0 module st fs pre f data idx st' Hinv Hbf Hfs Hag H.
  destruct (step_global_get C0 module st fs pre f data idx st' Hinv Hfs Hag H)
    as [t Hinv'].
  apply (step_plain_op C0 bt0 st' fs pre f _ _ Hinv' Hbf Hfs (eq_refl _)).
Qed.

Corollary step_global_set_op : forall C0 bt0 module st fs pre f data idx st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  globals_agree module C0 ->
  code_read_global_set st data module = Ok (Core_result_Result_Ok idx, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs'
                 = frames_flat fs
                   ++ [FO_plain (BI_global_set (Z.to_N (to_Z idx)))].
Proof.
  intros C0 bt0 module st fs pre f data idx st' Hinv Hbf Hfs Hag H.
  destruct (step_global_set C0 module st fs pre f data idx st' Hinv Hfs Hag H)
    as [seg' Hinv'].
  apply (step_plain_op C0 bt0 st' fs pre f _ _ Hinv' Hbf Hfs (eq_refl _)).
Qed.

Corollary step_load_op :
  forall C0 bt0 st fs pre f data module ty natural nt tp_sx m st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  mems_agree module C0 ->
  translate_vt_v ty = T_num nt ->
  (forall a, 0 <= a <= to_Z natural ->
     load_store_t_bounds (Z.to_N a) (option_projl tp_sx) nt = true) ->
  code_read_load st data module ty natural
    = Ok (Core_result_Result_Ok m, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs'
                 = frames_flat fs
                   ++ [FO_plain (BI_load nt tp_sx
                                   (Z.to_N (to_Z m.(code_MemArg_align)))
                                   (Z.to_N (to_Z m.(code_MemArg_offset))))].
Proof.
  intros C0 bt0 st fs pre f data module ty natural nt tp_sx m st'
         Hinv Hbf Hfs Hmems Hty Hbounds H.
  destruct (step_load C0 st fs pre f data module ty natural nt tp_sx m st'
              Hinv Hfs Hmems Hty Hbounds H) as [seg' Hinv'].
  eexists. split; [exact Hinv'|]. subst fs. split.
  - apply (body_first_last bt0 pre f _); [reflexivity | reflexivity | exact Hbf].
  - apply (frames_flat_plain pre f (fv_ctrl f)
             (seg' ++ [Code_StackType_Val ty]) _);
      [reflexivity | apply flat_of_one_load].
Qed.

Corollary step_store_op :
  forall C0 bt0 st fs pre f data module ty natural nt tp m st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  mems_agree module C0 ->
  translate_vt_v ty = T_num nt ->
  (forall a, 0 <= a <= to_Z natural ->
     load_store_t_bounds (Z.to_N a) tp nt = true) ->
  code_read_store st data module ty natural
    = Ok (Core_result_Result_Ok m, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs'
                 = frames_flat fs
                   ++ [FO_plain (BI_store nt tp
                                   (Z.to_N (to_Z m.(code_MemArg_align)))
                                   (Z.to_N (to_Z m.(code_MemArg_offset))))].
Proof.
  intros C0 bt0 st fs pre f data module ty natural nt tp m st'
         Hinv Hbf Hfs Hmems Hty Hbounds H.
  destruct (step_store C0 st fs pre f data module ty natural nt tp m st'
              Hinv Hfs Hmems Hty Hbounds H) as [seg' Hinv'].
  eexists. split; [exact Hinv'|]. subst fs. split.
  - apply (body_first_last bt0 pre f _); [reflexivity | reflexivity | exact Hbf].
  - apply (frames_flat_plain pre f (fv_ctrl f) seg' _);
      [reflexivity | apply flat_of_one_store].
Qed.

Corollary step_br_op : forall C0 bt0 st fs pre f data depth bt st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  code_read_br st data = Ok (Core_result_Result_Ok (depth, bt), st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs'
                 = frames_flat fs
                   ++ [FO_plain (BI_br (Z.to_N (to_Z depth)))].
Proof.
  intros C0 bt0 st fs pre f data depth bt st' Hinv Hbf Hfs H.
  eexists.
  split; [apply (step_br C0 st fs pre f data depth bt st' Hinv Hfs H)|].
  subst fs. split.
  - apply (body_first_last bt0 pre f _); [reflexivity | reflexivity | exact Hbf].
  - apply (frames_flat_plain pre f
             {| code_Ctrl_kind := (fv_ctrl f).(code_Ctrl_kind);
                code_Ctrl_block_type := (fv_ctrl f).(code_Ctrl_block_type);
                code_Ctrl_value_stack_base :=
                  (fv_ctrl f).(code_Ctrl_value_stack_base);
                code_Ctrl_polymorphic_base := true |}
             [] _);
      [reflexivity | apply flat_of_one_br].
Qed.

(** [br_if] rewrites the innermost frame like a plain operator, so this is
    [step_plain_op] on top of [step_br_if]. *)
Corollary step_br_if_op : forall C0 bt0 st fs pre f data depth bt st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  code_read_br_if st data = Ok (Core_result_Result_Ok (depth, bt), st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs'
                 = frames_flat fs
                   ++ [FO_plain (BI_br_if (Z.to_N (to_Z depth)))].
Proof.
  intros C0 bt0 st fs pre f data depth bt st' Hinv Hbf Hfs H.
  destruct (step_br_if C0 st fs pre f data depth bt st' Hinv Hfs H)
    as [seg' Hinv'].
  apply (step_plain_op C0 bt0 st' fs pre f _ _ Hinv' Hbf Hfs
           (flat_of_one_br_if _)).
Qed.

(** [br_table] rewrites the frame's ctrl exactly as [br] does, so this is
    [step_br_op]'s shape with the label list threaded through. *)
Corollary step_br_table_op : forall V (inst : code_OpVisitor_t V) v v' dflt
                                    C0 bt0 st fs pre f data ls x common st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  List.Forall (fun d => depth_target st d common) (ls ++ [x]) ->
  code_read_br_table inst st data v
    = Ok (Core_result_Result_Ok (dflt, common), st', v') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs'
                 = frames_flat fs
                   ++ [FO_plain (BI_br_table (List.map Z.to_N ls) (Z.to_N x))].
Proof.
  intros V inst v v' dflt C0 bt0 st fs pre f data ls x common st'
         Hinv Hbf Hfs Hdt H.
  eexists.
  split;
    [apply (step_br_table V inst v v' dflt C0 st fs pre f data ls x common st'
              Hinv Hfs Hdt H)|].
  subst fs. split.
  - apply (body_first_last bt0 pre f _); [reflexivity | reflexivity | exact Hbf].
  - apply (frames_flat_plain pre f
             {| code_Ctrl_kind := (fv_ctrl f).(code_Ctrl_kind);
                code_Ctrl_block_type := (fv_ctrl f).(code_Ctrl_block_type);
                code_Ctrl_value_stack_base :=
                  (fv_ctrl f).(code_Ctrl_value_stack_base);
                code_Ctrl_polymorphic_base := true |}
             [] _);
      [reflexivity | apply flat_of_one_br_table].
Qed.

(** [return] rewrites the frame's ctrl like [br], so this is [step_br_op]'s
    shape with the flag flipped and an empty segment. *)
Corollary step_return_op : forall C0 bt0 ctx st fs pre f st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  return_agree ctx C0 ->
  code_read_return st ctx = Ok (Core_result_Result_Ok tt, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs' = frames_flat fs ++ [FO_plain BI_return].
Proof.
  intros C0 bt0 ctx st fs pre f st' Hinv Hbf Hfs Hag H.
  eexists.
  split; [apply (step_return C0 ctx st fs pre f st' Hinv Hfs Hag H)|].
  subst fs. split.
  - apply (body_first_last bt0 pre f _); [reflexivity | reflexivity | exact Hbf].
  - apply (frames_flat_plain pre f
             {| code_Ctrl_kind := (fv_ctrl f).(code_Ctrl_kind);
                code_Ctrl_block_type := (fv_ctrl f).(code_Ctrl_block_type);
                code_Ctrl_value_stack_base :=
                  (fv_ctrl f).(code_Ctrl_value_stack_base);
                code_Ctrl_polymorphic_base := true |}
             [] _);
      [reflexivity | apply flat_of_one_return].
Qed.

(** The two call operators, each its step lemma plus [step_plain_op]. *)
Corollary step_call_op : forall C0 bt0 module st fs pre f data idx st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  funcs_agree module C0 ->
  code_read_call st data module = Ok (Core_result_Result_Ok idx, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs'
                 = frames_flat fs ++ [FO_plain (BI_call (Z.to_N (to_Z idx)))].
Proof.
  intros C0 bt0 module st fs pre f data idx st' Hinv Hbf Hfs Hag H.
  destruct (step_call C0 module st fs pre f data idx st' Hinv Hfs Hag H)
    as [seg' Hinv'].
  apply (step_plain_op C0 bt0 st' fs pre f _ seg' Hinv' Hbf Hfs
           (flat_of_one_call _)).
Qed.

Corollary step_call_indirect_op : forall C0 bt0 module st fs pre f data idx st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  types_agree module C0 -> tables_agree module C0 ->
  code_read_call_indirect st data module
    = Ok (Core_result_Result_Ok idx, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs'
                 = frames_flat fs
                   ++ [FO_plain (BI_call_indirect 0%N (Z.to_N (to_Z idx)))].
Proof.
  intros C0 bt0 module st fs pre f data idx st' Hinv Hbf Hfs Hty Htab H.
  destruct (step_call_indirect C0 module st fs pre f data idx st' Hinv Hfs Hty Htab
              H) as [seg' Hinv'].
  apply (step_plain_op C0 bt0 st' fs pre f _ seg' Hinv' Hbf Hfs
           (flat_of_one_call_indirect _ _)).
Qed.

(** [memory.size] and [memory.grow], each its step lemma plus
    [step_plain_op]. *)
Corollary step_memory_size_op : forall C0 bt0 module st fs pre f data st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  mems_agree module C0 ->
  code_read_memory_size st data module = Ok (Core_result_Result_Ok tt, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs' = frames_flat fs ++ [FO_plain BI_memory_size].
Proof.
  intros C0 bt0 module st fs pre f data st' Hinv Hbf Hfs Hag H.
  pose proof (step_memory_size C0 module st fs pre f data st' Hinv Hfs Hag H)
    as Hinv'.
  apply (step_plain_op C0 bt0 st' fs pre f _ _ Hinv' Hbf Hfs (eq_refl _)).
Qed.

Corollary step_memory_grow_op : forall C0 bt0 module st fs pre f data st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  mems_agree module C0 ->
  code_read_memory_grow st data module = Ok (Core_result_Result_Ok tt, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs' = frames_flat fs ++ [FO_plain BI_memory_grow].
Proof.
  intros C0 bt0 module st fs pre f data st' Hinv Hbf Hfs Hag H.
  destruct (step_memory_grow C0 module st fs pre f data st' Hinv Hfs Hag H)
    as [seg' Hinv'].
  apply (step_plain_op C0 bt0 st' fs pre f _ _ Hinv' Hbf Hfs (eq_refl _)).
Qed.

Corollary step_block_op : forall C0 bt0 st fs data bt st',
  Inv C0 st fs -> body_first bt0 fs ->
  code_read_block st data = Ok (Core_result_Result_Ok bt, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs'
                 = frames_flat fs ++ [FO_block (translate_bt bt)].
Proof.
  intros C0 bt0 st fs data bt st' Hinv Hbf H.
  destruct (step_block C0 st fs data bt st' Hinv H) as [base Hinv'].
  eexists. split; [exact Hinv'|]. split; [apply body_first_push; [left; reflexivity | exact Hbf]|].
  rewrite frames_flat_push.
  rewrite (frame_open_block
             {| fv_ctrl :=
                  {| code_Ctrl_kind := Code_LabelKind_Block;
                     code_Ctrl_block_type := bt;
                     code_Ctrl_value_stack_base := base;
                     code_Ctrl_polymorphic_base := false |};
                fv_seg := []; fv_done := []; fv_then := [] |} bt
             (eq_refl _) (eq_refl _)).
  reflexivity.
Qed.

Corollary step_loop_op : forall C0 bt0 st fs data bt st',
  Inv C0 st fs -> body_first bt0 fs ->
  code_read_loop st data = Ok (Core_result_Result_Ok bt, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs'
                 = frames_flat fs ++ [FO_loop (translate_bt bt)].
Proof.
  intros C0 bt0 st fs data bt st' Hinv Hbf H.
  destruct (step_loop C0 st fs data bt st' Hinv H) as [base Hinv'].
  eexists. split; [exact Hinv'|].
  split; [apply body_first_push; [right; left; reflexivity | exact Hbf]|].
  rewrite frames_flat_push.
  rewrite (frame_open_loop
             {| fv_ctrl :=
                  {| code_Ctrl_kind := Code_LabelKind_Loop;
                     code_Ctrl_block_type := bt;
                     code_Ctrl_value_stack_base := base;
                     code_Ctrl_polymorphic_base := false |};
                fv_seg := []; fv_done := []; fv_then := [] |} bt
             (eq_refl _) (eq_refl _)).
  reflexivity.
Qed.

Corollary step_end_block_op : forall C0 bt0 st fs pre f g r st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ++ [g] ->
  (fv_ctrl g).(code_Ctrl_kind) = Code_LabelKind_Block ->
  code_read_end st = Ok (Core_result_Result_Ok r, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs' = frames_flat fs ++ [FO_end].
Proof.
  intros C0 bt0 st fs pre f g r st' Hinv Hbf Hfs Hkind H.
  eexists.
  split; [apply (step_end_block C0 st fs pre f g r st' Hinv Hfs Hkind H)|].
  subst fs. split.
  - apply (body_first_end bt0 pre f _ g);
      [reflexivity | reflexivity | exact Hbf].
  - apply (frames_flat_end_block pre f g _
             (fv_ctrl g).(code_Ctrl_block_type) Hkind (eq_refl _)).
Qed.

Corollary step_end_loop_op : forall C0 bt0 st fs pre f g r st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ++ [g] ->
  (fv_ctrl g).(code_Ctrl_kind) = Code_LabelKind_Loop ->
  code_read_end st = Ok (Core_result_Result_Ok r, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs' = frames_flat fs ++ [FO_end].
Proof.
  intros C0 bt0 st fs pre f g r st' Hinv Hbf Hfs Hkind H.
  eexists.
  split; [apply (step_end_loop C0 st fs pre f g r st' Hinv Hfs Hkind H)|].
  subst fs. split.
  - apply (body_first_end bt0 pre f _ g);
      [reflexivity | reflexivity | exact Hbf].
  - apply (frames_flat_end_loop pre f g _
             (fv_ctrl g).(code_Ctrl_block_type) Hkind (eq_refl _)).
Qed.

(** [if] is the only push that also touches the frame below it, since the
    condition is popped before the [Then] frame goes on. [frames_flat_seg] is
    what says that pop is invisible to the stream. *)
Corollary step_if_op : forall C0 bt0 st fs pre f data bt st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ->
  code_read_if st data = Ok (Core_result_Result_Ok bt, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs' = frames_flat fs ++ [FO_if (translate_bt bt)].
Proof.
  intros C0 bt0 st fs pre f data bt st' Hinv Hbf Hfs H.
  destruct (step_if C0 st fs pre f data bt st' Hinv Hfs H) as [seg' [base Hinv']].
  eexists. split; [exact Hinv'|]. subst fs.
  assert (Hseg : body_first bt0
                   (pre ++ [{| fv_ctrl := fv_ctrl f; fv_seg := seg';
                               fv_done := fv_done f; fv_then := fv_then f |}])).
  { apply (body_first_last bt0 pre f); [reflexivity | reflexivity | exact Hbf]. }
  split.
  - rewrite List.app_assoc.
    apply body_first_push; [right; right; left; reflexivity | exact Hseg].
  - rewrite List.app_assoc. rewrite frames_flat_push.
    rewrite (frame_open_then
               {| fv_ctrl :=
                    {| code_Ctrl_kind := Code_LabelKind_Then;
                       code_Ctrl_block_type := bt;
                       code_Ctrl_value_stack_base := base;
                       code_Ctrl_polymorphic_base := false |};
                  fv_seg := []; fv_done := []; fv_then := [] |} bt
               (eq_refl _) (eq_refl _)).
    rewrite frames_flat_seg. reflexivity.
Qed.

Corollary step_switch_else_op : forall C0 bt0 st fs pre g bt st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [g] ->
  (fv_ctrl g).(code_Ctrl_kind) = Code_LabelKind_Then ->
  code_read_else st = Ok (Core_result_Result_Ok bt, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs' = frames_flat fs ++ [FO_else].
Proof.
  intros C0 bt0 st fs pre g bt st' Hinv Hbf Hfs Hkind H.
  eexists.
  split; [apply (step_switch_else C0 st fs pre g st' bt Hinv Hfs Hkind H)|].
  (* a [Then] frame is never the body's, so there is a frame below it *)
  destruct pre as [|h pre'].
  { exfalso. rewrite Hfs in Hbf. cbn [app body_first] in Hbf.
    destruct Hbf as [Hbody _]. rewrite Hkind in Hbody. discriminate Hbody. }
  subst fs. split.
  - apply (body_first_switch bt0 h pre' g);
      [right; right; right; reflexivity | exact Hbf].
  - apply (frames_flat_switch_else (h :: pre') g
             {| code_Ctrl_kind := Code_LabelKind_Else;
                code_Ctrl_block_type := (fv_ctrl g).(code_Ctrl_block_type);
                code_Ctrl_value_stack_base :=
                  (fv_ctrl g).(code_Ctrl_value_stack_base);
                code_Ctrl_polymorphic_base := false |}
             (fv_ctrl g).(code_Ctrl_block_type) Hkind (eq_refl _)
             (eq_refl _) (eq_refl _)).
Qed.

(** The two [end]s that close an [if]. [step_end_then_op] is the one step in the
    whole dispatch that appends two operators: see [frames_flat_end_then]. *)
Corollary step_end_then_op : forall C0 bt0 st fs pre f g r st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ++ [g] ->
  (fv_ctrl g).(code_Ctrl_kind) = Code_LabelKind_Then ->
  code_read_end st = Ok (Core_result_Result_Ok r, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs' = frames_flat fs ++ [FO_else; FO_end].
Proof.
  intros C0 bt0 st fs pre f g r st' Hinv Hbf Hfs Hkind H.
  eexists.
  split; [apply (step_end_then C0 st fs pre f g r st' Hinv Hfs Hkind H)|].
  subst fs. split.
  - apply (body_first_end bt0 pre f _ g);
      [reflexivity | reflexivity | exact Hbf].
  - apply (frames_flat_end_then pre f g _
             (fv_ctrl g).(code_Ctrl_block_type) Hkind (eq_refl _)).
Qed.

Corollary step_end_else_op : forall C0 bt0 st fs pre f g r st',
  Inv C0 st fs -> body_first bt0 fs -> fs = pre ++ [f] ++ [g] ->
  (fv_ctrl g).(code_Ctrl_kind) = Code_LabelKind_Else ->
  code_read_end st = Ok (Core_result_Result_Ok r, st') ->
  exists fs', Inv C0 st' fs' /\ body_first bt0 fs'
              /\ frames_flat fs' = frames_flat fs ++ [FO_end].
Proof.
  intros C0 bt0 st fs pre f g r st' Hinv Hbf Hfs Hkind H.
  eexists.
  split; [apply (step_end_else C0 st fs pre f g r st' Hinv Hfs Hkind H)|].
  subst fs. split.
  - apply (body_first_end bt0 pre f _ g);
      [reflexivity | reflexivity | exact Hbf].
  - apply (frames_flat_end_else pre f g _
             (fv_ctrl g).(code_Ctrl_block_type) Hkind (eq_refl _)).
Qed.
