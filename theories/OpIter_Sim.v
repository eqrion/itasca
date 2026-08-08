(** * Interpreting the streaming state as a WasmCert context

    The simulation invariant will relate the streaming state to what WasmCert's
    checker would compute. Two pieces of that interpretation are easy to get
    subtly wrong, so they are pinned here before anything is built on them:

    - which WasmCert label a control frame becomes, and
    - which way round the indexing goes.

    The control stack grows with the innermost frame *last*, and a branch at
    depth [n] resolves to [ctrls[len - 1 - n]]. WasmCert's [tc_labels] has the
    innermost label *first*, so the two are related by a reversal, and
    [ctx_at_label_lookup] below is where that is pinned down once. *)

Require Import Primitives.
Import Primitives.
Require Import Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Import Veriwasm.Aeneas_Specs.
Require Import Veriwasm.Translate.
(* For [fconst_val], the bits-to-float function spec 4.2.3 calls [float_N]:
   the float [const] step lemmas name the value they push, and this is the
   one place it is written down. *)
Require Import Veriwasm.Spec_Binary.
Require Import Veriwasm.OpIter_State.
Require Import Veriwasm.OpIter_Protocol.

From Wasm Require Import datatypes type_checker operations typing.
From mathcomp Require Import ssreflect ssrbool eqtype seq.

(* mathcomp's seq_scope makes bare [++] mean [cat], while the state and decode
   files (which do not import it) mean [List.app]. They are different constants,
   and although they are convertible, ssreflect's rewrite matches on the head
   symbol, so an [app]-keyed lemma such as [List.app_assoc] does not fire on a
   [cat]. Reopening list_scope is not enough on its own: mathcomp also does
   [Bind Scope seq_scope with list], which makes [++] mean [cat] in every
   argument position whose type is a list, however the ambient scope is set.
   Rebinding the type is what actually makes [++] mean [List.app] throughout. *)
Local Open Scope list_scope.
Local Bind Scope list_scope with list.

(* ================================================================== *)
(** ** What a control frame contributes                                *)
(* ================================================================== *)

(** Pure counterpart of [opiter_branch_target_types], which is monadic only
    because building a one-element [Vec] can in principle fail.

    A loop's branch target is its parameters, everything else's is its results,
    mirroring SpiderMonkey's [branchTargetType()]. Wasm 1.0 block types have no
    parameters, so a loop target is empty. *)
(** A Wasm 1.0 block type contributes at most one result. Pure counterpart of
    [opiter_block_results], which is monadic only because building a one-element
    [Vec] can in principle fail. *)
Definition block_results_of (bt : opiter_BlockType_t) : list types_ValueType_t :=
  match bt with
  | Opiter_BlockType_Empty => []
  | Opiter_BlockType_Value vt => [vt]
  end.

Lemma block_results_spec : forall bt v,
  opiter_block_results bt = Ok v -> vec_list v = block_results_of bt.
Proof.
  intros bt v H. unfold opiter_block_results, block_results_of in *.
  destruct bt as [|vt].
  - injection H as <-. reflexivity.
  - apply vec_push_spec in H. rewrite H. reflexivity.
Qed.

Definition ctrl_target (c : opiter_Ctrl_t) : list types_ValueType_t :=
  block_results_of (branch_target_bt_of c).

Lemma branch_target_types_spec : forall c v,
  opiter_branch_target_types c = Ok v -> vec_list v = ctrl_target c.
Proof.
  intros c v H. unfold ctrl_target, opiter_branch_target_types in *.
  rewrite branch_target_bt_spec in H. cbn [bind] in H.
  apply (block_results_spec _ v H).
Qed.

Definition ctrl_label (c : opiter_Ctrl_t) : list value_type :=
  translate_typelist (ctrl_target c).

(* ================================================================== *)
(** ** The context at a point in the stream                            *)
(* ================================================================== *)

(** [C0] carries the module-level fields; the labels come entirely from the
    control stack, including the outermost frame. [start_function] pushes a
    [Body] frame carrying the function's results, so the outermost label is the
    result type a [return] branches to. *)
Definition with_labels (C0 : t_context) (lbls : list (list value_type))
  : t_context :=
  {| tc_types := C0.(tc_types);
     tc_funcs := C0.(tc_funcs);
     tc_tables := C0.(tc_tables);
     tc_mems := C0.(tc_mems);
     tc_globals := C0.(tc_globals);
     tc_elems := C0.(tc_elems);
     tc_datas := C0.(tc_datas);
     tc_locals := C0.(tc_locals);
     tc_labels := lbls;
     tc_return := C0.(tc_return);
     tc_refs := C0.(tc_refs) |}.

Definition ctx_at (C0 : t_context) (st : opiter_OpIterState_t) : t_context :=
  with_labels C0
    (List.rev (List.map ctrl_label (vec_list st.(opiter_OpIterState_ctrls)))).

(* ================================================================== *)
(** ** Pinning the indexing                                           *)
(* ================================================================== *)

Lemma nth_error_rev_map : forall {A B} (f : A -> B) (l : list A) n,
  (n < List.length l)%nat ->
  List.nth_error (List.rev (List.map f l)) n
    = option_map f (List.nth_error l (List.length l - 1 - n)).
Proof.
  (* ssreflect is in scope, so avoid comma-separated rewrites and `by`. *)
  intros A B f l n Hn.
  rewrite <- List.map_rev.
  rewrite List.nth_error_map.
  f_equal.
  rewrite (nth_error_rev l n Hn).
  f_equal. lia.
Qed.

(** The bridge that matters: the frame [read_br] reaches for at depth [n],
    namely [ctrls[len - 1 - n]], is the one WasmCert finds at [tc_labels[n]].

    An off-by-one here would make every control-flow lemma fail confusingly, so
    it is stated once and reused rather than rederived. *)
Theorem ctx_at_label_lookup : forall C0 st n c,
  (n < List.length (vec_list st.(opiter_OpIterState_ctrls)))%nat ->
  List.nth_error (vec_list st.(opiter_OpIterState_ctrls))
                 (List.length (vec_list st.(opiter_OpIterState_ctrls)) - 1 - n)
    = Some c ->
  List.nth_error (tc_labels (ctx_at C0 st)) n = Some (ctrl_label c).
Proof.
  intros C0 st n c Hn Hnth. cbn [tc_labels ctx_at with_labels].
  rewrite (nth_error_rev_map ctrl_label _ n Hn). rewrite Hnth. reflexivity.
Qed.

(* ================================================================== *)
(** ** Translating the operand stack                                  *)
(* ================================================================== *)

(** [Bot] is a stack-only notion in the streaming design, kept out of
    [ValueType] so it cannot leak into a function signature. It maps onto
    WasmCert's [T_bot]. *)
Definition translate_st (t : opiter_StackType_t) : value_type :=
  match t with
  | Opiter_StackType_Val vt => translate_vt_v vt
  | Opiter_StackType_Bot => T_bot
  end.

(** VeriWasm's operand stack grows rightward (last = top); WasmCert's grows
    leftward, so every operand list is reversed on the way across. *)
Definition translate_vals (l : list opiter_StackType_t) : list value_type :=
  List.rev (List.map translate_st l).

(* ================================================================== *)
(** ** The simulation invariant                                        *)
(* ================================================================== *)

(** A frame, the operand segment it owns, and the instructions consumed inside
    it so far. The last field is ghost: it exists only in the proof, which is the
    whole point of the streaming design.

    Frames are listed outermost-first, matching the control stack, so the
    function body's frame is the head.

    [fv_then] is the then-branch of an open [Else] frame: [[]] for every other
    kind. It exists because an [Else] frame's closing obligation is WasmCert's
    [BI_if], which needs *both* bodies, and the then-branch's bytes are long
    gone by the time [else] fires -- this is where they are stashed. *)
Record fview := {
  fv_ctrl : opiter_Ctrl_t;
  fv_seg  : list opiter_StackType_t;
  fv_done : list basic_instruction;
  fv_then : list basic_instruction;
}.

Definition fv_ct (f : fview) : checker_type :=
  <<translate_vals (fv_seg f),
    (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>>.

(** Each frame's [value_stack_base] is the total size of everything outside it.
    That is what [push_ctrl] records: the operand stack's length at push time. *)
Fixpoint bases_ok_from (n : nat) (fs : list fview) : Prop :=
  match fs with
  | [] => True
  | f :: rest =>
      Z.to_nat (to_Z (fv_ctrl f).(opiter_Ctrl_value_stack_base)) = n
      /\ bases_ok_from (n + List.length (fv_seg f))%nat rest
  end.

(** What the frame right below an open [Then] or [Else] owes: the condition
    [if] already popped from it, eagerly, before the two bodies were known.
    WasmCert's [BI_if] only pops that same value once the whole construct
    closes at [end], so from [if] all the way to [end] -- through [else], not
    just up to it, since [else] only stashes the then-branch and reopens the
    body, without ever handing the enclosing frame its pop back -- the
    enclosing frame's ledger is one [i32] short of what [frames_ok] would
    otherwise demand of it. Exactly the "a single pop breaks frames_ok"
    situation [pop_with_type_sim] is built for, generalised from a single
    frame to the frame beneath an open child. [[]] for every other kind,
    which is what keeps every existing frame's conjunct in its original,
    non-existential shape.

    It reads only its argument's head, which is what makes the rewriting lemmas
    below cheap. *)
Definition frame_carry (rest : list fview) : list value_type :=
  match rest with
  | g :: _ =>
      match (fv_ctrl g).(opiter_Ctrl_kind) with
      | Opiter_LabelKind_Then | Opiter_LabelKind_Else => [T_num T_i32]
      | _ => []
      end
  | [] => []
  end.

(** Rewriting a frame's [fv_seg]/[fv_done]/[fv_then] but keeping its [fv_ctrl]
    -- every per-frame step, [unreachable] included -- leaves the carry one
    level up alone, so those steps' [frames_ok] proofs reuse the enclosing
    frame's original carry conjunct verbatim. *)
Lemma frame_carry_snoc : forall pre f f',
  (fv_ctrl f).(opiter_Ctrl_kind) = (fv_ctrl f').(opiter_Ctrl_kind) ->
  frame_carry (pre ++ [f]) = frame_carry (pre ++ [f']).
Proof.
  intros pre f f' Hk. destruct pre as [|h pre]; cbn [List.app];
    unfold frame_carry; [rewrite Hk|]; reflexivity.
Qed.

(** Walking outermost-first, each frame's consumed instructions must take it from
    an empty operand stack to the segment it currently owns, checked in the
    context that has a label for it and for every frame enclosing it.

    Wasm 1.0 block types have no parameters, so a frame is always entered with an
    empty stack; [labels] accumulates innermost-first, so by the last frame it is
    exactly [tc_labels (ctx_at C0 st)].

    A frame right below an open [Then] gets [frame_carry]'s extra [i32]: its
    ledger only has to reach the type *one pop short* of [fv_ct f], since the
    real pop already happened and [BI_if]'s own pop of it is still pending at
    [end]. Every other frame keeps the original, direct equation, because
    [frame_carry] is [[]] there and [consume ct0 [] = Some ct0]. *)
(** An [Else] frame owes a second obligation beyond the usual one: its
    [fv_then] -- the then-branch, stashed when [else] fired -- has to check
    out on its own, in the same context and from the same empty stack as
    [fv_done], and land on a type agreeing with the block's declared results.
    Without this, closing the frame at [end] could not produce WasmCert's
    [BI_if]'s two-body conjunction, since nothing else remembers that the
    then-branch ever checked. [[]] for every other kind, so the obligation is
    [True]: this is where [fv_then]'s "[[]] for every other kind" cashes out.
*)
Definition else_obligation (C0 : t_context) (labels' : list (list value_type))
                           (f : fview) : Prop :=
  match (fv_ctrl f).(opiter_Ctrl_kind) with
  | Opiter_LabelKind_Else =>
      exists ct_then,
        List.fold_left (check_single (with_labels C0 labels')) (fv_then f)
                       (Some <<[], false>>) = Some ct_then
        /\ c_types_agree ct_then
             (translate_typelist
                (block_results_of (fv_ctrl f).(opiter_Ctrl_block_type)))
           = true
  | _ => True
  end.

Fixpoint frames_ok (C0 : t_context) (labels : list (list value_type))
                   (fs : list fview) : Prop :=
  match fs with
  | [] => True
  | f :: rest =>
      let labels' := ctrl_label (fv_ctrl f) :: labels in
      ((match frame_carry rest with
        | [] => List.fold_left (check_single (with_labels C0 labels')) (fv_done f)
                               (Some <<[], false>>) = Some (fv_ct f)
        | carry =>
            exists ct0,
              List.fold_left (check_single (with_labels C0 labels')) (fv_done f)
                             (Some <<[], false>>) = Some ct0
              /\ consume ct0 carry = Some (fv_ct f)
        end)
       /\ else_obligation C0 labels' f)
      /\ frames_ok C0 labels' rest
  end.

Definition Inv (C0 : t_context) (st : opiter_OpIterState_t) (fs : list fview)
  : Prop :=
  vec_list st.(opiter_OpIterState_ctrls) = List.map fv_ctrl fs
  /\ vec_list st.(opiter_OpIterState_vals) = List.concat (List.map fv_seg fs)
  /\ bases_ok_from 0 fs
  /\ frames_ok C0 [] fs.

(** The last frame's base is the total size of everything before it. *)
Lemma bases_ok_last : forall pre f n,
  bases_ok_from n (pre ++ [f]) ->
  Z.to_nat (to_Z (fv_ctrl f).(opiter_Ctrl_value_stack_base))
    = (n + List.length (List.concat (List.map fv_seg pre)))%nat.
Proof.
  induction pre as [|g pre IH]; intros f n Hb.
  - simpl in Hb. destruct Hb as [Hb _]. simpl. lia.
  - simpl in Hb. destruct Hb as [_ Hb]. simpl.
    rewrite (IH f _ Hb). rewrite List.app_length. lia.
Qed.

(* ================================================================== *)
(** ** Establishing and maintaining the invariant                      *)
(* ================================================================== *)

(** The frame [start_function] pushes: kind [Body], the function's results as
    its block type, base 0, nothing consumed. *)
Definition body_fview (bt : opiter_BlockType_t) : fview :=
  {| fv_ctrl := {| opiter_Ctrl_kind := Opiter_LabelKind_Body;
                   opiter_Ctrl_block_type := bt;
                   opiter_Ctrl_value_stack_base :=
                     alloc_vec_Vec_len (alloc_vec_Vec_new opiter_StackType_t);
                   opiter_Ctrl_polymorphic_base := false |};
     fv_seg := [];
     fv_done := [];
     fv_then := [] |}.

Lemma Inv_start_push : forall C0 st bt,
  opiter_push_ctrl
    {| opiter_OpIterState_vals := alloc_vec_Vec_new opiter_StackType_t;
       opiter_OpIterState_ctrls := alloc_vec_Vec_new opiter_Ctrl_t;
       opiter_OpIterState_pos := 0%usize;
       opiter_OpIterState_pending := None |}
    Opiter_LabelKind_Body bt = Ok st ->
  Inv C0 st [body_fview bt].
Proof.
  intros C0 st bt H. unfold opiter_push_ctrl in H.
  destruct (alloc_vec_Vec_push (alloc_vec_Vec_new opiter_Ctrl_t)
              {| opiter_Ctrl_kind := Opiter_LabelKind_Body;
                 opiter_Ctrl_block_type := bt;
                 opiter_Ctrl_value_stack_base :=
                   alloc_vec_Vec_len (alloc_vec_Vec_new opiter_StackType_t);
                 opiter_Ctrl_polymorphic_base := false |}) as [v|] eqn:Hpush;
    cbn [bind] in H; [|discriminate].
  injection H as <-. apply vec_push_spec in Hpush.
  unfold Inv, body_fview.
  cbn [opiter_OpIterState_ctrls opiter_OpIterState_vals].
  repeat split.
  all: cbn [bases_ok_from frames_ok fv_ctrl fv_seg fv_done fv_ct
            opiter_Ctrl_value_stack_base].
  all: try (rewrite Hpush).
  all: try reflexivity.
Qed.

(** Also that the frame's block type is the function's result type. Needs the
    Wasm 1.0 restriction to at most one result: [start_function] maps any other
    length to [Empty], so a two-result signature would be silently read as
    returning nothing. The module validator is what rules that out. *)
Lemma Inv_start : forall C0 st results,
  (List.length (vec_list results) <= 1)%nat ->
  opiter_start_function results = Ok st ->
  exists bt, Inv C0 st [body_fview bt]
             /\ block_results_of bt = vec_list results.
Proof.
  intros C0 st results Hlen1 H. unfold opiter_start_function in H.
  destruct (slice_len results s= 1%usize) eqn:Hlen; cbn [bind] in H.
  - destruct (slice_index_usize results 0%usize) as [vt|] eqn:Hidx;
      cbn [bind] in H; [|discriminate].
    exists (Opiter_BlockType_Value vt).
    split; [apply Inv_start_push; exact H|].
    (* the slice has exactly one element, and that is the one indexed *)
    apply scalar_eqb_true in Hlen. rewrite slice_len_spec in Hlen.
    assert (H1 : to_Z 1%usize = 1) by reflexivity. rewrite H1 in Hlen.
    rewrite slice_index_usize_spec in Hidx.
    assert (H0 : Z.to_nat (to_Z 0%usize) = 0%nat) by reflexivity.
    rewrite H0 in Hidx.
    destruct (vec_list results) as [|x [|y l]];
      [cbn [List.length] in Hlen; lia
      | cbn [List.nth_error] in Hidx; injection Hidx as <-; reflexivity
      | cbn [List.length] in Hlen; lia].
  - exists Opiter_BlockType_Empty.
    split; [apply Inv_start_push; exact H|].
    apply scalar_eqb_false in Hlen. rewrite slice_len_spec in Hlen.
    assert (H1 : to_Z 1%usize = 1) by reflexivity. rewrite H1 in Hlen.
    destruct (vec_list results) as [|x l];
      [reflexivity | cbn [List.length] in Hlen, Hlen1; lia].
Qed.

(** [nop] leaves the state alone and appends [BI_nop] to the innermost frame's
    ghost list. WasmCert's [check_single] is the identity on it, so the fold
    still lands on the same [checker_type]. *)
Lemma frames_ok_append_nop : forall C0 labels pre f,
  frames_ok C0 labels (pre ++ [f]) ->
  frames_ok C0 labels
    (pre ++ [{| fv_ctrl := fv_ctrl f;
                fv_seg := fv_seg f;
                fv_done := fv_done f ++ [BI_nop];
                fv_then := fv_then f |}]).
Proof.
  intros C0 labels pre f. revert labels.
  induction pre as [|g pre IH]; intros labels H.
  - simpl in H |- *. destruct H as [[Hfold Helse] _]. split; [split|exact I].
    + cbn [fv_ctrl fv_seg fv_done fv_ct] in *.
      rewrite List.fold_left_app. rewrite Hfold. reflexivity.
    + cbn [fv_ctrl fv_then] in *. exact Helse.
  - simpl in H |- *. destruct H as [Hg Hrest]. split.
    + assert (Hk : (fv_ctrl f).(opiter_Ctrl_kind)
                   = (fv_ctrl {| fv_ctrl := fv_ctrl f; fv_seg := fv_seg f;
                                 fv_done := fv_done f ++ [BI_nop];
                                 fv_then := fv_then f |}).(opiter_Ctrl_kind))
        by reflexivity.
      rewrite (frame_carry_snoc pre f _ Hk) in Hg. exact Hg.
    + apply IH. exact Hrest.
Qed.

(** The invariant only mentions the two stacks, so any reader that leaves them
    alone preserves it. That covers every reader's [take_pending] prologue. *)
Lemma Inv_fields : forall C0 st st' fs,
  vec_list st'.(opiter_OpIterState_vals)
    = vec_list st.(opiter_OpIterState_vals) ->
  vec_list st'.(opiter_OpIterState_ctrls)
    = vec_list st.(opiter_OpIterState_ctrls) ->
  Inv C0 st fs -> Inv C0 st' fs.
Proof.
  intros C0 st st' fs Hv Hc [H1 [H2 [H3 H4]]].
  unfold Inv. rewrite Hv. rewrite Hc. repeat split; assumption.
Qed.

Lemma Inv_obs : forall C0 st st' fs,
  obs st' = obs st -> Inv C0 st fs -> Inv C0 st' fs.
Proof.
  intros C0 st st' fs Hobs Hinv.
  destruct (obs_fields st st' Hobs) as [Hv [Hc _]].
  apply (Inv_fields C0 st st' fs); [rewrite Hv | rewrite Hc | exact Hinv];
    reflexivity.
Qed.

(** Bases only look at the frames *before* each one, so replacing the innermost
    frame's segment or ghost list cannot disturb them. Every non-control step
    goes through this. *)
Lemma bases_ok_from_last : forall n pre f g,
  (fv_ctrl g).(opiter_Ctrl_value_stack_base)
    = (fv_ctrl f).(opiter_Ctrl_value_stack_base) ->
  bases_ok_from n (pre ++ [f]) -> bases_ok_from n (pre ++ [g]).
Proof.
  intros n pre f g Hbase. revert n.
  induction pre as [|h pre IH]; intros n H; simpl in H |- *.
  - destruct H as [Hb _]. rewrite Hbase. split; [exact Hb | exact I].
  - destruct H as [Hb Hrest]. split; [exact Hb | apply IH; exact Hrest].
Qed.

(** Packaging the three structural conjuncts for a step that only rewrites the
    innermost frame, so each step lemma need only supply the new operand array
    and the typing obligation. *)
Lemma Inv_step_last : forall C0 st st' pre f g,
  Inv C0 st (pre ++ [f]) ->
  (fv_ctrl g).(opiter_Ctrl_value_stack_base)
    = (fv_ctrl f).(opiter_Ctrl_value_stack_base) ->
  vec_list st'.(opiter_OpIterState_ctrls) = List.map fv_ctrl (pre ++ [g]) ->
  vec_list st'.(opiter_OpIterState_vals)
    = List.concat (List.map fv_seg (pre ++ [g])) ->
  frames_ok C0 [] (pre ++ [g]) ->
  Inv C0 st' (pre ++ [g]).
Proof.
  intros C0 st st' pre f g [H1 [H2 [H3 H4]]] Hbase Hc Hv Hf.
  unfold Inv. repeat split.
  - exact Hc.
  - exact Hv.
  - apply (bases_ok_from_last 0 pre f g Hbase). exact H3.
  - exact Hf.
Qed.

(** [nop]: the state is untouched and the innermost frame's ghost list grows by
    [BI_nop], on which WasmCert's [check_single] is the identity. *)
Theorem step_nop : forall C0 st fs pre f st',
  Inv C0 st fs -> fs = pre ++ [f] ->
  opiter_read_nop st = Ok (Core_result_Result_Ok tt, st') ->
  Inv C0 st'
      (pre ++ [{| fv_ctrl := fv_ctrl f;
                  fv_seg := fv_seg f;
                  fv_done := fv_done f ++ [BI_nop];
                  fv_then := fv_then f |}]).
Proof.
  intros C0 st fs pre f st' Hinv Hfs H. subst fs.
  unfold opiter_read_nop in H.
  pose proof (take_pending_ok_inv st opiter_op_nop st' H) as Hobs.
  destruct (obs_fields st st' Hobs) as [Hv [Hc _]].
  apply (Inv_step_last C0 st st' pre f _ Hinv).
  - reflexivity.
  - rewrite Hc. destruct Hinv as [H1 _]. rewrite H1.
    rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hv. destruct Hinv as [_ [H2 _]]. rewrite H2.
    rewrite List.map_app. rewrite List.map_app. reflexivity.
  - apply frames_ok_append_nop. destruct Hinv as [_ [_ [_ H4]]]. exact H4.
Qed.

(** [translate_vals] reverses, so appending to a segment (the Rust's push)
    conses onto WasmCert's stack (its [produce]). This is the bridge every
    stack-changing step needs. *)
Lemma translate_vals_snoc : forall seg t,
  translate_vals (seg ++ [t]) = translate_st t :: translate_vals seg.
Proof.
  intros seg t. unfold translate_vals.
  rewrite List.map_app. rewrite List.rev_app_distr. reflexivity.
Qed.

(** Appending an instruction to the innermost frame's ghost list, given the
    [check_single] fact for it. Generalises [frames_ok_append_nop]. *)
Lemma frames_ok_append : forall C0 labels pre f be seg',
  frames_ok C0 labels (pre ++ [f]) ->
  (forall lbls,
     check_single (with_labels C0 (ctrl_label (fv_ctrl f) :: lbls))
                  (Some (fv_ct f)) be
       = Some <<translate_vals seg',
               (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>>) ->
  frames_ok C0 labels
    (pre ++ [{| fv_ctrl := fv_ctrl f;
                fv_seg := seg';
                fv_done := fv_done f ++ [be];
                fv_then := fv_then f |}]).
Proof.
  intros C0 labels pre f be seg'. revert labels.
  induction pre as [|g pre IH]; intros labels H Hstep.
  - simpl in H |- *. destruct H as [[Hfold Helse] _]. split; [split|exact I].
    + cbn [fv_ctrl fv_seg fv_done fv_ct] in *.
      rewrite List.fold_left_app. rewrite Hfold. simpl. apply Hstep.
    + cbn [fv_ctrl fv_then] in *. exact Helse.
  - simpl in H |- *. destruct H as [Hg Hrest]. split.
    + assert (Hk : (fv_ctrl f).(opiter_Ctrl_kind)
                   = (fv_ctrl {| fv_ctrl := fv_ctrl f; fv_seg := seg';
                                 fv_done := fv_done f ++ [be];
                                 fv_then := fv_then f |}).(opiter_Ctrl_kind))
        by reflexivity.
      rewrite (frame_carry_snoc pre f _ Hk) in Hg. exact Hg.
    + apply IH; [exact Hrest | exact Hstep].
Qed.

(** [i32.const]: the Rust pushes onto the innermost segment; WasmCert's
    [type_update ts [] [T_num T_i32]] conses the same type onto its stack. *)
Theorem step_i32_const : forall C0 st fs pre f data v st',
  Inv C0 st fs -> fs = pre ++ [f] ->
  opiter_read_i32_const st data = Ok (Core_result_Result_Ok v, st') ->
  Inv C0 st'
      (pre ++ [{| fv_ctrl := fv_ctrl f;
                  fv_seg := fv_seg f ++ [Opiter_StackType_Val Types_ValueType_I32];
                  fv_done := fv_done f
                             ++ [BI_const_num (VAL_int32
                                                (Wasm_int.Int32.repr (to_Z v)))];
                                                fv_then := fv_then f |}]).
Proof.
  intros C0 st fs pre f data v st' Hinv Hfs H. subst fs.
  unfold opiter_read_i32_const in H.
  destruct (opiter_take_pending st opiter_op_i32_const) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (take_pending_ok_inv st opiter_op_i32_const st1 Htp) as Hobs.
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 _]].
  destruct (reader_read_s32_leb data st1.(opiter_OpIterState_pos))
    as [r1|] eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[v0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val _ (Opiter_StackType_Val Types_ValueType_I32))
    as [st2|] eqn:Hpv; cbn [bind] in H; [|discriminate].
  injection H as Hveq <-.
  (* the push appends to the operand array and leaves the control stack alone *)
  destruct (push_val_spec _ _ _ Hpv) as [Hpvals [Hpctrls _]].
  apply (Inv_step_last C0 st _ pre f _ Hinv).
  - reflexivity.
  - rewrite Hpctrls. cbn [opiter_OpIterState_ctrls]. rewrite Hc1.
    destruct Hinv as [H1 _]. rewrite H1.
    rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hpvals. cbn [opiter_OpIterState_vals]. rewrite Hv1.
    destruct Hinv as [_ [H2 _]]. rewrite H2.
    rewrite List.map_app. rewrite List.map_app.
    rewrite List.concat_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg].
    rewrite List.app_nil_r. rewrite List.app_nil_r.
    rewrite List.app_assoc. reflexivity.
  - apply frames_ok_append; [destruct Hinv as [_ [_ [_ H4]]]; exact H4|].
    intros lbls. cbn [check_single].
    unfold fv_ct. rewrite translate_vals_snoc.
    cbn [translate_st translate_vt_v typeof_num].
    unfold type_update, produce. cbn [consume CT_type CT_unr]. reflexivity.
Qed.

Theorem step_f32_const : forall C0 st fs pre f data v st',
  Inv C0 st fs -> fs = pre ++ [f] ->
  opiter_read_f32_const st data = Ok (Core_result_Result_Ok v, st') ->
  Inv C0 st'
      (pre ++ [{| fv_ctrl := fv_ctrl f;
                  fv_seg := fv_seg f ++ [Opiter_StackType_Val Types_ValueType_F32];
                  fv_done := fv_done f
                             ++ [BI_const_num (fconst_val T_f32 (to_Z v))];
                             fv_then := fv_then f |}]).
Proof.
  intros C0 st fs pre f data v st' Hinv Hfs H. subst fs.
  unfold opiter_read_f32_const in H.
  destruct (opiter_take_pending st opiter_op_f32_const) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (take_pending_ok_inv st opiter_op_f32_const st1 Htp) as Hobs.
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 _]].
  destruct (reader_read_f32_bits data st1.(opiter_OpIterState_pos))
    as [r1|] eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[v0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val _ (Opiter_StackType_Val Types_ValueType_F32))
    as [st2|] eqn:Hpv; cbn [bind] in H; [|discriminate].
  injection H as Hveq <-.
  (* the push appends to the operand array and leaves the control stack alone *)
  destruct (push_val_spec _ _ _ Hpv) as [Hpvals [Hpctrls _]].
  apply (Inv_step_last C0 st _ pre f _ Hinv).
  - reflexivity.
  - rewrite Hpctrls. cbn [opiter_OpIterState_ctrls]. rewrite Hc1.
    destruct Hinv as [H1 _]. rewrite H1.
    rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hpvals. cbn [opiter_OpIterState_vals]. rewrite Hv1.
    destruct Hinv as [_ [H2 _]]. rewrite H2.
    rewrite List.map_app. rewrite List.map_app.
    rewrite List.concat_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg].
    rewrite List.app_nil_r. rewrite List.app_nil_r.
    rewrite List.app_assoc. reflexivity.
  - apply frames_ok_append; [destruct Hinv as [_ [_ [_ H4]]]; exact H4|].
    intros lbls. cbn [check_single].
    unfold fv_ct. rewrite translate_vals_snoc.
    cbn [translate_st translate_vt_v fconst_val typeof_num].
    unfold type_update, produce. cbn [consume CT_type CT_unr]. reflexivity.
Qed.

Theorem step_f64_const : forall C0 st fs pre f data v st',
  Inv C0 st fs -> fs = pre ++ [f] ->
  opiter_read_f64_const st data = Ok (Core_result_Result_Ok v, st') ->
  Inv C0 st'
      (pre ++ [{| fv_ctrl := fv_ctrl f;
                  fv_seg := fv_seg f ++ [Opiter_StackType_Val Types_ValueType_F64];
                  fv_done := fv_done f
                             ++ [BI_const_num (fconst_val T_f64 (to_Z v))];
                             fv_then := fv_then f |}]).
Proof.
  intros C0 st fs pre f data v st' Hinv Hfs H. subst fs.
  unfold opiter_read_f64_const in H.
  destruct (opiter_take_pending st opiter_op_f64_const) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (take_pending_ok_inv st opiter_op_f64_const st1 Htp) as Hobs.
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 _]].
  destruct (reader_read_f64_bits data st1.(opiter_OpIterState_pos))
    as [r1|] eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[v0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val _ (Opiter_StackType_Val Types_ValueType_F64))
    as [st2|] eqn:Hpv; cbn [bind] in H; [|discriminate].
  injection H as Hveq <-.
  (* the push appends to the operand array and leaves the control stack alone *)
  destruct (push_val_spec _ _ _ Hpv) as [Hpvals [Hpctrls _]].
  apply (Inv_step_last C0 st _ pre f _ Hinv).
  - reflexivity.
  - rewrite Hpctrls. cbn [opiter_OpIterState_ctrls]. rewrite Hc1.
    destruct Hinv as [H1 _]. rewrite H1.
    rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hpvals. cbn [opiter_OpIterState_vals]. rewrite Hv1.
    destruct Hinv as [_ [H2 _]]. rewrite H2.
    rewrite List.map_app. rewrite List.map_app.
    rewrite List.concat_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg].
    rewrite List.app_nil_r. rewrite List.app_nil_r.
    rewrite List.app_assoc. reflexivity.
  - apply frames_ok_append; [destruct Hinv as [_ [_ [_ H4]]]; exact H4|].
    intros lbls. cbn [check_single].
    unfold fv_ct. rewrite translate_vals_snoc.
    cbn [translate_st translate_vt_v fconst_val typeof_num].
    unfold type_update, produce. cbn [consume CT_type CT_unr]. reflexivity.
Qed.

Theorem step_i64_const : forall C0 st fs pre f data v st',
  Inv C0 st fs -> fs = pre ++ [f] ->
  opiter_read_i64_const st data = Ok (Core_result_Result_Ok v, st') ->
  Inv C0 st'
      (pre ++ [{| fv_ctrl := fv_ctrl f;
                  fv_seg := fv_seg f ++ [Opiter_StackType_Val Types_ValueType_I64];
                  fv_done := fv_done f
                             ++ [BI_const_num (VAL_int64
                                                (Wasm_int.Int64.repr (to_Z v)))];
                                                fv_then := fv_then f |}]).
Proof.
  intros C0 st fs pre f data v st' Hinv Hfs H. subst fs.
  unfold opiter_read_i64_const in H.
  destruct (opiter_take_pending st opiter_op_i64_const) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (take_pending_ok_inv st opiter_op_i64_const st1 Htp) as Hobs.
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 _]].
  destruct (reader_read_s64_leb data st1.(opiter_OpIterState_pos))
    as [r1|] eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[v0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val _ (Opiter_StackType_Val Types_ValueType_I64))
    as [st2|] eqn:Hpv; cbn [bind] in H; [|discriminate].
  injection H as Hveq <-.
  (* the push appends to the operand array and leaves the control stack alone *)
  destruct (push_val_spec _ _ _ Hpv) as [Hpvals [Hpctrls _]].
  apply (Inv_step_last C0 st _ pre f _ Hinv).
  - reflexivity.
  - rewrite Hpctrls. cbn [opiter_OpIterState_ctrls]. rewrite Hc1.
    destruct Hinv as [H1 _]. rewrite H1.
    rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hpvals. cbn [opiter_OpIterState_vals]. rewrite Hv1.
    destruct Hinv as [_ [H2 _]]. rewrite H2.
    rewrite List.map_app. rewrite List.map_app.
    rewrite List.concat_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg].
    rewrite List.app_nil_r. rewrite List.app_nil_r.
    rewrite List.app_assoc. reflexivity.
  - apply frames_ok_append; [destruct Hinv as [_ [_ [_ H4]]]; exact H4|].
    intros lbls. cbn [check_single].
    unfold fv_ct. rewrite translate_vals_snoc.
    cbn [translate_st translate_vt_v typeof_num].
    unfold type_update, produce. cbn [consume CT_type CT_unr]. reflexivity.
Qed.

(* ================================================================== *)
(** ** Invariant consequences the pop-based steps need                  *)
(* ================================================================== *)

(** The innermost frame's base is the size of everything outside it, so the
    operand array splits as "enclosing segments, then this frame's". This is the
    fact [pop_stack_type_ok] deliberately does not claim, because it is about the
    invariant rather than about a single pop. *)
Lemma Inv_split : forall C0 st pre f,
  Inv C0 st (pre ++ [f]) ->
  cur_base_nat st = List.length (List.concat (List.map fv_seg pre))
  /\ vec_list st.(opiter_OpIterState_vals)
     = List.concat (List.map fv_seg pre) ++ fv_seg f
  /\ cur_unr st = (fv_ctrl f).(opiter_Ctrl_polymorphic_base).
Proof.
  intros C0 st pre f Hinv.
  assert (Hcc : cur_ctrl st = Some (fv_ctrl f)).
  { destruct Hinv as [H1 _]. apply (cur_ctrl_snoc st (List.map fv_ctrl pre)).
    rewrite H1. rewrite List.map_app. reflexivity. }
  destruct Hinv as [H1 [H2 [H3 H4]]].
  repeat split.
  - unfold cur_base_nat. rewrite Hcc.
    rewrite (bases_ok_last pre f 0 H3). lia.
  - rewrite H2. rewrite List.map_app. rewrite List.concat_app.
    cbn [List.map List.concat]. rewrite List.app_nil_r. reflexivity.
  - unfold cur_unr. rewrite Hcc. reflexivity.
Qed.

(** A real pop can only have taken from the innermost frame: the base check
    rules out reaching into an enclosing one. *)
Lemma Inv_pop_from_last : forall C0 st pre f,
  Inv C0 st (pre ++ [f]) ->
  cur_base_nat st <> List.length (vec_list st.(opiter_OpIterState_vals)) ->
  exists seg' t, fv_seg f = seg' ++ [t].
Proof.
  intros C0 st pre f Hinv Hne.
  destruct (Inv_split C0 st pre f Hinv) as [Hbase [Hvals _]].
  assert (Hlen : List.length (fv_seg f) <> 0%nat).
  { intros Hz. apply Hne. rewrite Hbase. rewrite Hvals.
    rewrite List.app_length. rewrite Hz. lia. }
  destruct (List.rev (fv_seg f)) as [|t rt] eqn:Hrev.
  - exfalso. apply Hlen.
    apply (f_equal (@List.length _)) in Hrev.
    rewrite List.rev_length in Hrev. cbn [List.length] in Hrev. exact Hrev.
  - exists (List.rev rt), t.
    apply (f_equal (@List.rev _)) in Hrev.
    rewrite List.rev_involutive in Hrev. rewrite Hrev. reflexivity.
Qed.

(** [drop]: either a real pop, shortening the innermost segment, or an exhausted
    unreachable frame yielding [Bot] and changing nothing. WasmCert's
    [type_update_drop] splits exactly the same two ways. *)
Theorem step_drop : forall C0 st fs pre f t st',
  Inv C0 st fs -> fs = pre ++ [f] ->
  opiter_read_drop st = Ok (Core_result_Result_Ok t, st') ->
  exists seg',
    Inv C0 st'
        (pre ++ [{| fv_ctrl := fv_ctrl f;
                    fv_seg := seg';
                    fv_done := fv_done f ++ [BI_drop];
                    fv_then := fv_then f |}]).
Proof.
  intros C0 st fs pre f t st' Hinv Hfs H. subst fs.
  unfold opiter_read_drop in H.
  destruct (opiter_take_pending st opiter_op_drop) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (take_pending_ok_inv st opiter_op_drop st1 Htp) as Hobs.
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 _]].
  (* the invariant transports to st1, which the prologue left alone *)
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  destruct (pop_stack_type_ok st1 t st' H) as [Hctrls [Hreal | Hbot]].
  - (* real pop *)
    destruct Hreal as [prev [Hvals [Hvals' Hne]]].
    destruct (Inv_pop_from_last C0 st1 pre f Hinv1 Hne) as [seg' [t0 Hseg]].
    destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase [Hsplit Hunr]].
    (* the popped element is the last of the innermost segment *)
    assert (Ht : t0 = t /\ prev = List.concat (List.map fv_seg pre) ++ seg').
    { (* ssreflect's rewrite does not take [<-], so re-associate forwards *)
      assert (Hre : List.concat (List.map fv_seg pre) ++ seg' ++ [t0]
                  = (List.concat (List.map fv_seg pre) ++ seg') ++ [t0]).
      { rewrite List.app_assoc. reflexivity. }
      rewrite Hsplit in Hvals. rewrite Hseg in Hvals. rewrite Hre in Hvals.
      apply List.app_inj_tail in Hvals as [Hp Ht0].
      split; [exact Ht0 | symmetry; exact Hp]. }
    destruct Ht as [Ht0 Hprev]. subst t0.
    exists seg'.
    apply (Inv_step_last C0 st1 st' pre f _ Hinv1).
    + reflexivity.
    + rewrite Hctrls. destruct Hinv1 as [K1 _]. rewrite K1.
      rewrite List.map_app. rewrite List.map_app. reflexivity.
    + rewrite Hvals'. rewrite Hprev.
      rewrite List.map_app. rewrite List.concat_app.
      cbn [List.map List.concat fv_seg]. rewrite List.app_nil_r. reflexivity.
    + apply frames_ok_append;
        [destruct Hinv1 as [_ [_ [_ K4]]]; exact K4|].
      intros lbls. cbn [check_single]. unfold fv_ct.
      rewrite Hseg. rewrite translate_vals_snoc.
      unfold type_update_drop. cbn [CT_type CT_unr]. reflexivity.
  - (* exhausted unreachable frame *)
    destruct Hbot as [Htbot [Hvals' [Hunr Hlen]]].
    destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase [Hsplit Hunrf]].
    assert (Hempty : fv_seg f = []).
    { rewrite Hbase in Hlen. rewrite Hsplit in Hlen.
      rewrite List.app_length in Hlen.
      destruct (fv_seg f); [reflexivity | cbn [List.length] in Hlen; lia]. }
    exists (fv_seg f).
    apply (Inv_step_last C0 st1 st' pre f _ Hinv1).
    + reflexivity.
    + rewrite Hctrls. destruct Hinv1 as [K1 _]. rewrite K1.
      rewrite List.map_app. rewrite List.map_app. reflexivity.
    + rewrite Hvals'. destruct Hinv1 as [_ [K2 _]]. rewrite K2.
      rewrite List.map_app. rewrite List.map_app. reflexivity.
    + apply frames_ok_append;
        [destruct Hinv1 as [_ [_ [_ K4]]]; exact K4|].
      intros lbls. cbn [check_single]. unfold fv_ct.
      rewrite Hempty. cbn [translate_vals List.map List.rev].
      unfold type_update_drop. cbn [CT_type CT_unr].
      rewrite <- Hunrf. rewrite Hunr. reflexivity.
Qed.

(* ================================================================== *)
(** ** One typed pop is one [consume] step                             *)
(* ================================================================== *)

Lemma vsub_refl : forall t, (t <t: t) = true.
Proof.
  intros t. unfold value_subtyping. rewrite eqxx. reflexivity.
Qed.

Lemma vsub_bot : forall t, (T_bot <t: t) = true.
Proof.
  intros t. unfold value_subtyping. rewrite eqxx. apply Bool.orb_true_r.
Qed.

(** The popped operand subtypes what was asked for, whichever case fired: a real
    pop yields either the exact type or [Bot], and [Bot] subtypes everything. *)
Lemma translate_st_sub : forall t vt,
  (t = Opiter_StackType_Bot \/ t = Opiter_StackType_Val vt) ->
  (translate_st t <t: translate_vt_v vt) = true.
Proof.
  intros t vt [-> | ->]; cbn [translate_st]; [apply vsub_bot | apply vsub_refl].
Qed.

(** [cur_base_nat] and [cur_unr] read only the control stack, so a step that
    leaves it alone leaves them alone. *)
Lemma cur_views_ctrls : forall st st',
  vec_list st'.(opiter_OpIterState_ctrls)
    = vec_list st.(opiter_OpIterState_ctrls) ->
  cur_base_nat st' = cur_base_nat st /\ cur_unr st' = cur_unr st.
Proof.
  intros st st' Hc. unfold cur_base_nat, cur_unr, cur_ctrl. rewrite Hc.
  split; reflexivity.
Qed.

(** The workhorse the multi-pop readers share.

    Deliberately *not* stated over [Inv]: a single pop breaks [frames_ok], since
    the frame's [checker_type] has moved but its ghost list has not. Only the
    complete reader restores it, by appending the instruction. So this takes the
    structural facts as hypotheses and returns them, letting pops chain. *)
Lemma pop_with_type_sim : forall st pre_seg f vt t st',
  vec_list st.(opiter_OpIterState_vals) = pre_seg ++ fv_seg f ->
  cur_base_nat st = List.length pre_seg ->
  cur_unr st = (fv_ctrl f).(opiter_Ctrl_polymorphic_base) ->
  opiter_pop_with_type st vt = Ok (Core_result_Result_Ok t, st') ->
  exists seg',
    vec_list st'.(opiter_OpIterState_ctrls)
      = vec_list st.(opiter_OpIterState_ctrls)
    /\ vec_list st'.(opiter_OpIterState_vals) = pre_seg ++ seg'
    /\ consume (fv_ct f) [translate_vt_v vt]
       = Some <<translate_vals seg',
                (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>>.
Proof.
  intros st pre_seg f vt t st' Hsplit Hbase Hunr H.
  destruct (pop_with_type_ok st vt t st' H) as [Hraw Hty].
  destruct (pop_stack_type_ok st t st' Hraw) as [Hctrls [Hreal | Hbot]].
  - (* real pop: the base check says it came from this frame's segment *)
    destruct Hreal as [prev [Hvals [Hvals' Hne]]].
    assert (Hnonempty : fv_seg f <> []).
    { intros Hz. apply Hne. rewrite Hbase. rewrite Hsplit. rewrite Hz.
      rewrite List.app_nil_r. reflexivity. }
    destruct (List.rev (fv_seg f)) as [|t0 rt] eqn:Hrev.
    { exfalso. apply Hnonempty.
      apply (f_equal (@List.rev _)) in Hrev.
      rewrite List.rev_involutive in Hrev. cbn [List.rev] in Hrev. exact Hrev. }
    assert (Hseg : fv_seg f = List.rev rt ++ [t0]).
    { apply (f_equal (@List.rev _)) in Hrev.
      rewrite List.rev_involutive in Hrev. rewrite Hrev. reflexivity. }
    assert (Ht : t0 = t /\ prev = pre_seg ++ List.rev rt).
    { assert (Hre : pre_seg ++ List.rev rt ++ [t0]
                  = (pre_seg ++ List.rev rt) ++ [t0]).
      { rewrite List.app_assoc. reflexivity. }
      rewrite Hsplit in Hvals. rewrite Hseg in Hvals. rewrite Hre in Hvals.
      apply List.app_inj_tail in Hvals as [Hp Ht0].
      split; [exact Ht0 | symmetry; exact Hp]. }
    destruct Ht as [Ht0 Hprev]. subst t0.
    exists (List.rev rt). repeat split.
    + rewrite Hctrls. reflexivity.
    + rewrite Hvals'. exact Hprev.
    + unfold fv_ct. rewrite Hseg. rewrite translate_vals_snoc.
      cbn [consume CT_type CT_unr].
      rewrite (translate_st_sub t vt Hty). reflexivity.
  - (* exhausted unreachable frame: nothing moves *)
    destruct Hbot as [Htbot [Hvals' [Hunrtrue Hlen]]].
    assert (Hempty : fv_seg f = []).
    { rewrite Hbase in Hlen. rewrite Hsplit in Hlen.
      rewrite List.app_length in Hlen.
      destruct (fv_seg f); [reflexivity | cbn [List.length] in Hlen; lia]. }
    exists (fv_seg f). repeat split.
    + rewrite Hctrls. reflexivity.
    + rewrite Hvals'. exact Hsplit.
    + unfold fv_ct. rewrite Hempty.
      cbn [translate_vals List.map List.rev consume CT_type CT_unr].
      rewrite <- Hunr. rewrite Hunrtrue. reflexivity.
Qed.


(** The untyped pop's counterpart to [pop_with_type_sim]. It reports what became
    of the segment rather than a [consume] step, because [select] is the one
    reader that has to know *which* type came off; the [consume] its operand
    lists mention is then the trivial one. *)
Lemma pop_stack_type_sim : forall st pre_seg f t st',
  vec_list st.(opiter_OpIterState_vals) = pre_seg ++ fv_seg f ->
  cur_base_nat st = List.length pre_seg ->
  cur_unr st = (fv_ctrl f).(opiter_Ctrl_polymorphic_base) ->
  opiter_pop_stack_type st = Ok (Core_result_Result_Ok t, st') ->
  exists seg',
    vec_list st'.(opiter_OpIterState_ctrls)
      = vec_list st.(opiter_OpIterState_ctrls)
    /\ vec_list st'.(opiter_OpIterState_vals) = pre_seg ++ seg'
    /\ (fv_seg f = seg' ++ [t]
        \/ (fv_seg f = [] /\ seg' = [] /\ t = Opiter_StackType_Bot
            /\ (fv_ctrl f).(opiter_Ctrl_polymorphic_base) = true)).
Proof.
  intros st pre_seg f t st' Hsplit Hbase Hunr H.
  destruct (pop_stack_type_ok st t st' H) as [Hctrls [Hreal | Hbot]].
  - destruct Hreal as [prev [Hvals [Hvals' Hne]]].
    assert (Hnonempty : fv_seg f <> []).
    { intros Hz. apply Hne. rewrite Hbase. rewrite Hsplit. rewrite Hz.
      rewrite List.app_nil_r. reflexivity. }
    destruct (List.rev (fv_seg f)) as [|t0 rt] eqn:Hrev.
    { exfalso. apply Hnonempty.
      apply (f_equal (@List.rev _)) in Hrev.
      rewrite List.rev_involutive in Hrev. cbn [List.rev] in Hrev. exact Hrev. }
    assert (Hseg : fv_seg f = List.rev rt ++ [t0]).
    { apply (f_equal (@List.rev _)) in Hrev.
      rewrite List.rev_involutive in Hrev. rewrite Hrev. reflexivity. }
    assert (Ht : t0 = t /\ prev = pre_seg ++ List.rev rt).
    { assert (Hre : pre_seg ++ List.rev rt ++ [t0]
                  = (pre_seg ++ List.rev rt) ++ [t0]).
      { rewrite List.app_assoc. reflexivity. }
      rewrite Hsplit in Hvals. rewrite Hseg in Hvals. rewrite Hre in Hvals.
      apply List.app_inj_tail in Hvals as [Hp Ht0].
      split; [exact Ht0 | symmetry; exact Hp]. }
    destruct Ht as [Ht0 Hprev]. subst t0.
    exists (List.rev rt). split; [rewrite Hctrls; reflexivity|].
    split; [rewrite Hvals'; exact Hprev | left; exact Hseg].
  - destruct Hbot as [Htbot [Hvals' [Hunrtrue Hlen]]].
    assert (Hempty : fv_seg f = []).
    { rewrite Hbase in Hlen. rewrite Hsplit in Hlen.
      rewrite List.app_length in Hlen.
      destruct (fv_seg f); [reflexivity | cbn [List.length] in Hlen; lia]. }
    exists []. split; [rewrite Hctrls; reflexivity|].
    split.
    + rewrite Hvals'. rewrite Hsplit. rewrite Hempty. reflexivity.
    + right. split; [exact Hempty|]. split; [reflexivity|].
      split; [exact Htbot | rewrite <- Hunr; exact Hunrtrue].
Qed.

(** [consume] over a list is [consume] one at a time. Holds in the exhausted
    unreachable case too, where both sides stop at [<<nil, true>>]. *)
Lemma consume_cons_split : forall ct a rest ct1,
  consume ct [a] = Some ct1 -> consume ct (a :: rest) = consume ct1 rest.
Proof.
  (* destructing the record makes the projections reduce *)
  intros [ts unr] a rest ct1 H. cbn [consume CT_type CT_unr] in H |- *.
  destruct ts as [|t ts'].
  - destruct unr; [|discriminate].
    injection H as <-. cbn [consume CT_type CT_unr]. destruct rest; reflexivity.
  - destruct (t <t: a) eqn:Hsub; [|discriminate].
    cbn [consume] in H. injection H as <-.
    (* [destruct ... eqn:] already substituted the guard in the goal *)
    cbn [consume CT_type CT_unr]. reflexivity.
Qed.

(** A pop sequence that exactly exhausts the frame's operands witnesses
    [c_types_agree]. Both of [c_types_agree]'s cases work out: a real pop leaves
    the segment matching the expected types up to subtyping, and an exhausted
    polymorphic frame leaves an empty segment, where the [take] makes the
    comparison trivial.

    This is what turns [end]'s "results popped, nothing left" check into the
    inner [b_e_type_checker]'s final obligation. *)
Lemma c_types_agree_consume_nil : forall ts ct unr,
  consume ct ts = Some <<[], unr>> -> c_types_agree ct ts = true.
Proof.
  induction ts as [|a ts IH]; intros ct unr H.
  - cbn [consume] in H. injection H as H. rewrite H.
    unfold c_types_agree, values_subtyping.
    cbn [CT_type CT_unr size take all2]. destruct unr; reflexivity.
  - destruct ct as [cts cunr]. cbn [consume CT_type CT_unr] in H.
    destruct cts as [|t cts'].
    + destruct cunr; [|discriminate].
      unfold c_types_agree, values_subtyping.
      cbn [CT_type CT_unr size take all2]. reflexivity.
    + destruct (t <t: a) eqn:Hsub; [|discriminate].
      pose proof (IH <<cts', cunr>> unr H) as Hrec.
      unfold c_types_agree, values_subtyping in Hrec |- *.
      cbn [CT_type CT_unr size take all2] in Hrec |- *.
      destruct cunr; rewrite Hsub; cbn [andb]; exact Hrec.
Qed.

(* ================================================================== *)
(** ** select                                                          *)
(* ================================================================== *)

(** Wasm 1.0 has only number types, so WasmCert's numeric side conditions on
    [select] are vacuous: every operand a segment can hold translates to a
    [T_num] or to [T_bot]. *)
Lemma translate_st_numeric : forall t, is_numeric_type (translate_st t) = true.
Proof. intros [vt|]; [destruct vt|]; reflexivity. Qed.

(** The Rust join is WasmCert's [value_type_select]: [T_bot] absorbs, and two
    real types have to be equal. *)
Lemma join_stack_type_spec : forall a b t,
  opiter_join_stack_type a b = Ok (Core_result_Result_Ok t) ->
  value_type_select (translate_st a) (translate_st b) = Some (translate_st t).
Proof.
  intros a b t H. unfold opiter_join_stack_type in H.
  destruct a as [va|].
  - destruct b as [vb|].
    + rewrite vt_eq_spec in H. cbn [bind] in H.
      destruct (types_ValueType_t_beq va vb) eqn:Hbeq; [|discriminate].
      apply vt_beq_eq in Hbeq. subst vb. injection H as <-.
      cbn [translate_st]. destruct va; reflexivity.
    + injection H as <-. cbn [translate_st]. destruct va; reflexivity.
  - injection H as <-. cbn [translate_st].
    destruct b as [vb|]; [destruct vb|]; reflexivity.
Qed.

(** Two degenerate joins, which is what the exhausted-frame cases need: with a
    [Bot] on one side the answer is the other side, and the [value_type_select]
    detour is not worth taking. *)
Lemma join_stack_type_bot_l : forall b t,
  opiter_join_stack_type Opiter_StackType_Bot b
    = Ok (Core_result_Result_Ok t) -> t = b.
Proof.
  intros b t H. unfold opiter_join_stack_type in H. injection H as <-.
  reflexivity.
Qed.

Lemma join_stack_type_bot_r : forall a t,
  opiter_join_stack_type a Opiter_StackType_Bot
    = Ok (Core_result_Result_Ok t) -> translate_st t = translate_st a.
Proof.
  intros a t H. unfold opiter_join_stack_type in H.
  destruct a as [va|]; injection H as <-; reflexivity.
Qed.

(** [read_select]: one typed pop and two untyped ones, then a push.
    [type_update_select] splits on the length of the *visible* segment, and the
    three pops split the same four ways, because [pop_stack_type] yields [Bot]
    exactly where WasmCert demands [CT_unr]:

    - three or more, so [value_type_select] joins the two real operands;
    - exactly two, so the second value came off as [Bot] and the join is the
      first, which is why that branch needs [CT_unr];
    - one or none, where both values came off as [Bot] and the operator pushes
      [T_bot]. That is the one place a [Bot] reaches the operand stack. *)
Theorem step_select : forall C0 st fs pre f t st',
  Inv C0 st fs -> fs = pre ++ [f] ->
  opiter_read_select st = Ok (Core_result_Result_Ok t, st') ->
  exists seg',
    Inv C0 st'
        (pre ++ [{| fv_ctrl := fv_ctrl f;
                    fv_seg := seg';
                    fv_done := fv_done f ++ [BI_select None];
                    fv_then := fv_then f |}]).
Proof.
  intros C0 st fs pre f t st' Hinv Hfs H. subst fs.
  unfold opiter_read_select in H.
  (* prologue *)
  destruct (opiter_take_pending st opiter_op_select) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (take_pending_ok_inv st opiter_op_select st1 Htp) as Hobs.
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  (* the condition *)
  destruct (opiter_pop_with_type st1 Types_ValueType_I32) as [[r1 st2]|] eqn:Hq1;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [t1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (pop_with_type_ok st1 _ t1 st2 Hq1) as [Hraw1 Hty1].
  destruct (pop_stack_type_sim st1 (List.concat (List.map fv_seg pre)) f
              t1 st2 Hsplit1 Hbase1 Hunr1 Hraw1) as [seg1 [Hc2 [Hv2 D1]]].
  pose proof (translate_st_sub t1 Types_ValueType_I32 Hty1) as Hsub1.
  cbn [translate_vt_v] in Hsub1.
  (* the second value *)
  destruct (opiter_pop_stack_type st2) as [[r2 st3]|] eqn:Hq2;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [t2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (cur_views_ctrls st1 st2 Hc2) as [Hb2 Hu2].
  destruct (pop_stack_type_sim st2 (List.concat (List.map fv_seg pre))
              {| fv_ctrl := fv_ctrl f; fv_seg := seg1; fv_done := fv_done f;
fv_then := fv_then f |}
              t2 st3) as [seg2 [Hc3 [Hv3 D2]]].
  { cbn [fv_seg]. exact Hv2. }
  { cbn [fv_ctrl]. rewrite Hb2. exact Hbase1. }
  { cbn [fv_ctrl]. rewrite Hu2. exact Hunr1. }
  { exact Hq2. }
  cbn [fv_seg fv_ctrl] in D2.
  (* the first value *)
  destruct (opiter_pop_stack_type st3) as [[r3 st4]|] eqn:Hq3;
    cbn [bind] in H; [|discriminate].
  destruct r3 as [t3|e3].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (cur_views_ctrls st2 st3 Hc3) as [Hb3 Hu3].
  destruct (pop_stack_type_sim st3 (List.concat (List.map fv_seg pre))
              {| fv_ctrl := fv_ctrl f; fv_seg := seg2; fv_done := fv_done f;
fv_then := fv_then f |}
              t3 st4) as [seg3 [Hc4 [Hv4 D3]]].
  { cbn [fv_seg]. exact Hv3. }
  { cbn [fv_ctrl]. rewrite Hb3. rewrite Hb2. exact Hbase1. }
  { cbn [fv_ctrl]. rewrite Hu3. rewrite Hu2. exact Hunr1. }
  { exact Hq3. }
  cbn [fv_seg fv_ctrl] in D3.
  (* the join and the push *)
  destruct (opiter_join_stack_type t2 t3) as [rj|] eqn:Hj;
    cbn [bind] in H; [|discriminate].
  destruct rj as [tj|ej].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val st4 tj) as [st5|] eqn:Hpv; cbn [bind] in H;
    [|discriminate].
  injection H as -> ->.
  destruct (push_val_spec _ _ _ Hpv) as [Hpvals [Hpctrls _]].
  exists (seg3 ++ [t]).
  apply (Inv_step_last C0 st1 st' pre f _ Hinv1).
  - reflexivity.
  - rewrite Hpctrls. rewrite Hc4. rewrite Hc3. rewrite Hc2.
    destruct Hinv1 as [K1 _]. rewrite K1.
    rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hpvals. rewrite Hv4.
    rewrite List.map_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg]. rewrite List.app_nil_r.
    rewrite List.app_assoc. reflexivity.
  - apply frames_ok_append; [destruct Hinv1 as [_ [_ [_ K4]]]; exact K4|].
    intros lbls. cbn [check_single]. unfold fv_ct.
    destruct D1 as [HA | [HA1 [HA2 [HA3 HA4]]]].
    + destruct D2 as [HB | [HB1 [HB2 [HB3 HB4]]]].
      * destruct D3 as [HC | [HC1 [HC2 [HC3 HC4]]]].
        -- (* three or more operands visible *)
           rewrite HC in HB. rewrite HB in HA. rewrite HA.
           rewrite (translate_vals_snoc _ t1).
           rewrite (translate_vals_snoc _ t2).
           rewrite (translate_vals_snoc seg3 t3).
           unfold type_update_select. cbn [CT_type CT_unr].
           rewrite (join_stack_type_spec t2 t3 t Hj).
           unfold type_update. cbn [consume CT_type CT_unr].
           rewrite Hsub1. rewrite vsub_refl. rewrite vsub_refl.
           rewrite (translate_vals_snoc seg3 t). cbn [produce CT_type CT_unr].
           reflexivity.
        -- (* exactly two: the first value came off Bot *)
           rewrite HB in HA. rewrite HC1 in HA. rewrite HA. rewrite HC2.
           cbn [translate_vals List.map List.rev List.app].
           rewrite HC3 in Hj. rewrite (join_stack_type_bot_r t2 t Hj).
           rewrite HC4.
           unfold type_update_select. cbn [CT_type CT_unr].
           rewrite translate_st_numeric. cbn [andb].
           unfold type_update. cbn [consume CT_type CT_unr].
           rewrite Hsub1. rewrite vsub_refl. reflexivity.
      * destruct D3 as [HC | [HC1 [HC2 [HC3 HC4]]]].
        -- exfalso. rewrite HB2 in HC. destruct seg3; discriminate HC.
        -- (* exactly one: only the condition was visible *)
           rewrite HB1 in HA. rewrite HA. rewrite HC2.
           cbn [translate_vals List.map List.rev List.app].
           rewrite HB3 in Hj. rewrite (join_stack_type_bot_l t3 t Hj).
           rewrite HC3. rewrite HB4.
           unfold type_update_select. cbn [CT_type CT_unr translate_st].
           cbn beta iota.
           unfold type_update. cbn [consume CT_type CT_unr].
           rewrite Hsub1. reflexivity.
    + destruct D2 as [HB | [HB1 [HB2 [HB3 HB4]]]].
      * exfalso. rewrite HA2 in HB. destruct seg2; discriminate HB.
      * destruct D3 as [HC | [HC1 [HC2 [HC3 HC4]]]].
        -- exfalso. rewrite HB2 in HC. destruct seg3; discriminate HC.
        -- (* nothing visible at all *)
           rewrite HA1. rewrite HC2.
           cbn [translate_vals List.map List.rev List.app].
           rewrite HB3 in Hj. rewrite (join_stack_type_bot_l t3 t Hj).
           rewrite HC3. rewrite HA4.
           unfold type_update_select. cbn [CT_type CT_unr translate_st].
           cbn beta iota. reflexivity.
Qed.

(** The typing effect of an instruction that neither consults the context nor
    carries a body: [check_single] on it is a [type_update] with fixed operand
    lists. Every numeric operator is of this kind, which is what lets one step
    lemma per *stack shape* cover the whole numeric opcode block. *)
Definition plain_effect (be : basic_instruction)
                       (pops pushes : list value_type) : Prop :=
  forall C ct, check_single C (Some ct) be = type_update ct pops pushes.

(** The same, for an instruction whose typing does depend on the module context:
    [check_single] reads only fields [with_labels] leaves alone, so fixing [C0]
    is enough. Every context-dependent operator is of this kind. *)
Definition effect_in (C0 : t_context) (be : basic_instruction)
                     (pops pushes : list value_type) : Prop :=
  forall lbls ct,
    check_single (with_labels C0 lbls) (Some ct) be = type_update ct pops pushes.

Lemma plain_effect_in : forall C0 be pops pushes,
  plain_effect be pops pushes -> effect_in C0 be pops pushes.
Proof. intros C0 be pops pushes H lbls ct. apply H. Qed.

(** [read_binary]: pop two operands of the same type, push one result.
    WasmCert's [type_update ts [t; t] [tr]] consumes twice then produces once, so
    the two [consume] steps come from [pop_with_type_sim] and the [produce] from
    [translate_vals_snoc].

    Covers every binary operator and every comparison: the operand and result
    types are parameters, and the instruction is whatever the opcode table says,
    constrained only by its [plain_effect]. *)
Theorem step_binary : forall C0 st fs pre f opcode ty res be st',
  Inv C0 st fs -> fs = pre ++ [f] ->
  effect_in C0 be [translate_vt_v ty; translate_vt_v ty] [translate_vt_v res] ->
  opiter_read_binary st opcode ty res = Ok (Core_result_Result_Ok tt, st') ->
  exists seg',
    Inv C0 st'
        (pre ++ [{| fv_ctrl := fv_ctrl f;
                    fv_seg := seg';
                    fv_done := fv_done f ++ [be];
                    fv_then := fv_then f |}]).
Proof.
  intros C0 st fs pre f opcode ty res be st' Hinv Hfs Heff H. subst fs.
  unfold opiter_read_binary in H.
  (* prologue *)
  destruct (opiter_take_pending st opcode) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (take_pending_ok_inv st opcode st1 Htp) as Hobs.
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 _]].
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  (* first pop *)
  destruct (opiter_pop_with_type st1 ty) as [[r1 st2]|] eqn:Hp1;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [t1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (pop_with_type_sim st1 (List.concat (List.map fv_seg pre)) f
              ty t1 st2 Hsplit1 Hbase1 Hunr1 Hp1)
    as [seg1 [Hc2 [Hv2 Hcon1]]].
  (* second pop, on the frame with the shortened segment *)
  destruct (opiter_pop_with_type st2 ty) as [[r2 st3]|] eqn:Hp2;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [t2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (cur_views_ctrls st1 st2 Hc2) as [Hb2 Hu2].
  destruct (pop_with_type_sim st2 (List.concat (List.map fv_seg pre))
              {| fv_ctrl := fv_ctrl f; fv_seg := seg1; fv_done := fv_done f;
fv_then := fv_then f |}
              ty t2 st3)
    as [seg2 [Hc3 [Hv3 Hcon2]]].
  { cbn [fv_seg]. exact Hv2. }
  { cbn [fv_ctrl]. rewrite Hb2. exact Hbase1. }
  { cbn [fv_ctrl]. rewrite Hu2. exact Hunr1. }
  { exact Hp2. }
  cbn [fv_ct fv_seg fv_ctrl] in Hcon2.
  (* push *)
  destruct (opiter_push_val st3 (Opiter_StackType_Val res))
    as [st4|] eqn:Hpv; cbn [bind] in H; [|discriminate].
  (* the unit payload collapses, so injection yields one equation *)
  injection H as <-.
  destruct (push_val_spec _ _ _ Hpv) as [Hpvals [Hpctrls _]].
  exists (seg2 ++ [Opiter_StackType_Val res]).
  apply (Inv_step_last C0 st1 st4 pre f _ Hinv1).
  - reflexivity.
  - rewrite Hpctrls. rewrite Hc3. rewrite Hc2.
    destruct Hinv1 as [K1 _]. rewrite K1.
    rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hpvals. rewrite Hv3.
    rewrite List.map_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg]. rewrite List.app_nil_r.
    rewrite List.app_assoc. reflexivity.
  - apply frames_ok_append; [destruct Hinv1 as [_ [_ [_ K4]]]; exact K4|].
    intros lbls. rewrite Heff.
    unfold type_update.
    rewrite (consume_cons_split (fv_ct f) (translate_vt_v ty)
               [translate_vt_v ty]
               <<translate_vals seg1,
                 (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>> Hcon1).
    rewrite Hcon2. cbn [produce CT_type CT_unr].
    rewrite translate_vals_snoc. reflexivity.
Qed.

(** WasmCert guards [BI_binop] on the operator matching the type: an integer
    operator needs an integer type and a float operator a float type. Both hold
    by computation once the type is known, which is what the opcode table
    delivers. *)
Lemma plain_effect_binop : forall nt op,
  (match op with
   | Binop_i _ => is_int_t nt
   | Binop_f _ => is_float_t nt
   end) = true ->
  plain_effect (BI_binop nt op) [T_num nt; T_num nt] [T_num nt].
Proof.
  intros nt op Hg C ct. cbn [check_single].
  destruct op as [iop|fop]; rewrite Hg; reflexivity.
Qed.

Lemma plain_effect_relop : forall nt op,
  (match op with
   | Relop_i _ => is_int_t nt
   | Relop_f _ => is_float_t nt
   end) = true ->
  plain_effect (BI_relop nt op) [T_num nt; T_num nt] [T_num T_i32].
Proof.
  intros nt op Hg C ct. cbn [check_single].
  destruct op as [iop|fop]; rewrite Hg; reflexivity.
Qed.

(** [read_conversion]: pop one operand, push one result. The same proof as
    [step_binary] with one pop instead of two, and it covers the unary
    operators, [eqz] and every conversion. *)
Theorem step_conversion : forall C0 st fs pre f opcode from to be st',
  Inv C0 st fs -> fs = pre ++ [f] ->
  effect_in C0 be [translate_vt_v from] [translate_vt_v to] ->
  opiter_read_conversion st opcode from to
    = Ok (Core_result_Result_Ok tt, st') ->
  exists seg',
    Inv C0 st'
        (pre ++ [{| fv_ctrl := fv_ctrl f;
                    fv_seg := seg';
                    fv_done := fv_done f ++ [be];
                    fv_then := fv_then f |}]).
Proof.
  intros C0 st fs pre f opcode from to be st' Hinv Hfs Heff H. subst fs.
  unfold opiter_read_conversion in H.
  destruct (opiter_take_pending st opcode) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (take_pending_ok_inv st opcode st1 Htp) as Hobs.
  destruct (obs_fields st st1 Hobs) as [Hv1 [Hc1 _]].
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  destruct (opiter_pop_with_type st1 from) as [[r1 st2]|] eqn:Hp1;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [t1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (pop_with_type_sim st1 (List.concat (List.map fv_seg pre)) f
              from t1 st2 Hsplit1 Hbase1 Hunr1 Hp1)
    as [seg1 [Hc2 [Hv2 Hcon1]]].
  destruct (opiter_push_val st2 (Opiter_StackType_Val to))
    as [st3|] eqn:Hpv; cbn [bind] in H; [|discriminate].
  injection H as <-.
  destruct (push_val_spec _ _ _ Hpv) as [Hpvals [Hpctrls _]].
  exists (seg1 ++ [Opiter_StackType_Val to]).
  apply (Inv_step_last C0 st1 st3 pre f _ Hinv1).
  - reflexivity.
  - rewrite Hpctrls. rewrite Hc2.
    destruct Hinv1 as [K1 _]. rewrite K1.
    rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hpvals. rewrite Hv2.
    rewrite List.map_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg]. rewrite List.app_nil_r.
    rewrite List.app_assoc. reflexivity.
  - apply frames_ok_append; [destruct Hinv1 as [_ [_ [_ K4]]]; exact K4|].
    intros lbls. rewrite Heff. unfold type_update. rewrite Hcon1.
    cbn [produce CT_type CT_unr]. rewrite translate_vals_snoc. reflexivity.
Qed.

(** The three families [read_conversion] covers, each guarded by WasmCert the
    same way: the operator has to match the type it is applied at. *)
Lemma plain_effect_unop : forall nt op,
  (match op with
   | Unop_i _ => is_int_t nt
   | Unop_f _ => is_float_t nt
   | Unop_extend _ => is_int_t nt
   end) = true ->
  plain_effect (BI_unop nt op) [T_num nt] [T_num nt].
Proof.
  intros nt op Hg C ct. cbn [check_single].
  destruct op as [iop|fop|n]; rewrite Hg; reflexivity.
Qed.

Lemma plain_effect_testop : forall nt op,
  is_int_t nt = true ->
  plain_effect (BI_testop nt op) [T_num nt] [T_num T_i32].
Proof.
  intros nt op Hg C ct. cbn [check_single]. rewrite Hg. reflexivity.
Qed.

Lemma plain_effect_cvtop : forall t2 op t1 sx,
  cvtop_valid t2 op t1 sx = true ->
  plain_effect (BI_cvtop t2 op t1 sx) [T_num t1] [T_num t2].
Proof.
  intros t2 op t1 sx Hg C ct. cbn [check_single]. rewrite Hg. reflexivity.
Qed.

(** [frames_ok_append] with the frame's [Ctrl] allowed to change, provided its
    label does not. [ctrl_label] reads only [kind] and [block_type], so flipping
    [polymorphic_base] is invisible to it. That is what makes [unreachable]
    expressible: it is the one step that rewrites the frame itself. *)
Lemma frames_ok_append_ctrl : forall C0 labels pre f c' be seg',
  ctrl_label c' = ctrl_label (fv_ctrl f) ->
  c'.(opiter_Ctrl_kind) = (fv_ctrl f).(opiter_Ctrl_kind) ->
  c'.(opiter_Ctrl_block_type) = (fv_ctrl f).(opiter_Ctrl_block_type) ->
  frames_ok C0 labels (pre ++ [f]) ->
  (forall lbls,
     check_single (with_labels C0 (ctrl_label (fv_ctrl f) :: lbls))
                  (Some (fv_ct f)) be
       = Some <<translate_vals seg',
               c'.(opiter_Ctrl_polymorphic_base)>>) ->
  frames_ok C0 labels
    (pre ++ [{| fv_ctrl := c'; fv_seg := seg'; fv_done := fv_done f ++ [be];
      fv_then := fv_then f |}]).
Proof.
  intros C0 labels pre f c' be seg' Hlbl Hknd Hbt. revert labels.
  induction pre as [|g pre IH]; intros labels H Hstep.
  - simpl in H |- *. destruct H as [[Hfold Helse] _]. split; [split|exact I].
    + cbn [fv_ctrl fv_seg fv_done fv_ct] in *.
      rewrite Hlbl. rewrite List.fold_left_app. rewrite Hfold. simpl. apply Hstep.
    + unfold else_obligation in Helse |- *. cbn [fv_ctrl fv_then] in *.
      rewrite Hlbl. rewrite Hknd. rewrite Hbt. exact Helse.
  - simpl in H |- *. destruct H as [Hg Hrest]. split.
    + assert (Hk : (fv_ctrl f).(opiter_Ctrl_kind)
                   = (fv_ctrl {| fv_ctrl := c'; fv_seg := seg';
                                 fv_done := fv_done f ++ [be];
                                 fv_then := fv_then f |}).(opiter_Ctrl_kind)).
      { cbn [fv_ctrl]. symmetry. exact Hknd. }
      rewrite (frame_carry_snoc pre f _ Hk) in Hg. exact Hg.
    + apply IH; [exact Hrest | exact Hstep].
Qed.

(** [unreachable]: the frame's operands are discarded and it becomes polymorphic.
    WasmCert's [BI_unreachable] gives [<<nil, true>>], which is exactly the
    emptied segment with the flag set. *)
Theorem step_unreachable : forall C0 st fs pre f st',
  Inv C0 st fs -> fs = pre ++ [f] ->
  opiter_read_unreachable st = Ok (Core_result_Result_Ok tt, st') ->
  Inv C0 st'
      (pre ++ [{| fv_ctrl :=
                    {| opiter_Ctrl_kind := (fv_ctrl f).(opiter_Ctrl_kind);
                       opiter_Ctrl_block_type :=
                         (fv_ctrl f).(opiter_Ctrl_block_type);
                       opiter_Ctrl_value_stack_base :=
                         (fv_ctrl f).(opiter_Ctrl_value_stack_base);
                       opiter_Ctrl_polymorphic_base := true |};
                  fv_seg := [];
                  fv_done := fv_done f ++ [BI_unreachable];
                  fv_then := fv_then f |}]).
Proof.
  intros C0 st fs pre f st' Hinv Hfs H. subst fs.
  unfold opiter_read_unreachable in H.
  destruct (opiter_take_pending st opiter_op_unreachable) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (take_pending_ok_inv st opiter_op_unreachable st1 Htp) as Hobs.
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  assert (Hsnoc : vec_list st1.(opiter_OpIterState_ctrls)
                  = List.map fv_ctrl pre ++ [fv_ctrl f]).
  { destruct Hinv1 as [K1 _]. rewrite K1. rewrite List.map_app. reflexivity. }
  assert (Hle : (Z.to_nat (to_Z (fv_ctrl f).(opiter_Ctrl_value_stack_base))
                   <= List.length (vec_list st1.(opiter_OpIterState_vals)))%nat).
  { unfold cur_base_nat in Hbase1.
    rewrite (cur_ctrl_snoc st1 (List.map fv_ctrl pre) (fv_ctrl f) Hsnoc)
      in Hbase1.
    rewrite Hbase1. rewrite Hsplit1. rewrite List.app_length. lia. }
  (* the reader binds mark_unreachable's result before wrapping it *)
  destruct (opiter_mark_unreachable st1) as [st2|] eqn:Hmu; cbn [bind] in H;
    [|discriminate].
  injection H as <-.
  destruct (mark_unreachable_spec st1 st2 (List.map fv_ctrl pre) (fv_ctrl f)
              Hsnoc Hle Hmu) as [Hvals Hctrls].
  apply (Inv_step_last C0 st1 st2 pre f _ Hinv1).
  - reflexivity.
  - rewrite Hctrls. rewrite List.map_app. reflexivity.
  - rewrite Hvals.
    unfold cur_base_nat in Hbase1.
    rewrite (cur_ctrl_snoc st1 (List.map fv_ctrl pre) (fv_ctrl f) Hsnoc)
      in Hbase1.
    rewrite Hbase1. rewrite Hsplit1. rewrite List.firstn_app.
    rewrite List.firstn_all.
    assert (Hz : (List.length (List.concat (List.map fv_seg pre))
                  - List.length (List.concat (List.map fv_seg pre)))%nat
                 = 0%nat).
    { lia. }
    rewrite Hz.
    cbn [List.firstn]. rewrite List.app_nil_r.
    rewrite List.map_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg]. rewrite List.app_nil_r.
    rewrite List.app_nil_r. reflexivity.
  - apply (frames_ok_append_ctrl C0 [] pre f _ BI_unreachable []).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + destruct Hinv1 as [_ [_ [_ K4]]]. exact K4.
    + intros lbls. cbn [check_single]. reflexivity.
Qed.

(* ================================================================== *)
(** ** The memory and alignment checks                                 *)
(* ================================================================== *)

(** The module-level context correspondence. Fixed for the whole function body,
    so it is a hypothesis of the memory steps rather than part of the invariant,
    which only tracks what the readers change.

    One clause per context field the readers consult; the memory clause is the
    first of seven. *)
Definition mems_agree (module : env_Env_t) (C0 : t_context) : Prop :=
  tc_mems C0
    = List.map translate_memtype (vec_list module.(env_Env_mem_types)).

(** The locals clause. *)
Definition locals_agree (ctx : opiter_Context_t) (C0 : t_context) : Prop :=
  tc_locals C0
    = List.map translate_vt_v (vec_list ctx.(opiter_Context_locals)).

(** The bounds-checked lookup is WasmCert's [lookup_N] on the translated list. *)
Lemma local_type_lookup : forall ctx C0 idx t,
  locals_agree ctx C0 ->
  opiter_local_type ctx idx = Ok (Core_result_Result_Ok t) ->
  lookup_N (tc_locals C0) (Z.to_N (to_Z idx)) = Some (translate_vt_v t).
Proof.
  intros ctx C0 idx t Hag H. unfold opiter_local_type in H.
  destruct (scalar_cast U32 Usize idx) as [i|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  destruct (i s>= alloc_vec_Vec_len ctx.(opiter_Context_locals)) eqn:Hge;
    [discriminate|].
  rewrite vec_index_spec in H.
  destruct (List.nth_error (vec_list ctx.(opiter_Context_locals))
              (Z.to_nat (to_Z i))) as [vt|] eqn:Hnth; cbn [bind] in H;
    [|discriminate].
  injection H as Hvt. rewrite -Hvt.
  assert (Hi : to_Z i = to_Z idx).
  { unfold scalar_cast in Hcast. apply mk_scalar_ok_to_Z in Hcast. exact Hcast. }
  unfold lookup_N. rewrite Hag. rewrite N_to_nat_Z_to_N. rewrite -Hi.
  rewrite List.nth_error_map. rewrite Hnth. reflexivity.
Qed.

(** The converse, for the completeness direction: if WasmCert found a local
    there, so does the bounds check. *)
Lemma local_type_complete : forall ctx C0 (idx : scalar U32) xx,
  locals_agree ctx C0 ->
  lookup_N (tc_locals C0) (Z.to_N (to_Z idx)) = Some xx ->
  exists t, opiter_local_type ctx idx = Ok (Core_result_Result_Ok t)
            /\ translate_vt_v t = xx.
Proof.
  intros ctx C0 idx xx Hag Hlk. unfold opiter_local_type.
  destruct (scalar_cast_u32_usize idx) as [i [Hcast Hi]].
  rewrite Hcast. cbn [bind].
  unfold lookup_N in Hlk. rewrite Hag in Hlk. rewrite N_to_nat_Z_to_N in Hlk.
  rewrite List.nth_error_map in Hlk.
  destruct (List.nth_error (vec_list ctx.(opiter_Context_locals))
              (Z.to_nat (to_Z idx))) as [vt|] eqn:Hnth;
    cbn [option_map] in Hlk; [|discriminate].
  injection Hlk as Hxx.
  assert (Hlt : (Z.to_nat (to_Z idx)
                 < List.length (vec_list ctx.(opiter_Context_locals)))%nat).
  { apply List.nth_error_Some. rewrite Hnth. discriminate. }
  assert (Hge : (i s>= alloc_vec_Vec_len ctx.(opiter_Context_locals)) = false).
  { apply scalar_geb_of_lt.
    assert (Hlen : to_Z (alloc_vec_Vec_len ctx.(opiter_Context_locals))
                   = Z.of_nat (List.length
                       (vec_list ctx.(opiter_Context_locals))))
      by reflexivity.
    rewrite Hlen. rewrite Hi.
    (* [lia] does not see through [Z.to_nat], so cross over by hand *)
    pose proof (usize_nonneg i) as Hnn. rewrite Hi in Hnn.
    assert (Hz : Z.of_nat (Z.to_nat (to_Z idx)) = to_Z idx)
      by (apply Z2Nat.id; lia).
    assert (Hlt' : Z.of_nat (Z.to_nat (to_Z idx))
                   < Z.of_nat (List.length (vec_list
                       ctx.(opiter_Context_locals))))
      by (apply (proj1 (Nat2Z.inj_lt _ _)); exact Hlt).
    rewrite Hz in Hlt'. exact Hlt'. }
  rewrite Hge. rewrite vec_index_spec. rewrite Hi. rewrite Hnth. cbn [bind].
  exists vt. split; [reflexivity | exact Hxx].
Qed.

(** The globals clause. A global carries a mutability as well as a type, so
    this one agrees on whole [global_type]s. *)
Definition globals_agree (module : env_Env_t) (C0 : t_context) : Prop :=
  tc_globals C0
    = List.map translate_globaltype (vec_list module.(env_Env_global_types)).

Lemma global_type_lookup : forall module C0 idx g,
  globals_agree module C0 ->
  opiter_global_type module idx = Ok (Core_result_Result_Ok g) ->
  lookup_N (tc_globals C0) (Z.to_N (to_Z idx)) = Some (translate_globaltype g).
Proof.
  intros module C0 idx g Hag H. unfold opiter_global_type in H.
  destruct (scalar_cast U32 Usize idx) as [i|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  destruct (i s>= alloc_vec_Vec_len module.(env_Env_global_types)) eqn:Hge;
    [discriminate|].
  rewrite vec_index_spec in H.
  destruct (List.nth_error (vec_list module.(env_Env_global_types))
              (Z.to_nat (to_Z i))) as [gt|] eqn:Hnth; cbn [bind] in H;
    [|discriminate].
  injection H as Hgt. rewrite -Hgt.
  assert (Hi : to_Z i = to_Z idx).
  { unfold scalar_cast in Hcast. apply mk_scalar_ok_to_Z in Hcast. exact Hcast. }
  unfold lookup_N. rewrite Hag. rewrite N_to_nat_Z_to_N. rewrite -Hi.
  rewrite List.nth_error_map. rewrite Hnth. reflexivity.
Qed.

Lemma global_type_complete : forall module C0 (idx : scalar U32) xx,
  globals_agree module C0 ->
  lookup_N (tc_globals C0) (Z.to_N (to_Z idx)) = Some xx ->
  exists g, opiter_global_type module idx = Ok (Core_result_Result_Ok g)
            /\ translate_globaltype g = xx.
Proof.
  intros module C0 idx xx Hag Hlk. unfold opiter_global_type.
  destruct (scalar_cast_u32_usize idx) as [i [Hcast Hi]].
  rewrite Hcast. cbn [bind].
  unfold lookup_N in Hlk. rewrite Hag in Hlk. rewrite N_to_nat_Z_to_N in Hlk.
  rewrite List.nth_error_map in Hlk.
  destruct (List.nth_error (vec_list module.(env_Env_global_types))
              (Z.to_nat (to_Z idx))) as [gt|] eqn:Hnth;
    cbn [option_map] in Hlk; [|discriminate].
  injection Hlk as Hxx.
  assert (Hlt : (Z.to_nat (to_Z idx)
                 < List.length (vec_list module.(env_Env_global_types)))%nat).
  { apply List.nth_error_Some. rewrite Hnth. discriminate. }
  assert (Hge : (i s>= alloc_vec_Vec_len module.(env_Env_global_types))
                = false).
  { apply scalar_geb_of_lt.
    assert (Hlen : to_Z (alloc_vec_Vec_len module.(env_Env_global_types))
                   = Z.of_nat (List.length
                       (vec_list module.(env_Env_global_types))))
      by reflexivity.
    rewrite Hlen. rewrite Hi.
    pose proof (usize_nonneg i) as Hnn. rewrite Hi in Hnn.
    assert (Hz : Z.of_nat (Z.to_nat (to_Z idx)) = to_Z idx)
      by (apply Z2Nat.id; lia).
    assert (Hlt' : Z.of_nat (Z.to_nat (to_Z idx))
                   < Z.of_nat (List.length (vec_list
                       module.(env_Env_global_types))))
      by (apply (proj1 (Nat2Z.inj_lt _ _)); exact Hlt).
    rewrite Hz in Hlt'. exact Hlt'. }
  rewrite Hge. rewrite vec_index_spec. rewrite Hi. rewrite Hnth. cbn [bind].
  exists gt. split; [reflexivity | exact Hxx].
Qed.

(** The return clause. A body always has a result list, so unlike WasmCert's
    [tc_return] there is no absent case to cover. *)
Definition return_agree (ctx : opiter_Context_t) (C0 : t_context) : Prop :=
  tc_return C0
    = Some (translate_typelist (vec_list ctx.(opiter_Context_results))).

(** The three clauses the call operators consult. [translate_ft] already
    reverses each list, which is the form WasmCert's reversed context wants
    (Translate.v's comment on [context_reverse]). *)
Definition funcs_agree (module : env_Env_t) (C0 : t_context) : Prop :=
  tc_funcs C0
    = List.map translate_ft (vec_list module.(env_Env_func_types)).

Definition types_agree (module : env_Env_t) (C0 : t_context) : Prop :=
  tc_types C0
    = List.map translate_ft (vec_list module.(env_Env_types)).

Definition tables_agree (module : env_Env_t) (C0 : t_context) : Prop :=
  tc_tables C0
    = List.map translate_tabletype (vec_list module.(env_Env_table_types)).

(** What the completeness direction needs of the function types the two call
    operators reach: at most one result, because the reader rejects more. The
    module validator's to supply, and it disappears with the restriction that
    puts it there. *)
Definition ft_results_wasm10 (ft : types_FuncType_t) : Prop :=
  (List.length (vec_list ft.(types_FuncType_results)) <= 1)%nat.

Definition funcs_wasm10 (module : env_Env_t) : Prop :=
  forall ft, List.In ft (vec_list module.(env_Env_func_types)) ->
             ft_results_wasm10 ft.

Definition types_wasm10 (module : env_Env_t) : Prop :=
  forall ft, List.In ft (vec_list module.(env_Env_types)) ->
             ft_results_wasm10 ft.

(** [call] and [call_indirect] index different vectors of function types, so the
    lookup lemma is stated over the vector rather than over a context field. *)
Lemma ft_lookup : forall (v : alloc_vec_Vec types_FuncType_t) l
                         (idx : scalar U32) (i : usize) ft,
  l = List.map translate_ft (vec_list v) ->
  to_Z i = to_Z idx ->
  alloc_vec_Vec_index (core_slice_index_SliceIndexUsizeSliceInst types_FuncType_t)
    v i = Ok ft ->
  lookup_N l (Z.to_N (to_Z idx)) = Some (translate_ft ft).
Proof.
  intros v l idx i ft Hag Hi H. rewrite vec_index_spec in H.
  destruct (List.nth_error (vec_list v) (Z.to_nat (to_Z i))) as [x|] eqn:Hnth;
    [|discriminate].
  injection H as <-.
  unfold lookup_N. rewrite Hag. rewrite N_to_nat_Z_to_N. rewrite -Hi.
  rewrite List.nth_error_map. rewrite Hnth. reflexivity.
Qed.

Lemma ft_lookup_complete : forall (v : alloc_vec_Vec types_FuncType_t) l
                                  (idx : scalar U32) tf,
  l = List.map translate_ft (vec_list v) ->
  lookup_N l (Z.to_N (to_Z idx)) = Some tf ->
  exists i ft,
    scalar_cast U32 Usize idx = Ok i
    /\ to_Z i = to_Z idx
    /\ (i s>= alloc_vec_Vec_len v) = false
    /\ alloc_vec_Vec_index
         (core_slice_index_SliceIndexUsizeSliceInst types_FuncType_t) v i = Ok ft
    /\ List.In ft (vec_list v)
    /\ translate_ft ft = tf.
Proof.
  intros v l idx tf Hag Hlk.
  destruct (scalar_cast_u32_usize idx) as [i [Hcast Hi]].
  rewrite Hag in Hlk. unfold lookup_N in Hlk. rewrite N_to_nat_Z_to_N in Hlk.
  rewrite List.nth_error_map in Hlk.
  destruct (List.nth_error (vec_list v) (Z.to_nat (to_Z idx))) as [ft|] eqn:Hnth;
    cbn [option_map] in Hlk; [|discriminate].
  injection Hlk as Htf.
  assert (Hlt : (Z.to_nat (to_Z idx) < List.length (vec_list v))%nat).
  { apply List.nth_error_Some. rewrite Hnth. discriminate. }
  assert (Hge : (i s>= alloc_vec_Vec_len v) = false).
  { apply scalar_geb_of_lt. rewrite vec_len_spec. rewrite Hi.
    pose proof (usize_nonneg i) as Hnn. rewrite Hi in Hnn.
    assert (Hz : Z.of_nat (Z.to_nat (to_Z idx)) = to_Z idx)
      by (apply Z2Nat.id; lia).
    assert (Hlt' : Z.of_nat (Z.to_nat (to_Z idx))
                   < Z.of_nat (List.length (vec_list v)))
      by (apply (proj1 (Nat2Z.inj_lt _ _)); exact Hlt).
    rewrite Hz in Hlt'. exact Hlt'. }
  exists i, ft. split; [exact Hcast|]. split; [exact Hi|]. split; [exact Hge|].
  rewrite vec_index_spec. rewrite Hi. rewrite Hnth.
  split; [reflexivity|].
  split; [apply (List.nth_error_In _ _ Hnth) | exact Htf].
Qed.

(** WasmCert guards [BI_call] on the same lookup the bounds check performs, and
    the effect is the callee's signature. *)
Lemma effect_call : forall C0 x tn tm,
  lookup_N (tc_funcs C0) x = Some (Tf tn tm) ->
  effect_in C0 (BI_call x) tn tm.
Proof.
  intros C0 x tn tm Hlk lbls ct. cbn [check_single with_labels tc_funcs].
  rewrite Hlk. reflexivity.
Qed.

(** [call_indirect] consults the table as well, and Wasm 1.0's only element type
    is [funcref], which is what [translate_tabletype] records. *)
Lemma effect_call_indirect : forall C0 x y tabt tn tm,
  lookup_N (tc_tables C0) x = Some tabt ->
  tt_elem_type tabt = T_funcref ->
  lookup_N (tc_types C0) y = Some (Tf tn tm) ->
  effect_in C0 (BI_call_indirect x y) (T_num T_i32 :: tn) tm.
Proof.
  intros C0 x y tabt tn tm Htab Helem Hty lbls ct.
  cbn [check_single with_labels tc_tables tc_types].
  rewrite Htab. rewrite Helem. rewrite eqxx. rewrite Hty. reflexivity.
Qed.

(** Wasm 1.0 has one table, so the reader's emptiness check is WasmCert's
    lookup at index zero. *)
Lemma tables_nonempty_lookup : forall module C0,
  tables_agree module C0 ->
  vec_list module.(env_Env_table_types) <> [] ->
  exists tabt, lookup_N (tc_tables C0) 0%N = Some tabt
               /\ tt_elem_type tabt = T_funcref.
Proof.
  intros module C0 Hag Hne. unfold tables_agree in Hag. rewrite Hag.
  destruct (vec_list module.(env_Env_table_types)) as [|t ts];
    [exfalso; apply Hne; reflexivity|].
  cbn [List.map lookup_N]. exists (translate_tabletype t).
  split; [reflexivity | reflexivity].
Qed.

(** The mutability guard, both ways: the [Mut] the code matches on and the
    [is_mut] WasmCert tests are the same bit. *)
Lemma is_mut_of_var : forall g,
  g.(types_GlobalType_mutability) = Types_Mut_Var ->
  is_mut (translate_globaltype g) = true.
Proof.
  intros g H. unfold is_mut, translate_globaltype. cbn [tg_mut].
  rewrite H. reflexivity.
Qed.

Lemma var_of_is_mut : forall g,
  is_mut (translate_globaltype g) = true ->
  g.(types_GlobalType_mutability) = Types_Mut_Var.
Proof.
  intros g H. destruct (g.(types_GlobalType_mutability)) eqn:Hm;
    [|reflexivity].
  unfold is_mut, translate_globaltype in H. cbn [tg_mut] in H.
  rewrite Hm in H. discriminate.
Qed.

(** [require_memory] succeeding gives WasmCert its memory lookup. *)
Lemma require_memory_lookup : forall module C0,
  mems_agree module C0 ->
  opiter_require_memory module = Ok (Core_result_Result_Ok tt) ->
  exists m, lookup_N (tc_mems C0) 0%N = Some m.
Proof.
  intros module C0 Hag H. unfold opiter_require_memory in H.
  rewrite vec_is_empty_spec in H. cbn [bind] in H.
  destruct (vec_list module.(env_Env_mem_types)) as [|m ms] eqn:Hms;
    [discriminate|].
  unfold mems_agree in Hag. rewrite Hag. rewrite Hms.
  cbn [List.map lookup_N]. exists (translate_memtype m). reflexivity.
Qed.

(** The alignment check bounds the exponent. Turning that into WasmCert's
    [load_store_t_bounds] is left to each call site, where the natural
    alignment is a literal and the exponent ranges over a handful of values, so
    the obligation is discharged by computation. *)
Lemma check_memory_and_alignment_ok : forall module C0 memarg natural,
  mems_agree module C0 ->
  opiter_check_memory_and_alignment module memarg natural
    = Ok (Core_result_Result_Ok tt) ->
  (exists m, lookup_N (tc_mems C0) 0%N = Some m)
  /\ to_Z memarg.(opiter_MemArg_align) <= to_Z natural.
Proof.
  intros module C0 memarg natural Hag H.
  unfold opiter_check_memory_and_alignment in H.
  destruct (opiter_require_memory module) as [r|] eqn:Hrm; cbn [bind] in H;
    [|discriminate].
  destruct r as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (memarg.(opiter_MemArg_align) s> natural) eqn:Hgt; [discriminate|].
  split.
  - apply (require_memory_lookup module C0 Hag). exact Hrm.
  - apply scalar_gtb_false in Hgt. exact Hgt.
Qed.

(** The three local operators. WasmCert guards each on the same lookup the
    bounds check performs, and their effects are the three shapes already
    covered: push one, pop one, pop then push. *)
Lemma effect_local_get : forall C0 x t,
  lookup_N (tc_locals C0) x = Some t ->
  effect_in C0 (BI_local_get x) [] [t].
Proof.
  intros C0 x t Hlk lbls ct. cbn [check_single with_labels tc_locals].
  rewrite Hlk. reflexivity.
Qed.

Lemma effect_local_set : forall C0 x t,
  lookup_N (tc_locals C0) x = Some t ->
  effect_in C0 (BI_local_set x) [t] [].
Proof.
  intros C0 x t Hlk lbls ct. cbn [check_single with_labels tc_locals].
  rewrite Hlk. reflexivity.
Qed.

Lemma effect_local_tee : forall C0 x t,
  lookup_N (tc_locals C0) x = Some t ->
  effect_in C0 (BI_local_tee x) [t] [t].
Proof.
  intros C0 x t Hlk lbls ct. cbn [check_single with_labels tc_locals].
  rewrite Hlk. reflexivity.
Qed.

(** [local.get]: the prologue moves only the cursor, so the invariant transports
    to the state it left, and what remains is the push. *)
Theorem step_local_get : forall C0 ctx st fs pre f data idx st',
  Inv C0 st fs -> fs = pre ++ [f] -> locals_agree ctx C0 ->
  opiter_read_local_get st data ctx = Ok (Core_result_Result_Ok idx, st') ->
  exists t,
    Inv C0 st'
        (pre ++ [{| fv_ctrl := fv_ctrl f;
                    fv_seg := fv_seg f ++ [Opiter_StackType_Val t];
                    fv_done := fv_done f
                               ++ [BI_local_get (Z.to_N (to_Z idx))];
                               fv_then := fv_then f |}]).
Proof.
  intros C0 ctx st fs pre f data idx st' Hinv Hfs Hag H. subst fs.
  unfold opiter_read_local_get in H.
  destruct (opiter_take_local st data ctx opiter_op_local_get) as [[r0 st1]|]
    eqn:Htl; cbn [bind] in H; [|discriminate].
  destruct r0 as [[idx0 t]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val st1 (Opiter_StackType_Val t)) as [st2|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as Hidx <-. rewrite -Hidx.
  pose proof (take_local_type st data ctx _ idx0 t st1 Htl) as Hlt.
  pose proof (local_type_lookup ctx C0 idx0 t Hag Hlt) as Hlk.
  destruct (take_local_fields st data ctx _ _ st1 Htl) as [Hv1 Hc1].
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_fields C0 st st1 _ Hv1 Hc1 Hinv)).
  destruct (push_val_spec _ _ _ Hpv) as [Hpvals [Hpctrls _]].
  exists t.
  apply (Inv_step_last C0 st1 st2 pre f _ Hinv1).
  - reflexivity.
  - rewrite Hpctrls. destruct Hinv1 as [K1 _]. rewrite K1.
    rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hpvals. destruct Hinv1 as [_ [K2 _]]. rewrite K2.
    rewrite List.map_app. rewrite List.map_app.
    rewrite List.concat_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg].
    rewrite List.app_nil_r. rewrite List.app_nil_r.
    rewrite List.app_assoc. reflexivity.
  - apply frames_ok_append; [destruct Hinv1 as [_ [_ [_ K4]]]; exact K4|].
    intros lbls.
    rewrite (effect_local_get C0 (Z.to_N (to_Z idx0)) (translate_vt_v t) Hlk).
    unfold type_update. cbn [consume produce CT_type CT_unr].
    rewrite translate_vals_snoc. reflexivity.
Qed.

(** [local.set]: one typed pop, as [read_binary]'s first. *)
Theorem step_local_set : forall C0 ctx st fs pre f data idx st',
  Inv C0 st fs -> fs = pre ++ [f] -> locals_agree ctx C0 ->
  opiter_read_local_set st data ctx = Ok (Core_result_Result_Ok idx, st') ->
  exists seg',
    Inv C0 st'
        (pre ++ [{| fv_ctrl := fv_ctrl f;
                    fv_seg := seg';
                    fv_done := fv_done f
                               ++ [BI_local_set (Z.to_N (to_Z idx))];
                               fv_then := fv_then f |}]).
Proof.
  intros C0 ctx st fs pre f data idx st' Hinv Hfs Hag H. subst fs.
  unfold opiter_read_local_set in H.
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
  rewrite branch_ok in H. cbn [bind] in H. injection H as Hidx <-. rewrite -Hidx.
  pose proof (take_local_type st data ctx _ idx0 t st1 Htl) as Hlt.
  pose proof (local_type_lookup ctx C0 idx0 t Hag Hlt) as Hlk.
  destruct (take_local_fields st data ctx _ _ st1 Htl) as [Hv1 Hc1].
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_fields C0 st st1 _ Hv1 Hc1 Hinv)).
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  destruct (pop_with_type_sim st1 (List.concat (List.map fv_seg pre)) f
              t t1 st2 Hsplit1 Hbase1 Hunr1 Hp1) as [seg1 [Hc2 [Hv2 Hcon1]]].
  exists seg1.
  apply (Inv_step_last C0 st1 st2 pre f _ Hinv1).
  - reflexivity.
  - rewrite Hc2. destruct Hinv1 as [K1 _]. rewrite K1.
    rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hv2. rewrite List.map_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg]. rewrite List.app_nil_r. reflexivity.
  - apply frames_ok_append; [destruct Hinv1 as [_ [_ [_ K4]]]; exact K4|].
    intros lbls.
    rewrite (effect_local_set C0 (Z.to_N (to_Z idx0)) (translate_vt_v t) Hlk).
    unfold type_update. rewrite Hcon1. cbn [produce CT_type CT_unr].
    reflexivity.
Qed.

(** [local.tee]: pop then push, as [read_conversion]. *)
Theorem step_local_tee : forall C0 ctx st fs pre f data idx st',
  Inv C0 st fs -> fs = pre ++ [f] -> locals_agree ctx C0 ->
  opiter_read_local_tee st data ctx = Ok (Core_result_Result_Ok idx, st') ->
  exists seg' t,
    Inv C0 st'
        (pre ++ [{| fv_ctrl := fv_ctrl f;
                    fv_seg := seg' ++ [Opiter_StackType_Val t];
                    fv_done := fv_done f
                               ++ [BI_local_tee (Z.to_N (to_Z idx))];
                               fv_then := fv_then f |}]).
Proof.
  intros C0 ctx st fs pre f data idx st' Hinv Hfs Hag H. subst fs.
  unfold opiter_read_local_tee in H.
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
  injection H as Hidx <-. rewrite -Hidx.
  pose proof (take_local_type st data ctx _ idx0 t st1 Htl) as Hlt.
  pose proof (local_type_lookup ctx C0 idx0 t Hag Hlt) as Hlk.
  destruct (take_local_fields st data ctx _ _ st1 Htl) as [Hv1 Hc1].
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_fields C0 st st1 _ Hv1 Hc1 Hinv)).
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  destruct (pop_with_type_sim st1 (List.concat (List.map fv_seg pre)) f
              t t1 st2 Hsplit1 Hbase1 Hunr1 Hp1) as [seg1 [Hc2 [Hv2 Hcon1]]].
  destruct (push_val_spec _ _ _ Hpv) as [Hpvals [Hpctrls _]].
  exists seg1, t.
  apply (Inv_step_last C0 st1 st3 pre f _ Hinv1).
  - reflexivity.
  - rewrite Hpctrls. rewrite Hc2. destruct Hinv1 as [K1 _]. rewrite K1.
    rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hpvals. rewrite Hv2.
    rewrite List.map_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg]. rewrite List.app_nil_r.
    rewrite List.app_assoc. reflexivity.
  - apply frames_ok_append; [destruct Hinv1 as [_ [_ [_ K4]]]; exact K4|].
    intros lbls.
    rewrite (effect_local_tee C0 (Z.to_N (to_Z idx0)) (translate_vt_v t) Hlk).
    unfold type_update. rewrite Hcon1. cbn [produce CT_type CT_unr].
    rewrite translate_vals_snoc. reflexivity.
Qed.

(** The two global operators. Their effects are [local.get]'s and
    [local.set]'s; what is new is that [global.set]'s typing sits behind
    [is_mut], which is outside the [type_update] and so applies in unreachable
    code too. *)
Lemma effect_global_get : forall C0 x g,
  lookup_N (tc_globals C0) x = Some g ->
  effect_in C0 (BI_global_get x) [] [tg_t g].
Proof.
  intros C0 x g Hlk lbls ct. cbn [check_single with_labels tc_globals].
  rewrite Hlk. reflexivity.
Qed.

Lemma effect_global_set : forall C0 x g,
  lookup_N (tc_globals C0) x = Some g -> is_mut g = true ->
  effect_in C0 (BI_global_set x) [tg_t g] [].
Proof.
  intros C0 x g Hlk Hmut lbls ct. cbn [check_single with_labels tc_globals].
  rewrite Hlk. rewrite Hmut. reflexivity.
Qed.

(** [global.get]: the push, as [local.get]. *)
Theorem step_global_get : forall C0 module st fs pre f data idx st',
  Inv C0 st fs -> fs = pre ++ [f] -> globals_agree module C0 ->
  opiter_read_global_get st data module = Ok (Core_result_Result_Ok idx, st') ->
  exists t,
    Inv C0 st'
        (pre ++ [{| fv_ctrl := fv_ctrl f;
                    fv_seg := fv_seg f ++ [Opiter_StackType_Val t];
                    fv_done := fv_done f
                               ++ [BI_global_get (Z.to_N (to_Z idx))];
                               fv_then := fv_then f |}]).
Proof.
  intros C0 module st fs pre f data idx st' Hinv Hfs Hag H. subst fs.
  unfold opiter_read_global_get in H.
  destruct (opiter_take_global st data module opiter_op_global_get) as [[r0 st1]|]
    eqn:Htg; cbn [bind] in H; [|discriminate].
  destruct r0 as [[idx0 g]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_val st1
              (Opiter_StackType_Val g.(types_GlobalType_valtype))) as [st2|]
    eqn:Hpv; cbn [bind] in H; [|discriminate].
  injection H as Hidx <-. rewrite -Hidx.
  pose proof (take_global_type st data module _ idx0 g st1 Htg) as Hgt.
  pose proof (global_type_lookup module C0 idx0 g Hag Hgt) as Hlk.
  destruct (take_global_fields st data module _ _ st1 Htg) as [Hv1 Hc1].
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_fields C0 st st1 _ Hv1 Hc1 Hinv)).
  destruct (push_val_spec _ _ _ Hpv) as [Hpvals [Hpctrls _]].
  exists g.(types_GlobalType_valtype).
  apply (Inv_step_last C0 st1 st2 pre f _ Hinv1).
  - reflexivity.
  - rewrite Hpctrls. destruct Hinv1 as [K1 _]. rewrite K1.
    rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hpvals. destruct Hinv1 as [_ [K2 _]]. rewrite K2.
    rewrite List.map_app. rewrite List.map_app.
    rewrite List.concat_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg].
    rewrite List.app_nil_r. rewrite List.app_nil_r.
    rewrite List.app_assoc. reflexivity.
  - apply frames_ok_append; [destruct Hinv1 as [_ [_ [_ K4]]]; exact K4|].
    intros lbls.
    rewrite (effect_global_get C0 (Z.to_N (to_Z idx0))
               (translate_globaltype g) Hlk).
    unfold type_update. cbn [consume produce CT_type CT_unr tg_t
                             translate_globaltype].
    rewrite translate_vals_snoc. reflexivity.
Qed.

(** [global.set]: one typed pop, behind the mutability guard. *)
Theorem step_global_set : forall C0 module st fs pre f data idx st',
  Inv C0 st fs -> fs = pre ++ [f] -> globals_agree module C0 ->
  opiter_read_global_set st data module = Ok (Core_result_Result_Ok idx, st') ->
  exists seg',
    Inv C0 st'
        (pre ++ [{| fv_ctrl := fv_ctrl f;
                    fv_seg := seg';
                    fv_done := fv_done f
                               ++ [BI_global_set (Z.to_N (to_Z idx))];
                               fv_then := fv_then f |}]).
Proof.
  intros C0 module st fs pre f data idx st' Hinv Hfs Hag H. subst fs.
  unfold opiter_read_global_set in H.
  destruct (opiter_take_global st data module opiter_op_global_set) as [[r0 st1]|]
    eqn:Htg; cbn [bind] in H; [|discriminate].
  destruct r0 as [[idx0 g]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (g.(types_GlobalType_mutability)) eqn:Hm; [discriminate|].
  destruct (opiter_pop_with_type st1 g.(types_GlobalType_valtype))
    as [[r1 st2]|] eqn:Hp1; cbn [bind] in H; [|discriminate].
  destruct r1 as [t1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H. injection H as Hidx <-. rewrite -Hidx.
  pose proof (take_global_type st data module _ idx0 g st1 Htg) as Hgt.
  pose proof (global_type_lookup module C0 idx0 g Hag Hgt) as Hlk.
  destruct (take_global_fields st data module _ _ st1 Htg) as [Hv1 Hc1].
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_fields C0 st st1 _ Hv1 Hc1 Hinv)).
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  destruct (pop_with_type_sim st1 (List.concat (List.map fv_seg pre)) f
              g.(types_GlobalType_valtype) t1 st2 Hsplit1 Hbase1 Hunr1 Hp1)
    as [seg1 [Hc2 [Hv2 Hcon1]]].
  exists seg1.
  apply (Inv_step_last C0 st1 st2 pre f _ Hinv1).
  - reflexivity.
  - rewrite Hc2. destruct Hinv1 as [K1 _]. rewrite K1.
    rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hv2. rewrite List.map_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg]. rewrite List.app_nil_r. reflexivity.
  - apply frames_ok_append; [destruct Hinv1 as [_ [_ [_ K4]]]; exact K4|].
    intros lbls.
    rewrite (effect_global_set C0 (Z.to_N (to_Z idx0))
               (translate_globaltype g) Hlk (is_mut_of_var g Hm)).
    unfold type_update.
    cbn [tg_t translate_globaltype]. rewrite Hcon1.
    cbn [produce CT_type CT_unr]. reflexivity.
Qed.

(** [load]: consume an i32 address, produce the loaded type. One
    [pop_with_type_sim] and one push, with the memory and alignment obligations
    discharged by the bridge lemmas.

    [load_store_t_bounds] is a hypothesis rather than derived here: at each call
    site the natural alignment is a literal and the exponent ranges over at most
    four values, so it falls to computation. *)
Theorem step_load :
  forall C0 st fs pre f data module opcode ty natural nt tp_sx m st',
  Inv C0 st fs -> fs = pre ++ [f] ->
  mems_agree module C0 ->
  translate_vt_v ty = T_num nt ->
  (forall a, 0 <= a <= to_Z natural ->
     load_store_t_bounds (Z.to_N a) (option_projl tp_sx) nt = true) ->
  opiter_read_load st data module opcode ty natural
    = Ok (Core_result_Result_Ok m, st') ->
  exists seg',
    Inv C0 st'
        (pre ++ [{| fv_ctrl := fv_ctrl f;
                    fv_seg := seg' ++ [Opiter_StackType_Val ty];
                    fv_done :=
                      fv_done f
                      ++ [BI_load nt tp_sx
                            (Z.to_N (to_Z m.(opiter_MemArg_align)))
                            (Z.to_N (to_Z m.(opiter_MemArg_offset)))];
                            fv_then := fv_then f |}]).
Proof.
  intros C0 st fs pre f data module opcode ty natural nt tp_sx m st'
         Hinv Hfs Hmems Hty Hbounds H. subst fs.
  unfold opiter_read_load in H.
  (* prologue *)
  destruct (opiter_take_pending st opcode) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (take_pending_ok_inv st opcode st1 Htp) as Hobs.
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  (* immediates: only the cursor moves *)
  destruct (opiter_read_memarg st1 data) as [[r1 st2]|] eqn:Hma;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [m0|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (read_memarg_state st1 data m0 st2 Hma) as [Hmv Hmc].
  assert (Hinv2 : Inv C0 st2 (pre ++ [f])).
  { apply (Inv_fields C0 st1 st2 _); [rewrite Hmv | rewrite Hmc |];
      try reflexivity. exact Hinv1. }
  (* memory and alignment *)
  destruct (opiter_check_memory_and_alignment module m0 natural) as [r2|] eqn:Hck;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (check_memory_and_alignment_ok module C0 m0 natural Hmems Hck)
    as [[mem Hlookup] Halign].
  (* the address pop *)
  destruct (Inv_split C0 st2 pre f Hinv2) as [Hbase2 [Hsplit2 Hunr2]].
  destruct (opiter_pop_with_type st2 Types_ValueType_I32) as [[r3 st3]|] eqn:Hp;
    cbn [bind] in H; [|discriminate].
  destruct r3 as [t3|e3].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (pop_with_type_sim st2 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 t3 st3 Hsplit2 Hbase2 Hunr2 Hp)
    as [seg1 [Hc3 [Hv3 Hcon]]].
  (* the push *)
  destruct (opiter_push_val st3 (Opiter_StackType_Val ty)) as [st4|] eqn:Hpv;
    cbn [bind] in H; [|discriminate].
  injection H as Hmeq <-.
  destruct (push_val_spec _ _ _ Hpv) as [Hpvals [Hpctrls _]].
  exists seg1.
  apply (Inv_step_last C0 st2 st4 pre f _ Hinv2).
  - reflexivity.
  - rewrite Hpctrls. rewrite Hc3. destruct Hinv2 as [K1 _]. rewrite K1.
    rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hpvals. rewrite Hv3.
    rewrite List.map_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg]. rewrite List.app_nil_r.
    rewrite List.app_assoc. reflexivity.
  - apply frames_ok_append; [destruct Hinv2 as [_ [_ [_ K4]]]; exact K4|].
    intros lbls. cbn [check_single].
    rewrite <- Hmeq. rewrite Hlookup.
    rewrite (Hbounds (to_Z m0.(opiter_MemArg_align)));
      [| split; [apply u32_nonneg | exact Halign]].
    unfold type_update. rewrite Hcon. cbn [produce CT_type CT_unr].
    rewrite translate_vals_snoc. cbn [translate_st]. rewrite Hty. reflexivity.
Qed.

(** [store]: consume the value then the i32 address, produce nothing. The Rust
    pops [ty] before [i32] and WasmCert's
    [type_update ts [T_num nt; T_num T_i32] []] consumes in the same order, so
    the two [consume] steps line up directly. *)
Theorem step_store :
  forall C0 st fs pre f data module opcode ty natural nt tp m st',
  Inv C0 st fs -> fs = pre ++ [f] ->
  mems_agree module C0 ->
  translate_vt_v ty = T_num nt ->
  (forall a, 0 <= a <= to_Z natural -> load_store_t_bounds (Z.to_N a) tp nt
                                       = true) ->
  opiter_read_store st data module opcode ty natural
    = Ok (Core_result_Result_Ok m, st') ->
  exists seg',
    Inv C0 st'
        (pre ++ [{| fv_ctrl := fv_ctrl f;
                    fv_seg := seg';
                    fv_done :=
                      fv_done f
                      ++ [BI_store nt tp
                            (Z.to_N (to_Z m.(opiter_MemArg_align)))
                            (Z.to_N (to_Z m.(opiter_MemArg_offset)))];
                            fv_then := fv_then f |}]).
Proof.
  intros C0 st fs pre f data module opcode ty natural nt tp m st'
         Hinv Hfs Hmems Hty Hbounds H. subst fs.
  unfold opiter_read_store in H.
  destruct (opiter_take_pending st opcode) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (take_pending_ok_inv st opcode st1 Htp) as Hobs.
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  destruct (opiter_read_memarg st1 data) as [[r1 st2]|] eqn:Hma;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [m0|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (read_memarg_state st1 data m0 st2 Hma) as [Hmv Hmc].
  assert (Hinv2 : Inv C0 st2 (pre ++ [f])).
  { apply (Inv_fields C0 st1 st2 _); [rewrite Hmv | rewrite Hmc |];
      try reflexivity. exact Hinv1. }
  destruct (opiter_check_memory_and_alignment module m0 natural) as [r2|] eqn:Hck;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (check_memory_and_alignment_ok module C0 m0 natural Hmems Hck)
    as [[mem Hlookup] Halign].
  destruct (Inv_split C0 st2 pre f Hinv2) as [Hbase2 [Hsplit2 Hunr2]].
  (* first pop: the stored value *)
  destruct (opiter_pop_with_type st2 ty) as [[r3 st3]|] eqn:Hp1;
    cbn [bind] in H; [|discriminate].
  destruct r3 as [t3|e3].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (pop_with_type_sim st2 (List.concat (List.map fv_seg pre)) f
              ty t3 st3 Hsplit2 Hbase2 Hunr2 Hp1)
    as [seg1 [Hc3 [Hv3 Hcon1]]].
  (* second pop: the address *)
  destruct (opiter_pop_with_type st3 Types_ValueType_I32) as [[r4 st4]|] eqn:Hp2;
    cbn [bind] in H; [|discriminate].
  destruct r4 as [t4|e4].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (cur_views_ctrls st2 st3 Hc3) as [Hb3 Hu3].
  destruct (pop_with_type_sim st3 (List.concat (List.map fv_seg pre))
              {| fv_ctrl := fv_ctrl f; fv_seg := seg1; fv_done := fv_done f;
fv_then := fv_then f |}
              Types_ValueType_I32 t4 st4)
    as [seg2 [Hc4 [Hv4 Hcon2]]].
  { cbn [fv_seg]. exact Hv3. }
  { cbn [fv_ctrl]. rewrite Hb3. exact Hbase2. }
  { cbn [fv_ctrl]. rewrite Hu3. exact Hunr2. }
  { exact Hp2. }
  cbn [fv_ct fv_seg fv_ctrl] in Hcon2.
  injection H as Hmeq <-.
  exists seg2.
  apply (Inv_step_last C0 st2 st4 pre f _ Hinv2).
  - reflexivity.
  - rewrite Hc4. rewrite Hc3. destruct Hinv2 as [K1 _]. rewrite K1.
    rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hv4.
    rewrite List.map_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg]. rewrite List.app_nil_r. reflexivity.
  - apply frames_ok_append; [destruct Hinv2 as [_ [_ [_ K4]]]; exact K4|].
    intros lbls. cbn [check_single].
    rewrite <- Hmeq. rewrite Hlookup.
    rewrite (Hbounds (to_Z m0.(opiter_MemArg_align)));
      [| split; [apply u32_nonneg | exact Halign]].
    unfold type_update.
    rewrite (consume_cons_split (fv_ct f) (T_num nt) [T_num T_i32]
               <<translate_vals seg1,
                 (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>>);
      [| rewrite <- Hty; exact Hcon1].
    rewrite Hcon2. cbn [produce CT_type CT_unr]. reflexivity.
Qed.

(* ================================================================== *)
(** ** Control steps: entering a block                                 *)
(* ================================================================== *)

(** WasmCert's [upd_label] is [with_labels]: both rebuild the record leaving
    every field but the labels alone. *)
Lemma upd_label_with_labels : forall C lbls,
  upd_label C lbls = with_labels C lbls.
Proof. intros C lbls. reflexivity. Qed.

(** The labels in scope after walking [fs] outermost-first. By the innermost
    frame this is [tc_labels (ctx_at C0 st)]. *)
Fixpoint labels_after (labels : list (list value_type)) (fs : list fview)
  : list (list value_type) :=
  match fs with
  | [] => labels
  | f :: rest => labels_after (ctrl_label (fv_ctrl f) :: labels) rest
  end.

(** Pushing a frame leaves every existing frame's obligation alone, since they are
    walked before it, and adds one of its own. *)
(** Appending [g] at the very end of a list can only disturb [frame_carry] of
    the element right before it (the one whose "next frame" *becomes* [g]);
    everything deeper is untouched, since [frame_carry] only ever looks one
    frame ahead. A [g] that does not itself demand a carry -- every existing
    caller, since [Then] is the only kind that does -- disturbs nothing at
    all. *)
Lemma frame_carry_app_r : forall fs g,
  frame_carry [g] = [] ->
  frame_carry (fs ++ [g]) = frame_carry fs.
Proof.
  intros fs g Hg. destruct fs as [|h fs]; [exact Hg | reflexivity].
Qed.

Lemma frames_ok_snoc : forall C0 labels fs g,
  frame_carry [g] = [] ->
  frames_ok C0 labels fs ->
  List.fold_left
    (check_single (with_labels C0 (ctrl_label (fv_ctrl g)
                                  :: labels_after labels fs)))
    (fv_done g) (Some <<[], false>>) = Some (fv_ct g) ->
  else_obligation C0 (ctrl_label (fv_ctrl g) :: labels_after labels fs) g ->
  frames_ok C0 labels (fs ++ [g]).
Proof.
  intros C0 labels fs g Hgc. revert labels.
  induction fs as [|h fs IH]; intros labels H Hg Helse; simpl in H |- *.
  - split; [split; [exact Hg | exact Helse] | exact I].
  - destruct H as [Hh Hrest]. split.
    + rewrite (frame_carry_app_r fs g Hgc). exact Hh.
    + apply IH; assumption.
Qed.

(** Appending past the head cannot change the carry, which lets [step_if]'s
    push (lengthening the tail from [[f]] to [f' :: [g]]) reuse
    [frame_carry_snoc]'s "same kind" argument instead of needing [g] itself to
    have any particular carry. *)
Lemma frame_carry_head : forall x rest, frame_carry (x :: rest) = frame_carry [x].
Proof. intros x rest. reflexivity. Qed.

Lemma frame_carry_app_hd : forall fs f f' rest,
  (fv_ctrl f).(opiter_Ctrl_kind) = (fv_ctrl f').(opiter_Ctrl_kind) ->
  frame_carry (fs ++ [f]) = frame_carry (fs ++ f' :: rest).
Proof.
  intros fs f f' rest Hk. destruct fs as [|h fs]; cbn [app].
  - rewrite (frame_carry_head f' rest). unfold frame_carry. rewrite Hk.
    reflexivity.
  - reflexivity.
Qed.

(** [step_if]'s push: unlike [frames_ok_snoc], the frame right below the new
    one ([f]) does not keep its old obligation verbatim -- [read_if] already
    popped the condition from it, eagerly, so its ledger is one [i32] short of
    [fv_ct f] until [end] eventually supplies [BI_if]'s own pop. [Hcon], from
    [pop_with_type_sim], is exactly that missing consume step: [f]'s *old*
    fold (from [carry = []], since it used to be the last frame) becomes the
    witness [ct0] the *new* carry-based conjunct asks for. *)
Lemma frames_ok_snoc_if : forall C0 labels fs f seg' g,
  (fv_ctrl g).(opiter_Ctrl_kind) = Opiter_LabelKind_Then ->
  frames_ok C0 labels (fs ++ [f]) ->
  consume (fv_ct f) [T_num T_i32]
    = Some <<translate_vals seg', (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>> ->
  List.fold_left
    (check_single (with_labels C0 (ctrl_label (fv_ctrl g)
                     :: labels_after labels
                          (fs ++ [{| fv_ctrl := fv_ctrl f; fv_seg := seg';
                                     fv_done := fv_done f;
                                     fv_then := fv_then f |}]))))
    (fv_done g) (Some <<[], false>>) = Some (fv_ct g) ->
  frames_ok C0 labels
    (fs ++ [{| fv_ctrl := fv_ctrl f; fv_seg := seg'; fv_done := fv_done f;
               fv_then := fv_then f |}] ++ [g]).
Proof.
  intros C0 labels fs f seg' g Hgk. revert labels.
  induction fs as [|h fs IH]; intros labels H Hcon Hg; simpl in H |- *.
  - destruct H as [[Hf Helse] _].
    split; [split|].
    + cbn [frame_carry fv_ctrl]. rewrite Hgk.
      exists (fv_ct f). split; [exact Hf|]. cbn [fv_ctrl] in Hcon. exact Hcon.
    + unfold else_obligation in Helse |- *. cbn [fv_ctrl fv_then] in *.
      exact Helse.
    + split; [split|exact I].
      * cbn [frame_carry]. exact Hg.
      * unfold else_obligation. rewrite Hgk. exact I.
  - destruct H as [Hh Hrest]. split.
    + assert (Hk : (fv_ctrl f).(opiter_Ctrl_kind)
                   = (fv_ctrl {| fv_ctrl := fv_ctrl f; fv_seg := seg';
                                 fv_done := fv_done f; fv_then := fv_then f |})
                       .(opiter_Ctrl_kind)) by reflexivity.
      rewrite (frame_carry_app_hd fs f
                 {| fv_ctrl := fv_ctrl f; fv_seg := seg'; fv_done := fv_done f;
                    fv_then := fv_then f |} [g] Hk) in Hh.
      exact Hh.
    + apply IH; assumption.
Qed.

Lemma bases_ok_from_snoc : forall n fs g,
  bases_ok_from n fs ->
  Z.to_nat (to_Z (fv_ctrl g).(opiter_Ctrl_value_stack_base))
    = (n + List.length (List.concat (List.map fv_seg fs)))%nat ->
  bases_ok_from n (fs ++ [g]).
Proof.
  intros n fs g. revert n.
  induction fs as [|h fs IH]; intros n H Hb; simpl in H |- *.
  - split; [|exact I]. rewrite Hb. simpl. lia.
  - destruct H as [Hh Hrest]. split; [exact Hh|].
    apply IH; [exact Hrest|]. rewrite Hb.
    cbn [List.map List.concat]. rewrite List.app_length. lia.
Qed.

(** A freshly pushed frame owns nothing and has consumed nothing, so its
    obligation is trivial. *)
Lemma frames_ok_fresh_obligation : forall C0 lbls kind bt base,
  List.fold_left (check_single (with_labels C0 lbls)) []
                 (Some <<[], false>>)
    = Some (fv_ct {| fv_ctrl :=
                       {| opiter_Ctrl_kind := kind;
                          opiter_Ctrl_block_type := bt;
                          opiter_Ctrl_value_stack_base := base;
                          opiter_Ctrl_polymorphic_base := false |};
                     fv_seg := []; fv_done := [];
                     fv_then := [] |}).
Proof. intros. reflexivity. Qed.

(** Entering a block or a loop: the operand array is untouched, a frame is
    pushed recording the array's length as its base, and the frame's obligation
    is trivially satisfied. The kind is what decides whether the frame's label is
    its results or its parameters, and that is [ctrl_target]'s business. *)
Lemma Inv_push_frame : forall C0 st st' fs kind bt,
  kind <> Opiter_LabelKind_Then ->
  kind <> Opiter_LabelKind_Else ->
  Inv C0 st fs ->
  opiter_push_ctrl st kind bt = Ok st' ->
  Inv C0 st'
      (fs ++ [{| fv_ctrl :=
                   {| opiter_Ctrl_kind := kind;
                      opiter_Ctrl_block_type := bt;
                      opiter_Ctrl_value_stack_base :=
                        alloc_vec_Vec_len st.(opiter_OpIterState_vals);
                      opiter_Ctrl_polymorphic_base := false |};
                 fv_seg := [];
                 fv_done := [];
                 fv_then := [] |}]).
Proof.
  intros C0 st st' fs kind bt Hknd Hknd2 Hinv Hpc.
  destruct (push_ctrl_spec st kind bt st' Hpc) as [Hv Hc].
  destruct Hinv as [K1 [K2 [K3 K4]]].
  unfold Inv. repeat split.
  - rewrite Hc. rewrite K1. rewrite List.map_app. reflexivity.
  - rewrite Hv. rewrite K2. rewrite List.map_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg].
    repeat rewrite List.app_nil_r. reflexivity.
  - apply bases_ok_from_snoc; [exact K3|].
    cbn [fv_ctrl opiter_Ctrl_value_stack_base].
    rewrite vec_len_spec. rewrite K2. lia.
  - apply frames_ok_snoc.
    + cbn [frame_carry fv_ctrl opiter_Ctrl_kind].
      destruct kind; [reflexivity | reflexivity | reflexivity | |].
      * exfalso. apply Hknd. reflexivity.
      * exfalso. apply Hknd2. reflexivity.
    + exact K4.
    + apply frames_ok_fresh_obligation.
    + unfold else_obligation. cbn [fv_ctrl opiter_Ctrl_kind].
      destruct kind; try exact I. exfalso. apply Hknd2. reflexivity.
Qed.

(** Entering a block. The frame's label will be its results, because
    [ctrl_target] sends [Block] there, matching WasmCert's
    [upd_label C ([tm] ++ tc_labels C)]. *)
Theorem step_block : forall C0 st fs data bt st',
  Inv C0 st fs ->
  opiter_read_block st data = Ok (Core_result_Result_Ok bt, st') ->
  exists base,
    Inv C0 st'
        (fs ++ [{| fv_ctrl :=
                     {| opiter_Ctrl_kind := Opiter_LabelKind_Block;
                        opiter_Ctrl_block_type := bt;
                        opiter_Ctrl_value_stack_base := base;
                        opiter_Ctrl_polymorphic_base := false |};
                   fv_seg := [];
                   fv_done := [];
                   fv_then := [] |}]).
Proof.
  intros C0 st fs data bt st' Hinv H. unfold opiter_read_block in H.
  destruct (opiter_take_pending st opiter_op_block) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (take_pending_ok_inv st opiter_op_block st1 Htp) as Hobs.
  assert (Hinv1 : Inv C0 st1 fs) by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  destruct (opiter_read_block_type data st1.(opiter_OpIterState_pos))
    as [r1|] eqn:Hbt; cbn [bind] in H; [|discriminate].
  destruct r1 as [[bt0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  (* the block type read moves only the cursor *)
  destruct (opiter_push_ctrl _ Opiter_LabelKind_Block bt0) as [st2|] eqn:Hpc;
    cbn [bind] in H; [|discriminate].
  injection H as Hbteq <-.
  eexists. rewrite <- Hbteq.
  (* the intermediate state is st1 with the cursor advanced past the block type *)
  apply (Inv_push_frame C0
           {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
              opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
              opiter_OpIterState_pos := p1;
              opiter_OpIterState_pending := st1.(opiter_OpIterState_pending) |}
           st2 fs Opiter_LabelKind_Block bt0); [discriminate | discriminate | | exact Hpc].
  apply (Inv_fields C0 st1 _ fs); [reflexivity | reflexivity | exact Hinv1].
Qed.

(** Entering a loop. Identical apart from the kind, which is what makes the
    frame's label its parameters instead of its results. *)
Theorem step_loop : forall C0 st fs data bt st',
  Inv C0 st fs ->
  opiter_read_loop st data = Ok (Core_result_Result_Ok bt, st') ->
  exists base,
    Inv C0 st'
        (fs ++ [{| fv_ctrl :=
                     {| opiter_Ctrl_kind := Opiter_LabelKind_Loop;
                        opiter_Ctrl_block_type := bt;
                        opiter_Ctrl_value_stack_base := base;
                        opiter_Ctrl_polymorphic_base := false |};
                   fv_seg := [];
                   fv_done := [];
                   fv_then := [] |}]).
Proof.
  intros C0 st fs data bt st' Hinv H. unfold opiter_read_loop in H.
  destruct (opiter_take_pending st opiter_op_loop) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (take_pending_ok_inv st opiter_op_loop st1 Htp) as Hobs.
  assert (Hinv1 : Inv C0 st1 fs) by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  destruct (opiter_read_block_type data st1.(opiter_OpIterState_pos))
    as [r1|] eqn:Hbt; cbn [bind] in H; [|discriminate].
  destruct r1 as [[bt0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_ctrl _ Opiter_LabelKind_Loop bt0) as [st2|] eqn:Hpc;
    cbn [bind] in H; [|discriminate].
  injection H as Hbteq <-.
  eexists. rewrite <- Hbteq.
  (* the intermediate state is st1 with the cursor advanced past the block type *)
  apply (Inv_push_frame C0
           {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
              opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
              opiter_OpIterState_pos := p1;
              opiter_OpIterState_pending := st1.(opiter_OpIterState_pending) |}
           st2 fs Opiter_LabelKind_Loop bt0); [discriminate | discriminate | | exact Hpc].
  apply (Inv_fields C0 st1 _ fs); [reflexivity | reflexivity | exact Hinv1].
Qed.

(** Entering an [if]'s then-branch. Unlike [block]/[loop], [read_if] pops the
    condition from the *enclosing* frame before pushing the new one, eagerly,
    since the condition must be gone from the visible stack before the
    then-branch runs. [frames_ok_snoc_if] is built exactly for the
    consequence: the enclosing frame's own conjunct picks up [frame_carry]'s
    [i32], discharged by [pop_with_type_sim]'s [consume] fact, rather than
    staying the direct equation [block]/[loop] leave it at. *)
Theorem step_if : forall C0 st fs pre f data bt st',
  Inv C0 st fs -> fs = pre ++ [f] ->
  opiter_read_if st data = Ok (Core_result_Result_Ok bt, st') ->
  exists seg' base,
    Inv C0 st'
        (pre ++ [{| fv_ctrl := fv_ctrl f; fv_seg := seg'; fv_done := fv_done f;
                    fv_then := fv_then f |}]
            ++ [{| fv_ctrl :=
                     {| opiter_Ctrl_kind := Opiter_LabelKind_Then;
                        opiter_Ctrl_block_type := bt;
                        opiter_Ctrl_value_stack_base := base;
                        opiter_Ctrl_polymorphic_base := false |};
                   fv_seg := []; fv_done := []; fv_then := [] |}]).
Proof.
  intros C0 st fs pre f data bt st' Hinv Hfs H. subst fs.
  unfold opiter_read_if in H.
  destruct (opiter_take_pending st opiter_op_if) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (take_pending_ok_inv st opiter_op_if st1 Htp) as Hobs.
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  destruct (opiter_read_block_type data st1.(opiter_OpIterState_pos))
    as [r1|] eqn:Hbt; cbn [bind] in H; [|discriminate].
  destruct r1 as [[bt0 p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  assert (Hinv1' : Inv C0
             {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                opiter_OpIterState_pos := p1;
                opiter_OpIterState_pending := st1.(opiter_OpIterState_pending) |}
             (pre ++ [f])).
  { apply (Inv_fields C0 st1 _ (pre ++ [f])); [reflexivity | reflexivity
    | exact Hinv1]. }
  destruct (opiter_pop_with_type
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending := st1.(opiter_OpIterState_pending)
              |} Types_ValueType_I32) as [[r2 st2]|] eqn:Hpw;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [t2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (opiter_push_ctrl st2 Opiter_LabelKind_Then bt0) as [st3|] eqn:Hpc;
    cbn [bind] in H; [|discriminate].
  injection H as Hbteq <-.
  destruct (Inv_split C0 _ pre f Hinv1') as [Hbase1 [Hsplit1 Hunr1]].
  destruct (pop_with_type_sim _ (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 t2 st2 Hsplit1 Hbase1 Hunr1 Hpw)
    as [seg' [Hc2 [Hv2 Hcon]]].
  exists seg', (alloc_vec_Vec_len st2.(opiter_OpIterState_vals)).
  rewrite <- Hbteq.
  destruct Hinv1' as [K1 [K2 [K3 K4]]].
  unfold Inv. repeat split.
  - destruct (push_ctrl_spec st2 Opiter_LabelKind_Then bt0 st3 Hpc) as [_ Hc3].
    rewrite Hc3. rewrite Hc2. rewrite K1.
    rewrite List.map_app. rewrite List.map_app. rewrite <- List.app_assoc.
    reflexivity.
  - destruct (push_ctrl_spec st2 Opiter_LabelKind_Then bt0 st3 Hpc) as [Hv3 _].
    rewrite Hv3. rewrite Hv2.
    rewrite List.map_app. rewrite List.map_app.
    rewrite List.concat_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg]. repeat rewrite List.app_nil_r.
    reflexivity.
  - rewrite List.app_assoc.
    apply (bases_ok_from_snoc 0
             (pre ++ [{| fv_ctrl := fv_ctrl f; fv_seg := seg';
                         fv_done := fv_done f; fv_then := fv_then f |}])).
    + apply (bases_ok_from_last 0 pre f); [reflexivity|]. exact K3.
    + cbn [fv_ctrl opiter_Ctrl_value_stack_base]. rewrite vec_len_spec.
      rewrite Hv2. rewrite List.map_app. rewrite List.concat_app.
      cbn [List.map List.concat fv_seg]. rewrite List.app_nil_r.
      rewrite List.app_length. lia.
  - assert (Hgk : (fv_ctrl {| fv_ctrl :=
                                {| opiter_Ctrl_kind := Opiter_LabelKind_Then;
                                   opiter_Ctrl_block_type := bt0;
                                   opiter_Ctrl_value_stack_base :=
                                     alloc_vec_Vec_len
                                       st2.(opiter_OpIterState_vals);
                                   opiter_Ctrl_polymorphic_base := false |};
                              fv_seg := []; fv_done := []; fv_then := [] |})
                     .(opiter_Ctrl_kind) = Opiter_LabelKind_Then)
      by reflexivity.
    apply (frames_ok_snoc_if C0 [] pre f seg' _ Hgk K4 Hcon).
    apply (frames_ok_fresh_obligation C0 _
             Opiter_LabelKind_Then bt0
             (alloc_vec_Vec_len st2.(opiter_OpIterState_vals))).
Qed.

(* ================================================================== *)
(** ** Control steps: leaving a block                                  *)
(* ================================================================== *)

(** The accumulated labels are the frames' labels innermost-first, which is
    exactly what [ctx_at] builds. *)
Lemma labels_after_rev : forall fs labels,
  labels_after labels fs
    = List.rev (List.map (fun f => ctrl_label (fv_ctrl f)) fs) ++ labels.
Proof.
  induction fs as [|f fs IH]; intros labels; simpl; [reflexivity|].
  rewrite IH. rewrite <- List.app_assoc. reflexivity.
Qed.

(** [frames_ok_append] with the labels instantiated to the ones actually in
    scope. The universally quantified version suffices for instructions that
    ignore labels, but [br] and [end] both inspect them. *)
Lemma frames_ok_append_at : forall C0 labels pre f be seg',
  frames_ok C0 labels (pre ++ [f]) ->
  check_single (with_labels C0 (ctrl_label (fv_ctrl f)
                               :: labels_after labels pre))
              (Some (fv_ct f)) be
    = Some <<translate_vals seg',
            (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>> ->
  frames_ok C0 labels
    (pre ++ [{| fv_ctrl := fv_ctrl f;
                fv_seg := seg';
                fv_done := fv_done f ++ [be];
                fv_then := fv_then f |}]).
Proof.
  intros C0 labels pre f be seg'. revert labels.
  induction pre as [|g pre IH]; intros labels H Hstep; simpl in H |- *.
  - destruct H as [[Hfold Helse] _]. split; [split|exact I].
    + cbn [fv_ctrl fv_seg fv_done fv_ct] in *.
      rewrite List.fold_left_app. rewrite Hfold. simpl. exact Hstep.
    + cbn [fv_ctrl fv_then] in *. exact Helse.
  - destruct H as [Hg Hrest]. split.
    + assert (Hk : (fv_ctrl f).(opiter_Ctrl_kind)
                   = (fv_ctrl {| fv_ctrl := fv_ctrl f; fv_seg := seg';
                                 fv_done := fv_done f ++ [be];
                                 fv_then := fv_then f |}).(opiter_Ctrl_kind))
        by reflexivity.
      rewrite (frame_carry_snoc pre f _ Hk) in Hg. exact Hg.
    + apply IH; [exact Hrest | exact Hstep].
Qed.

(** The converse of [frames_ok_snoc]: the innermost frame's obligation can be
    read back out. This is what makes [end] work, because that obligation is
    precisely the inner [b_e_type_checker] that [BI_block] demands. *)
Lemma frames_ok_last : forall C0 labels fs g,
  frame_carry [g] = [] ->
  frames_ok C0 labels (fs ++ [g]) ->
  frames_ok C0 labels fs
  /\ List.fold_left
       (check_single (with_labels C0 (ctrl_label (fv_ctrl g)
                                     :: labels_after labels fs)))
       (fv_done g) (Some <<[], false>>) = Some (fv_ct g)
  /\ else_obligation C0 (ctrl_label (fv_ctrl g) :: labels_after labels fs) g.
Proof.
  intros C0 labels fs g Hgc. revert labels.
  induction fs as [|h fs IH]; intros labels H; simpl in H |- *.
  - destruct H as [[Hg Helse] _]. split; [exact I | split; assumption].
  - destruct H as [Hh Hrest]. destruct (IH _ Hrest) as [Hfs [Hg Helse]].
    split; [split; [rewrite (frame_carry_app_r fs g Hgc) in Hh; exact Hh
                    | exact Hfs] | split; assumption].
Qed.

(** The heart of [end]: the closed frame's [frames_ok] obligation *is* the inner
    [b_e_type_checker] that [BI_block] demands.

    [ctrl_label] of a [Block] frame is its results, so the inner context
    [with_labels C0 (ctrl_label g :: lbls)] is exactly WasmCert's
    [upd_label C ([tm] ++ tc_labels C)]. That correspondence is what the whole
    ghost-list design exists to deliver.

    [c_types_agree] is a hypothesis; [step_end_block] discharges it from the
    fact that the results were popped and the segment then found empty. *)
Lemma end_block_typing : forall C0 lbls f g bt,
  (fv_ctrl g).(opiter_Ctrl_block_type) = bt ->
  (fv_ctrl g).(opiter_Ctrl_kind) = Opiter_LabelKind_Block ->
  List.fold_left
    (check_single (with_labels C0 (ctrl_label (fv_ctrl g) :: lbls)))
    (fv_done g) (Some <<[], false>>) = Some (fv_ct g) ->
  c_types_agree (fv_ct g) (translate_typelist (block_results_of bt)) = true ->
  check_single (with_labels C0 lbls) (Some (fv_ct f))
               (BI_block (translate_bt bt) (fv_done g))
    = Some <<translate_typelist (block_results_of bt)
             ++ translate_vals (fv_seg f),
             (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>>.
Proof.
  intros C0 lbls f g bt Hbt Hkind Hfold Hagree.
  (* [ctrl_label] of a Block frame is its results *)
  assert (Hlbl : ctrl_label (fv_ctrl g)
                 = translate_typelist (block_results_of bt)).
  { unfold ctrl_label, ctrl_target, branch_target_bt_of. rewrite Hkind.
    rewrite Hbt. destruct bt; reflexivity. }
  rewrite Hlbl in Hfold.
  cbn [check_single].
  (* expand_t on a Wasm 1.0 block type gives no parameters *)
  destruct bt as [|vt]; cbn [translate_bt block_results_of expand_t
                             translate_typelist List.map List.rev].
  - rewrite Hfold. rewrite Hagree.
    unfold type_update, produce. cbn [consume CT_type CT_unr]. reflexivity.
  - rewrite Hfold. rewrite Hagree.
    unfold type_update, produce. cbn [consume CT_type CT_unr]. reflexivity.
Qed.

(** The Loop sibling. A loop's label is its *parameters*, which Wasm 1.0 leaves
    empty, so the inner context differs from [end_block_typing]'s: WasmCert asks
    for [upd_label C ([tn] ++ tc_labels C)] with [tn = nil]. The results
    obligation is the same, since [b_e_type_checker] still ends by comparing
    against [tm]. *)
Lemma end_loop_typing : forall C0 lbls f g bt,
  (fv_ctrl g).(opiter_Ctrl_block_type) = bt ->
  (fv_ctrl g).(opiter_Ctrl_kind) = Opiter_LabelKind_Loop ->
  List.fold_left
    (check_single (with_labels C0 (ctrl_label (fv_ctrl g) :: lbls)))
    (fv_done g) (Some <<[], false>>) = Some (fv_ct g) ->
  c_types_agree (fv_ct g) (translate_typelist (block_results_of bt)) = true ->
  check_single (with_labels C0 lbls) (Some (fv_ct f))
               (BI_loop (translate_bt bt) (fv_done g))
    = Some <<translate_typelist (block_results_of bt)
             ++ translate_vals (fv_seg f),
             (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>>.
Proof.
  intros C0 lbls f g bt Hbt Hkind Hfold Hagree.
  (* a Loop frame's label is its parameters, and Wasm 1.0 has none *)
  assert (Hlbl : ctrl_label (fv_ctrl g) = []).
  { unfold ctrl_label, ctrl_target, branch_target_bt_of. rewrite Hkind.
    reflexivity. }
  rewrite Hlbl in Hfold.
  cbn [check_single].
  destruct bt as [|vt]; cbn [translate_bt block_results_of expand_t
                             translate_typelist List.map List.rev].
  - rewrite Hfold. rewrite Hagree.
    unfold type_update, produce. cbn [consume CT_type CT_unr]. reflexivity.
  - rewrite Hfold. rewrite Hagree.
    unfold type_update, produce. cbn [consume CT_type CT_unr]. reflexivity.
Qed.

(** The labels a frame sees are its own consed onto the enclosing ones. Moving
    across this is what lets a step lemma state its obligation in terms of
    [labels_after [] pre] while [frames_ok_last] hands it back in terms of
    [labels_after [] (pre ++ [f])]. *)
Lemma labels_after_snoc : forall labels fs g,
  labels_after labels (fs ++ [g])
    = ctrl_label (fv_ctrl g) :: labels_after labels fs.
Proof.
  intros labels fs g. rewrite labels_after_rev. rewrite labels_after_rev.
  rewrite List.map_app. rewrite List.rev_app_distr. reflexivity.
Qed.

(* ================================================================== *)
(** ** Switching a [Then] to an [Else]                                 *)
(* ================================================================== *)

(** The innermost frame's own obligation, read back regardless of what it is:
    unlike [frames_ok_last], this does not also hand back [frames_ok C0
    labels fs], so it needs no hypothesis about [frame_carry [g]] at all --
    [g]'s own conjunct is always the direct equation, since nothing follows
    it. This is exactly what [read_else] needs of the [Then] it is about to
    rewrite in place, whose carry is *not* [[]]. *)
Lemma frames_ok_last_fold : forall C0 labels fs g,
  frames_ok C0 labels (fs ++ [g]) ->
  List.fold_left (check_single (with_labels C0 (ctrl_label (fv_ctrl g)
                     :: labels_after labels fs)))
    (fv_done g) (Some <<[], false>>) = Some (fv_ct g)
  /\ else_obligation C0 (ctrl_label (fv_ctrl g) :: labels_after labels fs) g.
Proof.
  intros C0 labels fs g. revert labels.
  induction fs as [|h fs IH]; intros labels H; cbn [List.app] in H.
  - destruct H as [[Hg Helse] _]. cbn [frame_carry] in Hg. exact (conj Hg Helse).
  - destruct H as [_ Hrest]. apply IH. exact Hrest.
Qed.

(** Replacing the head by one with the same carry -- a [Then] becoming an
    [Else], since both demand [[T_num T_i32]] -- cannot change it. *)
Lemma frame_carry_replace1 : forall pre g g',
  frame_carry [g] = frame_carry [g'] ->
  frame_carry (pre ++ [g]) = frame_carry (pre ++ [g']).
Proof. intros pre g g' Heq. destruct pre as [|h pre]; [exact Heq | reflexivity]. Qed.

(** [read_else] rewrites the innermost frame in place: same position, same
    carry (a [Then] and an [Else] both demand [[T_num T_i32]] of whatever
    encloses them), so every enclosing frame's conjunct carries over
    unchanged and only the rewritten frame's own obligation needs supplying. *)
Lemma frames_ok_replace_last : forall C0 labels pre g g',
  frame_carry [g] = frame_carry [g'] ->
  frames_ok C0 labels (pre ++ [g]) ->
  List.fold_left (check_single (with_labels C0 (ctrl_label (fv_ctrl g')
                     :: labels_after labels pre)))
    (fv_done g') (Some <<[], false>>) = Some (fv_ct g') ->
  else_obligation C0 (ctrl_label (fv_ctrl g') :: labels_after labels pre) g' ->
  frames_ok C0 labels (pre ++ [g']).
Proof.
  intros C0 labels pre g g' Hgc. revert labels.
  induction pre as [|h pre IH]; intros labels H Hfold Helse;
    cbn [List.app] in H |- *.
  - split; [split; [exact Hfold | exact Helse] | exact I].
  - destruct H as [Hh Hrest]. split.
    + rewrite (frame_carry_replace1 pre g g' Hgc) in Hh. exact Hh.
    + apply IH; assumption.
Qed.


(* ================================================================== *)
(** ** Closing a [Then] or an [Else]                                   *)
(* ================================================================== *)

(** The pair right at the end of a frame list -- [f] carrying the carry that
    the open [g] (a [Then] or an [Else]) imposes on it, and [g]'s own two
    obligations. Unlike [frames_ok_last], this does not hand back
    [frames_ok C0 labels fs]: with [f] itself possibly a [Then] or an [Else]
    (nested [if]s), what the frame *before* [f] owes depends on [f]'s kind,
    which is exactly what [frames_ok_close_if] threads through instead of
    reconstructing here. *)
Lemma frames_ok_last_two_if : forall C0 labels fs f g,
  (fv_ctrl g).(opiter_Ctrl_kind) = Opiter_LabelKind_Then
  \/ (fv_ctrl g).(opiter_Ctrl_kind) = Opiter_LabelKind_Else ->
  frames_ok C0 labels (fs ++ [f] ++ [g]) ->
  (exists ct0,
     List.fold_left (check_single (with_labels C0 (ctrl_label (fv_ctrl f)
                        :: labels_after labels fs)))
       (fv_done f) (Some <<[], false>>) = Some ct0
     /\ consume ct0 [T_num T_i32] = Some (fv_ct f))
  /\ else_obligation C0 (ctrl_label (fv_ctrl f) :: labels_after labels fs) f
  /\ List.fold_left (check_single (with_labels C0 (ctrl_label (fv_ctrl g)
                        :: ctrl_label (fv_ctrl f) :: labels_after labels fs)))
       (fv_done g) (Some <<[], false>>) = Some (fv_ct g)
  /\ else_obligation C0 (ctrl_label (fv_ctrl g)
                          :: ctrl_label (fv_ctrl f) :: labels_after labels fs) g.
Proof.
  intros C0 labels fs f g Hkind. revert labels.
  induction fs as [|h fs IH]; intros labels H; cbn [List.app] in H |- *.
  - destruct H as [[Hf Helsef] [[Hg Helseg] _]].
    assert (Hc : frame_carry [g] = [T_num T_i32]).
    { cbn [frame_carry]. destruct Hkind as [Hk|Hk]; rewrite Hk; reflexivity. }
    rewrite Hc in Hf. repeat split; assumption.
  - destruct H as [_ Hrest]. apply IH. exact Hrest.
Qed.

(** Replacing the tail past the head -- [[f] ++ [g]] becoming [[f']] -- cannot
    change it either, as long as the new head keeps the old head's kind. This
    is what lets [frames_ok_close_if] rebuild every frame enclosing [f] without
    caring whether [f] itself is a [Then] or an [Else]. *)
Lemma frame_carry_replace_tail : forall pre f f' g,
  fv_ctrl f' = fv_ctrl f ->
  frame_carry (pre ++ [f] ++ [g]) = frame_carry (pre ++ [f']).
Proof.
  intros pre f f' g Hk. destruct pre as [|h pre]; cbn [List.app].
  - unfold frame_carry. rewrite Hk. reflexivity.
  - reflexivity.
Qed.

(** The [end] counterpart of [frames_ok_snoc_if]: closing the [Then]/[Else]
    at the top of the frame list collapses the last two frames, [f] and [g],
    into one, [f']. Every frame enclosing [f] keeps its own conjunct
    verbatim -- [frame_carry_replace_tail] is what lets the induction see
    through the collapse -- so only [f']'s own obligation needs to be
    supplied, already assembled by [end_if_typing]. *)
Lemma frames_ok_close_if : forall C0 labels pre f g f',
  fv_ctrl f' = fv_ctrl f ->
  frames_ok C0 labels (pre ++ [f] ++ [g]) ->
  List.fold_left (check_single (with_labels C0 (ctrl_label (fv_ctrl f)
                     :: labels_after labels pre)))
    (fv_done f') (Some <<[], false>>) = Some (fv_ct f') ->
  else_obligation C0 (ctrl_label (fv_ctrl f) :: labels_after labels pre) f' ->
  frames_ok C0 labels (pre ++ [f']).
Proof.
  intros C0 labels pre f g f' Hk. revert labels.
  induction pre as [|h pre IH]; intros labels H Hfold Helse;
    cbn [List.app labels_after frame_carry] in H, Hfold, Helse |- *.
  - cbn [frames_ok frame_carry]. rewrite Hk.
    split; [split; [exact Hfold | exact Helse] | exact I].
  - destruct H as [Hh Hrest]. split.
    + rewrite (frame_carry_replace_tail pre f f' g Hk) in Hh. exact Hh.
    + apply IH; assumption.
Qed.

(** The heart of closing an [if]: [BI_if]'s own type rule, mirroring
    [end_block_typing]/[end_loop_typing], but starting from [ct0] rather
    than [fv_ct f] -- [read_if] already popped the condition eagerly, so
    [BI_if]'s own consume of it (folded into [Hcon0]) is what brings [ct0]
    back down to [fv_ct f] before the two bodies' results get produced.
    Stated directly over both bodies' own obligations, exactly
    [check_single]'s own [BI_if] case, rather than through [ctrl_label] of
    some frame: the then- and else-bodies are not always a frame's [fv_done]
    -- the bare-[Then]-at-[end] case supplies [[::]] for the else-body,
    which owns no frame at all. [tn = [::]] throughout, since Wasm 1.0 block
    types carry no parameters. *)
Lemma end_if_typing : forall C0 lbls f bt then_body else_body ct_then ct_else ct0,
  List.fold_left
    (check_single (with_labels C0 (translate_typelist (block_results_of bt)
                                    :: lbls)))
    then_body (Some <<[], false>>) = Some ct_then ->
  c_types_agree ct_then (translate_typelist (block_results_of bt)) = true ->
  List.fold_left
    (check_single (with_labels C0 (translate_typelist (block_results_of bt)
                                    :: lbls)))
    else_body (Some <<[], false>>) = Some ct_else ->
  c_types_agree ct_else (translate_typelist (block_results_of bt)) = true ->
  consume ct0 [T_num T_i32] = Some (fv_ct f) ->
  check_single (with_labels C0 lbls) (Some ct0)
               (BI_if (translate_bt bt) then_body else_body)
    = Some <<translate_typelist (block_results_of bt)
             ++ translate_vals (fv_seg f),
             (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>>.
Proof.
  intros C0 lbls f bt then_body else_body ct_then ct_else ct0
    Hfold Hagree Hfold2 Hagree2 Hcon0.
  cbn [check_single].
  destruct bt as [|vt]; cbn [translate_bt block_results_of expand_t
                             translate_typelist List.map List.rev];
    rewrite Hfold; rewrite Hagree; rewrite Hfold2; rewrite Hagree2;
    cbn [andb]; unfold type_update; rewrite Hcon0;
    unfold produce; cbn [CT_type CT_unr]; reflexivity.
Qed.

(* ================================================================== *)
(** ** Popping and pushing a type list                                 *)
(* ================================================================== *)

Lemma translate_typelist_nil : translate_typelist [] = [].
Proof. reflexivity. Qed.

Lemma translate_typelist_one : forall vt,
  translate_typelist [vt] = [translate_vt_v vt].
Proof. intros vt. reflexivity. Qed.

(** [translate_typelist] is written with mathcomp's [rev] and [map], since
    [Translate.v] imports [seq]; everything here is written with the standard
    library's. They are the same functions but not the same constants, and an
    [ssreflect] rewrite matches on the head symbol, so the bridge has to be
    explicit. Once stated, the [List] lemmas apply to type lists of any length. *)
Lemma cat_app : forall {A} (l m : list A), seq.cat l m = List.app l m.
Proof.
  induction l as [|h t IH]; intros m; [reflexivity|]. cbn. rewrite IH.
  reflexivity.
Qed.

Lemma seq_map_map : forall {A B} (f : A -> B) l, seq.map f l = List.map f l.
Proof.
  induction l as [|h t IH]; [reflexivity|]. cbn. rewrite IH. reflexivity.
Qed.

Lemma seq_rev_rev : forall {A} (l : list A), seq.rev l = List.rev l.
Proof.
  induction l as [|h t IH]; [reflexivity|].
  rewrite rev_cons -cats1 cat_app IH. reflexivity.
Qed.

Lemma translate_typelist_list : forall l,
  translate_typelist l = List.rev (List.map translate_vt_v l).
Proof.
  intros l. unfold translate_typelist. rewrite seq_rev_rev seq_map_map.
  reflexivity.
Qed.

(** The reversal again: the Rust reads a type list left to right, WasmCert
    consumes it head first, so the last type read is the first consumed. *)
Lemma translate_typelist_snoc : forall l vt,
  translate_typelist (l ++ [vt]) = translate_vt_v vt :: translate_typelist l.
Proof.
  intros l vt. rewrite !translate_typelist_list. rewrite List.map_app.
  rewrite List.rev_unit. reflexivity.
Qed.

(** The operand-stack segment a block's results occupy. Wasm 1.0 block types
    carry at most one, so this is the whole story. *)
Definition results_seg (bt : opiter_BlockType_t) : list opiter_StackType_t :=
  match bt with
  | Opiter_BlockType_Empty => []
  | Opiter_BlockType_Value vt => [Opiter_StackType_Val vt]
  end.

Lemma translate_vals_results : forall seg bt,
  translate_vals (seg ++ results_seg bt)
    = translate_typelist (block_results_of bt) ++ translate_vals seg.
Proof.
  intros seg bt. destruct bt as [|vt]; cbn [results_seg block_results_of].
  - rewrite List.app_nil_r. rewrite translate_typelist_nil. reflexivity.
  - rewrite translate_vals_snoc. rewrite translate_typelist_one.
    cbn [translate_st]. reflexivity.
Qed.

(** The operand segment a type list occupies, and the two algebraic facts about
    it: appending a segment prepends its types on WasmCert's side, since the two
    stacks grow in opposite directions. *)
Definition types_seg (l : list types_ValueType_t) : list opiter_StackType_t :=
  List.map Opiter_StackType_Val l.

Lemma translate_vals_app : forall a b,
  translate_vals (a ++ b) = translate_vals b ++ translate_vals a.
Proof.
  intros a b. unfold translate_vals. rewrite List.map_app.
  rewrite List.rev_app_distr. reflexivity.
Qed.

Lemma translate_vals_types_seg : forall l,
  translate_vals (types_seg l) = translate_typelist l.
Proof.
  intros l. rewrite translate_typelist_list.
  unfold translate_vals, types_seg. rewrite List.map_map. reflexivity.
Qed.

(** [pop_types] counts the index down and pops [types[i-1]] first, so the loop
    from index [i] is [consume] over the first [i] types -- reversed, which is
    what [translate_typelist] already does.

    Like [pop_with_type_sim], which it chains, this is deliberately *not* stated
    over [Inv]: a pop on its own breaks [frames_ok], since the frame's
    [checker_type] has moved but its ghost list has not. *)
Lemma pop_types_loop_sim : forall n st pre_seg f (s : slice types_ValueType_t)
                                  (i : usize) st',
  Z.to_nat (to_Z i) = n ->
  (n <= List.length (vec_list s))%nat ->
  vec_list st.(opiter_OpIterState_vals) = pre_seg ++ fv_seg f ->
  cur_base_nat st = List.length pre_seg ->
  cur_unr st = (fv_ctrl f).(opiter_Ctrl_polymorphic_base) ->
  opiter_pop_types_loop st s i = Ok (Core_result_Result_Ok tt, st') ->
  exists seg',
    vec_list st'.(opiter_OpIterState_ctrls)
      = vec_list st.(opiter_OpIterState_ctrls)
    /\ vec_list st'.(opiter_OpIterState_vals) = pre_seg ++ seg'
    /\ consume (fv_ct f) (translate_typelist (List.firstn n (vec_list s)))
       = Some <<translate_vals seg',
                (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>>.
Proof.
  induction n as [|n IH];
    intros st pre_seg f s i st' Hi Hlen Hsplit Hbase Hunr H;
    unfold opiter_pop_types_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H.
  - (* the index is zero, so the loop stops and nothing has been popped *)
    assert (Hz : (i s= 0%usize) = true).
    { apply scalar_eqb_zero_true. pose proof (usize_nonneg i). lia. }
    rewrite Hz in H. cbn beta iota in H. injection H as <-.
    exists (fv_seg f). split; [reflexivity|]. split; [exact Hsplit|].
    cbn [List.firstn]. unfold fv_ct. reflexivity.
  - assert (Hpos : 0 < to_Z i) by (pose proof (usize_nonneg i); lia).
    assert (Hz : (i s= 0%usize) = false) by (apply scalar_eqb_zero_false; lia).
    rewrite Hz in H. cbn beta iota in H.
    destruct (usize_sub_1_ok i) as [i2 [Hsub Hi2]]; [lia|].
    rewrite Hsub in H. cbn [bind] in H.
    rewrite slice_index_usize_spec in H.
    assert (Hidx : Z.to_nat (to_Z i2) = n) by (rewrite Hi2; lia).
    rewrite Hidx in H.
    destruct (List.nth_error (vec_list s) n) as [vt|] eqn:Hnth;
      cbn [bind] in H; [|discriminate].
    destruct (opiter_pop_with_type st vt) as [[r0 st0]|] eqn:Hp;
      cbn [bind] in H; [|discriminate].
    destruct r0 as [t|e].
    2: { rewrite branch_err in H. cbn [bind] in H.
         rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (pop_with_type_sim st pre_seg f vt t st0 Hsplit Hbase Hunr Hp)
      as [seg0 [Hc0 [Hv0 Hcon0]]].
    (* the same frame with the shortened segment, so the pops chain *)
    pose (f0 := {| fv_ctrl := fv_ctrl f;
                   fv_seg := seg0;
                   fv_done := fv_done f;
                   fv_then := fv_then f |}).
    destruct (cur_views_ctrls st st0 Hc0) as [Hb0 Hu0].
    destruct (IH st0 pre_seg f0 s i2 st' Hidx ltac:(lia) Hv0
                 ltac:(rewrite Hb0; exact Hbase)
                 ltac:(rewrite Hu0; exact Hunr) H)
      as [seg' [Hc' [Hv' Hcon']]].
    exists seg'. split; [rewrite Hc'; exact Hc0|]. split; [exact Hv'|].
    rewrite (firstn_nth_error_snoc n (vec_list s) vt Hnth).
    rewrite translate_typelist_snoc.
    rewrite (consume_cons_split (fv_ct f) (translate_vt_v vt) _ _ Hcon0).
    exact Hcon'.
Qed.

Lemma pop_types_sim : forall st pre_seg f (s : slice types_ValueType_t) st',
  vec_list st.(opiter_OpIterState_vals) = pre_seg ++ fv_seg f ->
  cur_base_nat st = List.length pre_seg ->
  cur_unr st = (fv_ctrl f).(opiter_Ctrl_polymorphic_base) ->
  opiter_pop_types st s = Ok (Core_result_Result_Ok tt, st') ->
  exists seg',
    vec_list st'.(opiter_OpIterState_ctrls)
      = vec_list st.(opiter_OpIterState_ctrls)
    /\ vec_list st'.(opiter_OpIterState_vals) = pre_seg ++ seg'
    /\ consume (fv_ct f) (translate_typelist (vec_list s))
       = Some <<translate_vals seg',
                (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>>.
Proof.
  intros st pre_seg f s st' Hsplit Hbase Hunr H.
  unfold opiter_pop_types in H.
  assert (Hlen : Z.to_nat (to_Z (slice_len s)) = List.length (vec_list s)).
  { rewrite slice_len_spec. apply Z_to_nat_of_nat. }
  destruct (pop_types_loop_sim (List.length (vec_list s)) st pre_seg f s
              (slice_len s) st' Hlen (Nat.le_refl _) Hsplit Hbase Hunr H)
    as [seg' [Hc [Hv Hcon]]].
  exists seg'. split; [exact Hc|]. split; [exact Hv|].
  rewrite List.firstn_all in Hcon. exact Hcon.
Qed.

(** [push_types] counts up, so the loop from index [i] appends what is left of
    the slice. *)
Lemma push_types_loop_seg : forall n st (s : slice types_ValueType_t)
                                   (i : usize) st',
  (List.length (vec_list s) - Z.to_nat (to_Z i))%nat = n ->
  opiter_push_types_loop st s i = Ok st' ->
  vec_list st'.(opiter_OpIterState_vals)
    = vec_list st.(opiter_OpIterState_vals)
      ++ types_seg (List.skipn (Z.to_nat (to_Z i)) (vec_list s))
  /\ vec_list st'.(opiter_OpIterState_ctrls)
     = vec_list st.(opiter_OpIterState_ctrls).
Proof.
  induction n as [|n IH]; intros st s i st' Hn H;
    unfold opiter_push_types_loop in H; rewrite loop_unfold in H;
    cbn beta iota in H;
    destruct (i s>= slice_len s) eqn:Hge.
  - injection H as <-.
    assert (Hskip : List.skipn (Z.to_nat (to_Z i)) (vec_list s) = []).
    { apply List.skipn_all2. apply scalar_geb_true_ge in Hge.
      rewrite slice_len_spec in Hge. lia. }
    rewrite Hskip. cbn [types_seg List.map]. rewrite List.app_nil_r.
    split; reflexivity.
  - (* nothing is left, so the index cannot still be inside the slice *)
    exfalso. apply scalar_geb_false_lt in Hge. rewrite slice_len_spec in Hge.
    pose proof (usize_nonneg i). lia.
  - injection H as <-.
    assert (Hskip : List.skipn (Z.to_nat (to_Z i)) (vec_list s) = []).
    { apply List.skipn_all2. apply scalar_geb_true_ge in Hge.
      rewrite slice_len_spec in Hge. lia. }
    rewrite Hskip. cbn [types_seg List.map]. rewrite List.app_nil_r.
    split; reflexivity.
  - assert (Hlt : to_Z i < Z.of_nat (List.length (vec_list s))).
    { apply scalar_geb_false_lt in Hge. rewrite slice_len_spec in Hge.
      exact Hge. }
    rewrite slice_index_usize_spec in H.
    destruct (List.nth_error (vec_list s) (Z.to_nat (to_Z i))) as [vt|] eqn:Hnth;
      cbn [bind] in H; [|discriminate].
    destruct (opiter_push_val st (Opiter_StackType_Val vt)) as [st0|] eqn:Hpv;
      cbn [bind] in H; [|discriminate].
    destruct (push_val_spec st (Opiter_StackType_Val vt) st0 Hpv)
      as [Hv0 [Hc0 _]].
    destruct (usize_add_1_ok i) as [i3 [Hadd Hi3]];
      [apply (usize_add_1_lt_max i s Hge)|].
    rewrite Hadd in H. cbn [bind] in H.
    assert (Hi3n : Z.to_nat (to_Z i3) = S (Z.to_nat (to_Z i))).
    { rewrite Hi3. apply Z_to_nat_add1. apply usize_nonneg. }
    destruct (IH st0 s i3 st' ltac:(lia) H) as [Hv' Hc'].
    split.
    + rewrite Hv'. rewrite Hv0. rewrite Hi3n.
      rewrite <- List.app_assoc. f_equal.
      rewrite (skipn_nth_error _ (vec_list s) vt Hnth). reflexivity.
    + rewrite Hc'. rewrite Hc0. reflexivity.
Qed.

Lemma push_types_seg_spec : forall st (s : slice types_ValueType_t) st',
  opiter_push_types st s = Ok st' ->
  vec_list st'.(opiter_OpIterState_vals)
    = vec_list st.(opiter_OpIterState_vals) ++ types_seg (vec_list s)
  /\ vec_list st'.(opiter_OpIterState_ctrls)
     = vec_list st.(opiter_OpIterState_ctrls).
Proof.
  intros st s st' H. unfold opiter_push_types in H.
  assert (Hz : Z.to_nat (to_Z 0%usize) = 0%nat) by reflexivity.
  destruct (push_types_loop_seg (List.length (vec_list s)) st s 0%usize st'
              ltac:(rewrite Hz; lia) H) as [Hv Hc].
  rewrite Hz in Hv. cbn [List.skipn] in Hv.
  split; [exact Hv | exact Hc].
Qed.

Lemma results_seg_types_seg : forall bt,
  results_seg bt = types_seg (block_results_of bt).
Proof. intros [|vt]; reflexivity. Qed.

(** [push_types] over a block's result list appends [results_seg]. *)
Lemma push_results_spec : forall st (s : slice types_ValueType_t) bt st',
  vec_list s = block_results_of bt ->
  opiter_push_types st s = Ok st' ->
  vec_list st'.(opiter_OpIterState_vals)
    = vec_list st.(opiter_OpIterState_vals) ++ results_seg bt
  /\ vec_list st'.(opiter_OpIterState_ctrls)
     = vec_list st.(opiter_OpIterState_ctrls).
Proof.
  intros st s bt st' Hs H.
  destruct (push_types_seg_spec st s st' H) as [Hv Hc].
  split; [|exact Hc].
  rewrite Hv. rewrite Hs. rewrite results_seg_types_seg. reflexivity.
Qed.

(* ================================================================== *)
(** ** Closing a frame                                                 *)
(* ================================================================== *)

Lemma bases_ok_from_prefix : forall n fs g,
  bases_ok_from n (fs ++ [g]) -> bases_ok_from n fs.
Proof.
  intros n fs g. revert n.
  induction fs as [|h fs IH]; intros n H; simpl in H |- *; [exact I|].
  destruct H as [Hh Hrest]. split; [exact Hh | apply IH; exact Hrest].
Qed.

(** The [end] counterpart of [Inv_step_last]: the innermost frame disappears and
    the one below it is rewritten, so the bases come from the prefix rather than
    from the frame being replaced. *)
Lemma Inv_step_end : forall C0 st st' pre f g f',
  Inv C0 st (pre ++ [f] ++ [g]) ->
  fv_ctrl f' = fv_ctrl f ->
  vec_list st'.(opiter_OpIterState_ctrls) = List.map fv_ctrl (pre ++ [f']) ->
  vec_list st'.(opiter_OpIterState_vals)
    = List.concat (List.map fv_seg (pre ++ [f'])) ->
  frames_ok C0 [] (pre ++ [f']) ->
  Inv C0 st' (pre ++ [f']).
Proof.
  intros C0 st st' pre f g f' [H1 [H2 [H3 H4]]] Hctrl Hc Hv Hf.
  unfold Inv. split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hf].
  apply (bases_ok_from_last 0 pre f f'); [rewrite Hctrl; reflexivity|].
  apply (bases_ok_from_prefix 0 (pre ++ [f]) g).
  rewrite List.app_assoc in H3. exact H3.
Qed.

(** Everything [read_end] does to the state, and the results obligation it
    establishes, with the frame's kind left open: [Block] and [Loop] differ only
    in which WasmCert instruction the ghost list becomes.

    Stated over an opaque prefix rather than [pre ++ [f] ++ [g]], because nothing
    here needs a frame below the closed one: that is what lets the same lemma serve
    a nested [end] and the body's. The [n = 0] branch cannot fire since the frame
    list is non-empty, and the emptiness check on the operand stack is what turns
    the pops into [c_types_agree]. *)
(** [else]: the open [Then] is done -- its own obligation, read off by
    [frames_ok_last_fold], becomes exactly what [else_obligation] asks of the
    fresh [Else] that takes its place, stashed as [fv_then]. The [Else]
    itself starts owning nothing, just like a freshly pushed frame, and
    [frames_ok_replace_last] carries every enclosing frame's conjunct across
    unchanged since a [Then] and an [Else] impose the same carry. *)
Theorem step_switch_else : forall C0 st fs pre g st' bt,
  Inv C0 st fs -> fs = pre ++ [g] ->
  (fv_ctrl g).(opiter_Ctrl_kind) = Opiter_LabelKind_Then ->
  opiter_read_else st = Ok (Core_result_Result_Ok bt, st') ->
  Inv C0 st'
      (pre ++ [{| fv_ctrl :=
                    {| opiter_Ctrl_kind := Opiter_LabelKind_Else;
                       opiter_Ctrl_block_type := (fv_ctrl g).(opiter_Ctrl_block_type);
                       opiter_Ctrl_value_stack_base :=
                         (fv_ctrl g).(opiter_Ctrl_value_stack_base);
                       opiter_Ctrl_polymorphic_base := false |};
                  fv_seg := [];
                  fv_done := [];
                  fv_then := fv_done g |}]).
Proof.
  intros C0 st fs pre g st' bt Hinv Hfs Hkind H. subst fs.
  unfold opiter_read_else in H.
  destruct (opiter_take_pending st opiter_op_else) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (take_pending_ok_inv st opiter_op_else st1 Htp) as Hobs.
  assert (Hinv1 : Inv C0 st1 (pre ++ [g]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  destruct (Inv_split C0 st1 pre g Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  assert (Hsnoc : vec_list st1.(opiter_OpIterState_ctrls)
                  = List.map fv_ctrl pre ++ [fv_ctrl g]).
  { destruct Hinv1 as [K1 _]. rewrite K1. rewrite List.map_app. reflexivity. }
  destruct (alloc_vec_Vec_len st1.(opiter_OpIterState_ctrls) s= 0%usize) eqn:Hn;
    [discriminate|].
  destruct (usize_sub (alloc_vec_Vec_len st1.(opiter_OpIterState_ctrls))
              1%usize) as [i|] eqn:Hsub; cbn [bind] in H; [|discriminate].
  rewrite vec_index_spec in H.
  rewrite (ctrls_last_index st1 (List.map fv_ctrl pre) (fv_ctrl g) i
             Hsnoc Hsub) in H.
  cbn [bind] in H.
  destruct (opiter_is_then (fv_ctrl g).(opiter_Ctrl_kind)) as [b|] eqn:Hit;
    cbn [bind] in H; [|discriminate].
  rewrite Hkind in Hit. cbn [opiter_is_then] in Hit. injection Hit as <-.
  destruct (opiter_block_results (fv_ctrl g).(opiter_Ctrl_block_type))
    as [results|] eqn:Hbr; cbn [bind] in H; [|discriminate].
  pose proof (block_results_spec _ _ Hbr) as Hres.
  rewrite vec_deref_spec in H.
  destruct (opiter_pop_types st1 results) as [[r1 st2]|] eqn:Hpt;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [u1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u1. rewrite branch_ok in H. cbn [bind] in H.
  destruct (pop_types_sim st1 (List.concat (List.map fv_seg pre)) g
              results st2 Hsplit1 Hbase1 Hunr1 Hpt) as [seg' [Hc2 [Hv2 Hcon]]].
  destruct (alloc_vec_Vec_len st2.(opiter_OpIterState_vals)
            s<> (fv_ctrl g).(opiter_Ctrl_value_stack_base)) eqn:Hgb;
    [discriminate|].
  apply scalar_neqb_false in Hgb. rewrite vec_len_spec in Hgb.
  assert (Hgbase : Z.to_nat (to_Z (fv_ctrl g).(opiter_Ctrl_value_stack_base))
                   = List.length (List.concat (List.map fv_seg pre))).
  { unfold cur_base_nat in Hbase1.
    rewrite (cur_ctrl_snoc st1 (List.map fv_ctrl pre) (fv_ctrl g)
               Hsnoc) in Hbase1.
    exact Hbase1. }
  assert (Hempty : seg' = []).
  { assert (Hlen : List.length (vec_list st2.(opiter_OpIterState_vals))
                   = (List.length (List.concat (List.map fv_seg pre))
                      + List.length seg')%nat).
    { rewrite Hv2. rewrite List.app_length. reflexivity. }
    pose proof (usize_nonneg (fv_ctrl g).(opiter_Ctrl_value_stack_base)).
    destruct seg' as [|x xs]; [reflexivity|].
    exfalso. cbn [List.length] in Hlen. lia. }
  subst seg'.
  assert (Hidxlen : Z.to_nat (to_Z i) = List.length (List.map fv_ctrl pre)).
  { pose proof (ctrls_last_index_len st1 (List.map fv_ctrl pre) (fv_ctrl g)
                  i Hsnoc Hsub) as Hl.
    exact Hl. }
  assert (Hidxlen2 : (Z.to_nat (to_Z i)
                     < List.length (vec_list st2.(opiter_OpIterState_ctrls)))%nat).
  { rewrite Hc2. rewrite Hsnoc. rewrite List.app_length. cbn [List.length].
    rewrite Hidxlen. lia. }
  destruct (vec_index_mut_ok st2.(opiter_OpIterState_ctrls) i Hidxlen2)
    as [c [back Hidx2]].
  rewrite Hidx2 in H. cbn [bind] in H.
  destruct (vec_index_mut_of_snoc st2.(opiter_OpIterState_ctrls)
              (List.map fv_ctrl pre) (fv_ctrl g) i c back
              (ltac:(rewrite Hc2; exact Hsnoc)) Hidxlen Hidx2) as [Hceq Hback].
  subst c.
  set (mid := {| opiter_Ctrl_kind := Opiter_LabelKind_Else;
                 opiter_Ctrl_block_type := (fv_ctrl g).(opiter_Ctrl_block_type);
                 opiter_Ctrl_value_stack_base :=
                   (fv_ctrl g).(opiter_Ctrl_value_stack_base);
                 opiter_Ctrl_polymorphic_base :=
                   (fv_ctrl g).(opiter_Ctrl_polymorphic_base) |} : opiter_Ctrl_t)
    in H.
  assert (Hidxlen3 : (Z.to_nat (to_Z i)
                     < List.length (vec_list (back mid)))%nat).
  { rewrite (vec_index_mut_len _ _ _ _ Hidx2 mid). rewrite Hc2. rewrite Hsnoc.
    rewrite List.app_length. cbn [List.length]. rewrite Hidxlen. lia. }
  destruct (vec_index_mut_ok (back mid) i Hidxlen3) as [c1 [back1 Hidx3]].
  rewrite Hidx3 in H. cbn [bind] in H.
  injection H as Hr <-.
  set (g' := {| fv_ctrl :=
                  {| opiter_Ctrl_kind := Opiter_LabelKind_Else;
                     opiter_Ctrl_block_type := (fv_ctrl g).(opiter_Ctrl_block_type);
                     opiter_Ctrl_value_stack_base :=
                       (fv_ctrl g).(opiter_Ctrl_value_stack_base);
                     opiter_Ctrl_polymorphic_base := false |};
                fv_seg := []; fv_done := []; fv_then := fv_done g |} : fview).
  destruct (vec_index_mut_of_snoc (back mid) (List.map fv_ctrl pre) mid i c1
              back1 (Hback mid) Hidxlen Hidx3) as [Hc1eq Hback1].
  subst c1.
  destruct (frames_ok_last_fold C0 [] pre g
              (ltac:(destruct Hinv1 as [_ [_ [_ H4]]]; exact H4)))
    as [Hgfold Hgelse].
  assert (Hgc : frame_carry [g] = frame_carry [g']).
  { cbn [frame_carry]. rewrite Hkind. reflexivity. }
  unfold Inv. repeat split.
  - cbn [opiter_OpIterState_ctrls]. rewrite Hback1. rewrite List.map_app.
    reflexivity.
  - cbn [opiter_OpIterState_vals]. rewrite Hv2. rewrite List.map_app.
    rewrite List.concat_app. cbn [List.map List.concat fv_seg].
    repeat rewrite List.app_nil_r. reflexivity.
  - apply (bases_ok_from_snoc 0 pre g').
    + apply (bases_ok_from_prefix 0 pre g).
      destruct Hinv1 as [_ [_ [K3 _]]]. exact K3.
    + cbn [fv_ctrl opiter_Ctrl_value_stack_base]. rewrite Hgbase. lia.
  - apply (frames_ok_replace_last C0 [] pre g g' Hgc
             (ltac:(destruct Hinv1 as [_ [_ [_ H4]]]; exact H4))).
    + cbn [fv_ctrl fv_done fv_ct fv_seg]. reflexivity.
    + unfold else_obligation.
      cbn [fv_ctrl opiter_Ctrl_kind opiter_Ctrl_block_type fv_then].
      assert (Hlbl : ctrl_label (fv_ctrl g') = ctrl_label (fv_ctrl g)).
      { unfold ctrl_label, ctrl_target, branch_target_bt_of.
        cbn [fv_ctrl opiter_Ctrl_kind opiter_Ctrl_block_type].
        rewrite Hkind. reflexivity. }
      rewrite Hlbl.
      exists (fv_ct g). split; [exact Hgfold|].
      rewrite Hres in Hcon.
      apply (c_types_agree_consume_nil _ (fv_ct g)
               (fv_ctrl g).(opiter_Ctrl_polymorphic_base)).
      exact Hcon.
Qed.

Lemma end_state : forall C0 st fs pre' g r st',
  Inv C0 st fs -> fs = pre' ++ [g] ->
  opiter_read_end st = Ok (Core_result_Result_Ok r, st') ->
  r = ((fv_ctrl g).(opiter_Ctrl_kind), (fv_ctrl g).(opiter_Ctrl_block_type))
  /\ c_types_agree (fv_ct g)
       (translate_typelist
          (block_results_of (fv_ctrl g).(opiter_Ctrl_block_type))) = true
  /\ ((fv_ctrl g).(opiter_Ctrl_kind) = Opiter_LabelKind_Then ->
      block_results_of (fv_ctrl g).(opiter_Ctrl_block_type) = [])
  /\ vec_list st'.(opiter_OpIterState_ctrls) = List.map fv_ctrl pre'
  /\ vec_list st'.(opiter_OpIterState_vals)
     = List.concat (List.map fv_seg pre')
       ++ results_seg (fv_ctrl g).(opiter_Ctrl_block_type).
Proof.
  intros C0 st fs pre' g r st' Hinv Hfs H. subst fs.
  unfold opiter_read_end in H.
  destruct (opiter_take_pending st opiter_op_end) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (take_pending_ok_inv st opiter_op_end st1 Htp) as Hobs.
  assert (Hinv1 : Inv C0 st1 (pre' ++ [g]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  destruct (Inv_split C0 st1 pre' g Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  assert (Hsnoc : vec_list st1.(opiter_OpIterState_ctrls)
                  = List.map fv_ctrl pre' ++ [fv_ctrl g]).
  { destruct Hinv1 as [K1 _]. rewrite K1. rewrite List.map_app. reflexivity. }
  (* the frame list is non-empty, so the [n = 0] branch cannot fire *)
  destruct (alloc_vec_Vec_len st1.(opiter_OpIterState_ctrls) s= 0%usize) eqn:Hn;
    [discriminate|].
  destruct (usize_sub (alloc_vec_Vec_len st1.(opiter_OpIterState_ctrls))
              1%usize) as [i|] eqn:Hsub; cbn [bind] in H; [|discriminate].
  rewrite vec_index_spec in H.
  rewrite (ctrls_last_index st1 (List.map fv_ctrl pre') (fv_ctrl g) i
             Hsnoc Hsub) in H.
  cbn [bind] in H.
  destruct (opiter_block_results (fv_ctrl g).(opiter_Ctrl_block_type))
    as [results|] eqn:Hbr; cbn [bind] in H; [|discriminate].
  pose proof (block_results_spec _ _ Hbr) as Hres.
  destruct (opiter_is_then (fv_ctrl g).(opiter_Ctrl_kind)) as [b|] eqn:Hit;
    cbn [bind] in H; [|discriminate].
  destruct b.
  - destruct (alloc_vec_Vec_is_empty alloc_alloc_Global results) as [b1|]
      eqn:Hemp; cbn [bind] in H; [|discriminate].
    destruct b1; cbn [bind] in H; [|discriminate].
    rewrite vec_deref_spec in H.
    destruct (opiter_pop_types st1 results) as [[r1 st2]|] eqn:Hpt;
      cbn [bind] in H; [|discriminate].
    destruct r1 as [u1|e1].
    2: { rewrite branch_err in H. cbn [bind] in H.
         rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
    destruct u1. rewrite branch_ok in H. cbn [bind] in H.
    destruct (pop_types_sim st1 (List.concat (List.map fv_seg pre')) g
                results st2 Hsplit1 Hbase1 Hunr1 Hpt) as [seg' [Hc2 [Hv2 Hcon]]].
    destruct (alloc_vec_Vec_len st2.(opiter_OpIterState_vals)
              s<> (fv_ctrl g).(opiter_Ctrl_value_stack_base)) eqn:Hg;
      [discriminate|].
    apply scalar_neqb_false in Hg. rewrite vec_len_spec in Hg.
    assert (Hgbase : Z.to_nat (to_Z (fv_ctrl g).(opiter_Ctrl_value_stack_base))
                     = List.length (List.concat (List.map fv_seg pre'))).
    { unfold cur_base_nat in Hbase1.
      rewrite (cur_ctrl_snoc st1 (List.map fv_ctrl pre') (fv_ctrl g)
                 Hsnoc) in Hbase1.
      exact Hbase1. }
    assert (Hempty : seg' = []).
    { assert (Hlen : List.length (vec_list st2.(opiter_OpIterState_vals))
                     = (List.length (List.concat (List.map fv_seg pre'))
                        + List.length seg')%nat).
      { rewrite Hv2. rewrite List.app_length. reflexivity. }
      pose proof (usize_nonneg (fv_ctrl g).(opiter_Ctrl_value_stack_base)).
      destruct seg' as [|x xs]; [reflexivity|].
      exfalso. cbn [List.length] in Hlen. lia. }
    subst seg'.
    destruct (alloc_vec_Vec_pop alloc_alloc_Global st2.(opiter_OpIterState_ctrls))
      as [[o v]|] eqn:Hpop; cbn [bind] in H; [|discriminate].
    destruct (vec_pop_of_snoc st2.(opiter_OpIterState_ctrls)
                (List.map fv_ctrl pre') (fv_ctrl g) o v
                (ltac:(rewrite Hc2; exact Hsnoc)) Hpop) as [_ Hvctrls].
    destruct (opiter_push_types
                {| opiter_OpIterState_vals := st2.(opiter_OpIterState_vals);
                   opiter_OpIterState_ctrls := v;
                   opiter_OpIterState_pos := st2.(opiter_OpIterState_pos);
                   opiter_OpIterState_pending := st2.(opiter_OpIterState_pending)
                |} results) as [st3|] eqn:Hpush; cbn [bind] in H; [|discriminate].
    injection H as Hr <-.
    destruct (push_results_spec _ results
                (fv_ctrl g).(opiter_Ctrl_block_type) st3 Hres Hpush)
      as [Hpv Hpc].
    cbn [opiter_OpIterState_vals opiter_OpIterState_ctrls] in Hpv.
    cbn [opiter_OpIterState_vals opiter_OpIterState_ctrls] in Hpc.
    assert (Hresnil : vec_list results = []).
    { pose proof (vec_is_empty_spec alloc_alloc_Global results) as Hspec.
      rewrite Hemp in Hspec. injection Hspec as Hspec.
      destruct (vec_list results) as [|x xs]; [reflexivity | discriminate]. }
    repeat split.
    + symmetry. exact Hr.
    + rewrite Hres in Hcon.
      apply (c_types_agree_consume_nil _ (fv_ct g)
               (fv_ctrl g).(opiter_Ctrl_polymorphic_base)).
      exact Hcon.
    + intros _. rewrite <- Hres. exact Hresnil.
    + rewrite Hpc. exact Hvctrls.
    + rewrite Hpv. rewrite Hv2. rewrite List.app_nil_r. reflexivity.
  - rewrite vec_deref_spec in H.
    destruct (opiter_pop_types st1 results) as [[r1 st2]|] eqn:Hpt;
      cbn [bind] in H; [|discriminate].
    destruct r1 as [u1|e1].
    2: { rewrite branch_err in H. cbn [bind] in H.
         rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
    destruct u1. rewrite branch_ok in H. cbn [bind] in H.
    destruct (pop_types_sim st1 (List.concat (List.map fv_seg pre')) g
                results st2 Hsplit1 Hbase1 Hunr1 Hpt) as [seg' [Hc2 [Hv2 Hcon]]].
    destruct (alloc_vec_Vec_len st2.(opiter_OpIterState_vals)
              s<> (fv_ctrl g).(opiter_Ctrl_value_stack_base)) eqn:Hg;
      [discriminate|].
    apply scalar_neqb_false in Hg. rewrite vec_len_spec in Hg.
    assert (Hgbase : Z.to_nat (to_Z (fv_ctrl g).(opiter_Ctrl_value_stack_base))
                     = List.length (List.concat (List.map fv_seg pre'))).
    { unfold cur_base_nat in Hbase1.
      rewrite (cur_ctrl_snoc st1 (List.map fv_ctrl pre') (fv_ctrl g)
                 Hsnoc) in Hbase1.
      exact Hbase1. }
    assert (Hempty : seg' = []).
    { assert (Hlen : List.length (vec_list st2.(opiter_OpIterState_vals))
                     = (List.length (List.concat (List.map fv_seg pre'))
                        + List.length seg')%nat).
      { rewrite Hv2. rewrite List.app_length. reflexivity. }
      pose proof (usize_nonneg (fv_ctrl g).(opiter_Ctrl_value_stack_base)).
      destruct seg' as [|x xs]; [reflexivity|].
      exfalso. cbn [List.length] in Hlen. lia. }
    subst seg'.
    destruct (alloc_vec_Vec_pop alloc_alloc_Global st2.(opiter_OpIterState_ctrls))
      as [[o v]|] eqn:Hpop; cbn [bind] in H; [|discriminate].
    destruct (vec_pop_of_snoc st2.(opiter_OpIterState_ctrls)
                (List.map fv_ctrl pre') (fv_ctrl g) o v
                (ltac:(rewrite Hc2; exact Hsnoc)) Hpop) as [_ Hvctrls].
    destruct (opiter_push_types
                {| opiter_OpIterState_vals := st2.(opiter_OpIterState_vals);
                   opiter_OpIterState_ctrls := v;
                   opiter_OpIterState_pos := st2.(opiter_OpIterState_pos);
                   opiter_OpIterState_pending := st2.(opiter_OpIterState_pending)
                |} results) as [st3|] eqn:Hpush; cbn [bind] in H; [|discriminate].
    injection H as Hr <-.
    destruct (push_results_spec _ results
                (fv_ctrl g).(opiter_Ctrl_block_type) st3 Hres Hpush)
      as [Hpv Hpc].
    cbn [opiter_OpIterState_vals opiter_OpIterState_ctrls] in Hpv.
    cbn [opiter_OpIterState_vals opiter_OpIterState_ctrls] in Hpc.
    repeat split.
    + symmetry. exact Hr.
    + rewrite Hres in Hcon.
      apply (c_types_agree_consume_nil _ (fv_ct g)
               (fv_ctrl g).(opiter_Ctrl_polymorphic_base)).
      exact Hcon.
    + intros Hkindthen.
      destruct (is_then_spec _ _ Hit) as [[Ht _]|[_ Hne]]; [discriminate Ht|].
      exfalso. apply Hne. exact Hkindthen.
    + rewrite Hpc. exact Hvctrls.
    + rewrite Hpv. rewrite Hv2. rewrite List.app_nil_r. reflexivity.
Qed.

(** [end] closing a bare [Then] -- an [if] with no [else] at all. WasmCert has
    no such construct; it treats [if bt es end] as [if bt es else end], i.e.
    [BI_if bt es [::]], which is exactly why [read_end] rejects a nonempty
    result type here: the empty else-body only type-checks against [tm] when
    [tm] is itself empty. [end_state]'s third conjunct is that very fact. *)
Theorem step_end_then : forall C0 st fs pre f g r st',
  Inv C0 st fs -> fs = pre ++ [f] ++ [g] ->
  (fv_ctrl g).(opiter_Ctrl_kind) = Opiter_LabelKind_Then ->
  opiter_read_end st = Ok (Core_result_Result_Ok r, st') ->
  Inv C0 st'
      (pre ++ [{| fv_ctrl := fv_ctrl f;
                  fv_seg := fv_seg f
                            ++ results_seg (fv_ctrl g).(opiter_Ctrl_block_type);
                  fv_done :=
                    fv_done f
                    ++ [BI_if
                          (translate_bt (fv_ctrl g).(opiter_Ctrl_block_type))
                          (fv_done g) []];
                  fv_then := fv_then f |}]).
Proof.
  intros C0 st fs pre f g r st' Hinv Hfs Hkind H.
  assert (Hfs' : fs = (pre ++ [f]) ++ [g]).
  { rewrite Hfs. rewrite List.app_assoc. reflexivity. }
  destruct (end_state C0 st fs (pre ++ [f]) g r st' Hinv Hfs' H)
    as [_ [Hagree [Hresnil [Hc Hv]]]].
  subst fs. specialize (Hresnil Hkind).
  apply (Inv_step_end C0 st st' pre f g _ Hinv); [reflexivity | | |].
  - rewrite Hc. rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hv. repeat rewrite List.map_app. repeat rewrite List.concat_app.
    cbn [List.map List.concat fv_seg]. repeat rewrite List.app_nil_r.
    rewrite List.app_assoc. reflexivity.
  - destruct Hinv as [_ [_ [_ H4]]].
    destruct (frames_ok_last_two_if C0 [] pre f g (or_introl Hkind) H4)
      as [[ct0 [Hf0 Hcon0]] [Helsef [Hgfold Hgelse]]].
    assert (Hglbl : ctrl_label (fv_ctrl g)
                    = translate_typelist
                        (block_results_of (fv_ctrl g).(opiter_Ctrl_block_type))).
    { unfold ctrl_label, ctrl_target, branch_target_bt_of. rewrite Hkind.
      reflexivity. }
    rewrite Hglbl in Hgfold.
    assert (Hfeq : fv_ctrl
                     {| fv_ctrl := fv_ctrl f;
                        fv_seg := fv_seg f
                                  ++ results_seg
                                       (fv_ctrl g).(opiter_Ctrl_block_type);
                        fv_done :=
                          fv_done f
                          ++ [BI_if
                                (translate_bt (fv_ctrl g).(opiter_Ctrl_block_type))
                                (fv_done g) []];
                        fv_then := fv_then f |}
                   = fv_ctrl f) by reflexivity.
    apply (frames_ok_close_if C0 [] pre f g
             {| fv_ctrl := fv_ctrl f;
                fv_seg := fv_seg f
                          ++ results_seg (fv_ctrl g).(opiter_Ctrl_block_type);
                fv_done :=
                  fv_done f
                  ++ [BI_if (translate_bt (fv_ctrl g).(opiter_Ctrl_block_type))
                        (fv_done g) []];
                fv_then := fv_then f |}
             Hfeq H4).
    + rewrite List.fold_left_app. rewrite Hf0. cbn [List.fold_left].
      unfold fv_ct. cbn [fv_seg fv_ctrl].
      rewrite translate_vals_results.
      apply (end_if_typing C0 (ctrl_label (fv_ctrl f) :: labels_after [] pre) f
               (fv_ctrl g).(opiter_Ctrl_block_type) (fv_done g) [] (fv_ct g)
               <<[], false>> ct0).
      * exact Hgfold.
      * exact Hagree.
      * reflexivity.
      * rewrite Hresnil. reflexivity.
      * exact Hcon0.
    + exact Helsef.
Qed.

(** [end] closing an [Else]: [BI_if]'s two bodies are [fv_then] (stashed by
    [else]) and [fv_done] (accumulated since), each carrying its own
    obligation -- [else_obligation] for the former, [end_state]'s [Hagree]
    for the latter -- and [end_if_typing] combines them exactly as
    [check_single]'s own [BI_if] case does. *)
Theorem step_end_else : forall C0 st fs pre f g r st',
  Inv C0 st fs -> fs = pre ++ [f] ++ [g] ->
  (fv_ctrl g).(opiter_Ctrl_kind) = Opiter_LabelKind_Else ->
  opiter_read_end st = Ok (Core_result_Result_Ok r, st') ->
  Inv C0 st'
      (pre ++ [{| fv_ctrl := fv_ctrl f;
                  fv_seg := fv_seg f
                            ++ results_seg (fv_ctrl g).(opiter_Ctrl_block_type);
                  fv_done :=
                    fv_done f
                    ++ [BI_if
                          (translate_bt (fv_ctrl g).(opiter_Ctrl_block_type))
                          (fv_then g) (fv_done g)];
                  fv_then := fv_then f |}]).
Proof.
  intros C0 st fs pre f g r st' Hinv Hfs Hkind H.
  assert (Hfs' : fs = (pre ++ [f]) ++ [g]).
  { rewrite Hfs. rewrite List.app_assoc. reflexivity. }
  destruct (end_state C0 st fs (pre ++ [f]) g r st' Hinv Hfs' H)
    as [_ [Hagree [_ [Hc Hv]]]].
  subst fs.
  apply (Inv_step_end C0 st st' pre f g _ Hinv); [reflexivity | | |].
  - rewrite Hc. rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hv. repeat rewrite List.map_app. repeat rewrite List.concat_app.
    cbn [List.map List.concat fv_seg]. repeat rewrite List.app_nil_r.
    rewrite List.app_assoc. reflexivity.
  - destruct Hinv as [_ [_ [_ H4]]].
    destruct (frames_ok_last_two_if C0 [] pre f g (or_intror Hkind) H4)
      as [[ct0 [Hf0 Hcon0]] [Helsef [Hgfold Hgelse]]].
    assert (Hglbl : ctrl_label (fv_ctrl g)
                    = translate_typelist
                        (block_results_of (fv_ctrl g).(opiter_Ctrl_block_type))).
    { unfold ctrl_label, ctrl_target, branch_target_bt_of. rewrite Hkind.
      reflexivity. }
    rewrite Hglbl in Hgfold.
    unfold else_obligation in Hgelse. rewrite Hkind in Hgelse.
    destruct Hgelse as [ct_then [Hthenfold Hthenagree]].
    rewrite Hglbl in Hthenfold.
    assert (Hfeq : fv_ctrl
                     {| fv_ctrl := fv_ctrl f;
                        fv_seg := fv_seg f
                                  ++ results_seg
                                       (fv_ctrl g).(opiter_Ctrl_block_type);
                        fv_done :=
                          fv_done f
                          ++ [BI_if
                                (translate_bt (fv_ctrl g).(opiter_Ctrl_block_type))
                                (fv_then g) (fv_done g)];
                        fv_then := fv_then f |}
                   = fv_ctrl f) by reflexivity.
    apply (frames_ok_close_if C0 [] pre f g
             {| fv_ctrl := fv_ctrl f;
                fv_seg := fv_seg f
                          ++ results_seg (fv_ctrl g).(opiter_Ctrl_block_type);
                fv_done :=
                  fv_done f
                  ++ [BI_if (translate_bt (fv_ctrl g).(opiter_Ctrl_block_type))
                        (fv_then g) (fv_done g)];
                fv_then := fv_then f |}
             Hfeq H4).
    + rewrite List.fold_left_app. rewrite Hf0. cbn [List.fold_left].
      unfold fv_ct. cbn [fv_seg fv_ctrl]. rewrite translate_vals_results.
      apply (end_if_typing C0 (ctrl_label (fv_ctrl f) :: labels_after [] pre) f
               (fv_ctrl g).(opiter_Ctrl_block_type) (fv_then g) (fv_done g)
               ct_then (fv_ct g) ct0).
      * exact Hthenfold.
      * exact Hthenagree.
      * exact Hgfold.
      * exact Hagree.
      * exact Hcon0.
    + exact Helsef.
Qed.

(** [end] closing a [Block]. [end_state] does the state bookkeeping and
    establishes the results obligation; [frames_ok_last] hands back the closed
    frame's own obligation, which [end_block_typing] turns into exactly the
    [BI_block] that the enclosing frame's ghost list grows by.

    The outermost frame is deliberately not covered: closing it leaves no
    enclosing frame to append to, which is the top-level theorem's business
    rather than a step's. *)
Theorem step_end_block : forall C0 st fs pre f g r st',
  Inv C0 st fs -> fs = pre ++ [f] ++ [g] ->
  (fv_ctrl g).(opiter_Ctrl_kind) = Opiter_LabelKind_Block ->
  opiter_read_end st = Ok (Core_result_Result_Ok r, st') ->
  Inv C0 st'
      (pre ++ [{| fv_ctrl := fv_ctrl f;
                  fv_seg := fv_seg f
                            ++ results_seg (fv_ctrl g).(opiter_Ctrl_block_type);
                  fv_done :=
                    fv_done f
                    ++ [BI_block
                          (translate_bt (fv_ctrl g).(opiter_Ctrl_block_type))
                          (fv_done g)];
                          fv_then := fv_then f |}]).
Proof.
  intros C0 st fs pre f g r st' Hinv Hfs Hkind H.
  assert (Hfs' : fs = (pre ++ [f]) ++ [g]).
  { rewrite Hfs. rewrite List.app_assoc. reflexivity. }
  destruct (end_state C0 st fs (pre ++ [f]) g r st' Hinv Hfs' H)
    as [_ [Hagree [_ [Hc Hv]]]].
  subst fs.
  apply (Inv_step_end C0 st st' pre f g _ Hinv); [reflexivity | | |].
  - rewrite Hc. rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hv. repeat rewrite List.map_app. repeat rewrite List.concat_app.
    cbn [List.map List.concat fv_seg]. repeat rewrite List.app_nil_r.
    rewrite List.app_assoc. reflexivity.
  - destruct Hinv as [_ [_ [_ H4]]].
    (* ssreflect's rewrite does not take [<-], so re-associate forwards *)
    assert (Hre : pre ++ [f] ++ [g] = (pre ++ [f]) ++ [g]).
    { rewrite List.app_assoc. reflexivity. }
    rewrite Hre in H4.
    assert (Hgc : frame_carry [g] = []).
    { cbn [frame_carry]. rewrite Hkind. reflexivity. }
    destruct (frames_ok_last C0 [] (pre ++ [f]) g Hgc H4) as [Hfok [Hfold _]].
    rewrite (labels_after_snoc [] pre f) in Hfold.
    apply (frames_ok_append_at C0 [] pre f _ _ Hfok).
    rewrite translate_vals_results.
    apply (end_block_typing C0 _ f g (fv_ctrl g).(opiter_Ctrl_block_type));
      [reflexivity | exact Hkind | exact Hfold | exact Hagree].
Qed.

(** [end] closing a [Loop]. Identical apart from the instruction and the label
    the inner context carries, which is [end_loop_typing]'s business. *)
Theorem step_end_loop : forall C0 st fs pre f g r st',
  Inv C0 st fs -> fs = pre ++ [f] ++ [g] ->
  (fv_ctrl g).(opiter_Ctrl_kind) = Opiter_LabelKind_Loop ->
  opiter_read_end st = Ok (Core_result_Result_Ok r, st') ->
  Inv C0 st'
      (pre ++ [{| fv_ctrl := fv_ctrl f;
                  fv_seg := fv_seg f
                            ++ results_seg (fv_ctrl g).(opiter_Ctrl_block_type);
                  fv_done :=
                    fv_done f
                    ++ [BI_loop
                          (translate_bt (fv_ctrl g).(opiter_Ctrl_block_type))
                          (fv_done g)];
                          fv_then := fv_then f |}]).
Proof.
  intros C0 st fs pre f g r st' Hinv Hfs Hkind H.
  assert (Hfs' : fs = (pre ++ [f]) ++ [g]).
  { rewrite Hfs. rewrite List.app_assoc. reflexivity. }
  destruct (end_state C0 st fs (pre ++ [f]) g r st' Hinv Hfs' H)
    as [_ [Hagree [_ [Hc Hv]]]].
  subst fs.
  apply (Inv_step_end C0 st st' pre f g _ Hinv); [reflexivity | | |].
  - rewrite Hc. rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hv. repeat rewrite List.map_app. repeat rewrite List.concat_app.
    cbn [List.map List.concat fv_seg]. repeat rewrite List.app_nil_r.
    rewrite List.app_assoc. reflexivity.
  - destruct Hinv as [_ [_ [_ H4]]].
    assert (Hre : pre ++ [f] ++ [g] = (pre ++ [f]) ++ [g]).
    { rewrite List.app_assoc. reflexivity. }
    rewrite Hre in H4.
    assert (Hgc : frame_carry [g] = []).
    { cbn [frame_carry]. rewrite Hkind. reflexivity. }
    destruct (frames_ok_last C0 [] (pre ++ [f]) g Hgc H4) as [Hfok [Hfold _]].
    rewrite (labels_after_snoc [] pre f) in Hfold.
    apply (frames_ok_append_at C0 [] pre f _ _ Hfok).
    rewrite translate_vals_results.
    apply (end_loop_typing C0 _ f g (fv_ctrl g).(opiter_Ctrl_block_type));
      [reflexivity | exact Hkind | exact Hfold | exact Hagree].
Qed.

(* ================================================================== *)
(** ** Control steps: branching out of a frame                         *)
(* ================================================================== *)

(** [frames_ok]'s accumulator and [ctx_at]'s label list are the same thing,
    which is what lets [br] use [ctx_at_label_lookup] on an obligation stated in
    terms of [labels_after]. *)
Lemma labels_after_ctx_at : forall C0 st fs,
  vec_list st.(opiter_OpIterState_ctrls) = List.map fv_ctrl fs ->
  labels_after [] fs = tc_labels (ctx_at C0 st).
Proof.
  intros C0 st fs Hc. rewrite labels_after_rev. rewrite List.app_nil_r.
  cbn [tc_labels ctx_at with_labels]. rewrite Hc. rewrite List.map_map.
  reflexivity.
Qed.

(** [frames_ok_append_ctrl] with the labels instantiated, for a step that both
    rewrites the frame and inspects the labels. That is exactly [br]. *)
Lemma frames_ok_append_ctrl_at : forall C0 labels pre f c' be seg',
  ctrl_label c' = ctrl_label (fv_ctrl f) ->
  c'.(opiter_Ctrl_kind) = (fv_ctrl f).(opiter_Ctrl_kind) ->
  c'.(opiter_Ctrl_block_type) = (fv_ctrl f).(opiter_Ctrl_block_type) ->
  frames_ok C0 labels (pre ++ [f]) ->
  check_single (with_labels C0 (ctrl_label (fv_ctrl f)
                               :: labels_after labels pre))
              (Some (fv_ct f)) be
    = Some <<translate_vals seg', c'.(opiter_Ctrl_polymorphic_base)>> ->
  frames_ok C0 labels
    (pre ++ [{| fv_ctrl := c'; fv_seg := seg'; fv_done := fv_done f ++ [be];
      fv_then := fv_then f |}]).
Proof.
  intros C0 labels pre f c' be seg' Hlbl Hknd Hbt. revert labels.
  induction pre as [|g pre IH]; intros labels H Hstep; simpl in H |- *.
  - destruct H as [[Hfold Helse] _]. split; [split|exact I].
    + cbn [fv_ctrl fv_seg fv_done fv_ct] in *.
      rewrite Hlbl. rewrite List.fold_left_app. rewrite Hfold. simpl. exact Hstep.
    + unfold else_obligation in Helse |- *. cbn [fv_ctrl fv_then] in *.
      rewrite Hlbl. rewrite Hknd. rewrite Hbt. exact Helse.
  - destruct H as [Hg Hrest]. split.
    + assert (Hk : (fv_ctrl f).(opiter_Ctrl_kind)
                   = (fv_ctrl {| fv_ctrl := c'; fv_seg := seg';
                                 fv_done := fv_done f ++ [be];
                                 fv_then := fv_then f |}).(opiter_Ctrl_kind)).
      { cbn [fv_ctrl]. symmetry. exact Hknd. }
      rewrite (frame_carry_snoc pre f _ Hk) in Hg. exact Hg.
    + apply IH; [exact Hrest | exact Hstep].
Qed.

(** The label lookup's whole content: the cursor moved through the depth, the
    stacks did not, and the frame it resolved is the one WasmCert finds in
    [tc_labels] at that depth. The index arithmetic lives here once rather than
    in each branch operator's step lemma. *)
Lemma read_label_at : forall C0 st fs data depth target st',
  Inv C0 st fs ->
  opiter_read_label st data = Ok (Core_result_Result_Ok (depth, target), st') ->
  Inv C0 st' fs
  /\ lookup_N (tc_labels (ctx_at C0 st)) (Z.to_N (to_Z depth))
     = Some (ctrl_label target).
Proof.
  intros C0 st fs data depth target st' Hinv H.
  destruct (read_label_fields st data _ st' H) as [Hv Hc].
  split; [apply (Inv_fields C0 st st' fs Hv Hc Hinv)|].
  unfold opiter_read_label in H.
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
  injection H as Hd Hc0 _. rewrite -Hd. rewrite -Hc0.
  (* the depth reached is the one the checker looks up *)
  assert (Hdv : to_Z d = to_Z d0).
  { unfold scalar_cast in Hcast. apply mk_scalar_ok_to_Z in Hcast. exact Hcast. }
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
  assert (Hidx : Z.to_nat (to_Z i1)
                 = (List.length (vec_list st.(opiter_OpIterState_ctrls)) - 1
                    - Z.to_nat (to_Z d0))%nat) by lia.
  assert (Hlt : (Z.to_nat (to_Z d0)
                 < List.length (vec_list st.(opiter_OpIterState_ctrls)))%nat)
    by lia.
  rewrite Hidx in Hnth.
  unfold lookup_N. rewrite N_to_nat_Z_to_N.
  apply (ctx_at_label_lookup C0 st (Z.to_nat (to_Z d0)) c Hlt Hnth).
Qed.

(** The same for the branch operators' prologue, which is the opcode and then a
    label. [take_pending] leaves the control stack alone, so the label context
    the lookup is stated against is unchanged. *)
Lemma take_branch_target_at : forall C0 st fs data opcode depth target st',
  Inv C0 st fs ->
  opiter_take_branch_target st data opcode
    = Ok (Core_result_Result_Ok (depth, target), st') ->
  Inv C0 st' fs
  /\ lookup_N (tc_labels (ctx_at C0 st)) (Z.to_N (to_Z depth))
     = Some (ctrl_label target).
Proof.
  intros C0 st fs data opcode depth target st' Hinv H.
  unfold opiter_take_branch_target in H.
  destruct (opiter_take_pending st opcode) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  destruct (take_pending_stacks st opcode r0 st1 Htp) as [Hv1 Hc1].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  destruct (read_label_at C0 st1 fs data depth target st'
              (Inv_fields C0 st st1 fs Hv1 Hc1 Hinv) H) as [Hi Hl].
  split; [exact Hi|].
  assert (Hctx : ctx_at C0 st = ctx_at C0 st1)
    by (unfold ctx_at; rewrite Hc1; reflexivity).
  rewrite Hctx. exact Hl.
Qed.

(** [br]: the target frame's types must be on the stack, and the rest of the
    frame becomes unreachable. WasmCert's [type_update_top ts xx nil] consumes
    [xx] and then yields [<<nil, true>>], which is exactly what
    [mark_unreachable] does to the state: the segment is truncated to the frame's
    base and the frame's polymorphic flag is set. [step_unreachable] already
    established that half.

    Which frame the depth names is [take_branch_target_at]'s business. Since [br]
    inspects the labels, the [frames_ok] step has to be the [_at] variant. *)
Theorem step_br : forall C0 st fs pre f data depth bt st',
  Inv C0 st fs -> fs = pre ++ [f] ->
  opiter_read_br st data = Ok (Core_result_Result_Ok (depth, bt), st') ->
  Inv C0 st'
      (pre ++ [{| fv_ctrl :=
                    {| opiter_Ctrl_kind := (fv_ctrl f).(opiter_Ctrl_kind);
                       opiter_Ctrl_block_type :=
                         (fv_ctrl f).(opiter_Ctrl_block_type);
                       opiter_Ctrl_value_stack_base :=
                         (fv_ctrl f).(opiter_Ctrl_value_stack_base);
                       opiter_Ctrl_polymorphic_base := true |};
                  fv_seg := [];
                  fv_done := fv_done f ++ [BI_br (Z.to_N (to_Z depth))];
                  fv_then := fv_then f |}]).
Proof.
  intros C0 st fs pre f data depth bt st' Hinv Hfs H. subst fs.
  unfold opiter_read_br in H.
  destruct (opiter_take_branch_target st data opiter_op_br) as [[r0 st1]|]
    eqn:Htb; cbn [bind] in H; [|discriminate].
  destruct r0 as [[d0 target]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (take_branch_target_at C0 st (pre ++ [f]) data _ d0 target st1
              Hinv Htb) as [Hinv1 Hlookup].
  destruct (take_branch_target_fields st data _ _ st1 Htb) as [_ Hc1].
  assert (Hsnoc : vec_list st1.(opiter_OpIterState_ctrls)
                  = List.map fv_ctrl pre ++ [fv_ctrl f]).
  { destruct Hinv1 as [K1 _]. rewrite K1. rewrite List.map_app. reflexivity. }
  destruct (opiter_branch_target_types target) as [types|] eqn:Hbtt;
    cbn [bind] in H; [|discriminate].
  pose proof (branch_target_types_spec target types Hbtt) as Htypes.
  rewrite vec_deref_spec in H.
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  destruct (opiter_pop_types st1 types) as [[r2 st2]|] eqn:Hpt;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (pop_types_sim st1 (List.concat (List.map fv_seg pre)) f types st2
              Hsplit1 Hbase1 Hunr1 Hpt) as [seg1 [Hc2 [Hv2 Hcon]]].
  destruct (opiter_mark_unreachable st2) as [st3|] eqn:Hmu; cbn [bind] in H;
    [|discriminate].
  (* injection decomposes the returned pair, so this yields three equations *)
  injection H as Hd Hbtp <-. subst depth.
  (* [mark_unreachable] truncates to the frame's base and sets its flag *)
  assert (Hbf : Z.to_nat (to_Z (fv_ctrl f).(opiter_Ctrl_value_stack_base))
                = List.length (List.concat (List.map fv_seg pre))).
  { unfold cur_base_nat in Hbase1.
    rewrite (cur_ctrl_snoc st1 (List.map fv_ctrl pre) (fv_ctrl f) Hsnoc)
      in Hbase1.
    exact Hbase1. }
  assert (Hsnoc2 : vec_list st2.(opiter_OpIterState_ctrls)
                   = List.map fv_ctrl pre ++ [fv_ctrl f]).
  { rewrite Hc2. exact Hsnoc. }
  assert (Hle : (Z.to_nat (to_Z (fv_ctrl f).(opiter_Ctrl_value_stack_base))
                 <= List.length (vec_list st2.(opiter_OpIterState_vals)))%nat).
  { rewrite Hbf. rewrite Hv2. rewrite List.app_length. lia. }
  destruct (mark_unreachable_spec st2 st3 (List.map fv_ctrl pre) (fv_ctrl f)
              Hsnoc2 Hle Hmu) as [Hmv Hmc].
  assert (Hlbls : tc_labels (ctx_at C0 st)
                  = ctrl_label (fv_ctrl f) :: labels_after [] pre).
  { pose proof (labels_after_ctx_at C0 st (pre ++ [f])
                  (ltac:(rewrite -Hc1; destruct Hinv1 as [K1 _]; exact K1)))
      as Hla.
    rewrite (labels_after_snoc [] pre f) in Hla. symmetry. exact Hla. }
  rewrite Hlbls in Hlookup.
  apply (Inv_step_last C0 st1 st3 pre f _ Hinv1).
  - reflexivity.
  - rewrite Hmc. rewrite List.map_app. reflexivity.
  - rewrite Hmv. rewrite Hv2. rewrite Hbf. rewrite List.firstn_app.
    rewrite List.firstn_all.
    assert (Hz : (List.length (List.concat (List.map fv_seg pre))
                  - List.length (List.concat (List.map fv_seg pre)))%nat
                 = 0%nat).
    { lia. }
    rewrite Hz. cbn [List.firstn]. rewrite List.app_nil_r.
    rewrite List.map_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg]. rewrite List.app_nil_r.
    rewrite List.app_nil_r. reflexivity.
  - apply (frames_ok_append_ctrl_at C0 [] pre f _
             (BI_br (Z.to_N (to_Z d0))) []).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + destruct Hinv1 as [_ [_ [_ K4]]]. exact K4.
    + rewrite Htypes in Hcon.
      cbn [check_single]. cbn [tc_labels with_labels]. rewrite Hlookup.
      unfold type_update_top. rewrite Hcon. reflexivity.
Qed.

(** [br_if]: the condition is consumed and the target's types must be there, but
    they go back on the stack because the fall-through path continues with them.
    WasmCert's [type_update ts (i32 :: xx) xx] says exactly that, and unlike
    [br] there is no [mark_unreachable], so the frame's flag and base are
    untouched and the ordinary [frames_ok] step applies -- in its [_at] form,
    since the labels are consulted. *)
Theorem step_br_if : forall C0 st fs pre f data depth bt st',
  Inv C0 st fs -> fs = pre ++ [f] ->
  opiter_read_br_if st data = Ok (Core_result_Result_Ok (depth, bt), st') ->
  exists seg',
    Inv C0 st'
        (pre ++ [{| fv_ctrl := fv_ctrl f;
                    fv_seg := seg';
                    fv_done := fv_done f
                               ++ [BI_br_if (Z.to_N (to_Z depth))];
                               fv_then := fv_then f |}]).
Proof.
  intros C0 st fs pre f data depth bt st' Hinv Hfs H. subst fs.
  unfold opiter_read_br_if in H.
  destruct (opiter_take_branch_target st data opiter_op_br_if) as [[r0 st1]|]
    eqn:Htb; cbn [bind] in H; [|discriminate].
  destruct r0 as [[d0 target]|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (take_branch_target_at C0 st (pre ++ [f]) data _ d0 target st1
              Hinv Htb) as [Hinv1 Hlookup].
  destruct (take_branch_target_fields st data _ _ st1 Htb) as [_ Hc1].
  destruct (opiter_branch_target_types target) as [types|] eqn:Hbtt;
    cbn [bind] in H; [|discriminate].
  pose proof (branch_target_types_spec target types Hbtt) as Htypes.
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  (* the condition *)
  destruct (opiter_pop_with_type st1 Types_ValueType_I32) as [[r1 st2]|] eqn:Hp1;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [t1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (pop_with_type_sim st1 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 t1 st2 Hsplit1 Hbase1 Hunr1 Hp1)
    as [seg1 [Hc2 [Hv2 Hcon1]]].
  destruct (cur_views_ctrls st1 st2 Hc2) as [Hb2 Hu2].
  (* the target's types, on the frame with the shortened segment *)
  destruct (opiter_pop_types st2 (alloc_vec_Vec_deref types)) as [[r2 st3]|]
    eqn:Hpt; cbn [bind] in H; [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  rewrite vec_deref_spec in H, Hpt.
  destruct (pop_types_sim st2 (List.concat (List.map fv_seg pre))
              {| fv_ctrl := fv_ctrl f; fv_seg := seg1; fv_done := fv_done f;
fv_then := fv_then f |}
              types st3)
    as [seg2 [Hc3 [Hv3 Hcon2]]].
  { cbn [fv_seg]. exact Hv2. }
  { cbn [fv_ctrl]. rewrite Hb2. exact Hbase1. }
  { cbn [fv_ctrl]. rewrite Hu2. exact Hunr1. }
  { exact Hpt. }
  cbn [fv_ct fv_seg fv_ctrl] in Hcon2.
  (* and back on *)
  destruct (opiter_push_types st3 types) as [st4|] eqn:Hpush;
    cbn [bind] in H; [|discriminate].
  injection H as Hd Hbtp <-. subst depth.
  destruct (push_types_seg_spec st3 types st4 Hpush) as [Hv4 Hc4].
  assert (Hlbls : tc_labels (ctx_at C0 st)
                  = ctrl_label (fv_ctrl f) :: labels_after [] pre).
  { pose proof (labels_after_ctx_at C0 st (pre ++ [f])
                  (ltac:(rewrite -Hc1; destruct Hinv1 as [K1 _]; exact K1)))
      as Hla.
    rewrite (labels_after_snoc [] pre f) in Hla. symmetry. exact Hla. }
  rewrite Hlbls in Hlookup.
  exists (seg2 ++ types_seg (vec_list types)).
  apply (Inv_step_last C0 st1 st4 pre f _ Hinv1).
  - reflexivity.
  - rewrite Hc4. rewrite Hc3. rewrite Hc2. destruct Hinv1 as [K1 _].
    rewrite K1. rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hv4. rewrite Hv3.
    rewrite List.map_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg]. rewrite List.app_nil_r.
    rewrite List.app_assoc. reflexivity.
  - apply (frames_ok_append_ctrl_at C0 [] pre f (fv_ctrl f)
             (BI_br_if (Z.to_N (to_Z d0))) (seg2 ++ types_seg (vec_list types))).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + destruct Hinv1 as [_ [_ [_ K4]]]. exact K4.
    + cbn [check_single]. cbn [tc_labels with_labels]. rewrite Hlookup.
      unfold ctrl_label. rewrite -Htypes. unfold type_update.
      rewrite (consume_cons_split (fv_ct f) (T_num T_i32)
                 (translate_typelist (vec_list types))
                 <<translate_vals seg1,
                   (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>> Hcon1).
      rewrite Hcon2. cbn [produce CT_type CT_unr].
      rewrite translate_vals_app.
      rewrite translate_vals_types_seg.
      reflexivity.
Qed.

(** [return]: [br]'s effect with the function's result list in place of a
    frame's. WasmCert's [type_update_top ts tls nil] is the same shape, and
    [tc_return] is a field [with_labels] leaves alone, so the label context does
    not matter and the plain [frames_ok] step applies. *)
(** [br_table]: every label in the table has to have the same branch target
    type, and the effect is then [br]'s with an [i32] index consumed first.

    The reader does not return the depths, so the label list arrives here as a
    parameter, together with one [depth_target] per entry -- both produced by the
    same run in [read_br_table_sound]. That is what makes the two halves agree on
    a list neither can name on its own. *)

(** WasmCert's [same_lab_h] compares each entry against the previous one. With
    every entry looking up to the same list that is the same thing, and the
    result is that list. *)
Lemma same_lab_h_all : forall iss labels ts,
  (forall i, List.In i iss -> lookup_N labels i = Some ts) ->
  same_lab_h iss labels ts = Some ts.
Proof.
  induction iss as [|i iss IH]; intros labels ts Hall; [reflexivity|].
  cbn [same_lab_h].
  rewrite (Hall i (ltac:(left; reflexivity))). rewrite eqxx.
  apply IH. intros j Hj. apply Hall. right. exact Hj.
Qed.

Lemma same_lab_all : forall iss labels ts,
  iss <> [] ->
  (forall i, List.In i iss -> lookup_N labels i = Some ts) ->
  same_lab iss labels = Some ts.
Proof.
  intros iss labels ts Hne Hall. destruct iss as [|i iss]; [contradiction|].
  cbn [same_lab]. rewrite (Hall i (ltac:(left; reflexivity))).
  apply same_lab_h_all. intros j Hj. apply Hall. right. exact Hj.
Qed.

(** The converse, for the completeness direction: if the checker accepted the
    table then every entry does look up to the list it settled on. *)
Lemma same_lab_h_inv : forall iss labels ts tls,
  same_lab_h iss labels ts = Some tls ->
  tls = ts /\ forall i, List.In i iss -> lookup_N labels i = Some ts.
Proof.
  induction iss as [|i iss IH]; intros labels ts tls H.
  - cbn [same_lab_h] in H. injection H as <-.
    split; [reflexivity | intros j Hj; destruct Hj].
  - cbn [same_lab_h] in H.
    destruct (lookup_N labels i) as [xx|] eqn:Hl; [|discriminate].
    destruct (xx == ts) eqn:Heq; [|discriminate].
    move: Heq. move/eqP => Heq. subst xx.
    destruct (IH labels ts tls H) as [Htls Hrest].
    split; [exact Htls|]. intros j Hj. destruct Hj as [Hj|Hj].
    + subst j. exact Hl.
    + apply Hrest. exact Hj.
Qed.

Lemma same_lab_inv : forall iss labels tls,
  same_lab iss labels = Some tls ->
  forall i, List.In i iss -> lookup_N labels i = Some tls.
Proof.
  intros iss labels tls H. destruct iss as [|i iss]; [discriminate|].
  cbn [same_lab] in H.
  destruct (lookup_N labels i) as [xx|] eqn:Hl; [|discriminate].
  destruct (same_lab_h_inv iss labels xx tls H) as [-> Hrest].
  intros j Hj. destruct Hj as [Hj|Hj]; [subst j; exact Hl | apply Hrest; exact Hj].
Qed.

(** [translate_vt_v] is injective, so a frame's label determines its branch
    target's block type. That is what lets the completeness direction conclude
    that labels the checker gave one list to have the block type the reader's
    running comparison demands. *)
Lemma translate_vt_v_inj : forall a b,
  translate_vt_v a = translate_vt_v b -> a = b.
Proof. intros a b H. destruct a; destruct b; first [reflexivity | discriminate]. Qed.

Lemma ctrl_label_bt_inj : forall c c',
  ctrl_label c = ctrl_label c' ->
  branch_target_bt_of c = branch_target_bt_of c'.
Proof.
  intros c c' H. unfold ctrl_label, ctrl_target, translate_typelist in H.
  destruct (branch_target_bt_of c) as [|v]; destruct (branch_target_bt_of c') as [|v'];
    cbn in H; try discriminate.
  - reflexivity.
  - injection H as H. rewrite (translate_vt_v_inj v v' H). reflexivity.
Qed.

(** A resolved depth is a [tc_labels] lookup, and what it finds is the branch
    target's result list. *)
Lemma depth_target_label : forall C0 st d bt,
  depth_target st d bt ->
  lookup_N (tc_labels (ctx_at C0 st)) (Z.to_N d)
    = Some (translate_typelist (block_results_of bt)).
Proof.
  intros C0 st d bt [c [Hlt [Hnth Hbt]]].
  unfold lookup_N. rewrite N_to_nat_Z_to_N.
  rewrite (ctx_at_label_lookup C0 st (Z.to_nat d) c Hlt Hnth).
  unfold ctrl_label, ctrl_target. rewrite Hbt. reflexivity.
Qed.

Theorem step_br_table : forall C0 st fs pre f data ls x common st',
  Inv C0 st fs -> fs = pre ++ [f] ->
  List.Forall (fun d => depth_target st d common) (ls ++ [x]) ->
  opiter_read_br_table st data = Ok (Core_result_Result_Ok common, st') ->
  Inv C0 st'
      (pre ++ [{| fv_ctrl :=
                    {| opiter_Ctrl_kind := (fv_ctrl f).(opiter_Ctrl_kind);
                       opiter_Ctrl_block_type :=
                         (fv_ctrl f).(opiter_Ctrl_block_type);
                       opiter_Ctrl_value_stack_base :=
                         (fv_ctrl f).(opiter_Ctrl_value_stack_base);
                       opiter_Ctrl_polymorphic_base := true |};
                  fv_seg := [];
                  fv_done := fv_done f
                             ++ [BI_br_table (List.map Z.to_N ls)
                                             (Z.to_N x)];
                  fv_then := fv_then f |}]).
Proof.
  intros C0 st fs pre f data ls x common st' Hinv Hfs Hdt H. subst fs.
  unfold opiter_read_br_table in H.
  destruct (opiter_take_pending st opiter_op_br_table) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  destruct (take_pending_stacks st _ r0 st1 Htp) as [Hv1 Hc1].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_fields C0 st st1 _ Hv1 Hc1 Hinv)).
  destruct (reader_read_u32_leb data st1.(opiter_OpIterState_pos)) as [r1|]
    eqn:Hleb; cbn [bind] in H; [|discriminate].
  destruct r1 as [[count p1]|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  (* the count and the labels move only the cursor *)
  destruct (opiter_read_table_labels
              {| opiter_OpIterState_vals := st1.(opiter_OpIterState_vals);
                 opiter_OpIterState_ctrls := st1.(opiter_OpIterState_ctrls);
                 opiter_OpIterState_pos := p1;
                 opiter_OpIterState_pending := st1.(opiter_OpIterState_pending)
              |} data count) as [[r2 st2]|] eqn:Htl;
    cbn [bind] in H; [|discriminate].
  destruct (read_table_labels_fields _ data count r2 st2 Htl) as [Hv2 Hc2].
  cbn [opiter_OpIterState_vals opiter_OpIterState_ctrls] in Hv2, Hc2.
  destruct r2 as [expect|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  assert (Hinv2 : Inv C0 st2 (pre ++ [f]))
    by (apply (Inv_fields C0 st1 st2 _ Hv2 Hc2 Hinv1)).
  destruct (opiter_read_label st2 data) as [[r3 st3]|] eqn:Hrl;
    cbn [bind] in H; [|discriminate].
  destruct (read_label_fields st2 data r3 st3 Hrl) as [Hv3 Hc3].
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
  assert (Hinv3 : Inv C0 st3 (pre ++ [f]))
    by (apply (Inv_fields C0 st2 st3 _ Hv3 Hc3 Hinv2)).
  destruct (Inv_split C0 st3 pre f Hinv3) as [Hbase3 [Hsplit3 Hunr3]].
  (* the condition *)
  destruct (opiter_pop_with_type st3 Types_ValueType_I32) as [[r5 st4]|] eqn:Hp5;
    cbn [bind] in H; [|discriminate].
  destruct r5 as [t5|e5].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (pop_with_type_sim st3 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 t5 st4 Hsplit3 Hbase3 Hunr3 Hp5)
    as [seg1 [Hc4 [Hv4 Hcon1]]].
  destruct (cur_views_ctrls st3 st4 Hc4) as [Hb4 Hu4].
  (* the target's types *)
  destruct (opiter_block_results common0) as [types|] eqn:Hbr;
    cbn [bind] in H; [|discriminate].
  pose proof (block_results_spec _ types Hbr) as Htypes.
  rewrite vec_deref_spec in H.
  destruct (opiter_pop_types st4 types) as [[r6 st5]|] eqn:Hpt;
    cbn [bind] in H; [|discriminate].
  destruct r6 as [u6|e6].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u6. rewrite branch_ok in H. cbn [bind] in H.
  destruct (pop_types_sim st4 (List.concat (List.map fv_seg pre))
              {| fv_ctrl := fv_ctrl f; fv_seg := seg1; fv_done := fv_done f;
fv_then := fv_then f |}
              types st5)
    as [seg2 [Hc5 [Hv5 Hcon2]]].
  { cbn [fv_seg]. exact Hv4. }
  { cbn [fv_ctrl]. rewrite Hb4. exact Hbase3. }
  { cbn [fv_ctrl]. rewrite Hu4. exact Hunr3. }
  { exact Hpt. }
  cbn [fv_ct fv_seg fv_ctrl] in Hcon2.
  destruct (opiter_mark_unreachable st5) as [st6|] eqn:Hmu; cbn [bind] in H;
    [|discriminate].
  injection H as Hcv <-. subst common0.
  (* the frames, exactly as [br] leaves them *)
  assert (Hsnoc : vec_list st3.(opiter_OpIterState_ctrls)
                  = List.map fv_ctrl pre ++ [fv_ctrl f])
    by (destruct Hinv3 as [K1 _]; rewrite K1; rewrite List.map_app;
        reflexivity).
  assert (Hbf : Z.to_nat (to_Z (fv_ctrl f).(opiter_Ctrl_value_stack_base))
                = List.length (List.concat (List.map fv_seg pre))).
  { unfold cur_base_nat in Hbase3.
    rewrite (cur_ctrl_snoc st3 (List.map fv_ctrl pre) (fv_ctrl f) Hsnoc)
      in Hbase3.
    exact Hbase3. }
  assert (Hsnoc5 : vec_list st5.(opiter_OpIterState_ctrls)
                   = List.map fv_ctrl pre ++ [fv_ctrl f])
    by (rewrite Hc5; rewrite Hc4; exact Hsnoc).
  assert (Hle : (Z.to_nat (to_Z (fv_ctrl f).(opiter_Ctrl_value_stack_base))
                 <= List.length (vec_list st5.(opiter_OpIterState_vals)))%nat)
    by (rewrite Hbf; rewrite Hv5; rewrite List.app_length; lia).
  destruct (mark_unreachable_spec st5 st6 (List.map fv_ctrl pre) (fv_ctrl f)
              Hsnoc5 Hle Hmu) as [Hmv Hmc].
  (* the labels, and the table's own obligation *)
  assert (Hlbls : tc_labels (ctx_at C0 st)
                  = ctrl_label (fv_ctrl f) :: labels_after [] pre).
  { pose proof (labels_after_ctx_at C0 st (pre ++ [f])
                  (ltac:(destruct Hinv as [K1 _]; rewrite K1;
                         rewrite List.map_app; reflexivity)))
      as Hla.
    rewrite (labels_after_snoc [] pre f) in Hla. symmetry. exact Hla. }
  assert (Hsame : same_lab (List.map Z.to_N ls ++ [Z.to_N x])
                           (ctrl_label (fv_ctrl f) :: labels_after [] pre)
                  = Some (translate_typelist (block_results_of common))).
  { rewrite -Hlbls. apply same_lab_all.
    - intros Hbad. destruct ls as [|l0 ls0]; discriminate Hbad.
    - intros i Hi.
      assert (Hd : exists d, List.In d (ls ++ [x]) /\ i = Z.to_N d).
      { apply List.in_app_or in Hi. destruct Hi as [Hi|Hi].
        - apply List.in_map_iff in Hi. destruct Hi as [d [Hd Hin]].
          exists d. split; [apply List.in_or_app; left; exact Hin
                           | symmetry; exact Hd].
        - destruct Hi as [Hi|Hi]; [|contradiction].
          exists x. split; [apply List.in_or_app; right; left; reflexivity
                           | symmetry; exact Hi]. }
      destruct Hd as [d [Hin ->]].
      apply depth_target_label.
      rewrite (List.Forall_forall) in Hdt. apply (Hdt d Hin). }
  apply (Inv_step_last C0 st3 st6 pre f _ Hinv3).
  - reflexivity.
  - rewrite Hmc. rewrite List.map_app. reflexivity.
  - rewrite Hmv. rewrite Hv5. rewrite Hbf. rewrite List.firstn_app.
    rewrite List.firstn_all.
    assert (Hz : (List.length (List.concat (List.map fv_seg pre))
                  - List.length (List.concat (List.map fv_seg pre)))%nat
                 = 0%nat) by lia.
    rewrite Hz. cbn [List.firstn]. rewrite List.app_nil_r.
    rewrite List.map_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg]. rewrite List.app_nil_r.
    rewrite List.app_nil_r. reflexivity.
  - apply (frames_ok_append_ctrl_at C0 [] pre f _
             (BI_br_table (List.map Z.to_N ls) (Z.to_N x)) []).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + destruct Hinv3 as [_ [_ [_ K4]]]. exact K4.
    + cbn [check_single]. cbn [tc_labels with_labels].
      rewrite cat_app. rewrite Hsame.
      unfold type_update_top.
      rewrite (consume_cons_split (fv_ct f) (T_num T_i32)
                 (translate_typelist (block_results_of common))
                 <<translate_vals seg1,
                   (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>> Hcon1).
      rewrite Htypes in Hcon2. rewrite Hcon2. reflexivity.
Qed.

Theorem step_return : forall C0 ctx st fs pre f st',
  Inv C0 st fs -> fs = pre ++ [f] -> return_agree ctx C0 ->
  opiter_read_return st ctx = Ok (Core_result_Result_Ok tt, st') ->
  Inv C0 st'
      (pre ++ [{| fv_ctrl :=
                    {| opiter_Ctrl_kind := (fv_ctrl f).(opiter_Ctrl_kind);
                       opiter_Ctrl_block_type :=
                         (fv_ctrl f).(opiter_Ctrl_block_type);
                       opiter_Ctrl_value_stack_base :=
                         (fv_ctrl f).(opiter_Ctrl_value_stack_base);
                       opiter_Ctrl_polymorphic_base := true |};
                  fv_seg := [];
                  fv_done := fv_done f ++ [BI_return];
                  fv_then := fv_then f |}]).
Proof.
  intros C0 ctx st fs pre f st' Hinv Hfs Hag H. subst fs.
  unfold opiter_read_return in H.
  destruct (opiter_take_pending st opiter_op_return) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (take_pending_ok_inv st opiter_op_return st1 Htp) as Hobs.
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  assert (Hsnoc : vec_list st1.(opiter_OpIterState_ctrls)
                  = List.map fv_ctrl pre ++ [fv_ctrl f]).
  { destruct Hinv1 as [K1 _]. rewrite K1. rewrite List.map_app. reflexivity. }
  unfold return_agree in Hag.
  rename Hag into Hret.
  destruct (opiter_pop_types st1 (alloc_vec_Vec_deref ctx.(opiter_Context_results))) as [[r1 st2]|]
    eqn:Hpt; cbn [bind] in H; [|discriminate].
  destruct r1 as [u1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u1. rewrite branch_ok in H. cbn [bind] in H.
  rewrite vec_deref_spec in Hpt.
  destruct (pop_types_sim st1 (List.concat (List.map fv_seg pre)) f ctx.(opiter_Context_results) st2
              Hsplit1 Hbase1 Hunr1 Hpt) as [seg1 [Hc2 [Hv2 Hcon]]].
  destruct (opiter_mark_unreachable st2) as [st3|] eqn:Hmu; cbn [bind] in H;
    [|discriminate].
  injection H as <-.
  (* [mark_unreachable] truncates to the frame's base and sets its flag *)
  assert (Hbf : Z.to_nat (to_Z (fv_ctrl f).(opiter_Ctrl_value_stack_base))
                = List.length (List.concat (List.map fv_seg pre))).
  { unfold cur_base_nat in Hbase1.
    rewrite (cur_ctrl_snoc st1 (List.map fv_ctrl pre) (fv_ctrl f) Hsnoc)
      in Hbase1.
    exact Hbase1. }
  assert (Hsnoc2 : vec_list st2.(opiter_OpIterState_ctrls)
                   = List.map fv_ctrl pre ++ [fv_ctrl f]).
  { rewrite Hc2. exact Hsnoc. }
  assert (Hle : (Z.to_nat (to_Z (fv_ctrl f).(opiter_Ctrl_value_stack_base))
                 <= List.length (vec_list st2.(opiter_OpIterState_vals)))%nat).
  { rewrite Hbf. rewrite Hv2. rewrite List.app_length. lia. }
  destruct (mark_unreachable_spec st2 st3 (List.map fv_ctrl pre) (fv_ctrl f)
              Hsnoc2 Hle Hmu) as [Hmv Hmc].
  apply (Inv_step_last C0 st1 st3 pre f _ Hinv1).
  - reflexivity.
  - rewrite Hmc. rewrite List.map_app. reflexivity.
  - rewrite Hmv. rewrite Hv2. rewrite Hbf. rewrite List.firstn_app.
    rewrite List.firstn_all.
    assert (Hz : (List.length (List.concat (List.map fv_seg pre))
                  - List.length (List.concat (List.map fv_seg pre)))%nat
                 = 0%nat).
    { lia. }
    rewrite Hz. cbn [List.firstn]. rewrite List.app_nil_r.
    rewrite List.map_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg]. rewrite List.app_nil_r.
    rewrite List.app_nil_r. reflexivity.
  - apply (frames_ok_append_ctrl C0 [] pre f _ BI_return []).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + destruct Hinv1 as [_ [_ [_ K4]]]. exact K4.
    + intros lbls. cbn [check_single]. cbn [tc_return with_labels].
      rewrite Hret. unfold type_update_top. rewrite Hcon. reflexivity.
Qed.

(** [memory.size] and [memory.grow]: WasmCert guards both on the same memory
    lookup the loads and stores need, and their effects are the two shapes
    already covered, push one and pop-then-push. *)
(** [call]: the first operator whose pops and pushes are lists from the context
    rather than a shape fixed by the opcode. [pop_types_sim] is the whole of the
    consume side and [push_types_seg_spec] the whole of the produce side, so the
    proof is [step_binary]'s with the fixed lists replaced by the callee's. *)
Theorem step_call : forall C0 module st fs pre f data idx st',
  Inv C0 st fs -> fs = pre ++ [f] -> funcs_agree module C0 ->
  opiter_read_call st data module = Ok (Core_result_Result_Ok idx, st') ->
  exists seg',
    Inv C0 st'
        (pre ++ [{| fv_ctrl := fv_ctrl f;
                    fv_seg := seg';
                    fv_done := fv_done f
                               ++ [BI_call (Z.to_N (to_Z idx))];
                               fv_then := fv_then f |}]).
Proof.
  intros C0 module st fs pre f data idx st' Hinv Hfs Hag H. subst fs.
  unfold opiter_read_call in H.
  destruct (opiter_take_index st data opiter_op_call) as [[r0 st1]|] eqn:Hti;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [idx0|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (take_index_fields st data _ _ st1 Hti) as [Hv1 Hc1].
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_fields C0 st st1 _ Hv1 Hc1 Hinv)).
  destruct (Inv_split C0 st1 pre f Hinv1) as [Hbase1 [Hsplit1 Hunr1]].
  destruct (scalar_cast U32 Usize idx0) as [i|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  assert (Hi : to_Z i = to_Z idx0)
    by (unfold scalar_cast in Hcast; apply mk_scalar_ok_to_Z in Hcast;
        exact Hcast).
  destruct (i s>= alloc_vec_Vec_len module.(env_Env_func_types));
    [discriminate|].
  destruct (alloc_vec_Vec_index
              (core_slice_index_SliceIndexUsizeSliceInst types_FuncType_t)
              module.(env_Env_func_types) i) as [ft|] eqn:Hidx;
    cbn [bind] in H; [|discriminate].
  pose proof (ft_lookup _ _ idx0 i ft Hag Hi Hidx) as Hlk.
  destruct (opiter_require_single_result
              (alloc_vec_Vec_deref ft.(types_FuncType_results))) as [r1|] eqn:Hrs;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [u1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u1. rewrite branch_ok in H. cbn [bind] in H.
  (* the parameters come off *)
  destruct (opiter_pop_types st1 (alloc_vec_Vec_deref ft.(types_FuncType_params)))
    as [[r2 st2]|] eqn:Hpt; cbn [bind] in H; [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  rewrite vec_deref_spec in Hpt.
  destruct (pop_types_sim st1 (List.concat (List.map fv_seg pre)) f
              ft.(types_FuncType_params) st2 Hsplit1 Hbase1 Hunr1 Hpt)
    as [seg1 [Hc2 [Hv2 Hcon]]].
  (* and the results go on *)
  destruct (opiter_push_types st2
              (alloc_vec_Vec_deref ft.(types_FuncType_results))) as [st3|]
    eqn:Hpu; cbn [bind] in H; [|discriminate].
  injection H as Hidxe <-. rewrite -Hidxe.
  rewrite vec_deref_spec in Hpu.
  destruct (push_types_seg_spec st2 ft.(types_FuncType_results) st3 Hpu)
    as [Hv3 Hc3].
  exists (seg1 ++ types_seg (vec_list ft.(types_FuncType_results))).
  apply (Inv_step_last C0 st1 st3 pre f _ Hinv1).
  - reflexivity.
  - rewrite Hc3. rewrite Hc2. destruct Hinv1 as [K1 _]. rewrite K1.
    rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hv3. rewrite Hv2.
    rewrite List.map_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg]. rewrite List.app_nil_r.
    rewrite List.app_assoc. reflexivity.
  - apply frames_ok_append; [destruct Hinv1 as [_ [_ [_ K4]]]; exact K4|].
    intros lbls.
    rewrite (effect_call C0 (Z.to_N (to_Z idx0)) _ _ Hlk).
    unfold type_update. rewrite Hcon. cbn [produce CT_type CT_unr].
    rewrite translate_vals_app. rewrite translate_vals_types_seg. reflexivity.
Qed.

(** [call_indirect]: [call] with the table index popped first and the table
    looked up. The reserved zero byte moves only the cursor. *)
Theorem step_call_indirect : forall C0 module st fs pre f data idx st',
  Inv C0 st fs -> fs = pre ++ [f] -> types_agree module C0 -> tables_agree module C0 ->
  opiter_read_call_indirect st data module
    = Ok (Core_result_Result_Ok idx, st') ->
  exists seg',
    Inv C0 st'
        (pre ++ [{| fv_ctrl := fv_ctrl f;
                    fv_seg := seg';
                    fv_done := fv_done f
                               ++ [BI_call_indirect 0%N
                                     (Z.to_N (to_Z idx))];
                                     fv_then := fv_then f |}]).
Proof.
  intros C0 module st fs pre f data idx st' Hinv Hfs Hty Htab H. subst fs.
  unfold opiter_read_call_indirect in H.
  destruct (opiter_take_index st data opiter_op_call_indirect) as [[r0 st1]|]
    eqn:Hti; cbn [bind] in H; [|discriminate].
  destruct r0 as [idx0|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (take_index_fields st data _ _ st1 Hti) as [Hv1 Hc1].
  destruct (opiter_read_reserved_zero st1 data) as [[r1 st2]|] eqn:Hrz;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [u1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u1. rewrite branch_ok in H. cbn [bind] in H.
  destruct (read_reserved_zero_fields st1 data _ st2 Hrz) as [Hv2 Hc2].
  assert (Hinv2 : Inv C0 st2 (pre ++ [f])).
  { apply (Inv_fields C0 st st2 _ (ltac:(rewrite Hv2; exact Hv1))
             (ltac:(rewrite Hc2; exact Hc1)) Hinv). }
  destruct (Inv_split C0 st2 pre f Hinv2) as [Hbase2 [Hsplit2 Hunr2]].
  rewrite vec_is_empty_spec in H. cbn [bind] in H.
  destruct (vec_list module.(env_Env_table_types)) as [|t0 ts] eqn:Hts;
    [discriminate|].
  destruct (tables_nonempty_lookup module C0 Htab
              (ltac:(rewrite Hts; discriminate))) as [tabt [Htlk Helem]].
  destruct (scalar_cast U32 Usize idx0) as [i|] eqn:Hcast; cbn [bind] in H;
    [|discriminate].
  assert (Hi : to_Z i = to_Z idx0)
    by (unfold scalar_cast in Hcast; apply mk_scalar_ok_to_Z in Hcast;
        exact Hcast).
  destruct (i s>= alloc_vec_Vec_len module.(env_Env_types));
    [discriminate|].
  destruct (alloc_vec_Vec_index
              (core_slice_index_SliceIndexUsizeSliceInst types_FuncType_t)
              module.(env_Env_types) i) as [ft|] eqn:Hidx;
    cbn [bind] in H; [|discriminate].
  pose proof (ft_lookup _ _ idx0 i ft Hty Hi Hidx) as Hlk.
  destruct (opiter_require_single_result
              (alloc_vec_Vec_deref ft.(types_FuncType_results))) as [r2|] eqn:Hrs;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  (* the table index *)
  destruct (opiter_pop_with_type st2 Types_ValueType_I32) as [[r3 st3]|] eqn:Hpw;
    cbn [bind] in H; [|discriminate].
  destruct r3 as [t3|e3].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (pop_with_type_sim st2 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 t3 st3 Hsplit2 Hbase2 Hunr2 Hpw)
    as [seg1 [Hc3 [Hv3 Hcon1]]].
  destruct (cur_views_ctrls st2 st3 Hc3) as [Hb3 Hu3].
  (* then the parameters, on the frame with the shortened segment *)
  destruct (opiter_pop_types st3 (alloc_vec_Vec_deref ft.(types_FuncType_params)))
    as [[r4 st4]|] eqn:Hpt; cbn [bind] in H; [|discriminate].
  destruct r4 as [u4|e4].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u4. rewrite branch_ok in H. cbn [bind] in H.
  rewrite vec_deref_spec in Hpt.
  destruct (pop_types_sim st3 (List.concat (List.map fv_seg pre))
              {| fv_ctrl := fv_ctrl f; fv_seg := seg1; fv_done := fv_done f;
fv_then := fv_then f |}
              ft.(types_FuncType_params) st4)
    as [seg2 [Hc4 [Hv4 Hcon2]]].
  { cbn [fv_seg]. exact Hv3. }
  { cbn [fv_ctrl]. rewrite Hb3. exact Hbase2. }
  { cbn [fv_ctrl]. rewrite Hu3. exact Hunr2. }
  { exact Hpt. }
  cbn [fv_ct fv_seg fv_ctrl] in Hcon2.
  destruct (opiter_push_types st4
              (alloc_vec_Vec_deref ft.(types_FuncType_results))) as [st5|]
    eqn:Hpu; cbn [bind] in H; [|discriminate].
  injection H as Hidxe <-. rewrite -Hidxe.
  rewrite vec_deref_spec in Hpu.
  destruct (push_types_seg_spec st4 ft.(types_FuncType_results) st5 Hpu)
    as [Hv5 Hc5].
  exists (seg2 ++ types_seg (vec_list ft.(types_FuncType_results))).
  apply (Inv_step_last C0 st2 st5 pre f _ Hinv2).
  - reflexivity.
  - rewrite Hc5. rewrite Hc4. rewrite Hc3.
    destruct Hinv2 as [K1 _]. rewrite K1.
    rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hv5. rewrite Hv4.
    rewrite List.map_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg]. rewrite List.app_nil_r.
    rewrite List.app_assoc. reflexivity.
  - apply frames_ok_append; [destruct Hinv2 as [_ [_ [_ K4]]]; exact K4|].
    intros lbls.
    rewrite (effect_call_indirect C0 0%N (Z.to_N (to_Z idx0)) tabt _ _
               Htlk Helem Hlk).
    unfold type_update.
    rewrite (consume_cons_split (fv_ct f) (T_num T_i32)
               (translate_typelist (vec_list ft.(types_FuncType_params)))
               <<translate_vals seg1,
                 (fv_ctrl f).(opiter_Ctrl_polymorphic_base)>> Hcon1).
    rewrite Hcon2. cbn [produce CT_type CT_unr].
    rewrite translate_vals_app. rewrite translate_vals_types_seg. reflexivity.
Qed.

Lemma effect_memory_size : forall C0 m,
  lookup_N (tc_mems C0) 0%N = Some m ->
  effect_in C0 BI_memory_size [] [T_num T_i32].
Proof.
  intros C0 m Hlk lbls ct. cbn [check_single with_labels tc_mems].
  rewrite Hlk. reflexivity.
Qed.

Lemma effect_memory_grow : forall C0 m,
  lookup_N (tc_mems C0) 0%N = Some m ->
  effect_in C0 BI_memory_grow [T_num T_i32] [T_num T_i32].
Proof.
  intros C0 m Hlk lbls ct. cbn [check_single with_labels tc_mems].
  rewrite Hlk. reflexivity.
Qed.

Theorem step_memory_size : forall C0 module st fs pre f data st',
  Inv C0 st fs -> fs = pre ++ [f] -> mems_agree module C0 ->
  opiter_read_memory_size st data module = Ok (Core_result_Result_Ok tt, st') ->
  Inv C0 st'
      (pre ++ [{| fv_ctrl := fv_ctrl f;
                  fv_seg := fv_seg f ++ [Opiter_StackType_Val Types_ValueType_I32];
                  fv_done := fv_done f ++ [BI_memory_size];
                  fv_then := fv_then f |}]).
Proof.
  intros C0 module st fs pre f data st' Hinv Hfs Hag H. subst fs.
  unfold opiter_read_memory_size in H.
  destruct (opiter_take_pending st opiter_op_memory_size) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (take_pending_ok_inv st opiter_op_memory_size st1 Htp) as Hobs.
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  destruct (opiter_read_reserved_zero st1 data) as [[r1 st2]|] eqn:Hrz;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [u1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u1. rewrite branch_ok in H. cbn [bind] in H.
  destruct (read_reserved_zero_fields st1 data _ st2 Hrz) as [Hv2 Hc2].
  assert (Hinv2 : Inv C0 st2 (pre ++ [f]))
    by (apply (Inv_fields C0 st1 st2 _ Hv2 Hc2 Hinv1)).
  destruct (opiter_require_memory module) as [r2|] eqn:Hrm; cbn [bind] in H;
    [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (require_memory_lookup module C0 Hag Hrm) as [m Hlk].
  destruct (opiter_push_val st2 (Opiter_StackType_Val Types_ValueType_I32))
    as [st3|] eqn:Hpv; cbn [bind] in H; [|discriminate].
  injection H as <-.
  destruct (push_val_spec _ _ _ Hpv) as [Hpvals [Hpctrls _]].
  apply (Inv_step_last C0 st2 st3 pre f _ Hinv2).
  - reflexivity.
  - rewrite Hpctrls. destruct Hinv2 as [K1 _]. rewrite K1.
    rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hpvals. destruct Hinv2 as [_ [K2 _]]. rewrite K2.
    rewrite List.map_app. rewrite List.map_app.
    rewrite List.concat_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg].
    rewrite List.app_nil_r. rewrite List.app_nil_r.
    rewrite List.app_assoc. reflexivity.
  - apply frames_ok_append; [destruct Hinv2 as [_ [_ [_ K4]]]; exact K4|].
    intros lbls. rewrite (effect_memory_size C0 m Hlk).
    unfold type_update. cbn [consume produce CT_type CT_unr].
    rewrite translate_vals_snoc. reflexivity.
Qed.

Theorem step_memory_grow : forall C0 module st fs pre f data st',
  Inv C0 st fs -> fs = pre ++ [f] -> mems_agree module C0 ->
  opiter_read_memory_grow st data module = Ok (Core_result_Result_Ok tt, st') ->
  exists seg',
    Inv C0 st'
        (pre ++ [{| fv_ctrl := fv_ctrl f;
                    fv_seg := seg' ++ [Opiter_StackType_Val Types_ValueType_I32];
                    fv_done := fv_done f ++ [BI_memory_grow];
                    fv_then := fv_then f |}]).
Proof.
  intros C0 module st fs pre f data st' Hinv Hfs Hag H. subst fs.
  unfold opiter_read_memory_grow in H.
  destruct (opiter_take_pending st opiter_op_memory_grow) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (take_pending_ok_inv st opiter_op_memory_grow st1 Htp) as Hobs.
  assert (Hinv1 : Inv C0 st1 (pre ++ [f]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  destruct (opiter_read_reserved_zero st1 data) as [[r1 st2]|] eqn:Hrz;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [u1|e1].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u1. rewrite branch_ok in H. cbn [bind] in H.
  destruct (read_reserved_zero_fields st1 data _ st2 Hrz) as [Hv2 Hc2].
  assert (Hinv2 : Inv C0 st2 (pre ++ [f]))
    by (apply (Inv_fields C0 st1 st2 _ Hv2 Hc2 Hinv1)).
  destruct (opiter_require_memory module) as [r2|] eqn:Hrm; cbn [bind] in H;
    [|discriminate].
  destruct r2 as [u2|e2].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u2. rewrite branch_ok in H. cbn [bind] in H.
  destruct (require_memory_lookup module C0 Hag Hrm) as [m Hlk].
  destruct (Inv_split C0 st2 pre f Hinv2) as [Hbase2 [Hsplit2 Hunr2]].
  destruct (opiter_pop_with_type st2 Types_ValueType_I32) as [[r3 st3]|] eqn:Hp3;
    cbn [bind] in H; [|discriminate].
  destruct r3 as [t3|e3].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (pop_with_type_sim st2 (List.concat (List.map fv_seg pre)) f
              Types_ValueType_I32 t3 st3 Hsplit2 Hbase2 Hunr2 Hp3)
    as [seg3 [Hc3 [Hv3 Hcon3]]].
  destruct (opiter_push_val st3 (Opiter_StackType_Val Types_ValueType_I32))
    as [st4|] eqn:Hpv; cbn [bind] in H; [|discriminate].
  injection H as <-.
  destruct (push_val_spec _ _ _ Hpv) as [Hpvals [Hpctrls _]].
  exists seg3.
  apply (Inv_step_last C0 st2 st4 pre f _ Hinv2).
  - reflexivity.
  - rewrite Hpctrls. rewrite Hc3. destruct Hinv2 as [K1 _]. rewrite K1.
    rewrite List.map_app. rewrite List.map_app. reflexivity.
  - rewrite Hpvals. rewrite Hv3.
    rewrite List.map_app. rewrite List.concat_app.
    cbn [List.map List.concat fv_seg]. rewrite List.app_nil_r.
    rewrite List.app_assoc. reflexivity.
  - apply frames_ok_append; [destruct Hinv2 as [_ [_ [_ K4]]]; exact K4|].
    intros lbls. rewrite (effect_memory_grow C0 m Hlk).
    unfold type_update. rewrite Hcon3. cbn [produce CT_type CT_unr].
    rewrite translate_vals_snoc. reflexivity.
Qed.

(** The same for [else], which needs less: its guard rejects any frame but an
    open then-branch, so a successful run reports the kind by itself and the
    dispatch does not have to know it in advance. *)
Lemma read_else_frame : forall C0 st fs pre' g bt st',
  Inv C0 st fs -> fs = pre' ++ [g] ->
  opiter_read_else st = Ok (Core_result_Result_Ok bt, st') ->
  (fv_ctrl g).(opiter_Ctrl_kind) = Opiter_LabelKind_Then.
Proof.
  intros C0 st fs pre' g bt st' Hinv Hfs H. subst fs.
  unfold opiter_read_else in H.
  destruct (opiter_take_pending st opiter_op_else) as [[r0 st1]|] eqn:Htp;
    cbn [bind] in H; [|discriminate].
  destruct r0 as [u|e].
  2: { rewrite branch_err in H. cbn [bind] in H.
       rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
  destruct u. rewrite branch_ok in H. cbn [bind] in H.
  pose proof (take_pending_ok_inv st opiter_op_else st1 Htp) as Hobs.
  assert (Hinv1 : Inv C0 st1 (pre' ++ [g]))
    by (apply (Inv_obs C0 st st1 _ Hobs Hinv)).
  assert (Hsnoc : vec_list st1.(opiter_OpIterState_ctrls)
                  = List.map fv_ctrl pre' ++ [fv_ctrl g]).
  { destruct Hinv1 as [K1 _]. rewrite K1. rewrite List.map_app. reflexivity. }
  destruct (alloc_vec_Vec_len st1.(opiter_OpIterState_ctrls) s= 0%usize) eqn:Hn;
    [discriminate|].
  destruct (usize_sub (alloc_vec_Vec_len st1.(opiter_OpIterState_ctrls))
              1%usize) as [i|] eqn:Hsub; cbn [bind] in H; [|discriminate].
  rewrite vec_index_spec in H.
  rewrite (ctrls_last_index st1 (List.map fv_ctrl pre') (fv_ctrl g) i
             Hsnoc Hsub) in H.
  cbn [bind] in H.
  destruct (opiter_is_then (fv_ctrl g).(opiter_Ctrl_kind)) as [b|] eqn:Hit;
    cbn [bind] in H; [|discriminate].
  destruct b; [|discriminate].
  destruct (is_then_spec _ _ Hit) as [[_ Hk] | [Hbad _]];
    [exact Hk | discriminate Hbad].
Qed.

(** [end] closing the outermost frame is not a step: there is no enclosing frame
    to append to. What it yields instead is the finished function body, and the
    typing side of that turns out to be almost free.

    [frames_ok C0 [] [f]] *is* [b_e_type_checker_aux]'s fold, because a [Body]
    frame's label is its results just as a [Block]'s is, and [upd_label] is
    [with_labels]. So the top-level theorem's typing obligation is the invariant's
    own obligation, read in the other direction. *)
Lemma end_body_typing : forall C0 f bt,
  (fv_ctrl f).(opiter_Ctrl_kind) = Opiter_LabelKind_Body ->
  (fv_ctrl f).(opiter_Ctrl_block_type) = bt ->
  frames_ok C0 [] [f] ->
  c_types_agree (fv_ct f) (translate_typelist (block_results_of bt)) = true ->
  b_e_type_checker_aux
    (upd_label C0 [translate_typelist (block_results_of bt)])
    (fv_done f)
    (Tf [] (translate_typelist (block_results_of bt))) = true.
Proof.
  intros C0 f bt Hkind Hbt [[Hfold _] _] Hagree.
  assert (Hlbl : ctrl_label (fv_ctrl f)
                 = translate_typelist (block_results_of bt)).
  { unfold ctrl_label, ctrl_target, branch_target_bt_of. rewrite Hkind.
    rewrite Hbt. destruct bt; reflexivity. }
  rewrite Hlbl in Hfold.
  unfold b_e_type_checker_aux. rewrite upd_label_with_labels.
  rewrite Hfold. exact Hagree.
Qed.
