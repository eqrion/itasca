(** * One operator per loop iteration

    The dispatch. [read_op] takes the opcode byte and [step] dispatches to a
    reader; this says the pair advanced the state by exactly one operator, in both
    senses at once: the bytes consumed encode that operator, and the frames'
    consumed stream grew by it.

    Tying them in one conclusion is the point. Stated as two theorems each with its
    own existential, nothing would force them to agree on *which* operator, and
    agreeing is the whole content. Every branch produces the same operator from two
    directions -- [step_*_op] from the ghost lists, [repr_op] from the bytes -- and
    the branch only closes if they match.

    The [end] case is where the loop can finish, so the conclusion is a
    disjunction: either one more operator, or the body's [end] fired and what is
    left is the finished instruction sequence. *)

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
Require Import Veriwasm.OpIter_State.
Require Import Veriwasm.OpIter_Decode.
Require Import Veriwasm.OpIter_Protocol.
Require Import Veriwasm.OpIter_Sim.
Require Import Veriwasm.OpIter_Expr.
Require Import Veriwasm.OpIter_Table.
From Wasm Require Import datatypes numerics type_checker operations typing.
From Wasm Require Import type_checker_reflects_typing.

Local Open Scope list_scope.
Local Bind Scope list_scope with list.
Open Scope Z_scope.

(** One operator's worth of progress. *)
Definition op_step (C0 : t_context) (bt0 : opiter_BlockType_t) (data : slice u8)
                   (st st' : opiter_OpIterState_t)
                   (fs fs' : list fview) (op : flat_op) : Prop :=
  Inv C0 st' fs'
  /\ body_first bt0 fs'
  /\ frames_flat fs' = frames_flat fs ++ [op]
  /\ repr_op (bytes_from data st.(opiter_OpIterState_pos)) op
             (bytes_from data st'.(opiter_OpIterState_pos)).

(** The one iteration whose operator stream grows by two: the [end] that closes
    an [if] with no [else] at all. The frame becomes [BI_if bt es [::]], whose
    flattening writes the [FO_else] separating the two bodies, and the single
    [0x0B] byte encodes only the [FO_end]. [else_sugar] is what lets the loop
    put the two back together; see [OpIter_Expr.else_sugar] and spec 5.4.1's
    first [if] production. *)
Definition bare_if_step (C0 : t_context) (bt0 : opiter_BlockType_t)
                        (data : slice u8) (st st' : opiter_OpIterState_t)
                        (fs fs' : list fview) : Prop :=
  Inv C0 st' fs'
  /\ body_first bt0 fs'
  /\ frames_flat fs' = frames_flat fs ++ [FO_else; FO_end]
  /\ repr_op (bytes_from data st.(opiter_OpIterState_pos)) FO_end
             (bytes_from data st'.(opiter_OpIterState_pos)).

(** The body has been read to its closing [end]: nothing is left on the control
    stack, and the outermost frame's ghost list is the instruction sequence. *)
Definition body_done (C0 : t_context) (bt0 : opiter_BlockType_t) (data : slice u8)
                     (st st' : opiter_OpIterState_t) (fs : list fview) : Prop :=
  exists f,
    fs = [f]
    /\ (fv_ctrl f).(opiter_Ctrl_kind) = Opiter_LabelKind_Body
    /\ (fv_ctrl f).(opiter_Ctrl_block_type) = bt0
    /\ c_types_agree (fv_ct f)
         (translate_typelist (block_results_of bt0)) = true
    /\ vec_list st'.(opiter_OpIterState_ctrls) = []
    /\ repr_op (bytes_from data st.(opiter_OpIterState_pos)) FO_end
               (bytes_from data st'.(opiter_OpIterState_pos)).

(** The alignment side conditions, one tactic per natural alignment. The exponent
    ranges over at most four values, so each is a computation. *)
Local Ltac ls_bounds :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hz := fresh "Hz" in
  intros a Ha; cbn in Ha;
  first [ (assert (Hz : a = 0) by lia; subst a; reflexivity)
        | (assert (Hz : a = 0 \/ a = 1) by lia;
           destruct Hz as [Hz|Hz]; subst a; reflexivity)
        | (assert (Hz : a = 0 \/ a = 1 \/ a = 2) by lia;
           destruct Hz as [Hz|[Hz|Hz]]; subst a; reflexivity)
        | (assert (Hz : a = 0 \/ a = 1 \/ a = 2 \/ a = 3) by lia;
           destruct Hz as [Hz|[Hz|[Hz|Hz]]]; subst a; reflexivity) ].

Theorem step_op_step : forall C0 bt0 module ctx data st fs b st1 st2,
  Inv C0 st fs -> body_first bt0 fs ->
  mems_agree module C0 -> locals_agree ctx C0 -> globals_agree module C0 ->
  return_agree ctx C0 -> funcs_agree module C0 -> types_agree module C0 ->
  tables_agree module C0 ->
  opiter_read_op st data = Ok (Core_result_Result_Ok b, st1) ->
  opiter_step st1 data module ctx b = Ok (Core_result_Result_Ok tt, st2) ->
  (exists fs' op, op_step C0 bt0 data st st2 fs fs' op)
  \/ (exists fs', bare_if_step C0 bt0 data st st2 fs fs')
  \/ body_done C0 bt0 data st st2 fs.
Proof.
  intros C0 bt0 module ctx data st fs b st1 st2 Hinv Hbf Hmems Hlocals Hglobals Hret
         Hfuncs Htypes Htables Hro Hstep.
  (* [read_op] moves only the cursor, so the invariant transports to [st1] *)
  destruct (read_op_state st data _ st1 Hro) as [Hv1 Hc1].
  assert (Hinv1 : Inv C0 st1 fs)
    by (apply (Inv_fields C0 st st1 fs Hv1 Hc1 Hinv)).
  pose proof (read_op_sound st data b st1 Hro) as Hbytes.
  destruct (body_first_snoc bt0 fs Hbf) as [pre [f Hfs]].
  unfold opiter_step in Hstep.
  destruct (b s= opiter_op_nop) eqn:E1.
  { left. apply scalar_eqb_true in E1.
    destruct (step_nop_op C0 bt0 st1 fs pre f st2 Hinv1 Hbf Hfs Hstep)
      as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain BI_nop). unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_of_inert; [rewrite E1; reflexivity|].
    apply (read_nop_pos st1 _ st2 Hstep). }
  destruct (b s= opiter_op_unreachable) eqn:E2.
  { left. apply scalar_eqb_true in E2.
    destruct (step_unreachable_op C0 bt0 st1 fs pre f st2 Hinv1 Hbf Hfs Hstep)
      as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain BI_unreachable). unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_of_inert; [rewrite E2; reflexivity|].
    apply (read_unreachable_pos st1 _ st2 Hstep). }
  destruct (b s= opiter_op_i32_const) eqn:E3.
  { left. apply scalar_eqb_true in E3.
    destruct (step_wrap_ok _ _ st2 Hstep) as [v Hrd].
    destruct (step_i32_const_op C0 bt0 st1 fs pre f data v st2 Hinv1 Hbf Hfs Hrd)
      as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_const_num
                             (VAL_int32 (Wasm_int.Int32.repr (to_Z v))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply (repr_op_const _ T_i32);
      [rewrite E3; reflexivity|].
    apply (read_i32_const_sound st1 data v st2 Hrd). }
  destruct (b s= opiter_op_i64_const) eqn:E3b.
  { left. apply scalar_eqb_true in E3b.
    destruct (step_wrap_ok _ _ st2 Hstep) as [v Hrd].
    destruct (step_i64_const_op C0 bt0 st1 fs pre f data v st2 Hinv1 Hbf Hfs Hrd)
      as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_const_num
                             (VAL_int64 (Wasm_int.Int64.repr (to_Z v))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply (repr_op_const _ T_i64);
      [rewrite E3b; reflexivity|].
    apply (read_i64_const_sound st1 data v st2 Hrd). }
  destruct (b s= opiter_op_f32_const) eqn:E3c.
  { left. apply scalar_eqb_true in E3c.
    destruct (step_wrap_ok _ _ st2 Hstep) as [v Hrd].
    destruct (step_f32_const_op C0 bt0 st1 fs pre f data v st2 Hinv1 Hbf Hfs Hrd)
      as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_const_num (fconst_val T_f32 (to_Z v)))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply (repr_op_fconst _ T_f32);
      [rewrite E3c; reflexivity|].
    apply (read_f32_const_sound st1 data v st2 Hrd). }
  destruct (b s= opiter_op_f64_const) eqn:E3d.
  { left. apply scalar_eqb_true in E3d.
    destruct (step_wrap_ok _ _ st2 Hstep) as [v Hrd].
    destruct (step_f64_const_op C0 bt0 st1 fs pre f data v st2 Hinv1 Hbf Hfs Hrd)
      as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_const_num (fconst_val T_f64 (to_Z v)))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply (repr_op_fconst _ T_f64);
      [rewrite E3d; reflexivity|].
    apply (read_f64_const_sound st1 data v st2 Hrd). }
  destruct (b s= opiter_op_drop) eqn:E5.
  { left. apply scalar_eqb_true in E5.
    destruct (step_wrap_ok _ _ st2 Hstep) as [t Hrd].
    destruct (step_drop_op C0 bt0 st1 fs pre f t st2 Hinv1 Hbf Hfs Hrd)
      as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain BI_drop). unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_of_inert; [rewrite E5; reflexivity|].
    apply (read_drop_pos st1 _ st2 Hrd). }
  destruct (b s= opiter_op_select) eqn:E5s.
  { left. apply scalar_eqb_true in E5s.
    destruct (step_wrap_ok _ _ st2 Hstep) as [t Hrd].
    destruct (step_select_op C0 bt0 st1 fs pre f t st2 Hinv1 Hbf Hfs Hrd)
      as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_select None)). unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_of_inert; [rewrite E5s; reflexivity|].
    apply (read_select_pos st1 _ st2 Hrd). }
  destruct (b s= opiter_op_block) eqn:E6.
  { left. apply scalar_eqb_true in E6.
    destruct (step_wrap_ok _ _ st2 Hstep) as [bt Hrd].
    destruct (step_block_op C0 bt0 st1 fs data bt st2 Hinv1 Hbf Hrd)
      as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_block (translate_bt bt)). unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    destruct (read_block_sound st1 data bt st2 Hrd) as [bb [Hbb Hspec]].
    rewrite Hbytes. rewrite Hbb.
    apply repr_op_block; [rewrite E6; reflexivity | exact Hspec]. }
  destruct (b s= opiter_op_loop) eqn:E7.
  { left. apply scalar_eqb_true in E7.
    destruct (step_wrap_ok _ _ st2 Hstep) as [bt Hrd].
    destruct (step_loop_op C0 bt0 st1 fs data bt st2 Hinv1 Hbf Hrd)
      as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_loop (translate_bt bt)). unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    destruct (read_loop_sound st1 data bt st2 Hrd) as [bb [Hbb Hspec]].
    rewrite Hbytes. rewrite Hbb.
    apply repr_op_loop; [rewrite E7; reflexivity | exact Hspec]. }
  destruct (b s= opiter_op_if) eqn:E7i.
  { left. apply scalar_eqb_true in E7i.
    destruct (step_wrap_ok _ _ st2 Hstep) as [bt Hrd].
    destruct (step_if_op C0 bt0 st1 fs pre f data bt st2 Hinv1 Hbf Hfs Hrd)
      as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_if (translate_bt bt)). unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    destruct (read_if_sound st1 data bt st2 Hrd) as [bb [Hbb Hspec]].
    rewrite Hbytes. rewrite Hbb.
    apply repr_op_if; [rewrite E7i; reflexivity | exact Hspec]. }
  destruct (b s= opiter_op_else) eqn:E7e.
  { left. apply scalar_eqb_true in E7e.
    destruct (step_wrap_ok _ _ st2 Hstep) as [bt Hrd].
    (* [read_else] rejects anything but an open then-branch, so the innermost
       frame's kind is settled by the run rather than assumed *)
    pose proof (read_else_frame C0 st1 fs pre f bt st2 Hinv1 Hfs Hrd) as Hkind.
    destruct (step_switch_else_op C0 bt0 st1 fs pre f bt st2
                Hinv1 Hbf Hfs Hkind Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', FO_else. unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_of_else; [rewrite E7e; reflexivity|].
    apply (read_else_pos st1 _ st2 Hrd). }
  (* [end] is the one branch that can finish the run *)
  destruct (b s= opiter_op_end) eqn:E8.
  { apply scalar_eqb_true in E8.
    destruct (step_wrap_ok _ _ st2 Hstep) as [r Hrd].
    destruct (end_state C0 st1 fs pre f r st2 Hinv1 Hfs Hrd)
      as [_ [Hagree [_ [Hc2 _]]]].
    destruct (body_first_innermost bt0 fs pre f Hbf Hfs)
      as [[Hprenil [Hk Hbt]] | [pre2 [f2 [Hfs2 Hk]]]].
    - (* the body's own [end]: the run is over *)
      right. right. unfold body_done. exists f.
      split; [rewrite Hfs; rewrite Hprenil; reflexivity|].
      split; [exact Hk|]. split; [exact Hbt|].
      split; [rewrite <- Hbt; exact Hagree|]. split.
      + rewrite Hc2. rewrite Hprenil. reflexivity.
      + rewrite Hbytes. apply repr_op_of_end; [rewrite E8; reflexivity|].
        apply (read_end_pos st1 _ st2 Hrd).
    - (* a nested frame closed: block, loop, else, or a then-branch with no
         else, which is the two-operator case *)
      destruct Hk as [Hkb | [Hkl | [Hkt | Hke]]].
      + left.
        destruct (step_end_block_op C0 bt0 st1 fs pre2 f2 f r st2
                    Hinv1 Hbf Hfs2 Hkb Hrd) as [fs' [Hinv' [Hbf' Hff]]].
        exists fs', FO_end. unfold op_step.
        split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
        rewrite Hbytes. apply repr_op_of_end; [rewrite E8; reflexivity|].
        apply (read_end_pos st1 _ st2 Hrd).
      + left.
        destruct (step_end_loop_op C0 bt0 st1 fs pre2 f2 f r st2
                    Hinv1 Hbf Hfs2 Hkl Hrd) as [fs' [Hinv' [Hbf' Hff]]].
        exists fs', FO_end. unfold op_step.
        split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
        rewrite Hbytes. apply repr_op_of_end; [rewrite E8; reflexivity|].
        apply (read_end_pos st1 _ st2 Hrd).
      + right. left.
        destruct (step_end_then_op C0 bt0 st1 fs pre2 f2 f r st2
                    Hinv1 Hbf Hfs2 Hkt Hrd) as [fs' [Hinv' [Hbf' Hff]]].
        exists fs'. unfold bare_if_step.
        split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
        rewrite Hbytes. apply repr_op_of_end; [rewrite E8; reflexivity|].
        apply (read_end_pos st1 _ st2 Hrd).
      + left.
        destruct (step_end_else_op C0 bt0 st1 fs pre2 f2 f r st2
                    Hinv1 Hbf Hfs2 Hke Hrd) as [fs' [Hinv' [Hbf' Hff]]].
        exists fs', FO_end. unfold op_step.
        split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
        rewrite Hbytes. apply repr_op_of_end; [rewrite E8; reflexivity|].
        apply (read_end_pos st1 _ st2 Hrd). }
  destruct (b s= opiter_op_br) eqn:E9.
  { left. apply scalar_eqb_true in E9.
    destruct (step_wrap_ok _ _ st2 Hstep) as [dbt Hrd].
    destruct dbt as [depth bt].
    destruct (step_br_op C0 bt0 st1 fs pre f data depth bt st2 Hinv1 Hbf Hfs Hrd)
      as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_br (Z.to_N (to_Z depth)))). unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_idx with (io := IO_br);
      [rewrite E9; reflexivity|].
    apply (read_br_sound st1 data depth bt st2 Hrd). }
  destruct (b s= opiter_op_br_if) eqn:E9b.
  { left. apply scalar_eqb_true in E9b.
    destruct (step_wrap_ok _ _ st2 Hstep) as [[depth bt] Hrd].
    destruct (step_br_if_op C0 bt0 st1 fs pre f data depth bt st2
                Hinv1 Hbf Hfs Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_br_if (Z.to_N (to_Z depth)))). unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_idx with (io := IO_br_if);
      [rewrite E9b; reflexivity|].
    apply (read_br_if_sound st1 data depth bt st2 Hrd). }
  destruct (b s= opiter_op_br_table) eqn:E9t.
  { left. apply scalar_eqb_true in E9t.
    destruct (step_wrap_ok _ _ st2 Hstep) as [common Hrd].
    (* the label list and the per-label frame facts come out of the same run *)
    destruct (read_br_table_sound st1 data common st2 Hrd)
      as [ls [x [mid [Hvec [Hdef Hdt]]]]].
    destruct (step_br_table_op C0 bt0 st1 fs pre f data ls x common st2
                Hinv1 Hbf Hfs Hdt Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_br_table (List.map Z.to_N ls) (Z.to_N x))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes.
    apply repr_op_br_table with (mid := mid);
      [rewrite E9t; reflexivity | exact Hvec | exact Hdef]. }
  destruct (b s= opiter_op_return) eqn:E9r.
  { left. apply scalar_eqb_true in E9r.
    destruct (step_wrap_ok _ _ st2 Hstep) as [u Hrd]. destruct u.
    destruct (step_return_op C0 bt0 ctx st1 fs pre f st2
                Hinv1 Hbf Hfs Hret Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain BI_return). unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_of_inert; [rewrite E9r; reflexivity|].
    apply (read_return_pos st1 ctx _ st2 Hrd). }
  destruct (b s= opiter_op_call) eqn:EC1.
  { left. apply scalar_eqb_true in EC1.
    destruct (step_wrap_ok _ _ st2 Hstep) as [idx Hrd].
    destruct (step_call_op C0 bt0 module st1 fs pre f data idx st2
                Hinv1 Hbf Hfs Hfuncs Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_call (Z.to_N (to_Z idx)))). unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_idx with (io := IO_call);
      [rewrite EC1; reflexivity|].
    apply (read_call_sound st1 data module idx st2 Hrd). }
  destruct (b s= opiter_op_call_indirect) eqn:EC2.
  { left. apply scalar_eqb_true in EC2.
    destruct (step_wrap_ok _ _ st2 Hstep) as [idx Hrd].
    destruct (step_call_indirect_op C0 bt0 module st1 fs pre f data idx st2
                Hinv1 Hbf Hfs Htypes Htables Hrd)
      as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_call_indirect 0%N (Z.to_N (to_Z idx)))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_call_indirect;
      [rewrite EC2; reflexivity|].
    apply (read_call_indirect_sound st1 data module idx st2 Hrd). }
  destruct (b s= opiter_op_local_get) eqn:EL1.
  { left. apply scalar_eqb_true in EL1.
    destruct (step_wrap_ok _ _ st2 Hstep) as [idx Hrd].
    destruct (step_local_get_op C0 bt0 ctx st1 fs pre f data idx st2
                Hinv1 Hbf Hfs Hlocals Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_local_get (Z.to_N (to_Z idx)))). unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_idx with (io := IO_local_get);
      [rewrite EL1; reflexivity|].
    apply (take_local_sound_of_get st1 data ctx idx st2 Hrd). }
  destruct (b s= opiter_op_local_set) eqn:EL2.
  { left. apply scalar_eqb_true in EL2.
    destruct (step_wrap_ok _ _ st2 Hstep) as [idx Hrd].
    destruct (step_local_set_op C0 bt0 ctx st1 fs pre f data idx st2
                Hinv1 Hbf Hfs Hlocals Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_local_set (Z.to_N (to_Z idx)))). unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_idx with (io := IO_local_set);
      [rewrite EL2; reflexivity|].
    apply (take_local_sound_of_set st1 data ctx idx st2 Hrd). }
  destruct (b s= opiter_op_local_tee) eqn:EL3.
  { left. apply scalar_eqb_true in EL3.
    destruct (step_wrap_ok _ _ st2 Hstep) as [idx Hrd].
    destruct (step_local_tee_op C0 bt0 ctx st1 fs pre f data idx st2
                Hinv1 Hbf Hfs Hlocals Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_local_tee (Z.to_N (to_Z idx)))). unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_idx with (io := IO_local_tee);
      [rewrite EL3; reflexivity|].
    apply (take_local_sound_of_tee st1 data ctx idx st2 Hrd). }
  destruct (b s= opiter_op_global_get) eqn:EG1.
  { left. apply scalar_eqb_true in EG1.
    destruct (step_wrap_ok _ _ st2 Hstep) as [idx Hrd].
    destruct (step_global_get_op C0 bt0 module st1 fs pre f data idx st2
                Hinv1 Hbf Hfs Hglobals Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_global_get (Z.to_N (to_Z idx)))). unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_idx with (io := IO_global_get);
      [rewrite EG1; reflexivity|].
    apply (take_global_sound_of_get st1 data module idx st2 Hrd). }
  destruct (b s= opiter_op_global_set) eqn:EG2.
  { left. apply scalar_eqb_true in EG2.
    destruct (step_wrap_ok _ _ st2 Hstep) as [idx Hrd].
    destruct (step_global_set_op C0 bt0 module st1 fs pre f data idx st2
                Hinv1 Hbf Hfs Hglobals Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_global_set (Z.to_N (to_Z idx)))). unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_idx with (io := IO_global_set);
      [rewrite EG2; reflexivity|].
    apply (take_global_sound_of_set st1 data module idx st2 Hrd). }
  unfold opiter_step_memory in Hstep.
  destruct (b s= opiter_op_i32_load) eqn:E10.
  { left. apply scalar_eqb_true in E10.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_load_op C0 bt0 st1 fs pre f data module b Types_ValueType_I32 2%u32
                T_i32 None m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_load T_i32 None
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_load; [rewrite E10; reflexivity|].
    apply (read_load_sound st1 data module b Types_ValueType_I32 2%u32 m st2 Hrd). }
  destruct (b s= opiter_op_i64_load) eqn:E11.
  { left. apply scalar_eqb_true in E11.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_load_op C0 bt0 st1 fs pre f data module b Types_ValueType_I64 3%u32
                T_i64 None m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_load T_i64 None
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_load; [rewrite E11; reflexivity|].
    apply (read_load_sound st1 data module b Types_ValueType_I64 3%u32 m st2 Hrd). }
  destruct (b s= opiter_op_f32_load) eqn:E12.
  { left. apply scalar_eqb_true in E12.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_load_op C0 bt0 st1 fs pre f data module b Types_ValueType_F32 2%u32
                T_f32 None m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_load T_f32 None
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_load; [rewrite E12; reflexivity|].
    apply (read_load_sound st1 data module b Types_ValueType_F32 2%u32 m st2 Hrd). }
  destruct (b s= opiter_op_f64_load) eqn:E13.
  { left. apply scalar_eqb_true in E13.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_load_op C0 bt0 st1 fs pre f data module b Types_ValueType_F64 3%u32
                T_f64 None m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_load T_f64 None
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_load; [rewrite E13; reflexivity|].
    apply (read_load_sound st1 data module b Types_ValueType_F64 3%u32 m st2 Hrd). }
  destruct (b s= opiter_op_i32_load8_s) eqn:E14.
  { left. apply scalar_eqb_true in E14.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_load_op C0 bt0 st1 fs pre f data module b Types_ValueType_I32 0%u32
                T_i32 (Some (Tp_i8, SX_S)) m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_load T_i32 (Some (Tp_i8, SX_S))
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_load; [rewrite E14; reflexivity|].
    apply (read_load_sound st1 data module b Types_ValueType_I32 0%u32 m st2 Hrd). }
  destruct (b s= opiter_op_i32_load8_u) eqn:E15.
  { left. apply scalar_eqb_true in E15.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_load_op C0 bt0 st1 fs pre f data module b Types_ValueType_I32 0%u32
                T_i32 (Some (Tp_i8, SX_U)) m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_load T_i32 (Some (Tp_i8, SX_U))
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_load; [rewrite E15; reflexivity|].
    apply (read_load_sound st1 data module b Types_ValueType_I32 0%u32 m st2 Hrd). }
  destruct (b s= opiter_op_i32_load16_s) eqn:E16.
  { left. apply scalar_eqb_true in E16.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_load_op C0 bt0 st1 fs pre f data module b Types_ValueType_I32 1%u32
                T_i32 (Some (Tp_i16, SX_S)) m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_load T_i32 (Some (Tp_i16, SX_S))
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_load; [rewrite E16; reflexivity|].
    apply (read_load_sound st1 data module b Types_ValueType_I32 1%u32 m st2 Hrd). }
  destruct (b s= opiter_op_i32_load16_u) eqn:E17.
  { left. apply scalar_eqb_true in E17.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_load_op C0 bt0 st1 fs pre f data module b Types_ValueType_I32 1%u32
                T_i32 (Some (Tp_i16, SX_U)) m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_load T_i32 (Some (Tp_i16, SX_U))
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_load; [rewrite E17; reflexivity|].
    apply (read_load_sound st1 data module b Types_ValueType_I32 1%u32 m st2 Hrd). }
  destruct (b s= opiter_op_i64_load8_s) eqn:E18.
  { left. apply scalar_eqb_true in E18.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_load_op C0 bt0 st1 fs pre f data module b Types_ValueType_I64 0%u32
                T_i64 (Some (Tp_i8, SX_S)) m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_load T_i64 (Some (Tp_i8, SX_S))
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_load; [rewrite E18; reflexivity|].
    apply (read_load_sound st1 data module b Types_ValueType_I64 0%u32 m st2 Hrd). }
  destruct (b s= opiter_op_i64_load8_u) eqn:E19.
  { left. apply scalar_eqb_true in E19.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_load_op C0 bt0 st1 fs pre f data module b Types_ValueType_I64 0%u32
                T_i64 (Some (Tp_i8, SX_U)) m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_load T_i64 (Some (Tp_i8, SX_U))
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_load; [rewrite E19; reflexivity|].
    apply (read_load_sound st1 data module b Types_ValueType_I64 0%u32 m st2 Hrd). }
  destruct (b s= opiter_op_i64_load16_s) eqn:E20.
  { left. apply scalar_eqb_true in E20.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_load_op C0 bt0 st1 fs pre f data module b Types_ValueType_I64 1%u32
                T_i64 (Some (Tp_i16, SX_S)) m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_load T_i64 (Some (Tp_i16, SX_S))
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_load; [rewrite E20; reflexivity|].
    apply (read_load_sound st1 data module b Types_ValueType_I64 1%u32 m st2 Hrd). }
  destruct (b s= opiter_op_i64_load16_u) eqn:E21.
  { left. apply scalar_eqb_true in E21.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_load_op C0 bt0 st1 fs pre f data module b Types_ValueType_I64 1%u32
                T_i64 (Some (Tp_i16, SX_U)) m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_load T_i64 (Some (Tp_i16, SX_U))
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_load; [rewrite E21; reflexivity|].
    apply (read_load_sound st1 data module b Types_ValueType_I64 1%u32 m st2 Hrd). }
  destruct (b s= opiter_op_i64_load32_s) eqn:E22.
  { left. apply scalar_eqb_true in E22.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_load_op C0 bt0 st1 fs pre f data module b Types_ValueType_I64 2%u32
                T_i64 (Some (Tp_i32, SX_S)) m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_load T_i64 (Some (Tp_i32, SX_S))
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_load; [rewrite E22; reflexivity|].
    apply (read_load_sound st1 data module b Types_ValueType_I64 2%u32 m st2 Hrd). }
  destruct (b s= opiter_op_i64_load32_u) eqn:E23.
  { left. apply scalar_eqb_true in E23.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_load_op C0 bt0 st1 fs pre f data module b Types_ValueType_I64 2%u32
                T_i64 (Some (Tp_i32, SX_U)) m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_load T_i64 (Some (Tp_i32, SX_U))
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_load; [rewrite E23; reflexivity|].
    apply (read_load_sound st1 data module b Types_ValueType_I64 2%u32 m st2 Hrd). }
  destruct (b s= opiter_op_i32_store) eqn:E24.
  { left. apply scalar_eqb_true in E24.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_store_op C0 bt0 st1 fs pre f data module b Types_ValueType_I32 2%u32
                T_i32 None m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_store T_i32 None
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_store; [rewrite E24; reflexivity|].
    apply (read_store_sound st1 data module b Types_ValueType_I32 2%u32 m st2 Hrd). }
  destruct (b s= opiter_op_i64_store) eqn:E25.
  { left. apply scalar_eqb_true in E25.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_store_op C0 bt0 st1 fs pre f data module b Types_ValueType_I64 3%u32
                T_i64 None m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_store T_i64 None
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_store; [rewrite E25; reflexivity|].
    apply (read_store_sound st1 data module b Types_ValueType_I64 3%u32 m st2 Hrd). }
  destruct (b s= opiter_op_f32_store) eqn:E26.
  { left. apply scalar_eqb_true in E26.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_store_op C0 bt0 st1 fs pre f data module b Types_ValueType_F32 2%u32
                T_f32 None m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_store T_f32 None
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_store; [rewrite E26; reflexivity|].
    apply (read_store_sound st1 data module b Types_ValueType_F32 2%u32 m st2 Hrd). }
  destruct (b s= opiter_op_f64_store) eqn:E27.
  { left. apply scalar_eqb_true in E27.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_store_op C0 bt0 st1 fs pre f data module b Types_ValueType_F64 3%u32
                T_f64 None m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_store T_f64 None
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_store; [rewrite E27; reflexivity|].
    apply (read_store_sound st1 data module b Types_ValueType_F64 3%u32 m st2 Hrd). }
  destruct (b s= opiter_op_i32_store8) eqn:E28.
  { left. apply scalar_eqb_true in E28.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_store_op C0 bt0 st1 fs pre f data module b Types_ValueType_I32 0%u32
                T_i32 (Some Tp_i8) m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_store T_i32 (Some Tp_i8)
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_store; [rewrite E28; reflexivity|].
    apply (read_store_sound st1 data module b Types_ValueType_I32 0%u32 m st2 Hrd). }
  destruct (b s= opiter_op_i32_store16) eqn:E29.
  { left. apply scalar_eqb_true in E29.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_store_op C0 bt0 st1 fs pre f data module b Types_ValueType_I32 1%u32
                T_i32 (Some Tp_i16) m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_store T_i32 (Some Tp_i16)
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_store; [rewrite E29; reflexivity|].
    apply (read_store_sound st1 data module b Types_ValueType_I32 1%u32 m st2 Hrd). }
  destruct (b s= opiter_op_i64_store8) eqn:E30.
  { left. apply scalar_eqb_true in E30.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_store_op C0 bt0 st1 fs pre f data module b Types_ValueType_I64 0%u32
                T_i64 (Some Tp_i8) m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_store T_i64 (Some Tp_i8)
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_store; [rewrite E30; reflexivity|].
    apply (read_store_sound st1 data module b Types_ValueType_I64 0%u32 m st2 Hrd). }
  destruct (b s= opiter_op_i64_store16) eqn:E31.
  { left. apply scalar_eqb_true in E31.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_store_op C0 bt0 st1 fs pre f data module b Types_ValueType_I64 1%u32
                T_i64 (Some Tp_i16) m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_store T_i64 (Some Tp_i16)
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_store; [rewrite E31; reflexivity|].
    apply (read_store_sound st1 data module b Types_ValueType_I64 1%u32 m st2 Hrd). }
  destruct (b s= opiter_op_i64_store32) eqn:E32.
  { left. apply scalar_eqb_true in E32.
    destruct (step_wrap_ok _ _ st2 Hstep) as [m Hrd].
    destruct (step_store_op C0 bt0 st1 fs pre f data module b Types_ValueType_I64 2%u32
                T_i64 (Some Tp_i32) m st2 Hinv1 Hbf Hfs Hmems (eq_refl _)
                (ltac:(ls_bounds)) Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain (BI_store T_i64 (Some Tp_i32)
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))).
    unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_store; [rewrite E32; reflexivity|].
    apply (read_store_sound st1 data module b Types_ValueType_I64 2%u32 m st2 Hrd). }
  destruct (b s= opiter_op_memory_size) eqn:EM1.
  { left. apply scalar_eqb_true in EM1.
    destruct (step_wrap_ok _ _ st2 Hstep) as [u Hrd]. destruct u.
    destruct (step_memory_size_op C0 bt0 module st1 fs pre f data st2
                Hinv1 Hbf Hfs Hmems Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain BI_memory_size). unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_of_reserved; [rewrite EM1; reflexivity|].
    apply (read_memory_size_reserved st1 data module st2 Hrd). }
  destruct (b s= opiter_op_memory_grow) eqn:EM2.
  { left. apply scalar_eqb_true in EM2.
    destruct (step_wrap_ok _ _ st2 Hstep) as [u Hrd]. destruct u.
    destruct (step_memory_grow_op C0 bt0 module st1 fs pre f data st2
                Hinv1 Hbf Hfs Hmems Hrd) as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain BI_memory_grow). unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_of_reserved; [rewrite EM2; reflexivity|].
    apply (read_memory_grow_reserved st1 data module st2 Hrd). }
  (* the numeric opcodes, through the tables: one branch per shape for the whole
     block, because the row supplies the instruction and its typing effect *)
  unfold opiter_step_numeric in Hstep.
  destruct (opiter_convert_types b) as [o|] eqn:Hcv; cbn [bind] in Hstep;
    [|discriminate].
  destruct o as [[from to]|].
  { left.
    destruct (convert_types_spec b from to Hcv) as [be [Hsp [Heff Hflat]]].
    destruct (step_conversion_op C0 bt0 st1 fs pre f b from to be st2
                Hinv1 Hbf Hfs (plain_effect_in C0 _ _ _ Heff) Hflat Hstep)
      as [fs' [Hinv' [Hbf' Hff]]].
    exists fs', (FO_plain be). unfold op_step.
    split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
    rewrite Hbytes. apply repr_op_of_inert; [exact Hsp|].
    apply (read_conversion_pos st1 _ _ _ _ st2 Hstep). }
  destruct (opiter_binary_types b) as [o1|] eqn:Hbt; cbn [bind] in Hstep;
    [|discriminate].
  destruct o1 as [[ty res]|]; [|discriminate].
  left.
  destruct (binary_types_spec b ty res Hbt) as [be [Hsp [Heff Hflat]]].
  destruct (step_binary_op C0 bt0 st1 fs pre f b ty res be st2
              Hinv1 Hbf Hfs (plain_effect_in C0 _ _ _ Heff) Hflat Hstep)
    as [fs' [Hinv' [Hbf' Hff]]].
  exists fs', (FO_plain be). unfold op_step.
  split; [exact Hinv'|]. split; [exact Hbf'|]. split; [exact Hff|].
  rewrite Hbytes. apply repr_op_of_inert; [exact Hsp|].
  apply (read_binary_pos st1 _ _ _ _ st2 Hstep).
Qed.

(* ================================================================== *)
(** ** The loop                                                        *)
(* ================================================================== *)

(** Once the control stack is empty the loop does no more reading: it accepts if
    the cursor reached the end of the body and reports trailing bytes otherwise.
    So an accepting run that got here consumed every byte. *)
Lemma validate_body_loop_finished : forall data module ctx st,
  vec_list st.(opiter_OpIterState_ctrls) = [] ->
  opiter_validate_body_loop data module ctx.(opiter_Context_locals)
    ctx.(opiter_Context_results) st = Ok (Core_result_Result_Ok tt) ->
  to_Z st.(opiter_OpIterState_pos) = to_Z (slice_len data).
Proof.
  intros data module ctx st Hnil H.
  unfold opiter_validate_body_loop in H. rewrite loop_unfold in H.
  cbn beta iota in H. unfold opiter_control_stack_empty in H.
  rewrite vec_is_empty_spec in H. rewrite Hnil in H. cbn [bind] in H.
  destruct (st.(opiter_OpIterState_pos) s= slice_len data) eqn:Heq;
    [|discriminate].
  apply scalar_eqb_true in Heq. exact Heq.
Qed.

(** The run, by induction on the bytes left. While the body frame is on the stack
    the control stack is non-empty, so the loop cannot take its accepting branch;
    the only way out is the body's own [end], and [step_op_step] is what says so. *)
Lemma validate_body_loop_sound : forall m C0 bt0 module ctx data st fs,
  Inv C0 st fs -> body_first bt0 fs ->
  mems_agree module C0 -> locals_agree ctx C0 -> globals_agree module C0 ->
  return_agree ctx C0 -> funcs_agree module C0 -> types_agree module C0 ->
  tables_agree module C0 ->
  (exists ops, else_sugar (frames_flat fs) ops
               /\ repr_ops (byte_list data) ops
                    (bytes_from data st.(opiter_OpIterState_pos))) ->
  to_Z (slice_len data) - to_Z st.(opiter_OpIterState_pos) <= Z.of_nat m ->
  opiter_validate_body_loop data module ctx.(opiter_Context_locals)
    ctx.(opiter_Context_results) st = Ok (Core_result_Result_Ok tt) ->
  exists f,
    frames_ok C0 [] [f]
    /\ (fv_ctrl f).(opiter_Ctrl_kind) = Opiter_LabelKind_Body
    /\ (fv_ctrl f).(opiter_Ctrl_block_type) = bt0
    /\ c_types_agree (fv_ct f) (translate_typelist (block_results_of bt0)) = true
    /\ repr_expr (byte_list data) (fv_done f) [].
Proof.
  induction m as [|m IH]; intros C0 bt0 module ctx data st fs Hinv Hbf Hmems Hlocals
                                 Hglobals Hret Hfuncs Htypes Htables
                                 [ops [Hsug Hops]] Hmeas H.
  (* the body frame is still on the stack, so the accepting branch is not taken *)
  all: assert (Hcons : exists c cs,
                 vec_list st.(opiter_OpIterState_ctrls) = c :: cs)
         by (destruct Hinv as [K1 _]; rewrite K1; destruct fs as [|h t];
             [exfalso; exact Hbf
             | exists (fv_ctrl h), (List.map fv_ctrl t); reflexivity]).
  all: destruct Hcons as [c [cs Hcons]].
  all: unfold opiter_validate_body_loop in H; rewrite loop_unfold in H;
       cbn beta iota in H; unfold opiter_control_stack_empty in H;
       rewrite vec_is_empty_spec in H; rewrite Hcons in H; cbn [bind] in H;
       rewrite ctx_eta in H.
  - (* no bytes left, so [read_op] reports end of input *)
    assert (Hend : Z.of_nat (List.length (vec_list data))
                   <= to_Z st.(opiter_OpIterState_pos)).
    { rewrite slice_len_spec in Hmeas. cbn in Hmeas. lia. }
    rewrite (read_op_err_at_end st data Hend) in H. cbn [bind] in H.
    rewrite branch_err in H. cbn [bind] in H.
    rewrite from_residual_err in H. cbn [bind] in H. discriminate.
  - (* one operator, then either round again or the body is done *)
    destruct (opiter_read_op st data) as [[r0 st1]|] eqn:Hro; cbn [bind] in H;
      [|discriminate].
    destruct r0 as [b|e].
    2: { rewrite branch_err in H. cbn [bind] in H.
         rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (opiter_step st1 data module ctx b) as [[r1 st2]|] eqn:Hstep;
      cbn [bind] in H; [|discriminate].
    destruct r1 as [u1|e1].
    2: { rewrite branch_err in H. cbn [bind] in H.
         rewrite from_residual_err in H. cbn [bind] in H. discriminate. }
    destruct u1. rewrite branch_ok in H. cbn [bind] in H.
    pose proof (read_op_advance st data b st1 Hro) as Hadv.
    pose proof (step_mono st1 data module ctx b _ st2 Hstep) as Hmono.
    destruct (step_op_step C0 bt0 module ctx data st fs b st1 st2
                Hinv Hbf Hmems Hlocals Hglobals Hret Hfuncs Htypes Htables
                Hro Hstep)
      as [[fs' [op [Hinv' [Hbf' [Hff Hrop]]]]]
         | [[fs' [Hinv' [Hbf' [Hff Hrop]]]] | Hdone]].
    + apply (IH C0 bt0 module ctx data st2 fs'); try assumption.
      * exists (ops ++ [op]). split.
        { rewrite Hff. apply else_sugar_snoc. exact Hsug. }
        apply (repr_ops_snoc _ _ (bytes_from data st.(opiter_OpIterState_pos)));
          [exact Hops | exact Hrop].
      * cbn in Hmeas. lia.
    + (* the [end] of an [if] with no [else]: two operators for one byte, which
         is what [else_sugar] absorbs *)
      apply (IH C0 bt0 module ctx data st2 fs'); try assumption.
      * exists (ops ++ [FO_end]). split.
        { rewrite Hff. apply else_sugar_snoc_else_end. exact Hsug. }
        apply (repr_ops_snoc _ _ (bytes_from data st.(opiter_OpIterState_pos)));
          [exact Hops | exact Hrop].
      * cbn in Hmeas. lia.
    + (* the body's [end]: the stream is complete and the cursor is at the end *)
      destruct Hdone as [f [Hfs [Hk [Hbt [Hagree [Hc2 Hrop]]]]]].
      pose proof (validate_body_loop_finished data module ctx st2 Hc2 H) as Hpos.
      exists f. split.
      { destruct Hinv as [_ [_ [_ K4]]]. rewrite Hfs in K4. exact K4. }
      split; [exact Hk|]. split; [exact Hbt|]. split; [exact Hagree|].
      assert (Hflat : frames_flat fs ++ [FO_end]
                      = flat_of (fv_done f) ++ [FO_end]).
      { rewrite Hfs. apply frames_flat_body. exact Hk. }
      exists (ops ++ [FO_end]). split.
      { rewrite <- Hflat. apply else_sugar_snoc. exact Hsug. }
      assert (Hnilb : bytes_from data st2.(opiter_OpIterState_pos) = []).
      { apply bytes_from_end. exact Hpos. }
      rewrite <- Hnilb.
      apply (repr_ops_snoc _ _ (bytes_from data st.(opiter_OpIterState_pos)));
        [exact Hops | exact Hrop].
Qed.

(* ================================================================== *)
(** ** The theorem                                                     *)
(* ================================================================== *)

(** An accepting run means the body's bytes encode an instruction sequence that
    WasmCert's checker accepts, at the function's declared result type.

    The Wasm 1.0 restriction to at most one result is a hypothesis: with more,
    [start_function] reads the signature as returning nothing, and the module
    validator is what rules that out. *)
Theorem validate_body_sound : forall C0 module ctx data,
  mems_agree module C0 -> locals_agree ctx C0 -> globals_agree module C0 ->
  return_agree ctx C0 -> funcs_agree module C0 -> types_agree module C0 ->
  tables_agree module C0 ->
  (List.length (vec_list ctx.(opiter_Context_results)) <= 1)%nat ->
  opiter_validate_body data module ctx = Ok (Core_result_Result_Ok tt) ->
  exists es,
    repr_expr (byte_list data) es []
    /\ b_e_type_checker_aux
         (upd_label C0 [translate_typelist (vec_list ctx.(opiter_Context_results))]) es
         (Tf [] (translate_typelist (vec_list ctx.(opiter_Context_results)))) = true.
Proof.
  intros C0 module ctx data Hmems Hlocals Hglobals Hret Hfuncs Htypes Htables
         Hlen1 H.
  unfold opiter_validate_body in H.
  destruct (slice_len data s> limits_max_function_bytes); [discriminate|].
  rewrite vec_deref_spec in H.
  destruct (opiter_start_function ctx.(opiter_Context_results)) as [st|] eqn:Hsf; cbn [bind] in H;
    [|discriminate].
  destruct (Inv_start C0 st ctx.(opiter_Context_results) Hlen1 Hsf) as [bt [Hinv Hbt]].
  pose proof (start_function_pos ctx.(opiter_Context_results) st Hsf) as Hpos.
  destruct (validate_body_loop_sound (Z.to_nat (to_Z (slice_len data)))
              C0 bt module ctx data st [body_fview bt] Hinv (body_first_start bt)
              Hmems Hlocals Hglobals Hret Hfuncs Htypes Htables)
    as [f [Hfok [Hk [Hfbt [Hagree Hexpr]]]]].
  - exists []. rewrite frames_flat_start.
    split; [apply else_sugar_nil|].
    rewrite (bytes_from_at_zero data _ Hpos). apply repr_ops_nil.
  - rewrite Hpos. rewrite Z2Nat.id by apply usize_nonneg. lia.
  - exact H.
  - exists (fv_done f). split; [exact Hexpr|].
    rewrite <- Hbt.
    apply (end_body_typing C0 f bt Hk Hfbt Hfok). exact Hagree.
Qed.

(** The same result in the form WasmCert states its reflection lemma over.
    [translate_typelist] reverses, so the agreement clauses build [C0] already
    in the shape [b_e_type_checker_aux] consumes; [b_e_type_checker] applies
    [context_reverse] first, so getting there means reversing back. Chaining
    [b_e_type_checker_reflects_typing] from here gives [be_typing], which is the
    specification-level statement. *)
Corollary validate_body_checker : forall C0 module ctx data,
  mems_agree module C0 -> locals_agree ctx C0 -> globals_agree module C0 ->
  return_agree ctx C0 -> funcs_agree module C0 -> types_agree module C0 ->
  tables_agree module C0 ->
  (List.length (vec_list ctx.(opiter_Context_results)) <= 1)%nat ->
  opiter_validate_body data module ctx = Ok (Core_result_Result_Ok tt) ->
  exists es,
    repr_expr (byte_list data) es []
    /\ b_e_type_checker
         (context_reverse
            (upd_label C0 [translate_typelist (vec_list ctx.(opiter_Context_results))])) es
         (Tf [] (List.map translate_vt_v (vec_list ctx.(opiter_Context_results)))) = true.
Proof.
  intros C0 module ctx data Hmems Hlocals Hglobals Hret Hfuncs Htypes Htables
         Hlen1 H.
  destruct (validate_body_sound C0 module ctx data Hmems Hlocals Hglobals Hret
              Hfuncs Htypes Htables Hlen1 H)
    as [es [Hexpr Hchk]].
  exists es. split; [exact Hexpr|].
  unfold b_e_type_checker.
  rewrite (context_reverseK
             (upd_label C0 [translate_typelist (vec_list ctx.(opiter_Context_results))])).
  exact Hchk.
Qed.

(** [context_reverse] touches the four fields the reversed convention applies
    to, and [upd_label] only writes one of them, so the two commute. Reversing
    the label list twice is what leaves it in the specification's order. *)
Lemma context_reverse_upd_label : forall C rs,
  context_reverse (upd_label C [translate_typelist rs])
    = upd_label (context_reverse C) [List.map translate_vt_v rs].
Proof.
  intros C rs.
  unfold context_reverse, upd_label, upd_local_label_return, translate_typelist.
  cbn. rewrite !seq_rev_rev, List.rev_involutive. reflexivity.
Qed.

(** Soundness at the specification level, and the end of the body chain.
    [b_e_type_checker_reflects_typing] is an if-and-only-if, so an accepting run
    means [be_typing] itself rather than a decision procedure's opinion of it.

    The [context_reverse] moves off the label and onto [C0], which is where it
    belongs: [C0] is built reversed, the convention [b_e_type_checker_aux]
    consumes, so [context_reverse C0] is the context the specification talks
    about, and the body checks in it with the function's result type as its one
    label. *)
Corollary validate_body_typed : forall C0 module ctx data,
  mems_agree module C0 -> locals_agree ctx C0 -> globals_agree module C0 ->
  return_agree ctx C0 -> funcs_agree module C0 -> types_agree module C0 ->
  tables_agree module C0 ->
  (List.length (vec_list ctx.(opiter_Context_results)) <= 1)%nat ->
  opiter_validate_body data module ctx = Ok (Core_result_Result_Ok tt) ->
  exists es,
    repr_expr (byte_list data) es []
    /\ be_typing
         (upd_label (context_reverse C0)
            [List.map translate_vt_v (vec_list ctx.(opiter_Context_results))])
         es
         (Tf [] (List.map translate_vt_v (vec_list ctx.(opiter_Context_results)))).
Proof.
  intros C0 module ctx data Hmems Hlocals Hglobals Hret Hfuncs Htypes Htables
         Hlen1 H.
  destruct (validate_body_checker C0 module ctx data Hmems Hlocals Hglobals Hret
              Hfuncs Htypes Htables Hlen1 H) as [es [Hexpr Hchk]].
  exists es. split; [exact Hexpr|].
  rewrite <- context_reverse_upd_label.
  pose proof (b_e_type_checker_reflects_typing
                (context_reverse
                   (upd_label C0
                      [translate_typelist (vec_list ctx.(opiter_Context_results))]))
                es
                (Tf [] (List.map translate_vt_v
                          (vec_list ctx.(opiter_Context_results))))) as Hr.
  rewrite Hchk in Hr. inversion Hr as [Hty|]. exact Hty.
Qed.
