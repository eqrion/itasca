(** * The opcode table, on both sides

    The numeric operators all have the same handful of stack shapes, so the
    reference consumer dispatches them through a table ([opiter_convert_types])
    rather than through a branch each. This file relates that table to the
    specification's ([Spec_Binary.op_spec]): every row of the code's table names
    an operator the specification also has a row for, at matching types.

    That is what keeps both dispatch proofs one branch per *shape*. A new numeric
    opcode is then a row in the Rust table and a row in [op_spec], with no proof
    to write: the tactics below walk whichever table the goal is about and close
    every row by computation.

    Nothing here is a trust item. [op_spec] is the transcription; this file only
    checks the code against it. *)

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
Require Import Veriwasm.OpIter_Sim.
Require Import Veriwasm.OpIter_Expr.
From Wasm Require Import datatypes numerics type_checker operations typing.

Local Open Scope list_scope.
Open Scope Z_scope.

(* ================================================================== *)
(** ** What a table row has to deliver                                 *)
(* ================================================================== *)

(** Everything the two dispatch proofs need about the instruction a row names:
    its typing effect is the one [read_conversion] performs, and it flattens to
    a single plain operator. *)
Definition convert_ok (from to : types_ValueType_t) (be : basic_instruction)
  : Prop :=
  plain_effect be [translate_vt_v from] [translate_vt_v to]
  /\ flat_of_one be = [FO_plain be].

(** Close one row: the specification's table, consulted at this row's byte,
    computes to the operator, and the three obligations then hold by
    computation. Which of the three families the row belongs to is decided by
    [first], so the tactic is the same for all forty-seven. *)
Local Ltac convert_row :=
  eexists; split;
  [ reflexivity
  | cbn [translate_vt_v]; split;
    [ first [ apply plain_effect_unop
            | apply plain_effect_testop
            | apply plain_effect_cvtop ]; reflexivity
    | reflexivity ] ].

(** Walk a chain of opcode comparisons in a hypothesis, closing each row with
    [row] and carrying on down the [else]. The byte is a literal in every row,
    which is what makes the closers computations. *)
Local Ltac walk_rows H row :=
  repeat match type of H with
  | (if (?x s= ?y) then _ else _) = _ =>
      let E := fresh "E" in
      destruct (x s= y) eqn:E;
      [ cbn beta iota in H;
        apply scalar_eqb_true in E; rewrite E;
        injection H as <- <-; row
      | cbn beta iota in H ]
  end.

(* ================================================================== *)
(** ** The code's table agrees with the specification's                *)
(* ================================================================== *)

Theorem convert_types_spec : forall (b : u8) from to,
  opiter_convert_types b = Ok (Some (from, to)) ->
  exists be, op_spec (to_Z b) = Some (Sh_nullary be) /\ convert_ok from to be.
Proof.
  intros b from to H. unfold opiter_convert_types in H.
  walk_rows H convert_row.
  discriminate H.
Qed.

(** The same for the two-operand shape. [convert_ok]'s three obligations, with
    the effect at the binary shape. *)
Definition binary_ok (ty res : types_ValueType_t) (be : basic_instruction)
  : Prop :=
  plain_effect be [translate_vt_v ty; translate_vt_v ty] [translate_vt_v res]
  /\ flat_of_one be = [FO_plain be].

Local Ltac binary_row :=
  eexists; split;
  [ reflexivity
  | cbn [translate_vt_v]; split;
    [ first [ apply plain_effect_binop | apply plain_effect_relop ];
      reflexivity
    | reflexivity ] ].

Theorem binary_types_spec : forall (b : u8) ty res,
  opiter_binary_types b = Ok (Some (ty, res)) ->
  exists be, op_spec (to_Z b) = Some (Sh_nullary be) /\ binary_ok ty res be.
Proof.
  intros b ty res H. unfold opiter_binary_types in H.
  walk_rows H binary_row.
  discriminate H.
Qed.

(** The checker accepting an instruction of this kind means its operands are
    there to be consumed, which is the fact the reader's completeness lemma
    asks for. *)
Lemma plain_effect_consume : forall be pops pushes C ct ct2,
  plain_effect be pops pushes ->
  check_single C (Some ct) be = Some ct2 ->
  exists ct1, consume ct pops = Some ct1.
Proof.
  intros be pops pushes C ct ct2 Heff Hct. rewrite Heff in Hct.
  unfold type_update in Hct.
  destruct (consume ct pops) as [ct1|]; [exists ct1; reflexivity|].
  discriminate Hct.
Qed.

(* ================================================================== *)
(** ** The code recognises every opcode the specification has a row for *)
(* ================================================================== *)

(** One disjunct per dispatch guard in [opiter_step], plus the table. Stating
    coverage this way rather than as a list of byte values is what keeps the
    fallthrough branch of the completeness proof linear: "the code fell through
    every branch" becomes a single equation.

    It has to be kept in step with [opiter_step] by hand. It cannot drift
    silently: too few disjuncts and [op_spec_handled] stops holding, too many and
    the fallthrough stops closing. *)
Definition handled (b : u8) : bool :=
  (b s= opiter_op_nop)
  || (b s= opiter_op_unreachable)
  || (b s= opiter_op_i32_const)
  || (b s= opiter_op_i64_const)
  || (b s= opiter_op_f32_const)
  || (b s= opiter_op_f64_const)
  || (b s= opiter_op_drop)
  || (b s= opiter_op_select)
  || (b s= opiter_op_block)
  || (b s= opiter_op_loop)
  || (b s= opiter_op_if)
  || (b s= opiter_op_else)
  || (b s= opiter_op_end)
  || (b s= opiter_op_br)
  || (b s= opiter_op_br_if)
  || (b s= opiter_op_br_table)
  || (b s= opiter_op_return)
  || (b s= opiter_op_call)
  || (b s= opiter_op_call_indirect)
  || (b s= opiter_op_local_get)
  || (b s= opiter_op_local_set)
  || (b s= opiter_op_local_tee)
  || (b s= opiter_op_global_get)
  || (b s= opiter_op_global_set)
  || (b s= opiter_op_memory_size)
  || (b s= opiter_op_memory_grow)
  || (b s= opiter_op_i32_load)
  || (b s= opiter_op_i64_load)
  || (b s= opiter_op_f32_load)
  || (b s= opiter_op_f64_load)
  || (b s= opiter_op_i32_load8_s)
  || (b s= opiter_op_i32_load8_u)
  || (b s= opiter_op_i32_load16_s)
  || (b s= opiter_op_i32_load16_u)
  || (b s= opiter_op_i64_load8_s)
  || (b s= opiter_op_i64_load8_u)
  || (b s= opiter_op_i64_load16_s)
  || (b s= opiter_op_i64_load16_u)
  || (b s= opiter_op_i64_load32_s)
  || (b s= opiter_op_i64_load32_u)
  || (b s= opiter_op_i32_store)
  || (b s= opiter_op_i64_store)
  || (b s= opiter_op_f32_store)
  || (b s= opiter_op_f64_store)
  || (b s= opiter_op_i32_store8)
  || (b s= opiter_op_i32_store16)
  || (b s= opiter_op_i64_store8)
  || (b s= opiter_op_i64_store16)
  || (b s= opiter_op_i64_store32)
  || (match opiter_convert_types b with
      | Ok (Some _) => true
      | _ => false
      end)
  || (match opiter_binary_types b with
      | Ok (Some _) => true
      | _ => false
      end).

Theorem op_spec_handled : forall (b : u8) sh,
  op_spec (to_Z b) = Some sh -> handled b = true.
Proof.
  intros b sh H. unfold op_spec in H.
  unfold handled, opiter_convert_types, opiter_binary_types, scalar_eqb.
  repeat match type of H with
  | (if Z.eqb ?x ?k then _ else _) = _ =>
      let E := fresh "E" in
      destruct (Z.eqb x k) eqn:E;
      [ apply Z.eqb_eq in E; rewrite E; reflexivity
      | cbn beta iota in H ]
  end.
  discriminate H.
Qed.

(* ================================================================== *)
(** ** The table read backwards                                        *)
(* ================================================================== *)

(** Which byte a shape came from. [op_spec] is a function of the byte, so going
    the other way is an inversion and not a lookup, and it cannot be a
    computation either: the byte is a variable, so the [if] chain is stuck.

    The dispatch proofs never need this, because they walk the *code's* chain and
    the byte is a literal in every branch. The module's constant-expression
    reader does need it: its fallthrough is an error, and ruling that out means
    going from "the derivation says this operator is an [i32.const]" to "so the
    byte is 0x41".

    One walk over the table serves every query, which is why the conclusions are
    a conjunction rather than a lemma each. The four disequalities are the ones
    that matter for the argument to close at all: [Sh_nullary] and [Sh_reserved]
    carry an instruction, so their rows are the only ones a [repr_op] inversion
    cannot rule out by constructor, and what rules them out is that no row of the
    table names a [const] or a [global.get] that way.

    Both [const_val] and [fconst_val] have a catch-all arm, so a shape's number
    type is not determined by the value it builds -- [const_val T_f32] is
    [const_val T_i32] -- and the two [const] clauses therefore report the type
    alongside the byte rather than taking it as given. *)
Local Ltac inv_row :=
  repeat split; intros;
  first [ discriminate
        | reflexivity
        | (match goal with
           | [ H : Sh_const _ = Sh_const _ |- _ ] => injection H as <-
           | [ H : Sh_fconst _ = Sh_fconst _ |- _ ] => injection H as <-
           end;
           first [ (left; split; reflexivity) | (right; split; reflexivity) ]) ].

Theorem op_spec_invert : forall b sh,
  op_spec b = Some sh ->
  (sh = Sh_end -> b = 11)
  /\ (forall nt, sh = Sh_const nt ->
        (nt = T_i32 /\ b = 65) \/ (nt = T_i64 /\ b = 66))
  /\ (forall nt, sh = Sh_fconst nt ->
        (nt = T_f32 /\ b = 67) \/ (nt = T_f64 /\ b = 68))
  /\ (sh = Sh_idx IO_global_get -> b = 35)
  /\ (forall v, sh <> Sh_nullary (BI_const_num v))
  /\ (forall v, sh <> Sh_reserved (BI_const_num v))
  /\ (forall x, sh <> Sh_nullary (BI_global_get x))
  /\ (forall x, sh <> Sh_reserved (BI_global_get x)).
Proof.
  intros b sh H. unfold op_spec in H.
  repeat match type of H with
  | (if Z.eqb ?x ?k then _ else _) = _ =>
      let E := fresh "E" in
      destruct (Z.eqb x k) eqn:E;
      [ apply Z.eqb_eq in E; cbn beta iota in H; injection H as <-;
        rewrite E; inv_row
      | cbn beta iota in H ]
  end.
  discriminate H.
Qed.
