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
Require Import Itasca.Aeneas_Specs.
Require Import Itasca.Translate.
Require Import Itasca.Spec_Binary.
Require Import Itasca.OpIter_Visit.
Require Import Itasca.OpIter_Sim.
Require Import Itasca.OpIter_Expr.
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

(* ================================================================== *)
(** ** Which hook the generated fan-outs pick                          *)
(* ================================================================== *)

(** The recorder: a consumer that keeps the operators it was handed and the
    table labels it has been shown since the last table closed. Every row is
    read off the hook's own name -- for the numeric and memory hooks, off the
    mnemonic -- and never off the opcode, or the theorems below would be
    checking the tables against themselves. *)
Definition trace_visitor
  : visit_OpVisitor_t (list flat_op * list Z) := {|
  visit_OpVisitor_t_on_function_start :=
    fun p ctx tidx bb ee => Ok (Core_result_Result_Ok tt, p);
  visit_OpVisitor_t_on_unreachable :=
    fun p st =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_plain BI_unreachable], snd p));
  visit_OpVisitor_t_on_nop :=
    fun p st =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_plain BI_nop], snd p));
  visit_OpVisitor_t_on_block :=
    fun p st bt =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_block (translate_bt bt)], snd p));
  visit_OpVisitor_t_on_loop :=
    fun p st bt =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_loop (translate_bt bt)], snd p));
  visit_OpVisitor_t_on_if :=
    fun p st bt =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_if (translate_bt bt)], snd p));
  visit_OpVisitor_t_on_else :=
    fun p st bt =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_else], snd p));
  visit_OpVisitor_t_on_end :=
    fun p st kind bt =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_end], snd p));
  visit_OpVisitor_t_on_br :=
    fun p st d bt =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_plain (BI_br (Z.to_N (to_Z d)))], snd p));
  visit_OpVisitor_t_on_br_if :=
    fun p st d bt =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_plain (BI_br_if (Z.to_N (to_Z d)))], snd p));
  visit_OpVisitor_t_on_br_table_label :=
    fun p st d =>
      Ok (Core_result_Result_Ok tt, (fst p, snd p ++ [to_Z d]));
  visit_OpVisitor_t_on_br_table :=
    fun p st d common =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_br_table (List.map Z.to_N (snd p))
                                           (Z.to_N (to_Z d)))], []));
  visit_OpVisitor_t_on_return :=
    fun p st =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_plain BI_return], snd p));
  visit_OpVisitor_t_on_call :=
    fun p st idx =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_plain (BI_call (Z.to_N (to_Z idx)))], snd p));
  visit_OpVisitor_t_on_call_indirect :=
    fun p st idx =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_plain (BI_call_indirect 0%N (Z.to_N (to_Z idx)))], snd p));
  visit_OpVisitor_t_on_drop :=
    fun p st t =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_plain BI_drop], snd p));
  visit_OpVisitor_t_on_select :=
    fun p st t =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_plain (BI_select None)], snd p));
  visit_OpVisitor_t_on_local_get :=
    fun p st idx =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_plain (BI_local_get (Z.to_N (to_Z idx)))], snd p));
  visit_OpVisitor_t_on_local_set :=
    fun p st idx =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_plain (BI_local_set (Z.to_N (to_Z idx)))], snd p));
  visit_OpVisitor_t_on_local_tee :=
    fun p st idx =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_plain (BI_local_tee (Z.to_N (to_Z idx)))], snd p));
  visit_OpVisitor_t_on_global_get :=
    fun p st idx =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_plain (BI_global_get (Z.to_N (to_Z idx)))], snd p));
  visit_OpVisitor_t_on_global_set :=
    fun p st idx =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_plain (BI_global_set (Z.to_N (to_Z idx)))], snd p));
  visit_OpVisitor_t_on_memory_size :=
    fun p st =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_plain BI_memory_size], snd p));
  visit_OpVisitor_t_on_memory_grow :=
    fun p st =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_plain BI_memory_grow], snd p));
  visit_OpVisitor_t_on_i32_const :=
    fun p st x =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_plain (BI_const_num (VAL_int32 (Wasm_int.Int32.repr (to_Z x))))], snd p));
  visit_OpVisitor_t_on_i64_const :=
    fun p st x =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_plain (BI_const_num (VAL_int64 (Wasm_int.Int64.repr (to_Z x))))], snd p));
  visit_OpVisitor_t_on_f32_const :=
    fun p st x =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_plain (BI_const_num (fconst_val T_f32 (to_Z x)))], snd p));
  visit_OpVisitor_t_on_f64_const :=
    fun p st x =>
      Ok (Core_result_Result_Ok tt, (fst p ++ [FO_plain (BI_const_num (fconst_val T_f64 (to_Z x)))], snd p));
  visit_OpVisitor_t_on_i32_load :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_load T_i32 None (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_i64_load :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_load T_i64 None (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_f32_load :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_load T_f32 None (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_f64_load :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_load T_f64 None (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_i32_load8_s :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_load T_i32 (Some (Tp_i8, SX_S)) (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_i32_load8_u :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_load T_i32 (Some (Tp_i8, SX_U)) (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_i32_load16_s :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_load T_i32 (Some (Tp_i16, SX_S)) (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_i32_load16_u :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_load T_i32 (Some (Tp_i16, SX_U)) (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_i64_load8_s :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_load T_i64 (Some (Tp_i8, SX_S)) (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_i64_load8_u :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_load T_i64 (Some (Tp_i8, SX_U)) (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_i64_load16_s :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_load T_i64 (Some (Tp_i16, SX_S)) (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_i64_load16_u :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_load T_i64 (Some (Tp_i16, SX_U)) (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_i64_load32_s :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_load T_i64 (Some (Tp_i32, SX_S)) (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_i64_load32_u :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_load T_i64 (Some (Tp_i32, SX_U)) (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_i32_store :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_store T_i32 None (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_i64_store :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_store T_i64 None (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_f32_store :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_store T_f32 None (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_f64_store :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_store T_f64 None (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_i32_store8 :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_store T_i32 (Some Tp_i8) (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_i32_store16 :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_store T_i32 (Some Tp_i16) (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_i64_store8 :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_store T_i64 (Some Tp_i8) (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_i64_store16 :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_store T_i64 (Some Tp_i16) (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_i64_store32 :=
    fun p st m =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_store T_i64 (Some Tp_i32) (Z.to_N (to_Z m.(opiter_MemArg_align))) (Z.to_N (to_Z m.(opiter_MemArg_offset))))], snd p));
  visit_OpVisitor_t_on_i32_eqz :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_testop T_i32 TO_eqz)], snd p));
  visit_OpVisitor_t_on_i32_eq :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_i32 (Relop_i ROI_eq))], snd p));
  visit_OpVisitor_t_on_i32_ne :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_i32 (Relop_i ROI_ne))], snd p));
  visit_OpVisitor_t_on_i32_lt_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_i32 (Relop_i (ROI_lt SX_S)))], snd p));
  visit_OpVisitor_t_on_i32_lt_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_i32 (Relop_i (ROI_lt SX_U)))], snd p));
  visit_OpVisitor_t_on_i32_gt_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_i32 (Relop_i (ROI_gt SX_S)))], snd p));
  visit_OpVisitor_t_on_i32_gt_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_i32 (Relop_i (ROI_gt SX_U)))], snd p));
  visit_OpVisitor_t_on_i32_le_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_i32 (Relop_i (ROI_le SX_S)))], snd p));
  visit_OpVisitor_t_on_i32_le_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_i32 (Relop_i (ROI_le SX_U)))], snd p));
  visit_OpVisitor_t_on_i32_ge_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_i32 (Relop_i (ROI_ge SX_S)))], snd p));
  visit_OpVisitor_t_on_i32_ge_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_i32 (Relop_i (ROI_ge SX_U)))], snd p));
  visit_OpVisitor_t_on_i64_eqz :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_testop T_i64 TO_eqz)], snd p));
  visit_OpVisitor_t_on_i64_eq :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_i64 (Relop_i ROI_eq))], snd p));
  visit_OpVisitor_t_on_i64_ne :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_i64 (Relop_i ROI_ne))], snd p));
  visit_OpVisitor_t_on_i64_lt_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_i64 (Relop_i (ROI_lt SX_S)))], snd p));
  visit_OpVisitor_t_on_i64_lt_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_i64 (Relop_i (ROI_lt SX_U)))], snd p));
  visit_OpVisitor_t_on_i64_gt_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_i64 (Relop_i (ROI_gt SX_S)))], snd p));
  visit_OpVisitor_t_on_i64_gt_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_i64 (Relop_i (ROI_gt SX_U)))], snd p));
  visit_OpVisitor_t_on_i64_le_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_i64 (Relop_i (ROI_le SX_S)))], snd p));
  visit_OpVisitor_t_on_i64_le_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_i64 (Relop_i (ROI_le SX_U)))], snd p));
  visit_OpVisitor_t_on_i64_ge_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_i64 (Relop_i (ROI_ge SX_S)))], snd p));
  visit_OpVisitor_t_on_i64_ge_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_i64 (Relop_i (ROI_ge SX_U)))], snd p));
  visit_OpVisitor_t_on_f32_eq :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_f32 (Relop_f ROF_eq))], snd p));
  visit_OpVisitor_t_on_f32_ne :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_f32 (Relop_f ROF_ne))], snd p));
  visit_OpVisitor_t_on_f32_lt :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_f32 (Relop_f ROF_lt))], snd p));
  visit_OpVisitor_t_on_f32_gt :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_f32 (Relop_f ROF_gt))], snd p));
  visit_OpVisitor_t_on_f32_le :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_f32 (Relop_f ROF_le))], snd p));
  visit_OpVisitor_t_on_f32_ge :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_f32 (Relop_f ROF_ge))], snd p));
  visit_OpVisitor_t_on_f64_eq :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_f64 (Relop_f ROF_eq))], snd p));
  visit_OpVisitor_t_on_f64_ne :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_f64 (Relop_f ROF_ne))], snd p));
  visit_OpVisitor_t_on_f64_lt :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_f64 (Relop_f ROF_lt))], snd p));
  visit_OpVisitor_t_on_f64_gt :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_f64 (Relop_f ROF_gt))], snd p));
  visit_OpVisitor_t_on_f64_le :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_f64 (Relop_f ROF_le))], snd p));
  visit_OpVisitor_t_on_f64_ge :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_relop T_f64 (Relop_f ROF_ge))], snd p));
  visit_OpVisitor_t_on_i32_sub :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i32 (Binop_i BOI_sub))], snd p));
  visit_OpVisitor_t_on_i32_mul :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i32 (Binop_i BOI_mul))], snd p));
  visit_OpVisitor_t_on_i32_div_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i32 (Binop_i (BOI_div SX_S)))], snd p));
  visit_OpVisitor_t_on_i32_div_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i32 (Binop_i (BOI_div SX_U)))], snd p));
  visit_OpVisitor_t_on_i32_rem_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i32 (Binop_i (BOI_rem SX_S)))], snd p));
  visit_OpVisitor_t_on_i32_rem_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i32 (Binop_i (BOI_rem SX_U)))], snd p));
  visit_OpVisitor_t_on_i32_and :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i32 (Binop_i BOI_and))], snd p));
  visit_OpVisitor_t_on_i32_or :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i32 (Binop_i BOI_or))], snd p));
  visit_OpVisitor_t_on_i32_xor :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i32 (Binop_i BOI_xor))], snd p));
  visit_OpVisitor_t_on_i32_shl :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i32 (Binop_i BOI_shl))], snd p));
  visit_OpVisitor_t_on_i32_shr_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i32 (Binop_i (BOI_shr SX_S)))], snd p));
  visit_OpVisitor_t_on_i32_shr_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i32 (Binop_i (BOI_shr SX_U)))], snd p));
  visit_OpVisitor_t_on_i32_rotl :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i32 (Binop_i BOI_rotl))], snd p));
  visit_OpVisitor_t_on_i32_rotr :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i32 (Binop_i BOI_rotr))], snd p));
  visit_OpVisitor_t_on_i64_add :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i64 (Binop_i BOI_add))], snd p));
  visit_OpVisitor_t_on_i64_sub :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i64 (Binop_i BOI_sub))], snd p));
  visit_OpVisitor_t_on_i64_mul :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i64 (Binop_i BOI_mul))], snd p));
  visit_OpVisitor_t_on_i64_div_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i64 (Binop_i (BOI_div SX_S)))], snd p));
  visit_OpVisitor_t_on_i64_div_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i64 (Binop_i (BOI_div SX_U)))], snd p));
  visit_OpVisitor_t_on_i64_rem_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i64 (Binop_i (BOI_rem SX_S)))], snd p));
  visit_OpVisitor_t_on_i64_rem_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i64 (Binop_i (BOI_rem SX_U)))], snd p));
  visit_OpVisitor_t_on_i64_and :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i64 (Binop_i BOI_and))], snd p));
  visit_OpVisitor_t_on_i64_or :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i64 (Binop_i BOI_or))], snd p));
  visit_OpVisitor_t_on_i64_xor :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i64 (Binop_i BOI_xor))], snd p));
  visit_OpVisitor_t_on_i64_shl :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i64 (Binop_i BOI_shl))], snd p));
  visit_OpVisitor_t_on_i64_shr_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i64 (Binop_i (BOI_shr SX_S)))], snd p));
  visit_OpVisitor_t_on_i64_shr_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i64 (Binop_i (BOI_shr SX_U)))], snd p));
  visit_OpVisitor_t_on_i64_rotl :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i64 (Binop_i BOI_rotl))], snd p));
  visit_OpVisitor_t_on_i64_rotr :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i64 (Binop_i BOI_rotr))], snd p));
  visit_OpVisitor_t_on_f32_add :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_f32 (Binop_f BOF_add))], snd p));
  visit_OpVisitor_t_on_f32_sub :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_f32 (Binop_f BOF_sub))], snd p));
  visit_OpVisitor_t_on_f32_mul :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_f32 (Binop_f BOF_mul))], snd p));
  visit_OpVisitor_t_on_f32_div :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_f32 (Binop_f BOF_div))], snd p));
  visit_OpVisitor_t_on_f32_min :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_f32 (Binop_f BOF_min))], snd p));
  visit_OpVisitor_t_on_f32_max :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_f32 (Binop_f BOF_max))], snd p));
  visit_OpVisitor_t_on_f32_copysign :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_f32 (Binop_f BOF_copysign))], snd p));
  visit_OpVisitor_t_on_f64_add :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_f64 (Binop_f BOF_add))], snd p));
  visit_OpVisitor_t_on_f64_sub :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_f64 (Binop_f BOF_sub))], snd p));
  visit_OpVisitor_t_on_f64_mul :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_f64 (Binop_f BOF_mul))], snd p));
  visit_OpVisitor_t_on_f64_div :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_f64 (Binop_f BOF_div))], snd p));
  visit_OpVisitor_t_on_f64_min :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_f64 (Binop_f BOF_min))], snd p));
  visit_OpVisitor_t_on_f64_max :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_f64 (Binop_f BOF_max))], snd p));
  visit_OpVisitor_t_on_f64_copysign :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_f64 (Binop_f BOF_copysign))], snd p));
  visit_OpVisitor_t_on_i32_clz :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_unop T_i32 (Unop_i UOI_clz))], snd p));
  visit_OpVisitor_t_on_i32_ctz :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_unop T_i32 (Unop_i UOI_ctz))], snd p));
  visit_OpVisitor_t_on_i32_popcnt :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_unop T_i32 (Unop_i UOI_popcnt))], snd p));
  visit_OpVisitor_t_on_i32_add :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_binop T_i32 (Binop_i BOI_add))], snd p));
  visit_OpVisitor_t_on_i64_clz :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_unop T_i64 (Unop_i UOI_clz))], snd p));
  visit_OpVisitor_t_on_i64_ctz :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_unop T_i64 (Unop_i UOI_ctz))], snd p));
  visit_OpVisitor_t_on_i64_popcnt :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_unop T_i64 (Unop_i UOI_popcnt))], snd p));
  visit_OpVisitor_t_on_f32_abs :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_unop T_f32 (Unop_f UOF_abs))], snd p));
  visit_OpVisitor_t_on_f32_neg :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_unop T_f32 (Unop_f UOF_neg))], snd p));
  visit_OpVisitor_t_on_f32_ceil :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_unop T_f32 (Unop_f UOF_ceil))], snd p));
  visit_OpVisitor_t_on_f32_floor :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_unop T_f32 (Unop_f UOF_floor))], snd p));
  visit_OpVisitor_t_on_f32_trunc :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_unop T_f32 (Unop_f UOF_trunc))], snd p));
  visit_OpVisitor_t_on_f32_nearest :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_unop T_f32 (Unop_f UOF_nearest))], snd p));
  visit_OpVisitor_t_on_f32_sqrt :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_unop T_f32 (Unop_f UOF_sqrt))], snd p));
  visit_OpVisitor_t_on_f64_abs :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_unop T_f64 (Unop_f UOF_abs))], snd p));
  visit_OpVisitor_t_on_f64_neg :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_unop T_f64 (Unop_f UOF_neg))], snd p));
  visit_OpVisitor_t_on_f64_ceil :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_unop T_f64 (Unop_f UOF_ceil))], snd p));
  visit_OpVisitor_t_on_f64_floor :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_unop T_f64 (Unop_f UOF_floor))], snd p));
  visit_OpVisitor_t_on_f64_trunc :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_unop T_f64 (Unop_f UOF_trunc))], snd p));
  visit_OpVisitor_t_on_f64_nearest :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_unop T_f64 (Unop_f UOF_nearest))], snd p));
  visit_OpVisitor_t_on_f64_sqrt :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_unop T_f64 (Unop_f UOF_sqrt))], snd p));
  visit_OpVisitor_t_on_i32_wrap_i64 :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_i32 CVO_wrap T_i64 None)], snd p));
  visit_OpVisitor_t_on_i32_trunc_f32_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_i32 CVO_trunc T_f32 (Some SX_S))], snd p));
  visit_OpVisitor_t_on_i32_trunc_f32_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_i32 CVO_trunc T_f32 (Some SX_U))], snd p));
  visit_OpVisitor_t_on_i32_trunc_f64_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_i32 CVO_trunc T_f64 (Some SX_S))], snd p));
  visit_OpVisitor_t_on_i32_trunc_f64_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_i32 CVO_trunc T_f64 (Some SX_U))], snd p));
  visit_OpVisitor_t_on_i64_extend_i32_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_i64 CVO_extend T_i32 (Some SX_S))], snd p));
  visit_OpVisitor_t_on_i64_extend_i32_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_i64 CVO_extend T_i32 (Some SX_U))], snd p));
  visit_OpVisitor_t_on_i64_trunc_f32_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_i64 CVO_trunc T_f32 (Some SX_S))], snd p));
  visit_OpVisitor_t_on_i64_trunc_f32_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_i64 CVO_trunc T_f32 (Some SX_U))], snd p));
  visit_OpVisitor_t_on_i64_trunc_f64_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_i64 CVO_trunc T_f64 (Some SX_S))], snd p));
  visit_OpVisitor_t_on_i64_trunc_f64_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_i64 CVO_trunc T_f64 (Some SX_U))], snd p));
  visit_OpVisitor_t_on_f32_convert_i32_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_f32 CVO_convert T_i32 (Some SX_S))], snd p));
  visit_OpVisitor_t_on_f32_convert_i32_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_f32 CVO_convert T_i32 (Some SX_U))], snd p));
  visit_OpVisitor_t_on_f32_convert_i64_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_f32 CVO_convert T_i64 (Some SX_S))], snd p));
  visit_OpVisitor_t_on_f32_convert_i64_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_f32 CVO_convert T_i64 (Some SX_U))], snd p));
  visit_OpVisitor_t_on_f32_demote_f64 :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_f32 CVO_demote T_f64 None)], snd p));
  visit_OpVisitor_t_on_f64_convert_i32_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_f64 CVO_convert T_i32 (Some SX_S))], snd p));
  visit_OpVisitor_t_on_f64_convert_i32_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_f64 CVO_convert T_i32 (Some SX_U))], snd p));
  visit_OpVisitor_t_on_f64_convert_i64_s :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_f64 CVO_convert T_i64 (Some SX_S))], snd p));
  visit_OpVisitor_t_on_f64_convert_i64_u :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_f64 CVO_convert T_i64 (Some SX_U))], snd p));
  visit_OpVisitor_t_on_f64_promote_f32 :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_f64 CVO_promote T_f32 None)], snd p));
  visit_OpVisitor_t_on_i32_reinterpret_f32 :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_i32 CVO_reinterpret T_f32 None)], snd p));
  visit_OpVisitor_t_on_i64_reinterpret_f64 :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_i64 CVO_reinterpret T_f64 None)], snd p));
  visit_OpVisitor_t_on_f32_reinterpret_i32 :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_f32 CVO_reinterpret T_i32 None)], snd p));
  visit_OpVisitor_t_on_f64_reinterpret_i64 :=
    fun p st =>
      Ok (Core_result_Result_Ok tt,
          (fst p ++ [FO_plain (BI_cvtop T_f64 CVO_reinterpret T_i64 None)], snd p))
|}.

(** One row of the numeric fan-out: the byte is known, so both tables compute,
    and what is left is whether they agree. *)
Local Ltac visit_row E Hspec :=
  rewrite E in Hspec; cbn in Hspec; injection Hspec as <-;
  unfold visit_visit_numeric, visit_visit_memory, scalar_eqb;
  rewrite E; cbn; reflexivity.

Local Ltac walk_visit H Hspec :=
  repeat match type of H with
  | (if (?x s= ?y) then _ else _) = _ =>
      let E := fresh "E" in
      destruct (x s= y) eqn:E;
      [ cbn beta iota in H;
        apply scalar_eqb_true in E;
        visit_row E Hspec
      | cbn beta iota in H ]
  end.

(** The numeric fan-out picks the hook whose mnemonic names the instruction the
    specification's table gives that byte. Stated over the two shapes the
    validator dispatches through, so the byte is never a variable and the
    fallthrough is [convert_types]'s own. *)
Theorem visit_numeric_names_convert : forall (b : u8) from to be tr pend st,
  opiter_convert_types b = Ok (Some (from, to)) ->
  op_spec (to_Z b) = Some (Sh_nullary be) ->
  visit_visit_numeric trace_visitor (tr, pend) st b
    = Ok (Core_result_Result_Ok tt, (tr ++ [FO_plain be], pend)).
Proof.
  intros b from to be tr pend st Hcv Hspec. unfold opiter_convert_types in Hcv.
  walk_visit Hcv Hspec.
  discriminate Hcv.
Qed.

Theorem visit_numeric_names_binary : forall (b : u8) ty res be tr pend st,
  opiter_binary_types b = Ok (Some (ty, res)) ->
  op_spec (to_Z b) = Some (Sh_nullary be) ->
  visit_visit_numeric trace_visitor (tr, pend) st b
    = Ok (Core_result_Result_Ok tt, (tr ++ [FO_plain be], pend)).
Proof.
  intros b ty res be tr pend st Hbt Hspec. unfold opiter_binary_types in Hbt.
  walk_visit Hbt Hspec.
  discriminate Hbt.
Qed.

(** The memory fan-out, walked from the specification's side: [Sh_load] and
    [Sh_store] pin the byte to a memory opcode, so no guard from the code's
    tables is needed. The alignment and the offset come from the [memarg] the
    reader decoded, which is what the hook is handed. *)
Local Ltac walk_visit_mem Hspec :=
  repeat match type of Hspec with
  | (if Z.eqb ?x ?k then _ else _) = _ =>
      let E := fresh "E" in
      destruct (Z.eqb x k) eqn:E;
      [ cbn beta iota in Hspec;
        first [ discriminate Hspec
              | apply Z.eqb_eq in E;
                injection Hspec as <- <-;
                unfold visit_visit_memory, scalar_eqb; rewrite E; cbn;
                reflexivity ]
      | cbn beta iota in Hspec ]
  end.

Theorem visit_memory_names_load : forall (b : u8) nt tp tr pend st m,
  op_spec (to_Z b) = Some (Sh_load nt tp) ->
  visit_visit_memory trace_visitor (tr, pend) st b m
    = Ok (Core_result_Result_Ok tt,
          (tr ++ [FO_plain (BI_load nt tp
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))], pend)).
Proof.
  intros b nt tp tr pend st m Hspec. unfold op_spec in Hspec.
  walk_visit_mem Hspec.
  discriminate Hspec.
Qed.

Theorem visit_memory_names_store : forall (b : u8) nt tp tr pend st m,
  op_spec (to_Z b) = Some (Sh_store nt tp) ->
  visit_visit_memory trace_visitor (tr, pend) st b m
    = Ok (Core_result_Result_Ok tt,
          (tr ++ [FO_plain (BI_store nt tp
                             (Z.to_N (to_Z m.(opiter_MemArg_align)))
                             (Z.to_N (to_Z m.(opiter_MemArg_offset))))], pend)).
Proof.
  intros b nt tp tr pend st m Hspec. unfold op_spec in Hspec.
  walk_visit_mem Hspec.
  discriminate Hspec.
Qed.


(** The recorder records: every row but the four fan-outs is a computation on
    its own hook, and the fan-outs are the four theorems above. Naming the
    projections is what keeps [cbn] from normalising a hundred-and-seventy-four
    field record sixty-four times over. *)
Lemma trace_records : records trace_visitor fst snd.
Proof.
  unfold records. repeat split.
  (* the four fan-outs: the theorems above, at a state split into its halves *)
  1-8: destruct v as [tr pend];
       match goal with
       | Hc : opiter_convert_types _ = _, Hs : op_spec _ = _,
         H : visit_visit_numeric _ _ _ _ = _ |- _ =>
           rewrite (visit_numeric_names_convert _ _ _ _ tr pend _ Hc Hs) in H;
           injection H as <-
       | Hb : opiter_binary_types _ = _, Hs : op_spec _ = _,
         H : visit_visit_numeric _ _ _ _ = _ |- _ =>
           rewrite (visit_numeric_names_binary _ _ _ _ tr pend _ Hb Hs) in H;
           injection H as <-
       | Hs : op_spec _ = Some (Sh_load _ _),
         H : visit_visit_memory _ _ _ _ _ = _ |- _ =>
           rewrite (visit_memory_names_load _ _ _ tr pend _ _ Hs) in H;
           injection H as <-
       | Hs : op_spec _ = Some (Sh_store _ _),
         H : visit_visit_memory _ _ _ _ _ = _ |- _ =>
           rewrite (visit_memory_names_store _ _ _ tr pend _ _ Hs) in H;
           injection H as <-
       end;
       reflexivity.
  (* every other row is its own hook, computed *)
  all: cbn [visit_OpVisitor_t_on_function_start visit_OpVisitor_t_on_unreachable visit_OpVisitor_t_on_nop
              visit_OpVisitor_t_on_block visit_OpVisitor_t_on_loop visit_OpVisitor_t_on_if
              visit_OpVisitor_t_on_else visit_OpVisitor_t_on_end visit_OpVisitor_t_on_br
              visit_OpVisitor_t_on_br_if visit_OpVisitor_t_on_br_table_label visit_OpVisitor_t_on_br_table
              visit_OpVisitor_t_on_return visit_OpVisitor_t_on_call visit_OpVisitor_t_on_call_indirect
              visit_OpVisitor_t_on_drop visit_OpVisitor_t_on_select visit_OpVisitor_t_on_local_get
              visit_OpVisitor_t_on_local_set visit_OpVisitor_t_on_local_tee visit_OpVisitor_t_on_global_get
              visit_OpVisitor_t_on_global_set visit_OpVisitor_t_on_memory_size visit_OpVisitor_t_on_memory_grow
              visit_OpVisitor_t_on_i32_const visit_OpVisitor_t_on_i64_const visit_OpVisitor_t_on_f32_const
              visit_OpVisitor_t_on_f64_const visit_OpVisitor_t_on_i32_load visit_OpVisitor_t_on_i64_load
              visit_OpVisitor_t_on_f32_load visit_OpVisitor_t_on_f64_load visit_OpVisitor_t_on_i32_load8_s
              visit_OpVisitor_t_on_i32_load8_u visit_OpVisitor_t_on_i32_load16_s visit_OpVisitor_t_on_i32_load16_u
              visit_OpVisitor_t_on_i64_load8_s visit_OpVisitor_t_on_i64_load8_u visit_OpVisitor_t_on_i64_load16_s
              visit_OpVisitor_t_on_i64_load16_u visit_OpVisitor_t_on_i64_load32_s visit_OpVisitor_t_on_i64_load32_u
              visit_OpVisitor_t_on_i32_store visit_OpVisitor_t_on_i64_store visit_OpVisitor_t_on_f32_store
              visit_OpVisitor_t_on_f64_store visit_OpVisitor_t_on_i32_store8 visit_OpVisitor_t_on_i32_store16
              visit_OpVisitor_t_on_i64_store8 visit_OpVisitor_t_on_i64_store16 visit_OpVisitor_t_on_i64_store32
              visit_OpVisitor_t_on_i32_eqz visit_OpVisitor_t_on_i32_eq visit_OpVisitor_t_on_i32_ne
              visit_OpVisitor_t_on_i32_lt_s visit_OpVisitor_t_on_i32_lt_u visit_OpVisitor_t_on_i32_gt_s
              visit_OpVisitor_t_on_i32_gt_u visit_OpVisitor_t_on_i32_le_s visit_OpVisitor_t_on_i32_le_u
              visit_OpVisitor_t_on_i32_ge_s visit_OpVisitor_t_on_i32_ge_u visit_OpVisitor_t_on_i64_eqz
              visit_OpVisitor_t_on_i64_eq visit_OpVisitor_t_on_i64_ne visit_OpVisitor_t_on_i64_lt_s
              visit_OpVisitor_t_on_i64_lt_u visit_OpVisitor_t_on_i64_gt_s visit_OpVisitor_t_on_i64_gt_u
              visit_OpVisitor_t_on_i64_le_s visit_OpVisitor_t_on_i64_le_u visit_OpVisitor_t_on_i64_ge_s
              visit_OpVisitor_t_on_i64_ge_u visit_OpVisitor_t_on_f32_eq visit_OpVisitor_t_on_f32_ne
              visit_OpVisitor_t_on_f32_lt visit_OpVisitor_t_on_f32_gt visit_OpVisitor_t_on_f32_le
              visit_OpVisitor_t_on_f32_ge visit_OpVisitor_t_on_f64_eq visit_OpVisitor_t_on_f64_ne
              visit_OpVisitor_t_on_f64_lt visit_OpVisitor_t_on_f64_gt visit_OpVisitor_t_on_f64_le
              visit_OpVisitor_t_on_f64_ge visit_OpVisitor_t_on_i32_sub visit_OpVisitor_t_on_i32_mul
              visit_OpVisitor_t_on_i32_div_s visit_OpVisitor_t_on_i32_div_u visit_OpVisitor_t_on_i32_rem_s
              visit_OpVisitor_t_on_i32_rem_u visit_OpVisitor_t_on_i32_and visit_OpVisitor_t_on_i32_or
              visit_OpVisitor_t_on_i32_xor visit_OpVisitor_t_on_i32_shl visit_OpVisitor_t_on_i32_shr_s
              visit_OpVisitor_t_on_i32_shr_u visit_OpVisitor_t_on_i32_rotl visit_OpVisitor_t_on_i32_rotr
              visit_OpVisitor_t_on_i64_add visit_OpVisitor_t_on_i64_sub visit_OpVisitor_t_on_i64_mul
              visit_OpVisitor_t_on_i64_div_s visit_OpVisitor_t_on_i64_div_u visit_OpVisitor_t_on_i64_rem_s
              visit_OpVisitor_t_on_i64_rem_u visit_OpVisitor_t_on_i64_and visit_OpVisitor_t_on_i64_or
              visit_OpVisitor_t_on_i64_xor visit_OpVisitor_t_on_i64_shl visit_OpVisitor_t_on_i64_shr_s
              visit_OpVisitor_t_on_i64_shr_u visit_OpVisitor_t_on_i64_rotl visit_OpVisitor_t_on_i64_rotr
              visit_OpVisitor_t_on_f32_add visit_OpVisitor_t_on_f32_sub visit_OpVisitor_t_on_f32_mul
              visit_OpVisitor_t_on_f32_div visit_OpVisitor_t_on_f32_min visit_OpVisitor_t_on_f32_max
              visit_OpVisitor_t_on_f32_copysign visit_OpVisitor_t_on_f64_add visit_OpVisitor_t_on_f64_sub
              visit_OpVisitor_t_on_f64_mul visit_OpVisitor_t_on_f64_div visit_OpVisitor_t_on_f64_min
              visit_OpVisitor_t_on_f64_max visit_OpVisitor_t_on_f64_copysign visit_OpVisitor_t_on_i32_clz
              visit_OpVisitor_t_on_i32_ctz visit_OpVisitor_t_on_i32_popcnt visit_OpVisitor_t_on_i32_add
              visit_OpVisitor_t_on_i64_clz visit_OpVisitor_t_on_i64_ctz visit_OpVisitor_t_on_i64_popcnt
              visit_OpVisitor_t_on_f32_abs visit_OpVisitor_t_on_f32_neg visit_OpVisitor_t_on_f32_ceil
              visit_OpVisitor_t_on_f32_floor visit_OpVisitor_t_on_f32_trunc visit_OpVisitor_t_on_f32_nearest
              visit_OpVisitor_t_on_f32_sqrt visit_OpVisitor_t_on_f64_abs visit_OpVisitor_t_on_f64_neg
              visit_OpVisitor_t_on_f64_ceil visit_OpVisitor_t_on_f64_floor visit_OpVisitor_t_on_f64_trunc
              visit_OpVisitor_t_on_f64_nearest visit_OpVisitor_t_on_f64_sqrt visit_OpVisitor_t_on_i32_wrap_i64
              visit_OpVisitor_t_on_i32_trunc_f32_s visit_OpVisitor_t_on_i32_trunc_f32_u visit_OpVisitor_t_on_i32_trunc_f64_s
              visit_OpVisitor_t_on_i32_trunc_f64_u visit_OpVisitor_t_on_i64_extend_i32_s visit_OpVisitor_t_on_i64_extend_i32_u
              visit_OpVisitor_t_on_i64_trunc_f32_s visit_OpVisitor_t_on_i64_trunc_f32_u visit_OpVisitor_t_on_i64_trunc_f64_s
              visit_OpVisitor_t_on_i64_trunc_f64_u visit_OpVisitor_t_on_f32_convert_i32_s visit_OpVisitor_t_on_f32_convert_i32_u
              visit_OpVisitor_t_on_f32_convert_i64_s visit_OpVisitor_t_on_f32_convert_i64_u visit_OpVisitor_t_on_f32_demote_f64
              visit_OpVisitor_t_on_f64_convert_i32_s visit_OpVisitor_t_on_f64_convert_i32_u visit_OpVisitor_t_on_f64_convert_i64_s
              visit_OpVisitor_t_on_f64_convert_i64_u visit_OpVisitor_t_on_f64_promote_f32 visit_OpVisitor_t_on_i32_reinterpret_f32
              visit_OpVisitor_t_on_i64_reinterpret_f64 visit_OpVisitor_t_on_f32_reinterpret_i32 visit_OpVisitor_t_on_f64_reinterpret_i64 trace_visitor] in *;
       match goal with H : Ok _ = Ok _ |- _ => injection H as <- end;
       reflexivity.
Qed.
