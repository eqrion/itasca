(** * The consumer's hooks

    [validate_body_with] hands each accepted operator to a hook, and a hook is
    unverified code: it can report a [VisitError], and nothing in its type stops
    it from panicking or looping instead. So every theorem about the generic
    validator carries [hooks_total], which says exactly that the hooks return.
    It is the whole of what a consumer has to be trusted for.

    Two things are proved here. The generated fan-outs inherit totality, which
    is what lets the dispatch proofs treat a numeric or memory operator as one
    branch rather than 146. And [EmptyOpVisitor] satisfies [hooks_total] by
    computation, which is what makes [validate_body]'s theorems unconditional.

    The definition is one conjunct per hook, in the order the trait declares
    them. It is mechanical, and it is long for the same reason the trait is. *)

Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Import Itasca.Aeneas_Specs.
Open Scope Z_scope.

(** Every hook returns. It may still report a [VisitError]: that is a value,
    not a failure, and the loop stops on it by design. *)
Definition hooks_total {V : Type} (inst : code_OpVisitor_t V) : Prop :=
  (forall v st x0 x1 x2, exists r v', inst.(code_OpVisitor_t_on_function_start) v st x0 x1 x2 = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_unreachable) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_nop) v st = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_block) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_loop) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_if) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_else) v st x0 = Ok (r, v'))
  /\
  (forall v st x0 x1, exists r v', inst.(code_OpVisitor_t_on_end) v st x0 x1 = Ok (r, v'))
  /\
  (forall v st x0 x1, exists r v', inst.(code_OpVisitor_t_on_br) v st x0 x1 = Ok (r, v'))
  /\
  (forall v st x0 x1, exists r v', inst.(code_OpVisitor_t_on_br_if) v st x0 x1 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_br_table_label) v st x0 = Ok (r, v'))
  /\
  (forall v st x0 x1, exists r v', inst.(code_OpVisitor_t_on_br_table) v st x0 x1 = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_return) v st = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_call) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_call_indirect) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_drop) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_select) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_local_get) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_local_set) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_local_tee) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_global_get) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_global_set) v st x0 = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_memory_size) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_memory_grow) v st = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_i32_const) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_i64_const) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_f32_const) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_f64_const) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_i32_load) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_i64_load) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_f32_load) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_f64_load) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_i32_load8_s) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_i32_load8_u) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_i32_load16_s) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_i32_load16_u) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_i64_load8_s) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_i64_load8_u) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_i64_load16_s) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_i64_load16_u) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_i64_load32_s) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_i64_load32_u) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_i32_store) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_i64_store) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_f32_store) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_f64_store) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_i32_store8) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_i32_store16) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_i64_store8) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_i64_store16) v st x0 = Ok (r, v'))
  /\
  (forall v st x0, exists r v', inst.(code_OpVisitor_t_on_i64_store32) v st x0 = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_eqz) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_eq) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_ne) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_lt_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_lt_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_gt_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_gt_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_le_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_le_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_ge_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_ge_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_eqz) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_eq) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_ne) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_lt_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_lt_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_gt_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_gt_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_le_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_le_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_ge_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_ge_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_eq) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_ne) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_lt) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_gt) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_le) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_ge) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_eq) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_ne) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_lt) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_gt) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_le) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_ge) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_sub) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_mul) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_div_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_div_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_rem_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_rem_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_and) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_or) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_xor) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_shl) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_shr_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_shr_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_rotl) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_rotr) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_add) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_sub) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_mul) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_div_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_div_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_rem_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_rem_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_and) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_or) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_xor) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_shl) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_shr_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_shr_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_rotl) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_rotr) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_add) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_sub) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_mul) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_div) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_min) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_max) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_copysign) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_add) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_sub) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_mul) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_div) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_min) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_max) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_copysign) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_clz) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_ctz) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_popcnt) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_add) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_clz) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_ctz) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_popcnt) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_abs) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_neg) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_ceil) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_floor) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_trunc) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_nearest) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_sqrt) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_abs) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_neg) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_ceil) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_floor) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_trunc) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_nearest) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_sqrt) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_wrap_i64) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_trunc_f32_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_trunc_f32_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_trunc_f64_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_trunc_f64_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_extend_i32_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_extend_i32_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_trunc_f32_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_trunc_f32_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_trunc_f64_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_trunc_f64_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_convert_i32_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_convert_i32_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_convert_i64_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_convert_i64_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_demote_f64) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_convert_i32_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_convert_i32_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_convert_i64_s) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_convert_i64_u) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_promote_f32) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i32_reinterpret_f32) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_i64_reinterpret_f64) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f32_reinterpret_i32) v st = Ok (r, v'))
  /\
  (forall v st, exists r v', inst.(code_OpVisitor_t_on_f64_reinterpret_i64) v st = Ok (r, v')).

(** The one hook a reader calls, named on its own: the [br_table] label loop
    needs it round by round, and pulling it out of the conjunction each time
    would mean destructuring 174 conjuncts inside an induction. *)
Lemma label_hook_total : forall V (inst : code_OpVisitor_t V) v st d,
  hooks_total inst ->
  exists r v', inst.(code_OpVisitor_t_on_br_table_label) v st d = Ok (r, v').
Proof.
  intros V inst v st d H. unfold hooks_total in H.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  eauto.
Qed.


(** The fan-outs are a chain of opcode tests ending in a hook call, so they
    return whenever the hooks do, and they cannot touch the validator state:
    they are handed a shared borrow of it and Rust gives them no way to write
    through it. The dispatch proofs need exactly these two facts. *)
Lemma visit_numeric_total : forall V (inst : code_OpVisitor_t V) v st opcode,
  hooks_total inst ->
  exists r v', code_visit_numeric inst v st opcode = Ok (r, v').
Proof.
  intros V inst v st opcode H. unfold hooks_total in H.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  unfold code_visit_numeric.
  repeat match goal with |- context [ if ?c then _ else _ ] => destruct c end;
    eauto.
Qed.

Lemma visit_memory_total : forall V (inst : code_OpVisitor_t V) v st opcode m,
  hooks_total inst ->
  exists r v', code_visit_memory inst v st opcode m = Ok (r, v').
Proof.
  intros V inst v st opcode m H. unfold hooks_total in H.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  unfold code_visit_memory.
  repeat match goal with |- context [ if ?c then _ else _ ] => destruct c end;
    eauto.
Qed.

(** [EmptyOpVisitor]'s hooks are all [fun self _ => Ok (Ok tt, self)], so this is a
    computation. It is what turns every theorem below into an unconditional
    statement about [validate_body]. *)
Lemma nop_hooks_total : hooks_total code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor.
Proof.
  unfold hooks_total, code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor.
  repeat split; intros;
    cbn [code_OpVisitor_t_on_function_start code_OpVisitor_t_on_unreachable code_OpVisitor_t_on_nop code_OpVisitor_t_on_block code_OpVisitor_t_on_loop code_OpVisitor_t_on_if code_OpVisitor_t_on_else code_OpVisitor_t_on_end code_OpVisitor_t_on_br code_OpVisitor_t_on_br_if code_OpVisitor_t_on_br_table_label code_OpVisitor_t_on_br_table code_OpVisitor_t_on_return code_OpVisitor_t_on_call code_OpVisitor_t_on_call_indirect code_OpVisitor_t_on_drop code_OpVisitor_t_on_select code_OpVisitor_t_on_local_get code_OpVisitor_t_on_local_set code_OpVisitor_t_on_local_tee code_OpVisitor_t_on_global_get code_OpVisitor_t_on_global_set code_OpVisitor_t_on_memory_size code_OpVisitor_t_on_memory_grow code_OpVisitor_t_on_i32_const code_OpVisitor_t_on_i64_const code_OpVisitor_t_on_f32_const code_OpVisitor_t_on_f64_const code_OpVisitor_t_on_i32_load code_OpVisitor_t_on_i64_load code_OpVisitor_t_on_f32_load code_OpVisitor_t_on_f64_load code_OpVisitor_t_on_i32_load8_s code_OpVisitor_t_on_i32_load8_u code_OpVisitor_t_on_i32_load16_s code_OpVisitor_t_on_i32_load16_u code_OpVisitor_t_on_i64_load8_s code_OpVisitor_t_on_i64_load8_u code_OpVisitor_t_on_i64_load16_s code_OpVisitor_t_on_i64_load16_u code_OpVisitor_t_on_i64_load32_s code_OpVisitor_t_on_i64_load32_u code_OpVisitor_t_on_i32_store code_OpVisitor_t_on_i64_store code_OpVisitor_t_on_f32_store code_OpVisitor_t_on_f64_store code_OpVisitor_t_on_i32_store8 code_OpVisitor_t_on_i32_store16 code_OpVisitor_t_on_i64_store8 code_OpVisitor_t_on_i64_store16 code_OpVisitor_t_on_i64_store32 code_OpVisitor_t_on_i32_eqz code_OpVisitor_t_on_i32_eq code_OpVisitor_t_on_i32_ne code_OpVisitor_t_on_i32_lt_s code_OpVisitor_t_on_i32_lt_u code_OpVisitor_t_on_i32_gt_s code_OpVisitor_t_on_i32_gt_u code_OpVisitor_t_on_i32_le_s code_OpVisitor_t_on_i32_le_u code_OpVisitor_t_on_i32_ge_s code_OpVisitor_t_on_i32_ge_u code_OpVisitor_t_on_i64_eqz code_OpVisitor_t_on_i64_eq code_OpVisitor_t_on_i64_ne code_OpVisitor_t_on_i64_lt_s code_OpVisitor_t_on_i64_lt_u code_OpVisitor_t_on_i64_gt_s code_OpVisitor_t_on_i64_gt_u code_OpVisitor_t_on_i64_le_s code_OpVisitor_t_on_i64_le_u code_OpVisitor_t_on_i64_ge_s code_OpVisitor_t_on_i64_ge_u code_OpVisitor_t_on_f32_eq code_OpVisitor_t_on_f32_ne code_OpVisitor_t_on_f32_lt code_OpVisitor_t_on_f32_gt code_OpVisitor_t_on_f32_le code_OpVisitor_t_on_f32_ge code_OpVisitor_t_on_f64_eq code_OpVisitor_t_on_f64_ne code_OpVisitor_t_on_f64_lt code_OpVisitor_t_on_f64_gt code_OpVisitor_t_on_f64_le code_OpVisitor_t_on_f64_ge code_OpVisitor_t_on_i32_sub code_OpVisitor_t_on_i32_mul code_OpVisitor_t_on_i32_div_s code_OpVisitor_t_on_i32_div_u code_OpVisitor_t_on_i32_rem_s code_OpVisitor_t_on_i32_rem_u code_OpVisitor_t_on_i32_and code_OpVisitor_t_on_i32_or code_OpVisitor_t_on_i32_xor code_OpVisitor_t_on_i32_shl code_OpVisitor_t_on_i32_shr_s code_OpVisitor_t_on_i32_shr_u code_OpVisitor_t_on_i32_rotl code_OpVisitor_t_on_i32_rotr code_OpVisitor_t_on_i64_add code_OpVisitor_t_on_i64_sub code_OpVisitor_t_on_i64_mul code_OpVisitor_t_on_i64_div_s code_OpVisitor_t_on_i64_div_u code_OpVisitor_t_on_i64_rem_s code_OpVisitor_t_on_i64_rem_u code_OpVisitor_t_on_i64_and code_OpVisitor_t_on_i64_or code_OpVisitor_t_on_i64_xor code_OpVisitor_t_on_i64_shl code_OpVisitor_t_on_i64_shr_s code_OpVisitor_t_on_i64_shr_u code_OpVisitor_t_on_i64_rotl code_OpVisitor_t_on_i64_rotr code_OpVisitor_t_on_f32_add code_OpVisitor_t_on_f32_sub code_OpVisitor_t_on_f32_mul code_OpVisitor_t_on_f32_div code_OpVisitor_t_on_f32_min code_OpVisitor_t_on_f32_max code_OpVisitor_t_on_f32_copysign code_OpVisitor_t_on_f64_add code_OpVisitor_t_on_f64_sub code_OpVisitor_t_on_f64_mul code_OpVisitor_t_on_f64_div code_OpVisitor_t_on_f64_min code_OpVisitor_t_on_f64_max code_OpVisitor_t_on_f64_copysign code_OpVisitor_t_on_i32_clz code_OpVisitor_t_on_i32_ctz code_OpVisitor_t_on_i32_popcnt code_OpVisitor_t_on_i32_add code_OpVisitor_t_on_i64_clz code_OpVisitor_t_on_i64_ctz code_OpVisitor_t_on_i64_popcnt code_OpVisitor_t_on_f32_abs code_OpVisitor_t_on_f32_neg code_OpVisitor_t_on_f32_ceil code_OpVisitor_t_on_f32_floor code_OpVisitor_t_on_f32_trunc code_OpVisitor_t_on_f32_nearest code_OpVisitor_t_on_f32_sqrt code_OpVisitor_t_on_f64_abs code_OpVisitor_t_on_f64_neg code_OpVisitor_t_on_f64_ceil code_OpVisitor_t_on_f64_floor code_OpVisitor_t_on_f64_trunc code_OpVisitor_t_on_f64_nearest code_OpVisitor_t_on_f64_sqrt code_OpVisitor_t_on_i32_wrap_i64 code_OpVisitor_t_on_i32_trunc_f32_s code_OpVisitor_t_on_i32_trunc_f32_u code_OpVisitor_t_on_i32_trunc_f64_s code_OpVisitor_t_on_i32_trunc_f64_u code_OpVisitor_t_on_i64_extend_i32_s code_OpVisitor_t_on_i64_extend_i32_u code_OpVisitor_t_on_i64_trunc_f32_s code_OpVisitor_t_on_i64_trunc_f32_u code_OpVisitor_t_on_i64_trunc_f64_s code_OpVisitor_t_on_i64_trunc_f64_u code_OpVisitor_t_on_f32_convert_i32_s code_OpVisitor_t_on_f32_convert_i32_u code_OpVisitor_t_on_f32_convert_i64_s code_OpVisitor_t_on_f32_convert_i64_u code_OpVisitor_t_on_f32_demote_f64 code_OpVisitor_t_on_f64_convert_i32_s code_OpVisitor_t_on_f64_convert_i32_u code_OpVisitor_t_on_f64_convert_i64_s code_OpVisitor_t_on_f64_convert_i64_u code_OpVisitor_t_on_f64_promote_f32 code_OpVisitor_t_on_i32_reinterpret_f32 code_OpVisitor_t_on_i64_reinterpret_f64 code_OpVisitor_t_on_f32_reinterpret_i32 code_OpVisitor_t_on_f64_reinterpret_i64];
    unfold code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_function_start,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_unreachable,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_nop,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_block,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_loop,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_if,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_else,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_end,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_br,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_br_if,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_br_table_label,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_br_table,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_return,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_call,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_call_indirect,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_drop,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_select,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_local_get,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_local_set,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_local_tee,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_global_get,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_global_set,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_memory_size,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_memory_grow,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_const,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_const,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_const,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_const,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_load,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_load,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_load,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_load,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_load8_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_load8_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_load16_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_load16_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_load8_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_load8_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_load16_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_load16_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_load32_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_load32_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_store,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_store,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_store,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_store,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_store8,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_store16,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_store8,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_store16,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_store32,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_eqz,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_eq,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_ne,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_lt_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_lt_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_gt_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_gt_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_le_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_le_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_ge_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_ge_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_eqz,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_eq,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_ne,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_lt_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_lt_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_gt_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_gt_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_le_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_le_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_ge_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_ge_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_eq,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_ne,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_lt,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_gt,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_le,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_ge,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_eq,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_ne,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_lt,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_gt,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_le,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_ge,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_sub,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_mul,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_div_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_div_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_rem_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_rem_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_and,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_or,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_xor,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_shl,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_shr_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_shr_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_rotl,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_rotr,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_add,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_sub,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_mul,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_div_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_div_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_rem_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_rem_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_and,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_or,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_xor,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_shl,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_shr_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_shr_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_rotl,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_rotr,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_add,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_sub,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_mul,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_div,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_min,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_max,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_copysign,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_add,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_sub,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_mul,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_div,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_min,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_max,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_copysign,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_clz,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_ctz,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_popcnt,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_add,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_clz,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_ctz,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_popcnt,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_abs,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_neg,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_ceil,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_floor,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_trunc,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_nearest,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_sqrt,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_abs,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_neg,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_ceil,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_floor,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_trunc,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_nearest,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_sqrt,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_wrap_i64,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_trunc_f32_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_trunc_f32_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_trunc_f64_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_trunc_f64_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_extend_i32_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_extend_i32_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_trunc_f32_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_trunc_f32_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_trunc_f64_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_trunc_f64_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_convert_i32_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_convert_i32_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_convert_i64_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_convert_i64_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_demote_f64,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_convert_i32_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_convert_i32_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_convert_i64_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_convert_i64_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_promote_f32,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_reinterpret_f32,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_reinterpret_f64,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_reinterpret_i32,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_reinterpret_i64;
    eauto.
Qed.

(** Every hook returns [Ok]: the consumer accepts every operator it is shown.
    Completeness needs this rather than [hooks_total], because a consumer that
    declines a well-typed body stops the loop, and rightly so. *)
Definition hooks_accept {V : Type} (inst : code_OpVisitor_t V) : Prop :=
  (forall v st x0 x1 x2, exists v', inst.(code_OpVisitor_t_on_function_start) v st x0 x1 x2 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_unreachable) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_nop) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_block) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_loop) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_if) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_else) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0 x1, exists v', inst.(code_OpVisitor_t_on_end) v st x0 x1 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0 x1, exists v', inst.(code_OpVisitor_t_on_br) v st x0 x1 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0 x1, exists v', inst.(code_OpVisitor_t_on_br_if) v st x0 x1 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_br_table_label) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0 x1, exists v', inst.(code_OpVisitor_t_on_br_table) v st x0 x1 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_return) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_call) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_call_indirect) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_drop) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_select) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_local_get) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_local_set) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_local_tee) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_global_get) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_global_set) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_memory_size) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_memory_grow) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_i32_const) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_i64_const) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_f32_const) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_f64_const) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_i32_load) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_i64_load) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_f32_load) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_f64_load) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_i32_load8_s) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_i32_load8_u) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_i32_load16_s) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_i32_load16_u) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_i64_load8_s) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_i64_load8_u) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_i64_load16_s) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_i64_load16_u) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_i64_load32_s) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_i64_load32_u) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_i32_store) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_i64_store) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_f32_store) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_f64_store) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_i32_store8) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_i32_store16) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_i64_store8) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_i64_store16) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st x0, exists v', inst.(code_OpVisitor_t_on_i64_store32) v st x0 = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_eqz) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_eq) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_ne) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_lt_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_lt_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_gt_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_gt_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_le_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_le_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_ge_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_ge_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_eqz) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_eq) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_ne) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_lt_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_lt_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_gt_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_gt_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_le_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_le_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_ge_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_ge_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_eq) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_ne) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_lt) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_gt) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_le) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_ge) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_eq) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_ne) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_lt) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_gt) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_le) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_ge) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_sub) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_mul) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_div_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_div_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_rem_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_rem_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_and) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_or) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_xor) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_shl) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_shr_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_shr_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_rotl) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_rotr) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_add) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_sub) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_mul) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_div_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_div_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_rem_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_rem_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_and) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_or) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_xor) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_shl) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_shr_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_shr_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_rotl) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_rotr) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_add) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_sub) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_mul) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_div) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_min) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_max) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_copysign) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_add) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_sub) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_mul) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_div) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_min) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_max) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_copysign) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_clz) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_ctz) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_popcnt) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_add) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_clz) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_ctz) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_popcnt) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_abs) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_neg) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_ceil) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_floor) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_trunc) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_nearest) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_sqrt) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_abs) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_neg) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_ceil) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_floor) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_trunc) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_nearest) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_sqrt) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_wrap_i64) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_trunc_f32_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_trunc_f32_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_trunc_f64_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_trunc_f64_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_extend_i32_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_extend_i32_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_trunc_f32_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_trunc_f32_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_trunc_f64_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_trunc_f64_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_convert_i32_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_convert_i32_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_convert_i64_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_convert_i64_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_demote_f64) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_convert_i32_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_convert_i32_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_convert_i64_s) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_convert_i64_u) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_promote_f32) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i32_reinterpret_f32) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_i64_reinterpret_f64) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f32_reinterpret_i32) v st = Ok (Core_result_Result_Ok tt, v'))
  /\
  (forall v st, exists v', inst.(code_OpVisitor_t_on_f64_reinterpret_i64) v st = Ok (Core_result_Result_Ok tt, v')).

Lemma frame_hook_accept : forall V (inst : code_OpVisitor_t V) v ctx tidx bb ee,
  hooks_accept inst ->
  exists v', inst.(code_OpVisitor_t_on_function_start) v ctx tidx bb ee
             = Ok (Core_result_Result_Ok tt, v').
Proof.
  intros V inst v ctx tidx bb ee H. unfold hooks_accept in H.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  eauto.
Qed.

Lemma label_hook_accept : forall V (inst : code_OpVisitor_t V) v st d,
  hooks_accept inst ->
  exists v', inst.(code_OpVisitor_t_on_br_table_label) v st d
             = Ok (Core_result_Result_Ok tt, v').
Proof.
  intros V inst v st d H. unfold hooks_accept in H.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  eauto.
Qed.

(** The fan-outs inherit acceptance the same way they inherit totality. *)
Lemma visit_numeric_accept : forall V (inst : code_OpVisitor_t V) v st opcode,
  hooks_accept inst ->
  exists v', code_visit_numeric inst v st opcode
             = Ok (Core_result_Result_Ok tt, v').
Proof.
  intros V inst v st opcode H. unfold hooks_accept in H.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  unfold code_visit_numeric.
  repeat match goal with |- context [ if ?c then _ else _ ] => destruct c end;
    eauto.
Qed.

Lemma visit_memory_accept : forall V (inst : code_OpVisitor_t V) v st opcode m,
  hooks_accept inst ->
  exists v', code_visit_memory inst v st opcode m
             = Ok (Core_result_Result_Ok tt, v').
Proof.
  intros V inst v st opcode m H. unfold hooks_accept in H.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  unfold code_visit_memory.
  repeat match goal with |- context [ if ?c then _ else _ ] => destruct c end;
    eauto.
Qed.

Lemma nop_hooks_accept : hooks_accept code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor.
Proof.
  unfold hooks_accept, code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor.
  repeat split; intros;
    cbn [code_OpVisitor_t_on_function_start code_OpVisitor_t_on_unreachable code_OpVisitor_t_on_nop code_OpVisitor_t_on_block code_OpVisitor_t_on_loop code_OpVisitor_t_on_if code_OpVisitor_t_on_else code_OpVisitor_t_on_end code_OpVisitor_t_on_br code_OpVisitor_t_on_br_if code_OpVisitor_t_on_br_table_label code_OpVisitor_t_on_br_table code_OpVisitor_t_on_return code_OpVisitor_t_on_call code_OpVisitor_t_on_call_indirect code_OpVisitor_t_on_drop code_OpVisitor_t_on_select code_OpVisitor_t_on_local_get code_OpVisitor_t_on_local_set code_OpVisitor_t_on_local_tee code_OpVisitor_t_on_global_get code_OpVisitor_t_on_global_set code_OpVisitor_t_on_memory_size code_OpVisitor_t_on_memory_grow code_OpVisitor_t_on_i32_const code_OpVisitor_t_on_i64_const code_OpVisitor_t_on_f32_const code_OpVisitor_t_on_f64_const code_OpVisitor_t_on_i32_load code_OpVisitor_t_on_i64_load code_OpVisitor_t_on_f32_load code_OpVisitor_t_on_f64_load code_OpVisitor_t_on_i32_load8_s code_OpVisitor_t_on_i32_load8_u code_OpVisitor_t_on_i32_load16_s code_OpVisitor_t_on_i32_load16_u code_OpVisitor_t_on_i64_load8_s code_OpVisitor_t_on_i64_load8_u code_OpVisitor_t_on_i64_load16_s code_OpVisitor_t_on_i64_load16_u code_OpVisitor_t_on_i64_load32_s code_OpVisitor_t_on_i64_load32_u code_OpVisitor_t_on_i32_store code_OpVisitor_t_on_i64_store code_OpVisitor_t_on_f32_store code_OpVisitor_t_on_f64_store code_OpVisitor_t_on_i32_store8 code_OpVisitor_t_on_i32_store16 code_OpVisitor_t_on_i64_store8 code_OpVisitor_t_on_i64_store16 code_OpVisitor_t_on_i64_store32 code_OpVisitor_t_on_i32_eqz code_OpVisitor_t_on_i32_eq code_OpVisitor_t_on_i32_ne code_OpVisitor_t_on_i32_lt_s code_OpVisitor_t_on_i32_lt_u code_OpVisitor_t_on_i32_gt_s code_OpVisitor_t_on_i32_gt_u code_OpVisitor_t_on_i32_le_s code_OpVisitor_t_on_i32_le_u code_OpVisitor_t_on_i32_ge_s code_OpVisitor_t_on_i32_ge_u code_OpVisitor_t_on_i64_eqz code_OpVisitor_t_on_i64_eq code_OpVisitor_t_on_i64_ne code_OpVisitor_t_on_i64_lt_s code_OpVisitor_t_on_i64_lt_u code_OpVisitor_t_on_i64_gt_s code_OpVisitor_t_on_i64_gt_u code_OpVisitor_t_on_i64_le_s code_OpVisitor_t_on_i64_le_u code_OpVisitor_t_on_i64_ge_s code_OpVisitor_t_on_i64_ge_u code_OpVisitor_t_on_f32_eq code_OpVisitor_t_on_f32_ne code_OpVisitor_t_on_f32_lt code_OpVisitor_t_on_f32_gt code_OpVisitor_t_on_f32_le code_OpVisitor_t_on_f32_ge code_OpVisitor_t_on_f64_eq code_OpVisitor_t_on_f64_ne code_OpVisitor_t_on_f64_lt code_OpVisitor_t_on_f64_gt code_OpVisitor_t_on_f64_le code_OpVisitor_t_on_f64_ge code_OpVisitor_t_on_i32_sub code_OpVisitor_t_on_i32_mul code_OpVisitor_t_on_i32_div_s code_OpVisitor_t_on_i32_div_u code_OpVisitor_t_on_i32_rem_s code_OpVisitor_t_on_i32_rem_u code_OpVisitor_t_on_i32_and code_OpVisitor_t_on_i32_or code_OpVisitor_t_on_i32_xor code_OpVisitor_t_on_i32_shl code_OpVisitor_t_on_i32_shr_s code_OpVisitor_t_on_i32_shr_u code_OpVisitor_t_on_i32_rotl code_OpVisitor_t_on_i32_rotr code_OpVisitor_t_on_i64_add code_OpVisitor_t_on_i64_sub code_OpVisitor_t_on_i64_mul code_OpVisitor_t_on_i64_div_s code_OpVisitor_t_on_i64_div_u code_OpVisitor_t_on_i64_rem_s code_OpVisitor_t_on_i64_rem_u code_OpVisitor_t_on_i64_and code_OpVisitor_t_on_i64_or code_OpVisitor_t_on_i64_xor code_OpVisitor_t_on_i64_shl code_OpVisitor_t_on_i64_shr_s code_OpVisitor_t_on_i64_shr_u code_OpVisitor_t_on_i64_rotl code_OpVisitor_t_on_i64_rotr code_OpVisitor_t_on_f32_add code_OpVisitor_t_on_f32_sub code_OpVisitor_t_on_f32_mul code_OpVisitor_t_on_f32_div code_OpVisitor_t_on_f32_min code_OpVisitor_t_on_f32_max code_OpVisitor_t_on_f32_copysign code_OpVisitor_t_on_f64_add code_OpVisitor_t_on_f64_sub code_OpVisitor_t_on_f64_mul code_OpVisitor_t_on_f64_div code_OpVisitor_t_on_f64_min code_OpVisitor_t_on_f64_max code_OpVisitor_t_on_f64_copysign code_OpVisitor_t_on_i32_clz code_OpVisitor_t_on_i32_ctz code_OpVisitor_t_on_i32_popcnt code_OpVisitor_t_on_i32_add code_OpVisitor_t_on_i64_clz code_OpVisitor_t_on_i64_ctz code_OpVisitor_t_on_i64_popcnt code_OpVisitor_t_on_f32_abs code_OpVisitor_t_on_f32_neg code_OpVisitor_t_on_f32_ceil code_OpVisitor_t_on_f32_floor code_OpVisitor_t_on_f32_trunc code_OpVisitor_t_on_f32_nearest code_OpVisitor_t_on_f32_sqrt code_OpVisitor_t_on_f64_abs code_OpVisitor_t_on_f64_neg code_OpVisitor_t_on_f64_ceil code_OpVisitor_t_on_f64_floor code_OpVisitor_t_on_f64_trunc code_OpVisitor_t_on_f64_nearest code_OpVisitor_t_on_f64_sqrt code_OpVisitor_t_on_i32_wrap_i64 code_OpVisitor_t_on_i32_trunc_f32_s code_OpVisitor_t_on_i32_trunc_f32_u code_OpVisitor_t_on_i32_trunc_f64_s code_OpVisitor_t_on_i32_trunc_f64_u code_OpVisitor_t_on_i64_extend_i32_s code_OpVisitor_t_on_i64_extend_i32_u code_OpVisitor_t_on_i64_trunc_f32_s code_OpVisitor_t_on_i64_trunc_f32_u code_OpVisitor_t_on_i64_trunc_f64_s code_OpVisitor_t_on_i64_trunc_f64_u code_OpVisitor_t_on_f32_convert_i32_s code_OpVisitor_t_on_f32_convert_i32_u code_OpVisitor_t_on_f32_convert_i64_s code_OpVisitor_t_on_f32_convert_i64_u code_OpVisitor_t_on_f32_demote_f64 code_OpVisitor_t_on_f64_convert_i32_s code_OpVisitor_t_on_f64_convert_i32_u code_OpVisitor_t_on_f64_convert_i64_s code_OpVisitor_t_on_f64_convert_i64_u code_OpVisitor_t_on_f64_promote_f32 code_OpVisitor_t_on_i32_reinterpret_f32 code_OpVisitor_t_on_i64_reinterpret_f64 code_OpVisitor_t_on_f32_reinterpret_i32 code_OpVisitor_t_on_f64_reinterpret_i64];
    unfold code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_function_start,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_unreachable,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_nop,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_block,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_loop,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_if,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_else,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_end,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_br,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_br_if,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_br_table_label,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_br_table,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_return,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_call,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_call_indirect,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_drop,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_select,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_local_get,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_local_set,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_local_tee,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_global_get,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_global_set,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_memory_size,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_memory_grow,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_const,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_const,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_const,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_const,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_load,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_load,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_load,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_load,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_load8_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_load8_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_load16_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_load16_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_load8_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_load8_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_load16_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_load16_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_load32_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_load32_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_store,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_store,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_store,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_store,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_store8,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_store16,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_store8,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_store16,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_store32,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_eqz,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_eq,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_ne,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_lt_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_lt_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_gt_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_gt_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_le_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_le_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_ge_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_ge_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_eqz,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_eq,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_ne,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_lt_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_lt_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_gt_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_gt_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_le_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_le_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_ge_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_ge_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_eq,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_ne,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_lt,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_gt,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_le,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_ge,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_eq,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_ne,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_lt,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_gt,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_le,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_ge,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_sub,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_mul,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_div_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_div_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_rem_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_rem_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_and,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_or,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_xor,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_shl,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_shr_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_shr_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_rotl,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_rotr,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_add,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_sub,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_mul,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_div_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_div_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_rem_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_rem_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_and,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_or,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_xor,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_shl,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_shr_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_shr_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_rotl,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_rotr,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_add,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_sub,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_mul,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_div,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_min,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_max,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_copysign,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_add,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_sub,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_mul,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_div,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_min,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_max,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_copysign,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_clz,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_ctz,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_popcnt,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_add,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_clz,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_ctz,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_popcnt,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_abs,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_neg,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_ceil,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_floor,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_trunc,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_nearest,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_sqrt,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_abs,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_neg,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_ceil,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_floor,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_trunc,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_nearest,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_sqrt,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_wrap_i64,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_trunc_f32_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_trunc_f32_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_trunc_f64_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_trunc_f64_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_extend_i32_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_extend_i32_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_trunc_f32_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_trunc_f32_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_trunc_f64_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_trunc_f64_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_convert_i32_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_convert_i32_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_convert_i64_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_convert_i64_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_demote_f64,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_convert_i32_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_convert_i32_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_convert_i64_s,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_convert_i64_u,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_promote_f32,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i32_reinterpret_f32,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_i64_reinterpret_f64,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f32_reinterpret_i32,
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor_on_f64_reinterpret_i64;
    eauto.
Qed.

(* ================================================================== *)
(** ** The shape of a dispatch branch                                  *)
(* ================================================================== *)

(** [step] calls a reader, hands the immediate it decoded to a hook, and lets
    either verdict out through [?]. Naming the two halves once turns each of the
    172 opcode branches into a line, and the three lemmas below are what the
    totality, the cursor and the soundness proofs each need of a branch. *)
Definition visit_hook {V}
  (h : result ((core_result_Result_t unit error_VisitError_t) * V))
  (st : code_OpIterState_t)
  : result ((core_result_Result_t unit error_OpError_t) * code_OpIterState_t
            * V) :=
  p <- h;
  let (r, v1) := p in
  r1 <- code_visit r;
  cf <- core_result_Result_Insts_CoreOpsTry_traitTryTResultInfallibleE_branch r1;
  match cf with
  | Core_ops_control_flow_ControlFlow_Continue _ =>
      Ok (Core_result_Result_Ok tt, st, v1)
  | Core_ops_control_flow_ControlFlow_Break residual =>
      r2 <-
        core_result_Result_Insts_CoreOpsTry_traitFromResidualResultInfallibleE_from_residual
          unit (core_convert_From_Blanket error_OpError_t) residual;
      Ok (r2, st, v1)
  end.

Definition visit_wrap {T V}
  (m : result (core_result_Result_t T error_OpError_t * code_OpIterState_t))
  (k : code_OpIterState_t -> T ->
       result ((core_result_Result_t unit error_VisitError_t) * V))
  (v : V)
  : result ((core_result_Result_t unit error_OpError_t) * code_OpIterState_t
            * V) :=
  p <- m;
  let (r, st1) := p in
  cf <- core_result_Result_Insts_CoreOpsTry_traitTryTResultInfallibleE_branch r;
  match cf with
  | Core_ops_control_flow_ControlFlow_Continue val => visit_hook (k st1 val) st1
  | Core_ops_control_flow_ControlFlow_Break residual =>
      r1 <-
        core_result_Result_Insts_CoreOpsTry_traitFromResidualResultInfallibleE_from_residual
          unit (core_convert_From_Blanket error_OpError_t) residual;
      Ok (r1, st1, v)
  end.

(** A hook that returns leaves the branch total, and the state it reports is
    the one the reader left: a hook cannot move the cursor or the stacks. *)
Lemma visit_hook_total : forall V
  (h : result ((core_result_Result_t unit error_VisitError_t) * V)) st,
  (exists r v', h = Ok (r, v')) ->
  exists r v', visit_hook h st = Ok (r, st, v').
Proof.
  intros V h st [r0 [v0 Hh]]. unfold visit_hook. rewrite Hh. cbn [bind].
  destruct r0 as [x|e]; cbn [code_visit bind].
  - rewrite branch_ok. cbn [bind]. eauto.
  - rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind]. eauto.
Qed.

Lemma visit_hook_state : forall V
  (h : result ((core_result_Result_t unit error_VisitError_t) * V)) st r st' v',
  visit_hook h st = Ok (r, st', v') -> st' = st.
Proof.
  intros V h st r st' v' H. unfold visit_hook in H.
  destruct h as [[r0 v0]|]; cbn [bind] in H; [|discriminate].
  destruct r0 as [x|e]; cbn [code_visit bind] in H.
  - rewrite branch_ok in H. cbn [bind] in H. inversion H. reflexivity.
  - rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
    cbn [bind] in H. inversion H. reflexivity.
Qed.

(** Reaching [Ok] means the hook accepted. *)
Lemma visit_hook_ok : forall V
  (h : result ((core_result_Result_t unit error_VisitError_t) * V)) st st' v',
  visit_hook h st = Ok (Core_result_Result_Ok tt, st', v') ->
  h = Ok (Core_result_Result_Ok tt, v').
Proof.
  intros V h st st' v' H. unfold visit_hook in H.
  destruct h as [[r0 v0]|] eqn:Hh; cbn [bind] in H; [|discriminate].
  destruct r0 as [x|e]; cbn [code_visit bind] in H.
  - rewrite branch_ok in H. cbn [bind] in H. inversion H. subst v0.
    destruct x. reflexivity.
  - rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
    cbn [bind] in H. discriminate.
Qed.

(** An accepting hook keeps the branch accepting. *)
Lemma visit_hook_accept : forall V
  (h : result ((core_result_Result_t unit error_VisitError_t) * V)) st,
  (exists v', h = Ok (Core_result_Result_Ok tt, v')) ->
  exists v', visit_hook h st = Ok (Core_result_Result_Ok tt, st, v').
Proof.
  intros V h st [v0 Hh]. unfold visit_hook. rewrite Hh.
  cbn [bind code_visit]. rewrite branch_ok. cbn [bind]. eauto.
Qed.

(** The three, lifted to a whole branch. *)
Lemma visit_wrap_total : forall T V
  (m : result (core_result_Result_t T error_OpError_t * code_OpIterState_t))
  k (v : V),
  (exists r0 st0, m = Ok (r0, st0)) ->
  (forall st0 x, exists r v', k st0 x = Ok (r, v')) ->
  exists r st' v', visit_wrap m k v = Ok (r, st', v').
Proof.
  intros T V m k v [r0 [st0 Hm]] Hk. unfold visit_wrap. rewrite Hm. cbn [bind].
  destruct r0 as [x|e].
  - rewrite branch_ok. cbn [bind].
    destruct (visit_hook_total V (k st0 x) st0 (Hk st0 x)) as [r [v' Hv]].
    exists r, st0, v'. exact Hv.
  - rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind]. eauto.
Qed.

Lemma visit_wrap_state : forall T V
  (m : result (core_result_Result_t T error_OpError_t * code_OpIterState_t))
  k (v : V) r st' v',
  visit_wrap m k v = Ok (r, st', v') -> exists r0, m = Ok (r0, st').
Proof.
  intros T V m k v r st' v' H. unfold visit_wrap in H.
  destruct m as [[r0 st0]|] eqn:Hm; cbn [bind] in H; [|discriminate].
  destruct r0 as [x|e].
  - rewrite branch_ok in H. cbn [bind] in H.
    rewrite (visit_hook_state V (k st0 x) st0 r st' v' H). eauto.
  - rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
    cbn [bind] in H. inversion H. subst st0. eauto.
Qed.

Lemma visit_wrap_ok : forall T V
  (m : result (core_result_Result_t T error_OpError_t * code_OpIterState_t))
  k (v : V) st' v',
  visit_wrap m k v = Ok (Core_result_Result_Ok tt, st', v') ->
  exists x, m = Ok (Core_result_Result_Ok x, st').
Proof.
  intros T V m k v st' v' H. unfold visit_wrap in H.
  destruct m as [[r0 st0]|] eqn:Hm; cbn [bind] in H; [|discriminate].
  destruct r0 as [x|e].
  - rewrite branch_ok in H. cbn [bind] in H.
    pose proof (visit_hook_state V (k st0 x) st0 _ st' v' H) as Hst.
    subst st0. exists x. reflexivity.
  - rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
    cbn [bind] in H. discriminate.
Qed.

Lemma visit_wrap_accept : forall T V
  (m : result (core_result_Result_t T error_OpError_t * code_OpIterState_t))
  k (v : V) x st0,
  m = Ok (Core_result_Result_Ok x, st0) ->
  (exists v', k st0 x = Ok (Core_result_Result_Ok tt, v')) ->
  exists v', visit_wrap m k v = Ok (Core_result_Result_Ok tt, st0, v').
Proof.
  intros T V m k v x st0 Hm Hk. unfold visit_wrap. rewrite Hm. cbn [bind].
  rewrite branch_ok. cbn [bind]. apply visit_hook_accept. exact Hk.
Qed.

(** Three readers hand back a pair, and [step] destructures it before calling
    the hook, so the pair pattern sits between the [?] and the hook where
    [visit_wrap] expects nothing. Same four facts, one shape further in. *)
Definition visit_wrap2 {T1 T2 V}
  (m : result (core_result_Result_t (T1 * T2) error_OpError_t
               * code_OpIterState_t))
  (k : code_OpIterState_t -> T1 -> T2 ->
       result ((core_result_Result_t unit error_VisitError_t) * V))
  (v : V)
  : result ((core_result_Result_t unit error_OpError_t) * code_OpIterState_t
            * V) :=
  p <- m;
  let (r, st1) := p in
  cf <- core_result_Result_Insts_CoreOpsTry_traitTryTResultInfallibleE_branch r;
  match cf with
  | Core_ops_control_flow_ControlFlow_Continue (x, y) =>
      visit_hook (k st1 x y) st1
  | Core_ops_control_flow_ControlFlow_Break residual =>
      r1 <-
        core_result_Result_Insts_CoreOpsTry_traitFromResidualResultInfallibleE_from_residual
          unit (core_convert_From_Blanket error_OpError_t) residual;
      Ok (r1, st1, v)
  end.

Lemma visit_wrap2_total : forall T1 T2 V
  (m : result (core_result_Result_t (T1 * T2) error_OpError_t
               * code_OpIterState_t))
  k (v : V),
  (exists r0 st0, m = Ok (r0, st0)) ->
  (forall st0 x y, exists r v', k st0 x y = Ok (r, v')) ->
  exists r st' v', visit_wrap2 m k v = Ok (r, st', v').
Proof.
  intros T1 T2 V m k v [r0 [st0 Hm]] Hk. unfold visit_wrap2. rewrite Hm.
  cbn [bind]. destruct r0 as [[x y]|e].
  - rewrite branch_ok. cbn [bind].
    destruct (visit_hook_total V (k st0 x y) st0 (Hk st0 x y)) as [r [v' Hv]].
    exists r, st0, v'. exact Hv.
  - rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind]. eauto.
Qed.

Lemma visit_wrap2_state : forall T1 T2 V
  (m : result (core_result_Result_t (T1 * T2) error_OpError_t
               * code_OpIterState_t))
  k (v : V) r st' v',
  visit_wrap2 m k v = Ok (r, st', v') -> exists r0, m = Ok (r0, st').
Proof.
  intros T1 T2 V m k v r st' v' H. unfold visit_wrap2 in H.
  destruct m as [[r0 st0]|] eqn:Hm; cbn [bind] in H; [|discriminate].
  destruct r0 as [[x y]|e].
  - rewrite branch_ok in H. cbn [bind] in H.
    rewrite (visit_hook_state V (k st0 x y) st0 r st' v' H). eauto.
  - rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
    cbn [bind] in H. inversion H. subst st0. eauto.
Qed.

Lemma visit_wrap2_ok : forall T1 T2 V
  (m : result (core_result_Result_t (T1 * T2) error_OpError_t
               * code_OpIterState_t))
  k (v : V) st' v',
  visit_wrap2 m k v = Ok (Core_result_Result_Ok tt, st', v') ->
  exists x y, m = Ok (Core_result_Result_Ok (x, y), st').
Proof.
  intros T1 T2 V m k v st' v' H. unfold visit_wrap2 in H.
  destruct m as [[r0 st0]|] eqn:Hm; cbn [bind] in H; [|discriminate].
  destruct r0 as [[x y]|e].
  - rewrite branch_ok in H. cbn [bind] in H.
    pose proof (visit_hook_state V (k st0 x y) st0 _ st' v' H) as Hst.
    subst st0. exists x, y. reflexivity.
  - rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
    cbn [bind] in H. discriminate.
Qed.

Lemma visit_wrap2_accept : forall T1 T2 V
  (m : result (core_result_Result_t (T1 * T2) error_OpError_t
               * code_OpIterState_t))
  k (v : V) x y st0,
  m = Ok (Core_result_Result_Ok (x, y), st0) ->
  (exists v', k st0 x y = Ok (Core_result_Result_Ok tt, v')) ->
  exists v', visit_wrap2 m k v = Ok (Core_result_Result_Ok tt, st0, v').
Proof.
  intros T1 T2 V m k v x y st0 Hm Hk. unfold visit_wrap2. rewrite Hm.
  cbn [bind]. rewrite branch_ok. cbn [bind]. apply visit_hook_accept. exact Hk.
Qed.

(** [br_table] is the one reader that carries the visitor itself, because its
    label loop hands each depth over as it reads it. So its branch starts from a
    reader that already returns a visitor state, and the hook is called with
    that one rather than with the incoming one. *)
Definition visit_wrapv {T1 T2 V}
  (m : result (core_result_Result_t (T1 * T2) error_OpError_t
               * code_OpIterState_t * V))
  (k : code_OpIterState_t -> V -> T1 -> T2 ->
       result ((core_result_Result_t unit error_VisitError_t) * V))
  : result ((core_result_Result_t unit error_OpError_t) * code_OpIterState_t
            * V) :=
  t <- m;
  let '(r, st1, v1) := t in
  cf <- core_result_Result_Insts_CoreOpsTry_traitTryTResultInfallibleE_branch r;
  match cf with
  | Core_ops_control_flow_ControlFlow_Continue (x, y) =>
      visit_hook (k st1 v1 x y) st1
  | Core_ops_control_flow_ControlFlow_Break residual =>
      r1 <-
        core_result_Result_Insts_CoreOpsTry_traitFromResidualResultInfallibleE_from_residual
          unit (core_convert_From_Blanket error_OpError_t) residual;
      Ok (r1, st1, v1)
  end.

Lemma visit_wrapv_total : forall T1 T2 V
  (m : result (core_result_Result_t (T1 * T2) error_OpError_t
               * code_OpIterState_t * V)) k,
  (exists r0 st0 v0, m = Ok (r0, st0, v0)) ->
  (forall st0 v0 x y, exists r v', k st0 v0 x y = Ok (r, v')) ->
  exists r st' v', visit_wrapv m k = Ok (r, st', v').
Proof.
  intros T1 T2 V m k [r0 [st0 [v0 Hm]]] Hk. unfold visit_wrapv. rewrite Hm.
  cbn [bind]. destruct r0 as [[x y]|e].
  - rewrite branch_ok. cbn [bind].
    destruct (visit_hook_total V (k st0 v0 x y) st0 (Hk st0 v0 x y))
      as [r [v' Hv]].
    exists r, st0, v'. exact Hv.
  - rewrite branch_err. cbn [bind]. rewrite from_residual_err. cbn [bind]. eauto.
Qed.

Lemma visit_wrapv_state : forall T1 T2 V
  (m : result (core_result_Result_t (T1 * T2) error_OpError_t
               * code_OpIterState_t * V)) k r st' v',
  visit_wrapv m k = Ok (r, st', v') -> exists r0 v0, m = Ok (r0, st', v0).
Proof.
  intros T1 T2 V m k r st' v' H. unfold visit_wrapv in H.
  destruct m as [[[r0 st0] v0]|] eqn:Hm; cbn [bind] in H; [|discriminate].
  destruct r0 as [[x y]|e].
  - rewrite branch_ok in H. cbn [bind] in H.
    rewrite (visit_hook_state V (k st0 v0 x y) st0 r st' v' H). eauto.
  - rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
    cbn [bind] in H. inversion H; subst. eauto.
Qed.

Lemma visit_wrapv_ok : forall T1 T2 V
  (m : result (core_result_Result_t (T1 * T2) error_OpError_t
               * code_OpIterState_t * V)) k st' v',
  visit_wrapv m k = Ok (Core_result_Result_Ok tt, st', v') ->
  exists x y v0, m = Ok (Core_result_Result_Ok (x, y), st', v0).
Proof.
  intros T1 T2 V m k st' v' H. unfold visit_wrapv in H.
  destruct m as [[[r0 st0] v0]|] eqn:Hm; cbn [bind] in H; [|discriminate].
  destruct r0 as [[x y]|e].
  - rewrite branch_ok in H. cbn [bind] in H.
    pose proof (visit_hook_state V (k st0 v0 x y) st0 _ st' v' H) as Hst.
    subst st0. exists x, y, v0. reflexivity.
  - rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
    cbn [bind] in H. discriminate.
Qed.

Lemma visit_wrapv_accept : forall T1 T2 V
  (m : result (core_result_Result_t (T1 * T2) error_OpError_t
               * code_OpIterState_t * V)) k x y st0 v0,
  m = Ok (Core_result_Result_Ok (x, y), st0, v0) ->
  (exists v', k st0 v0 x y = Ok (Core_result_Result_Ok tt, v')) ->
  exists v', visit_wrapv m k = Ok (Core_result_Result_Ok tt, st0, v').
Proof.
  intros T1 T2 V m k x y st0 v0 Hm Hk. unfold visit_wrapv. rewrite Hm.
  cbn [bind]. rewrite branch_ok. cbn [bind]. apply visit_hook_accept. exact Hk.
Qed.

(** The three [_ok] lemmas keep the reader's result and drop the hook's. The
    trace argument needs both: what the reader decoded, and that the hook it was
    handed to accepted it. *)
Lemma visit_wrap_hook : forall T V
  (m : result (core_result_Result_t T error_OpError_t * code_OpIterState_t))
  k (v : V) st' v',
  visit_wrap m k v = Ok (Core_result_Result_Ok tt, st', v') ->
  exists x, m = Ok (Core_result_Result_Ok x, st')
            /\ k st' x = Ok (Core_result_Result_Ok tt, v').
Proof.
  intros T V m k v st' v' H. unfold visit_wrap in H.
  destruct m as [[r0 st0]|] eqn:Hm; cbn [bind] in H; [|discriminate].
  destruct r0 as [x|e].
  - rewrite branch_ok in H. cbn [bind] in H.
    pose proof (visit_hook_state V (k st0 x) st0 _ st' v' H) as Hst.
    subst st0. exists x. split; [reflexivity|].
    apply (visit_hook_ok V (k st' x) st' st' v' H).
  - rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
    cbn [bind] in H. discriminate.
Qed.

Lemma visit_wrap2_hook : forall T1 T2 V
  (m : result (core_result_Result_t (T1 * T2) error_OpError_t
               * code_OpIterState_t))
  k (v : V) st' v',
  visit_wrap2 m k v = Ok (Core_result_Result_Ok tt, st', v') ->
  exists x y, m = Ok (Core_result_Result_Ok (x, y), st')
              /\ k st' x y = Ok (Core_result_Result_Ok tt, v').
Proof.
  intros T1 T2 V m k v st' v' H. unfold visit_wrap2 in H.
  destruct m as [[r0 st0]|] eqn:Hm; cbn [bind] in H; [|discriminate].
  destruct r0 as [[x y]|e].
  - rewrite branch_ok in H. cbn [bind] in H.
    pose proof (visit_hook_state V (k st0 x y) st0 _ st' v' H) as Hst.
    subst st0. exists x, y. split; [reflexivity|].
    apply (visit_hook_ok V (k st' x y) st' st' v' H).
  - rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
    cbn [bind] in H. discriminate.
Qed.

Lemma visit_wrapv_hook : forall T1 T2 V
  (m : result (core_result_Result_t (T1 * T2) error_OpError_t
               * code_OpIterState_t * V)) k st' v',
  visit_wrapv m k = Ok (Core_result_Result_Ok tt, st', v') ->
  exists x y v0, m = Ok (Core_result_Result_Ok (x, y), st', v0)
                 /\ k st' v0 x y = Ok (Core_result_Result_Ok tt, v').
Proof.
  intros T1 T2 V m k st' v' H. unfold visit_wrapv in H.
  destruct m as [[[r0 st0] v0]|] eqn:Hm; cbn [bind] in H; [|discriminate].
  destruct r0 as [[x y]|e].
  - rewrite branch_ok in H. cbn [bind] in H.
    pose proof (visit_hook_state V (k st0 v0 x y) st0 _ st' v' H) as Hst.
    subst st0. exists x, y, v0. split; [reflexivity|].
    apply (visit_hook_ok V (k st' v0 x y) st' st' v' H).
  - rewrite branch_err in H. cbn [bind] in H. rewrite from_residual_err in H.
    cbn [bind] in H. discriminate.
Qed.

(* The operator vocabulary, needed only from here down: requiring it earlier
   would put [Z_scope] over the product types the definitions above use. *)
Require Import Itasca.Translate.
Require Import Itasca.Spec_Binary.
From Wasm Require Import datatypes numerics.

(* ================================================================== *)
(** ** What the consumer was shown                                     *)
(* ================================================================== *)

(** A consumer that keeps a list of the operators it has been handed. [obs] is
    that list and [pend] is the [br_table] labels seen so far, which are not an
    operator of their own: they accumulate until the table closes.

    Stated over an arbitrary instance and an arbitrary pair of projections, so
    it is a property a real consumer can claim of its own state rather than
    something only the proof's recorder satisfies. The two fan-outs cover 146 of
    the hooks in one conjunct each, against the specification's table, which is
    what keeps this to thirty lines rather than a hundred and seventy. *)
Definition records {V : Type} (inst : code_OpVisitor_t V)
                   (obs : V -> list flat_op) (pend : V -> list Z) : Prop :=
  (* the numeric and memory fan-outs, by way of [op_spec] *)
  (forall v st b from to be v', code_convert_types b = Ok (Some (from, to)) ->
     op_spec (to_Z b) = Some (Sh_nullary be) ->
     code_visit_numeric inst v st b = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain be] /\ pend v' = pend v)
  /\
  (forall v st b ty res be v', code_binary_types b = Ok (Some (ty, res)) ->
     op_spec (to_Z b) = Some (Sh_nullary be) ->
     code_visit_numeric inst v st b = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain be] /\ pend v' = pend v)
  /\
  (forall v st b m nt tp v', op_spec (to_Z b) = Some (Sh_load nt tp) ->
     code_visit_memory inst v st b m = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain (BI_load nt tp
                          (Z.to_N (to_Z m.(code_MemArg_align)))
                          (Z.to_N (to_Z m.(code_MemArg_offset))))]
     /\ pend v' = pend v)
  /\
  (forall v st b m nt tp v', op_spec (to_Z b) = Some (Sh_store nt tp) ->
     code_visit_memory inst v st b m = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain (BI_store nt tp
                          (Z.to_N (to_Z m.(code_MemArg_align)))
                          (Z.to_N (to_Z m.(code_MemArg_offset))))]
     /\ pend v' = pend v)
  /\
  (* the frame hook is not an operator *)
  (forall v ctx tidx bb ee v',
     inst.(code_OpVisitor_t_on_function_start) v ctx tidx bb ee
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v /\ pend v' = pend v)
  /\
  (* a table's labels are not operators of their own; they wait for the close *)
  (forall v st d v',
     inst.(code_OpVisitor_t_on_br_table_label) v st d
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v /\ pend v' = pend v ++ [to_Z d])
  /\
  (forall v st d common v',
     inst.(code_OpVisitor_t_on_br_table) v st d common
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain (BI_br_table (List.map Z.to_N (pend v))
                                              (Z.to_N (to_Z d)))]
     /\ pend v' = [])
  /\
  (forall v st v',
     inst.(code_OpVisitor_t_on_unreachable) v st
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain BI_unreachable] /\ pend v' = pend v)
  /\
  (forall v st v',
     inst.(code_OpVisitor_t_on_nop) v st
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain BI_nop] /\ pend v' = pend v)
  /\
  (forall v st bt v',
     inst.(code_OpVisitor_t_on_block) v st bt
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_block (translate_bt bt)] /\ pend v' = pend v)
  /\
  (forall v st bt v',
     inst.(code_OpVisitor_t_on_loop) v st bt
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_loop (translate_bt bt)] /\ pend v' = pend v)
  /\
  (forall v st bt v',
     inst.(code_OpVisitor_t_on_if) v st bt
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_if (translate_bt bt)] /\ pend v' = pend v)
  /\
  (forall v st bt v',
     inst.(code_OpVisitor_t_on_else) v st bt
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_else] /\ pend v' = pend v)
  /\
  (forall v st kind bt v',
     inst.(code_OpVisitor_t_on_end) v st kind bt
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_end] /\ pend v' = pend v)
  /\
  (forall v st d bt v',
     inst.(code_OpVisitor_t_on_br) v st d bt
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain (BI_br (Z.to_N (to_Z d)))] /\ pend v' = pend v)
  /\
  (forall v st d bt v',
     inst.(code_OpVisitor_t_on_br_if) v st d bt
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain (BI_br_if (Z.to_N (to_Z d)))] /\ pend v' = pend v)
  /\
  (forall v st v',
     inst.(code_OpVisitor_t_on_return) v st
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain BI_return] /\ pend v' = pend v)
  /\
  (forall v st idx v',
     inst.(code_OpVisitor_t_on_call) v st idx
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain (BI_call (Z.to_N (to_Z idx)))] /\ pend v' = pend v)
  /\
  (forall v st idx v',
     inst.(code_OpVisitor_t_on_call_indirect) v st idx
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain (BI_call_indirect 0%N (Z.to_N (to_Z idx)))] /\ pend v' = pend v)
  /\
  (forall v st t v',
     inst.(code_OpVisitor_t_on_drop) v st t
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain BI_drop] /\ pend v' = pend v)
  /\
  (forall v st t v',
     inst.(code_OpVisitor_t_on_select) v st t
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain (BI_select None)] /\ pend v' = pend v)
  /\
  (forall v st idx v',
     inst.(code_OpVisitor_t_on_local_get) v st idx
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain (BI_local_get (Z.to_N (to_Z idx)))] /\ pend v' = pend v)
  /\
  (forall v st idx v',
     inst.(code_OpVisitor_t_on_local_set) v st idx
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain (BI_local_set (Z.to_N (to_Z idx)))] /\ pend v' = pend v)
  /\
  (forall v st idx v',
     inst.(code_OpVisitor_t_on_local_tee) v st idx
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain (BI_local_tee (Z.to_N (to_Z idx)))] /\ pend v' = pend v)
  /\
  (forall v st idx v',
     inst.(code_OpVisitor_t_on_global_get) v st idx
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain (BI_global_get (Z.to_N (to_Z idx)))] /\ pend v' = pend v)
  /\
  (forall v st idx v',
     inst.(code_OpVisitor_t_on_global_set) v st idx
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain (BI_global_set (Z.to_N (to_Z idx)))] /\ pend v' = pend v)
  /\
  (forall v st v',
     inst.(code_OpVisitor_t_on_memory_size) v st
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain BI_memory_size] /\ pend v' = pend v)
  /\
  (forall v st v',
     inst.(code_OpVisitor_t_on_memory_grow) v st
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain BI_memory_grow] /\ pend v' = pend v)
  /\
  (forall v st x v',
     inst.(code_OpVisitor_t_on_i32_const) v st x
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain (BI_const_num (VAL_int32 (Wasm_int.Int32.repr (to_Z x))))] /\ pend v' = pend v)
  /\
  (forall v st x v',
     inst.(code_OpVisitor_t_on_i64_const) v st x
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain (BI_const_num (VAL_int64 (Wasm_int.Int64.repr (to_Z x))))] /\ pend v' = pend v)
  /\
  (forall v st x v',
     inst.(code_OpVisitor_t_on_f32_const) v st x
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain (BI_const_num (fconst_val T_f32 (to_Z x)))] /\ pend v' = pend v)
  /\
  (forall v st x v',
     inst.(code_OpVisitor_t_on_f64_const) v st x
       = Ok (Core_result_Result_Ok tt, v') ->
     obs v' = obs v ++ [FO_plain (BI_const_num (fconst_val T_f64 (to_Z x)))] /\ pend v' = pend v).

(** "Between these two states the consumer was shown exactly [ops]" -- said
    once, for every recorder at once, so a theorem can carry it without asking
    its caller to be a recorder. The empty pending list on either side is part
    of it: a [br_table]'s labels are only half an operator until it closes. *)
Definition traced {V : Type} (inst : code_OpVisitor_t V) (v v' : V)
                  (ops : list flat_op) : Prop :=
  forall obs pend, records inst obs pend -> pend v = [] ->
    obs v' = obs v ++ ops /\ pend v' = [].

Lemma traced_nil : forall V (inst : code_OpVisitor_t V) v,
  traced inst v v [].
Proof.
  intros V inst v obs pend Hrec Hpd.
  rewrite List.app_nil_r. split; [reflexivity | exact Hpd].
Qed.

(** The frame hook, which [validate_code_entry_with] fires before the body:
    it is not an operator, so it leaves the trace where it was. *)
Lemma traced_frame : forall V (inst : code_OpVisitor_t V) v v' ctx tidx bb ee,
  inst.(code_OpVisitor_t_on_function_start) v ctx tidx bb ee
    = Ok (Core_result_Result_Ok tt, v') ->
  traced inst v v' [].
Proof.
  intros V inst v v' ctx tidx bb ee Hhk obs pend Hrec Hpd.
  destruct Hrec as [_ [_ [_ [_ [Hfs _]]]]].
  destruct (Hfs v ctx tidx bb ee v' Hhk) as [Hobs Hpend].
  rewrite List.app_nil_r. split; [exact Hobs | rewrite Hpend; exact Hpd].
Qed.

(** A [br_table]'s labels, mid-operator: they land on the pending list, in
    order, and nothing is observed until the operator closes. *)
Definition traced_labels {V : Type} (inst : code_OpVisitor_t V) (v v' : V)
                         (ls : list Z) : Prop :=
  forall obs pend, records inst obs pend ->
    obs v' = obs v /\ pend v' = pend v ++ ls.

Lemma traced_labels_nil : forall V (inst : code_OpVisitor_t V) v,
  traced_labels inst v v [].
Proof.
  intros V inst v obs pend Hrec.
  split; [reflexivity | rewrite List.app_nil_r; reflexivity].
Qed.

Lemma traced_labels_step : forall V (inst : code_OpVisitor_t V) v v1 v' st d ls,
  inst.(code_OpVisitor_t_on_br_table_label) v st d
    = Ok (Core_result_Result_Ok tt, v1) ->
  traced_labels inst v1 v' ls ->
  traced_labels inst v v' (to_Z d :: ls).
Proof.
  intros V inst v v1 v' st d ls Hhk Hrest obs pend Hrec.
  destruct (Hrest obs pend Hrec) as [Hobs Hpend].
  destruct Hrec as [_ [_ [_ [_ [_ [Hlab _]]]]]].
  destruct (Hlab v st d v1 Hhk) as [Hobs1 Hpend1].
  split; [rewrite Hobs; exact Hobs1|].
  rewrite Hpend. rewrite Hpend1. rewrite <- List.app_assoc. reflexivity.
Qed.

(** Two stretches in a row are one stretch. This is what turns the per-operator
    fact into the whole run's. *)
Lemma traced_trans : forall V (inst : code_OpVisitor_t V) v1 v2 v3 o1 o2,
  traced inst v1 v2 o1 -> traced inst v2 v3 o2 ->
  traced inst v1 v3 (o1 ++ o2).
Proof.
  intros V inst v1 v2 v3 o1 o2 H1 H2 obs pend Hrec Hpd.
  destruct (H1 obs pend Hrec Hpd) as [Ho1 Hp1].
  destruct (H2 obs pend Hrec Hp1) as [Ho2 Hp2].
  split; [|exact Hp2].
  rewrite Ho2. rewrite Ho1. rewrite List.app_assoc. reflexivity.
Qed.
