import Itasca.Results.Definitions.Visitor

/-!
# Callback contract projections

Public contracts quantify over events once. These derived projections specialize
that quantifier to individual hooks for extracted-function proofs. They introduce
no second contract or assumptions: each proof is one application of the public
contract to the corresponding event.
-/

open Aeneas Aeneas.Std
namespace Itasca.Visitor

theorem Total.on_function_start {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (context : code.Context) (typeIndex : U32)
      (bodyStart : Usize) (bodyEnd : Usize),
      ∃ reply nextVisitorState,
        visitor.on_function_start visitorState context typeIndex bodyStart bodyEnd = .ok
          (reply, nextVisitorState) := by
  intro v ctx typeidx bodybegin bodyend
  exact h v (.functionStart ctx typeidx bodybegin bodyend)

theorem Total.on_unreachable {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_unreachable visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.unreachable))

theorem Total.on_nop {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState, visitor.on_nop visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.nop))

theorem Total.on_block {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (blockType : signature.BlockType),
      ∃ reply nextVisitorState,
        visitor.on_block visitorState state blockType = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.block a0))

theorem Total.on_loop {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (blockType : signature.BlockType),
      ∃ reply nextVisitorState,
        visitor.on_loop visitorState state blockType = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.loop a0))

theorem Total.on_if {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (blockType : signature.BlockType),
      ∃ reply nextVisitorState,
        visitor.on_if visitorState state blockType = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.if_ a0))

theorem Total.on_else {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (blockType : signature.BlockType),
      ∃ reply nextVisitorState,
        visitor.on_else visitorState state blockType = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.else_ a0))

theorem Total.on_end {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (kind : code.LabelKind)
      (blockType : signature.BlockType),
      ∃ reply nextVisitorState,
        visitor.on_end visitorState state kind blockType = .ok (reply, nextVisitorState) := by
  intro v st a0 a1
  exact h v (.op st (.end_ a0 a1))

theorem Total.on_br {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (depth : U32)
      (resultTypes : signature.ResultType),
      ∃ reply nextVisitorState,
        visitor.on_br visitorState state depth resultTypes = .ok (reply, nextVisitorState) := by
  intro v st a0 a1
  exact h v (.op st (.br a0 a1))

theorem Total.on_br_if {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (depth : U32)
      (resultTypes : signature.ResultType),
      ∃ reply nextVisitorState,
        visitor.on_br_if visitorState state depth resultTypes = .ok (reply, nextVisitorState) := by
  intro v st a0 a1
  exact h v (.op st (.br_if a0 a1))

theorem Total.on_br_table_label {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (depth : U32),
      ∃ reply nextVisitorState,
        visitor.on_br_table_label visitorState state depth = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.br_table_label a0))

theorem Total.on_br_table {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (fallback : U32)
      (resultTypes : signature.ResultType),
      ∃ reply nextVisitorState,
        visitor.on_br_table visitorState state fallback resultTypes = .ok (reply, nextVisitorState) := by
  intro v st a0 a1
  exact h v (.op st (.br_table a0 a1))

theorem Total.on_return {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState, visitor.on_return visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.return_))

theorem Total.on_call {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (index : U32),
      ∃ reply nextVisitorState,
        visitor.on_call visitorState state index = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.call a0))

theorem Total.on_call_indirect {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (typeIndex : U32)
      (tableIndex : U32),
      ∃ reply nextVisitorState,
        visitor.on_call_indirect visitorState state typeIndex tableIndex = .ok
          (reply, nextVisitorState) := by
  intro v st a0 a1
  exact h v (.op st (.call_indirect a0 a1))

theorem Total.on_drop {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (valueType : code.StackType),
      ∃ reply nextVisitorState,
        visitor.on_drop visitorState state valueType = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.drop a0))

theorem Total.on_select {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (valueType : code.StackType),
      ∃ reply nextVisitorState,
        visitor.on_select visitorState state valueType = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.select a0))

theorem Total.on_local_get {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (index : U32),
      ∃ reply nextVisitorState,
        visitor.on_local_get visitorState state index = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.local_get a0))

theorem Total.on_local_set {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (index : U32),
      ∃ reply nextVisitorState,
        visitor.on_local_set visitorState state index = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.local_set a0))

theorem Total.on_local_tee {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (index : U32),
      ∃ reply nextVisitorState,
        visitor.on_local_tee visitorState state index = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.local_tee a0))

theorem Total.on_global_get {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (index : U32),
      ∃ reply nextVisitorState,
        visitor.on_global_get visitorState state index = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.global_get a0))

theorem Total.on_global_set {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (index : U32),
      ∃ reply nextVisitorState,
        visitor.on_global_set visitorState state index = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.global_set a0))

theorem Total.on_memory_size {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_memory_size visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.memory_size))

theorem Total.on_memory_grow {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_memory_grow visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.memory_grow))

theorem Total.on_i32_const {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (value : I32),
      ∃ reply nextVisitorState,
        visitor.on_i32_const visitorState state value = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.i32_const a0))

theorem Total.on_i64_const {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (value : I64),
      ∃ reply nextVisitorState,
        visitor.on_i64_const visitorState state value = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.i64_const a0))

theorem Total.on_f32_const {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (bits : U32),
      ∃ reply nextVisitorState,
        visitor.on_f32_const visitorState state bits = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.f32_const a0))

theorem Total.on_f64_const {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (bits : U64),
      ∃ reply nextVisitorState,
        visitor.on_f64_const visitorState state bits = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.f64_const a0))

theorem Total.on_i32_load {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_i32_load visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i32_load arg))

theorem Total.on_i64_load {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_i64_load visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i64_load arg))

theorem Total.on_f32_load {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_f32_load visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .f32_load arg))

theorem Total.on_f64_load {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_f64_load visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .f64_load arg))

theorem Total.on_i32_load8_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_i32_load8_s visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i32_load8_s arg))

theorem Total.on_i32_load8_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_i32_load8_u visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i32_load8_u arg))

theorem Total.on_i32_load16_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_i32_load16_s visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i32_load16_s arg))

theorem Total.on_i32_load16_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_i32_load16_u visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i32_load16_u arg))

theorem Total.on_i64_load8_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_i64_load8_s visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i64_load8_s arg))

theorem Total.on_i64_load8_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_i64_load8_u visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i64_load8_u arg))

theorem Total.on_i64_load16_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_i64_load16_s visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i64_load16_s arg))

theorem Total.on_i64_load16_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_i64_load16_u visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i64_load16_u arg))

theorem Total.on_i64_load32_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_i64_load32_s visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i64_load32_s arg))

theorem Total.on_i64_load32_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_i64_load32_u visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i64_load32_u arg))

theorem Total.on_i32_store {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_i32_store visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i32_store arg))

theorem Total.on_i64_store {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_i64_store visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i64_store arg))

theorem Total.on_f32_store {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_f32_store visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .f32_store arg))

theorem Total.on_f64_store {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_f64_store visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .f64_store arg))

theorem Total.on_i32_store8 {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_i32_store8 visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i32_store8 arg))

theorem Total.on_i32_store16 {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_i32_store16 visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i32_store16 arg))

theorem Total.on_i64_store8 {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_i64_store8 visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i64_store8 arg))

theorem Total.on_i64_store16 {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_i64_store16 visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i64_store16 arg))

theorem Total.on_i64_store32 {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_i64_store32 visitorState state argument = .ok (reply, nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i64_store32 arg))

theorem Total.on_i32_eqz {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_eqz visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_eqz))

theorem Total.on_i32_eq {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState, visitor.on_i32_eq visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_eq))

theorem Total.on_i32_ne {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState, visitor.on_i32_ne visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_ne))

theorem Total.on_i32_lt_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_lt_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_lt_s))

theorem Total.on_i32_lt_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_lt_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_lt_u))

theorem Total.on_i32_gt_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_gt_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_gt_s))

theorem Total.on_i32_gt_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_gt_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_gt_u))

theorem Total.on_i32_le_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_le_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_le_s))

theorem Total.on_i32_le_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_le_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_le_u))

theorem Total.on_i32_ge_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_ge_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_ge_s))

theorem Total.on_i32_ge_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_ge_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_ge_u))

theorem Total.on_i64_eqz {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_eqz visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_eqz))

theorem Total.on_i64_eq {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState, visitor.on_i64_eq visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_eq))

theorem Total.on_i64_ne {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState, visitor.on_i64_ne visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_ne))

theorem Total.on_i64_lt_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_lt_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_lt_s))

theorem Total.on_i64_lt_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_lt_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_lt_u))

theorem Total.on_i64_gt_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_gt_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_gt_s))

theorem Total.on_i64_gt_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_gt_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_gt_u))

theorem Total.on_i64_le_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_le_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_le_s))

theorem Total.on_i64_le_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_le_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_le_u))

theorem Total.on_i64_ge_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_ge_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_ge_s))

theorem Total.on_i64_ge_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_ge_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_ge_u))

theorem Total.on_f32_eq {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState, visitor.on_f32_eq visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_eq))

theorem Total.on_f32_ne {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState, visitor.on_f32_ne visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_ne))

theorem Total.on_f32_lt {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState, visitor.on_f32_lt visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_lt))

theorem Total.on_f32_gt {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState, visitor.on_f32_gt visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_gt))

theorem Total.on_f32_le {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState, visitor.on_f32_le visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_le))

theorem Total.on_f32_ge {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState, visitor.on_f32_ge visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_ge))

theorem Total.on_f64_eq {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState, visitor.on_f64_eq visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_eq))

theorem Total.on_f64_ne {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState, visitor.on_f64_ne visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_ne))

theorem Total.on_f64_lt {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState, visitor.on_f64_lt visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_lt))

theorem Total.on_f64_gt {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState, visitor.on_f64_gt visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_gt))

theorem Total.on_f64_le {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState, visitor.on_f64_le visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_le))

theorem Total.on_f64_ge {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState, visitor.on_f64_ge visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_ge))

theorem Total.on_i32_sub {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_sub visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_sub))

theorem Total.on_i32_mul {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_mul visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_mul))

theorem Total.on_i32_div_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_div_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_div_s))

theorem Total.on_i32_div_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_div_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_div_u))

theorem Total.on_i32_rem_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_rem_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_rem_s))

theorem Total.on_i32_rem_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_rem_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_rem_u))

theorem Total.on_i32_and {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_and visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_and))

theorem Total.on_i32_or {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState, visitor.on_i32_or visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_or))

theorem Total.on_i32_xor {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_xor visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_xor))

theorem Total.on_i32_shl {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_shl visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_shl))

theorem Total.on_i32_shr_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_shr_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_shr_s))

theorem Total.on_i32_shr_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_shr_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_shr_u))

theorem Total.on_i32_rotl {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_rotl visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_rotl))

theorem Total.on_i32_rotr {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_rotr visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_rotr))

theorem Total.on_i64_add {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_add visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_add))

theorem Total.on_i64_sub {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_sub visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_sub))

theorem Total.on_i64_mul {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_mul visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_mul))

theorem Total.on_i64_div_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_div_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_div_s))

theorem Total.on_i64_div_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_div_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_div_u))

theorem Total.on_i64_rem_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_rem_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_rem_s))

theorem Total.on_i64_rem_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_rem_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_rem_u))

theorem Total.on_i64_and {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_and visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_and))

theorem Total.on_i64_or {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState, visitor.on_i64_or visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_or))

theorem Total.on_i64_xor {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_xor visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_xor))

theorem Total.on_i64_shl {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_shl visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_shl))

theorem Total.on_i64_shr_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_shr_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_shr_s))

theorem Total.on_i64_shr_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_shr_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_shr_u))

theorem Total.on_i64_rotl {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_rotl visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_rotl))

theorem Total.on_i64_rotr {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_rotr visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_rotr))

theorem Total.on_f32_add {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f32_add visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_add))

theorem Total.on_f32_sub {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f32_sub visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_sub))

theorem Total.on_f32_mul {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f32_mul visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_mul))

theorem Total.on_f32_div {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f32_div visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_div))

theorem Total.on_f32_min {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f32_min visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_min))

theorem Total.on_f32_max {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f32_max visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_max))

theorem Total.on_f32_copysign {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f32_copysign visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_copysign))

theorem Total.on_f64_add {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f64_add visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_add))

theorem Total.on_f64_sub {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f64_sub visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_sub))

theorem Total.on_f64_mul {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f64_mul visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_mul))

theorem Total.on_f64_div {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f64_div visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_div))

theorem Total.on_f64_min {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f64_min visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_min))

theorem Total.on_f64_max {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f64_max visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_max))

theorem Total.on_f64_copysign {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f64_copysign visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_copysign))

theorem Total.on_i32_clz {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_clz visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_clz))

theorem Total.on_i32_ctz {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_ctz visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_ctz))

theorem Total.on_i32_popcnt {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_popcnt visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_popcnt))

theorem Total.on_i32_add {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_add visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_add))

theorem Total.on_i64_clz {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_clz visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_clz))

theorem Total.on_i64_ctz {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_ctz visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_ctz))

theorem Total.on_i64_popcnt {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_popcnt visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_popcnt))

theorem Total.on_f32_abs {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f32_abs visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_abs))

theorem Total.on_f32_neg {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f32_neg visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_neg))

theorem Total.on_f32_ceil {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f32_ceil visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_ceil))

theorem Total.on_f32_floor {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f32_floor visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_floor))

theorem Total.on_f32_trunc {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f32_trunc visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_trunc))

theorem Total.on_f32_nearest {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f32_nearest visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_nearest))

theorem Total.on_f32_sqrt {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f32_sqrt visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_sqrt))

theorem Total.on_f64_abs {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f64_abs visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_abs))

theorem Total.on_f64_neg {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f64_neg visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_neg))

theorem Total.on_f64_ceil {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f64_ceil visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_ceil))

theorem Total.on_f64_floor {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f64_floor visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_floor))

theorem Total.on_f64_trunc {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f64_trunc visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_trunc))

theorem Total.on_f64_nearest {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f64_nearest visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_nearest))

theorem Total.on_f64_sqrt {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f64_sqrt visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_sqrt))

theorem Total.on_i32_wrap_i64 {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_wrap_i64 visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_wrap_i64))

theorem Total.on_i32_trunc_f32_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_trunc_f32_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_trunc_f32_s))

theorem Total.on_i32_trunc_f32_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_trunc_f32_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_trunc_f32_u))

theorem Total.on_i32_trunc_f64_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_trunc_f64_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_trunc_f64_s))

theorem Total.on_i32_trunc_f64_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_trunc_f64_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_trunc_f64_u))

theorem Total.on_i64_extend_i32_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_extend_i32_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_extend_i32_s))

theorem Total.on_i64_extend_i32_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_extend_i32_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_extend_i32_u))

theorem Total.on_i64_trunc_f32_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_trunc_f32_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_trunc_f32_s))

theorem Total.on_i64_trunc_f32_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_trunc_f32_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_trunc_f32_u))

theorem Total.on_i64_trunc_f64_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_trunc_f64_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_trunc_f64_s))

theorem Total.on_i64_trunc_f64_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_trunc_f64_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_trunc_f64_u))

theorem Total.on_f32_convert_i32_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f32_convert_i32_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_convert_i32_s))

theorem Total.on_f32_convert_i32_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f32_convert_i32_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_convert_i32_u))

theorem Total.on_f32_convert_i64_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f32_convert_i64_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_convert_i64_s))

theorem Total.on_f32_convert_i64_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f32_convert_i64_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_convert_i64_u))

theorem Total.on_f32_demote_f64 {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f32_demote_f64 visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_demote_f64))

theorem Total.on_f64_convert_i32_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f64_convert_i32_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_convert_i32_s))

theorem Total.on_f64_convert_i32_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f64_convert_i32_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_convert_i32_u))

theorem Total.on_f64_convert_i64_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f64_convert_i64_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_convert_i64_s))

theorem Total.on_f64_convert_i64_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f64_convert_i64_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_convert_i64_u))

theorem Total.on_f64_promote_f32 {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f64_promote_f32 visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_promote_f32))

theorem Total.on_i32_reinterpret_f32 {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_reinterpret_f32 visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_reinterpret_f32))

theorem Total.on_i64_reinterpret_f64 {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_reinterpret_f64 visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_reinterpret_f64))

theorem Total.on_f32_reinterpret_i32 {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f32_reinterpret_i32 visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_reinterpret_i32))

theorem Total.on_f64_reinterpret_i64 {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_f64_reinterpret_i64 visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_reinterpret_i64))

theorem Total.on_i32_extend8_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_extend8_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i32_extend8_s))

theorem Total.on_i32_extend16_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_extend16_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i32_extend16_s))

theorem Total.on_i64_extend8_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_extend8_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i64_extend8_s))

theorem Total.on_i64_extend16_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_extend16_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i64_extend16_s))

theorem Total.on_i64_extend32_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_extend32_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i64_extend32_s))

theorem Total.on_i32_trunc_sat_f32_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_trunc_sat_f32_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i32_trunc_sat_f32_s))

theorem Total.on_i32_trunc_sat_f32_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_trunc_sat_f32_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i32_trunc_sat_f32_u))

theorem Total.on_i32_trunc_sat_f64_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_trunc_sat_f64_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i32_trunc_sat_f64_s))

theorem Total.on_i32_trunc_sat_f64_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i32_trunc_sat_f64_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i32_trunc_sat_f64_u))

theorem Total.on_i64_trunc_sat_f32_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_trunc_sat_f32_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i64_trunc_sat_f32_s))

theorem Total.on_i64_trunc_sat_f32_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_trunc_sat_f32_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i64_trunc_sat_f32_u))

theorem Total.on_i64_trunc_sat_f64_s {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_trunc_sat_f64_s visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i64_trunc_sat_f64_s))

theorem Total.on_i64_trunc_sat_f64_u {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_i64_trunc_sat_f64_u visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i64_trunc_sat_f64_u))

theorem Total.on_ref_null {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (valueType : wasm_types.ElemType),
      ∃ reply nextVisitorState,
        visitor.on_ref_null visitorState state valueType = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.ref_null a0))

theorem Total.on_ref_is_null {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_ref_is_null visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.ref_is_null))

theorem Total.on_ref_func {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (index : U32),
      ∃ reply nextVisitorState,
        visitor.on_ref_func visitorState state index = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.ref_func a0))

theorem Total.on_select_typed {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState)
      (valueType : wasm_types.ValueType),
      ∃ reply nextVisitorState,
        visitor.on_select_typed visitorState state valueType = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.select_typed a0))

theorem Total.on_table_get {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (index : U32),
      ∃ reply nextVisitorState,
        visitor.on_table_get visitorState state index = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.table_get a0))

theorem Total.on_table_set {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (index : U32),
      ∃ reply nextVisitorState,
        visitor.on_table_set visitorState state index = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.table_set a0))

theorem Total.on_memory_init {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (dataIndex : U32),
      ∃ reply nextVisitorState,
        visitor.on_memory_init visitorState state dataIndex = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.memory_init a0))

theorem Total.on_data_drop {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (dataIndex : U32),
      ∃ reply nextVisitorState,
        visitor.on_data_drop visitorState state dataIndex = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.data_drop a0))

theorem Total.on_memory_copy {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_memory_copy visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.memory_copy))

theorem Total.on_memory_fill {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ reply nextVisitorState,
        visitor.on_memory_fill visitorState state = .ok (reply, nextVisitorState) := by
  intro v st
  exact h v (.op st (.memory_fill))

theorem Total.on_table_init {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (elementIndex : U32)
      (tableIndex : U32),
      ∃ reply nextVisitorState,
        visitor.on_table_init visitorState state elementIndex tableIndex = .ok
          (reply, nextVisitorState) := by
  intro v st a0 a1
  exact h v (.op st (.table_init a0 a1))

theorem Total.on_elem_drop {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (elementIndex : U32),
      ∃ reply nextVisitorState,
        visitor.on_elem_drop visitorState state elementIndex = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.elem_drop a0))

theorem Total.on_table_copy {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (destinationTable : U32)
      (sourceTable : U32),
      ∃ reply nextVisitorState,
        visitor.on_table_copy visitorState state destinationTable sourceTable = .ok
          (reply, nextVisitorState) := by
  intro v st a0 a1
  exact h v (.op st (.table_copy a0 a1))

theorem Total.on_table_grow {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (tableIndex : U32),
      ∃ reply nextVisitorState,
        visitor.on_table_grow visitorState state tableIndex = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.table_grow a0))

theorem Total.on_table_size {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (tableIndex : U32),
      ∃ reply nextVisitorState,
        visitor.on_table_size visitorState state tableIndex = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.table_size a0))

theorem Total.on_table_fill {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (tableIndex : U32),
      ∃ reply nextVisitorState,
        visitor.on_table_fill visitorState state tableIndex = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.table_fill a0))

theorem Total.on_simd {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (subopcode : U32),
      ∃ reply nextVisitorState,
        visitor.on_simd visitorState state subopcode = .ok (reply, nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.simd a0))

theorem Total.on_simd_lane {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (subopcode : U32) (lane : U8),
      ∃ reply nextVisitorState,
        visitor.on_simd_lane visitorState state subopcode lane = .ok (reply, nextVisitorState) := by
  intro v st a0 a1
  exact h v (.op st (.simd_lane a0 a1))

theorem Total.on_simd_memory {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (subopcode : U32)
      (argument : code.MemArg),
      ∃ reply nextVisitorState,
        visitor.on_simd_memory visitorState state subopcode argument = .ok (reply, nextVisitorState) := by
  intro v st a0 a1
  exact h v (.op st (.simd_memory a0 a1))

theorem Total.on_simd_memory_lane {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (subopcode : U32)
      (argument : code.MemArg) (lane : U8),
      ∃ reply nextVisitorState,
        visitor.on_simd_memory_lane visitorState state subopcode argument lane = .ok
          (reply, nextVisitorState) := by
  intro v st a0 a1 a2
  exact h v (.op st (.simd_memory_lane a0 a1 a2))

theorem Total.on_simd_const {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (lowBits : U64) (highBits : U64),
      ∃ reply nextVisitorState,
        visitor.on_simd_const visitorState state lowBits highBits = .ok (reply, nextVisitorState) := by
  intro v st a0 a1
  exact h v (.op st (.simd_const a0 a1))

theorem Total.on_simd_shuffle {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (lowBits : U64) (highBits : U64),
      ∃ reply nextVisitorState,
        visitor.on_simd_shuffle visitorState state lowBits highBits = .ok (reply, nextVisitorState) := by
  intro v st a0 a1
  exact h v (.op st (.simd_shuffle a0 a1))

theorem Accepts.on_function_start {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (context : code.Context) (typeIndex : U32)
      (bodyStart : Usize) (bodyEnd : Usize),
      ∃ nextVisitorState,
        visitor.on_function_start visitorState context typeIndex bodyStart bodyEnd = .ok (.Ok () ,
          nextVisitorState) := by
  intro v ctx typeidx bodybegin bodyend
  exact h v (.functionStart ctx typeidx bodybegin bodyend)

theorem Accepts.on_unreachable {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_unreachable visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.unreachable))

theorem Accepts.on_nop {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_nop visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.nop))

theorem Accepts.on_block {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (blockType : signature.BlockType),
      ∃ nextVisitorState,
        visitor.on_block visitorState state blockType = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.block a0))

theorem Accepts.on_loop {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (blockType : signature.BlockType),
      ∃ nextVisitorState,
        visitor.on_loop visitorState state blockType = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.loop a0))

theorem Accepts.on_if {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (blockType : signature.BlockType),
      ∃ nextVisitorState,
        visitor.on_if visitorState state blockType = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.if_ a0))

theorem Accepts.on_else {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (blockType : signature.BlockType),
      ∃ nextVisitorState,
        visitor.on_else visitorState state blockType = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.else_ a0))

theorem Accepts.on_end {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (kind : code.LabelKind)
      (blockType : signature.BlockType),
      ∃ nextVisitorState,
        visitor.on_end visitorState state kind blockType = .ok (.Ok () , nextVisitorState) := by
  intro v st a0 a1
  exact h v (.op st (.end_ a0 a1))

theorem Accepts.on_br {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (depth : U32)
      (resultTypes : signature.ResultType),
      ∃ nextVisitorState,
        visitor.on_br visitorState state depth resultTypes = .ok (.Ok () , nextVisitorState) := by
  intro v st a0 a1
  exact h v (.op st (.br a0 a1))

theorem Accepts.on_br_if {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (depth : U32)
      (resultTypes : signature.ResultType),
      ∃ nextVisitorState,
        visitor.on_br_if visitorState state depth resultTypes = .ok (.Ok () , nextVisitorState) := by
  intro v st a0 a1
  exact h v (.op st (.br_if a0 a1))

theorem Accepts.on_br_table_label {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (depth : U32),
      ∃ nextVisitorState,
        visitor.on_br_table_label visitorState state depth = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.br_table_label a0))

theorem Accepts.on_br_table {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (fallback : U32)
      (resultTypes : signature.ResultType),
      ∃ nextVisitorState,
        visitor.on_br_table visitorState state fallback resultTypes = .ok (.Ok () ,
          nextVisitorState) := by
  intro v st a0 a1
  exact h v (.op st (.br_table a0 a1))

theorem Accepts.on_return {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_return visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.return_))

theorem Accepts.on_call {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (index : U32),
      ∃ nextVisitorState, visitor.on_call visitorState state index = .ok (.Ok (), nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.call a0))

theorem Accepts.on_call_indirect {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (typeIndex : U32)
      (tableIndex : U32),
      ∃ nextVisitorState,
        visitor.on_call_indirect visitorState state typeIndex tableIndex = .ok (.Ok () ,
          nextVisitorState) := by
  intro v st a0 a1
  exact h v (.op st (.call_indirect a0 a1))

theorem Accepts.on_drop {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (valueType : code.StackType),
      ∃ nextVisitorState,
        visitor.on_drop visitorState state valueType = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.drop a0))

theorem Accepts.on_select {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (valueType : code.StackType),
      ∃ nextVisitorState,
        visitor.on_select visitorState state valueType = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.select a0))

theorem Accepts.on_local_get {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (index : U32),
      ∃ nextVisitorState,
        visitor.on_local_get visitorState state index = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.local_get a0))

theorem Accepts.on_local_set {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (index : U32),
      ∃ nextVisitorState,
        visitor.on_local_set visitorState state index = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.local_set a0))

theorem Accepts.on_local_tee {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (index : U32),
      ∃ nextVisitorState,
        visitor.on_local_tee visitorState state index = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.local_tee a0))

theorem Accepts.on_global_get {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (index : U32),
      ∃ nextVisitorState,
        visitor.on_global_get visitorState state index = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.global_get a0))

theorem Accepts.on_global_set {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (index : U32),
      ∃ nextVisitorState,
        visitor.on_global_set visitorState state index = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.global_set a0))

theorem Accepts.on_memory_size {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_memory_size visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.memory_size))

theorem Accepts.on_memory_grow {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_memory_grow visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.memory_grow))

theorem Accepts.on_i32_const {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (value : I32),
      ∃ nextVisitorState,
        visitor.on_i32_const visitorState state value = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.i32_const a0))

theorem Accepts.on_i64_const {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (value : I64),
      ∃ nextVisitorState,
        visitor.on_i64_const visitorState state value = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.i64_const a0))

theorem Accepts.on_f32_const {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (bits : U32),
      ∃ nextVisitorState,
        visitor.on_f32_const visitorState state bits = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.f32_const a0))

theorem Accepts.on_f64_const {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (bits : U64),
      ∃ nextVisitorState,
        visitor.on_f64_const visitorState state bits = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.f64_const a0))

theorem Accepts.on_i32_load {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_i32_load visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i32_load arg))

theorem Accepts.on_i64_load {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_i64_load visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i64_load arg))

theorem Accepts.on_f32_load {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_f32_load visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .f32_load arg))

theorem Accepts.on_f64_load {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_f64_load visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .f64_load arg))

theorem Accepts.on_i32_load8_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_i32_load8_s visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i32_load8_s arg))

theorem Accepts.on_i32_load8_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_i32_load8_u visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i32_load8_u arg))

theorem Accepts.on_i32_load16_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_i32_load16_s visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i32_load16_s arg))

theorem Accepts.on_i32_load16_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_i32_load16_u visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i32_load16_u arg))

theorem Accepts.on_i64_load8_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_i64_load8_s visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i64_load8_s arg))

theorem Accepts.on_i64_load8_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_i64_load8_u visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i64_load8_u arg))

theorem Accepts.on_i64_load16_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_i64_load16_s visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i64_load16_s arg))

theorem Accepts.on_i64_load16_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_i64_load16_u visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i64_load16_u arg))

theorem Accepts.on_i64_load32_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_i64_load32_s visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i64_load32_s arg))

theorem Accepts.on_i64_load32_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_i64_load32_u visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i64_load32_u arg))

theorem Accepts.on_i32_store {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_i32_store visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i32_store arg))

theorem Accepts.on_i64_store {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_i64_store visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i64_store arg))

theorem Accepts.on_f32_store {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_f32_store visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .f32_store arg))

theorem Accepts.on_f64_store {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_f64_store visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .f64_store arg))

theorem Accepts.on_i32_store8 {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_i32_store8 visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i32_store8 arg))

theorem Accepts.on_i32_store16 {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_i32_store16 visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i32_store16 arg))

theorem Accepts.on_i64_store8 {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_i64_store8 visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i64_store8 arg))

theorem Accepts.on_i64_store16 {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_i64_store16 visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i64_store16 arg))

theorem Accepts.on_i64_store32 {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_i64_store32 visitorState state argument = .ok (.Ok () , nextVisitorState) := by
  intro v st arg
  exact h v (.op st (.memory .i64_store32 arg))

theorem Accepts.on_i32_eqz {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_eqz visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_eqz))

theorem Accepts.on_i32_eq {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_eq visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_eq))

theorem Accepts.on_i32_ne {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_ne visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_ne))

theorem Accepts.on_i32_lt_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_lt_s visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_lt_s))

theorem Accepts.on_i32_lt_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_lt_u visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_lt_u))

theorem Accepts.on_i32_gt_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_gt_s visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_gt_s))

theorem Accepts.on_i32_gt_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_gt_u visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_gt_u))

theorem Accepts.on_i32_le_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_le_s visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_le_s))

theorem Accepts.on_i32_le_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_le_u visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_le_u))

theorem Accepts.on_i32_ge_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_ge_s visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_ge_s))

theorem Accepts.on_i32_ge_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_ge_u visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_ge_u))

theorem Accepts.on_i64_eqz {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_eqz visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_eqz))

theorem Accepts.on_i64_eq {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_eq visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_eq))

theorem Accepts.on_i64_ne {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_ne visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_ne))

theorem Accepts.on_i64_lt_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_lt_s visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_lt_s))

theorem Accepts.on_i64_lt_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_lt_u visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_lt_u))

theorem Accepts.on_i64_gt_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_gt_s visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_gt_s))

theorem Accepts.on_i64_gt_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_gt_u visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_gt_u))

theorem Accepts.on_i64_le_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_le_s visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_le_s))

theorem Accepts.on_i64_le_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_le_u visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_le_u))

theorem Accepts.on_i64_ge_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_ge_s visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_ge_s))

theorem Accepts.on_i64_ge_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_ge_u visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_ge_u))

theorem Accepts.on_f32_eq {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f32_eq visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_eq))

theorem Accepts.on_f32_ne {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f32_ne visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_ne))

theorem Accepts.on_f32_lt {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f32_lt visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_lt))

theorem Accepts.on_f32_gt {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f32_gt visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_gt))

theorem Accepts.on_f32_le {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f32_le visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_le))

theorem Accepts.on_f32_ge {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f32_ge visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_ge))

theorem Accepts.on_f64_eq {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f64_eq visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_eq))

theorem Accepts.on_f64_ne {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f64_ne visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_ne))

theorem Accepts.on_f64_lt {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f64_lt visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_lt))

theorem Accepts.on_f64_gt {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f64_gt visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_gt))

theorem Accepts.on_f64_le {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f64_le visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_le))

theorem Accepts.on_f64_ge {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f64_ge visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_ge))

theorem Accepts.on_i32_sub {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_sub visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_sub))

theorem Accepts.on_i32_mul {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_mul visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_mul))

theorem Accepts.on_i32_div_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_div_s visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_div_s))

theorem Accepts.on_i32_div_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_div_u visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_div_u))

theorem Accepts.on_i32_rem_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_rem_s visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_rem_s))

theorem Accepts.on_i32_rem_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_rem_u visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_rem_u))

theorem Accepts.on_i32_and {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_and visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_and))

theorem Accepts.on_i32_or {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_or visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_or))

theorem Accepts.on_i32_xor {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_xor visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_xor))

theorem Accepts.on_i32_shl {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_shl visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_shl))

theorem Accepts.on_i32_shr_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_shr_s visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_shr_s))

theorem Accepts.on_i32_shr_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_shr_u visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_shr_u))

theorem Accepts.on_i32_rotl {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_rotl visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_rotl))

theorem Accepts.on_i32_rotr {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_rotr visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_rotr))

theorem Accepts.on_i64_add {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_add visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_add))

theorem Accepts.on_i64_sub {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_sub visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_sub))

theorem Accepts.on_i64_mul {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_mul visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_mul))

theorem Accepts.on_i64_div_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_div_s visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_div_s))

theorem Accepts.on_i64_div_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_div_u visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_div_u))

theorem Accepts.on_i64_rem_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_rem_s visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_rem_s))

theorem Accepts.on_i64_rem_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_rem_u visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_rem_u))

theorem Accepts.on_i64_and {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_and visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_and))

theorem Accepts.on_i64_or {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_or visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_or))

theorem Accepts.on_i64_xor {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_xor visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_xor))

theorem Accepts.on_i64_shl {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_shl visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_shl))

theorem Accepts.on_i64_shr_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_shr_s visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_shr_s))

theorem Accepts.on_i64_shr_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_shr_u visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_shr_u))

theorem Accepts.on_i64_rotl {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_rotl visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_rotl))

theorem Accepts.on_i64_rotr {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_rotr visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_rotr))

theorem Accepts.on_f32_add {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f32_add visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_add))

theorem Accepts.on_f32_sub {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f32_sub visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_sub))

theorem Accepts.on_f32_mul {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f32_mul visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_mul))

theorem Accepts.on_f32_div {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f32_div visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_div))

theorem Accepts.on_f32_min {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f32_min visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_min))

theorem Accepts.on_f32_max {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f32_max visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_max))

theorem Accepts.on_f32_copysign {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_f32_copysign visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_copysign))

theorem Accepts.on_f64_add {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f64_add visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_add))

theorem Accepts.on_f64_sub {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f64_sub visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_sub))

theorem Accepts.on_f64_mul {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f64_mul visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_mul))

theorem Accepts.on_f64_div {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f64_div visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_div))

theorem Accepts.on_f64_min {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f64_min visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_min))

theorem Accepts.on_f64_max {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f64_max visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_max))

theorem Accepts.on_f64_copysign {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_f64_copysign visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_copysign))

theorem Accepts.on_i32_clz {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_clz visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_clz))

theorem Accepts.on_i32_ctz {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_ctz visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_ctz))

theorem Accepts.on_i32_popcnt {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_popcnt visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_popcnt))

theorem Accepts.on_i32_add {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i32_add visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_add))

theorem Accepts.on_i64_clz {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_clz visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_clz))

theorem Accepts.on_i64_ctz {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_ctz visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_ctz))

theorem Accepts.on_i64_popcnt {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_i64_popcnt visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_popcnt))

theorem Accepts.on_f32_abs {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f32_abs visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_abs))

theorem Accepts.on_f32_neg {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f32_neg visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_neg))

theorem Accepts.on_f32_ceil {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f32_ceil visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_ceil))

theorem Accepts.on_f32_floor {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f32_floor visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_floor))

theorem Accepts.on_f32_trunc {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f32_trunc visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_trunc))

theorem Accepts.on_f32_nearest {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f32_nearest visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_nearest))

theorem Accepts.on_f32_sqrt {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f32_sqrt visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_sqrt))

theorem Accepts.on_f64_abs {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f64_abs visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_abs))

theorem Accepts.on_f64_neg {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f64_neg visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_neg))

theorem Accepts.on_f64_ceil {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f64_ceil visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_ceil))

theorem Accepts.on_f64_floor {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f64_floor visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_floor))

theorem Accepts.on_f64_trunc {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f64_trunc visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_trunc))

theorem Accepts.on_f64_nearest {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f64_nearest visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_nearest))

theorem Accepts.on_f64_sqrt {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_f64_sqrt visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_sqrt))

theorem Accepts.on_i32_wrap_i64 {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i32_wrap_i64 visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_wrap_i64))

theorem Accepts.on_i32_trunc_f32_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i32_trunc_f32_s visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_trunc_f32_s))

theorem Accepts.on_i32_trunc_f32_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i32_trunc_f32_u visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_trunc_f32_u))

theorem Accepts.on_i32_trunc_f64_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i32_trunc_f64_s visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_trunc_f64_s))

theorem Accepts.on_i32_trunc_f64_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i32_trunc_f64_u visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_trunc_f64_u))

theorem Accepts.on_i64_extend_i32_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i64_extend_i32_s visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_extend_i32_s))

theorem Accepts.on_i64_extend_i32_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i64_extend_i32_u visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_extend_i32_u))

theorem Accepts.on_i64_trunc_f32_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i64_trunc_f32_s visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_trunc_f32_s))

theorem Accepts.on_i64_trunc_f32_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i64_trunc_f32_u visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_trunc_f32_u))

theorem Accepts.on_i64_trunc_f64_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i64_trunc_f64_s visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_trunc_f64_s))

theorem Accepts.on_i64_trunc_f64_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i64_trunc_f64_u visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_trunc_f64_u))

theorem Accepts.on_f32_convert_i32_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_f32_convert_i32_s visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_convert_i32_s))

theorem Accepts.on_f32_convert_i32_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_f32_convert_i32_u visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_convert_i32_u))

theorem Accepts.on_f32_convert_i64_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_f32_convert_i64_s visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_convert_i64_s))

theorem Accepts.on_f32_convert_i64_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_f32_convert_i64_u visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_convert_i64_u))

theorem Accepts.on_f32_demote_f64 {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_f32_demote_f64 visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_demote_f64))

theorem Accepts.on_f64_convert_i32_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_f64_convert_i32_s visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_convert_i32_s))

theorem Accepts.on_f64_convert_i32_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_f64_convert_i32_u visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_convert_i32_u))

theorem Accepts.on_f64_convert_i64_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_f64_convert_i64_s visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_convert_i64_s))

theorem Accepts.on_f64_convert_i64_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_f64_convert_i64_u visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_convert_i64_u))

theorem Accepts.on_f64_promote_f32 {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_f64_promote_f32 visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_promote_f32))

theorem Accepts.on_i32_reinterpret_f32 {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i32_reinterpret_f32 visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i32_reinterpret_f32))

theorem Accepts.on_i64_reinterpret_f64 {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i64_reinterpret_f64 visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .i64_reinterpret_f64))

theorem Accepts.on_f32_reinterpret_i32 {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_f32_reinterpret_i32 visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f32_reinterpret_i32))

theorem Accepts.on_f64_reinterpret_i64 {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_f64_reinterpret_i64 visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.numeric .f64_reinterpret_i64))

theorem Accepts.on_i32_extend8_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i32_extend8_s visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i32_extend8_s))

theorem Accepts.on_i32_extend16_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i32_extend16_s visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i32_extend16_s))

theorem Accepts.on_i64_extend8_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i64_extend8_s visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i64_extend8_s))

theorem Accepts.on_i64_extend16_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i64_extend16_s visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i64_extend16_s))

theorem Accepts.on_i64_extend32_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i64_extend32_s visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i64_extend32_s))

theorem Accepts.on_i32_trunc_sat_f32_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i32_trunc_sat_f32_s visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i32_trunc_sat_f32_s))

theorem Accepts.on_i32_trunc_sat_f32_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i32_trunc_sat_f32_u visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i32_trunc_sat_f32_u))

theorem Accepts.on_i32_trunc_sat_f64_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i32_trunc_sat_f64_s visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i32_trunc_sat_f64_s))

theorem Accepts.on_i32_trunc_sat_f64_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i32_trunc_sat_f64_u visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i32_trunc_sat_f64_u))

theorem Accepts.on_i64_trunc_sat_f32_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i64_trunc_sat_f32_s visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i64_trunc_sat_f32_s))

theorem Accepts.on_i64_trunc_sat_f32_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i64_trunc_sat_f32_u visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i64_trunc_sat_f32_u))

theorem Accepts.on_i64_trunc_sat_f64_s {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i64_trunc_sat_f64_s visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i64_trunc_sat_f64_s))

theorem Accepts.on_i64_trunc_sat_f64_u {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState,
        visitor.on_i64_trunc_sat_f64_u visitorState state = .ok (.Ok () , nextVisitorState) := by
  intro v st
  exact h v (.op st (.extendedNumeric .i64_trunc_sat_f64_u))

theorem Accepts.on_ref_null {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (valueType : wasm_types.ElemType),
      ∃ nextVisitorState,
        visitor.on_ref_null visitorState state valueType = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.ref_null a0))

theorem Accepts.on_ref_is_null {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_ref_is_null visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.ref_is_null))

theorem Accepts.on_ref_func {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (index : U32),
      ∃ nextVisitorState,
        visitor.on_ref_func visitorState state index = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.ref_func a0))

theorem Accepts.on_select_typed {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState)
      (valueType : wasm_types.ValueType),
      ∃ nextVisitorState,
        visitor.on_select_typed visitorState state valueType = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.select_typed a0))

theorem Accepts.on_table_get {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (index : U32),
      ∃ nextVisitorState,
        visitor.on_table_get visitorState state index = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.table_get a0))

theorem Accepts.on_table_set {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (index : U32),
      ∃ nextVisitorState,
        visitor.on_table_set visitorState state index = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.table_set a0))

theorem Accepts.on_memory_init {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (dataIndex : U32),
      ∃ nextVisitorState,
        visitor.on_memory_init visitorState state dataIndex = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.memory_init a0))

theorem Accepts.on_data_drop {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (dataIndex : U32),
      ∃ nextVisitorState,
        visitor.on_data_drop visitorState state dataIndex = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.data_drop a0))

theorem Accepts.on_memory_copy {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_memory_copy visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.memory_copy))

theorem Accepts.on_memory_fill {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState),
      ∃ nextVisitorState, visitor.on_memory_fill visitorState state = .ok (.Ok (), nextVisitorState) := by
  intro v st
  exact h v (.op st (.memory_fill))

theorem Accepts.on_table_init {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (elementIndex : U32)
      (tableIndex : U32),
      ∃ nextVisitorState,
        visitor.on_table_init visitorState state elementIndex tableIndex = .ok (.Ok () ,
          nextVisitorState) := by
  intro v st a0 a1
  exact h v (.op st (.table_init a0 a1))

theorem Accepts.on_elem_drop {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (elementIndex : U32),
      ∃ nextVisitorState,
        visitor.on_elem_drop visitorState state elementIndex = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.elem_drop a0))

theorem Accepts.on_table_copy {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (destinationTable : U32)
      (sourceTable : U32),
      ∃ nextVisitorState,
        visitor.on_table_copy visitorState state destinationTable sourceTable = .ok (.Ok () ,
          nextVisitorState) := by
  intro v st a0 a1
  exact h v (.op st (.table_copy a0 a1))

theorem Accepts.on_table_grow {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (tableIndex : U32),
      ∃ nextVisitorState,
        visitor.on_table_grow visitorState state tableIndex = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.table_grow a0))

theorem Accepts.on_table_size {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (tableIndex : U32),
      ∃ nextVisitorState,
        visitor.on_table_size visitorState state tableIndex = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.table_size a0))

theorem Accepts.on_table_fill {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (tableIndex : U32),
      ∃ nextVisitorState,
        visitor.on_table_fill visitorState state tableIndex = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.table_fill a0))

theorem Accepts.on_simd {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (subopcode : U32),
      ∃ nextVisitorState,
        visitor.on_simd visitorState state subopcode = .ok (.Ok () , nextVisitorState) := by
  intro v st a0
  exact h v (.op st (.simd a0))

theorem Accepts.on_simd_lane {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (subopcode : U32) (lane : U8),
      ∃ nextVisitorState,
        visitor.on_simd_lane visitorState state subopcode lane = .ok (.Ok () , nextVisitorState) := by
  intro v st a0 a1
  exact h v (.op st (.simd_lane a0 a1))

theorem Accepts.on_simd_memory {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (subopcode : U32)
      (argument : code.MemArg),
      ∃ nextVisitorState,
        visitor.on_simd_memory visitorState state subopcode argument = .ok (.Ok () ,
          nextVisitorState) := by
  intro v st a0 a1
  exact h v (.op st (.simd_memory a0 a1))

theorem Accepts.on_simd_memory_lane {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (subopcode : U32)
      (argument : code.MemArg) (lane : U8),
      ∃ nextVisitorState,
        visitor.on_simd_memory_lane visitorState state subopcode argument lane = .ok (.Ok () ,
          nextVisitorState) := by
  intro v st a0 a1 a2
  exact h v (.op st (.simd_memory_lane a0 a1 a2))

theorem Accepts.on_simd_const {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (lowBits : U64) (highBits : U64),
      ∃ nextVisitorState,
        visitor.on_simd_const visitorState state lowBits highBits = .ok (.Ok () , nextVisitorState) := by
  intro v st a0 a1
  exact h v (.op st (.simd_const a0 a1))

theorem Accepts.on_simd_shuffle {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    ∀ (visitorState : V) (state : code.OpIterState) (lowBits : U64) (highBits : U64),
      ∃ nextVisitorState,
        visitor.on_simd_shuffle visitorState state lowBits highBits = .ok (.Ok () ,
          nextVisitorState) := by
  intro v st a0 a1
  exact h v (.op st (.simd_shuffle a0 a1))

/-- The empty visitor preserves its state and accepts every event. -/
theorem empty_invoke (v : code.DefaultOpVisitor) (event : Trace.Event) :
    Trace.invoke code.DefaultOpVisitor.Insts.ItascaCodeOpVisitor v event = .ok (.Ok (), v) := by
  cases event with
  | functionStart ctx idx first last => rfl
  | op st action =>
    cases action with
    | unreachable => rfl
    | nop => rfl
    | block a0 => rfl
    | loop a0 => rfl
    | if_ a0 => rfl
    | else_ a0 => rfl
    | end_ a0 a1 => rfl
    | br a0 a1 => rfl
    | br_if a0 a1 => rfl
    | br_table_label a0 => rfl
    | br_table a0 a1 => rfl
    | return_ => rfl
    | call a0 => rfl
    | call_indirect a0 a1 => rfl
    | drop a0 => rfl
    | select a0 => rfl
    | local_get a0 => rfl
    | local_set a0 => rfl
    | local_tee a0 => rfl
    | global_get a0 => rfl
    | global_set a0 => rfl
    | memory_size => rfl
    | memory_grow => rfl
    | i32_const a0 => rfl
    | i64_const a0 => rfl
    | f32_const a0 => rfl
    | f64_const a0 => rfl
    | ref_null a0 => rfl
    | ref_is_null => rfl
    | ref_func a0 => rfl
    | select_typed a0 => rfl
    | table_get a0 => rfl
    | table_set a0 => rfl
    | memory_init a0 => rfl
    | data_drop a0 => rfl
    | memory_copy => rfl
    | memory_fill => rfl
    | table_init a0 a1 => rfl
    | elem_drop a0 => rfl
    | table_copy a0 a1 => rfl
    | table_grow a0 => rfl
    | table_size a0 => rfl
    | table_fill a0 => rfl
    | simd a0 => rfl
    | simd_lane a0 a1 => rfl
    | simd_memory a0 a1 => rfl
    | simd_memory_lane a0 a1 a2 => rfl
    | simd_const a0 a1 => rfl
    | simd_shuffle a0 a1 => rfl
    | extendedNumeric hook =>
      cases hook with
      | i32_extend8_s => rfl
      | i32_extend16_s => rfl
      | i64_extend8_s => rfl
      | i64_extend16_s => rfl
      | i64_extend32_s => rfl
      | i32_trunc_sat_f32_s => rfl
      | i32_trunc_sat_f32_u => rfl
      | i32_trunc_sat_f64_s => rfl
      | i32_trunc_sat_f64_u => rfl
      | i64_trunc_sat_f32_s => rfl
      | i64_trunc_sat_f32_u => rfl
      | i64_trunc_sat_f64_s => rfl
      | i64_trunc_sat_f64_u => rfl
    | numeric hook =>
      cases hook with
      | i32_eqz => rfl
      | i32_eq => rfl
      | i32_ne => rfl
      | i32_lt_s => rfl
      | i32_lt_u => rfl
      | i32_gt_s => rfl
      | i32_gt_u => rfl
      | i32_le_s => rfl
      | i32_le_u => rfl
      | i32_ge_s => rfl
      | i32_ge_u => rfl
      | i64_eqz => rfl
      | i64_eq => rfl
      | i64_ne => rfl
      | i64_lt_s => rfl
      | i64_lt_u => rfl
      | i64_gt_s => rfl
      | i64_gt_u => rfl
      | i64_le_s => rfl
      | i64_le_u => rfl
      | i64_ge_s => rfl
      | i64_ge_u => rfl
      | f32_eq => rfl
      | f32_ne => rfl
      | f32_lt => rfl
      | f32_gt => rfl
      | f32_le => rfl
      | f32_ge => rfl
      | f64_eq => rfl
      | f64_ne => rfl
      | f64_lt => rfl
      | f64_gt => rfl
      | f64_le => rfl
      | f64_ge => rfl
      | i32_sub => rfl
      | i32_mul => rfl
      | i32_div_s => rfl
      | i32_div_u => rfl
      | i32_rem_s => rfl
      | i32_rem_u => rfl
      | i32_and => rfl
      | i32_or => rfl
      | i32_xor => rfl
      | i32_shl => rfl
      | i32_shr_s => rfl
      | i32_shr_u => rfl
      | i32_rotl => rfl
      | i32_rotr => rfl
      | i64_add => rfl
      | i64_sub => rfl
      | i64_mul => rfl
      | i64_div_s => rfl
      | i64_div_u => rfl
      | i64_rem_s => rfl
      | i64_rem_u => rfl
      | i64_and => rfl
      | i64_or => rfl
      | i64_xor => rfl
      | i64_shl => rfl
      | i64_shr_s => rfl
      | i64_shr_u => rfl
      | i64_rotl => rfl
      | i64_rotr => rfl
      | f32_add => rfl
      | f32_sub => rfl
      | f32_mul => rfl
      | f32_div => rfl
      | f32_min => rfl
      | f32_max => rfl
      | f32_copysign => rfl
      | f64_add => rfl
      | f64_sub => rfl
      | f64_mul => rfl
      | f64_div => rfl
      | f64_min => rfl
      | f64_max => rfl
      | f64_copysign => rfl
      | i32_clz => rfl
      | i32_ctz => rfl
      | i32_popcnt => rfl
      | i32_add => rfl
      | i64_clz => rfl
      | i64_ctz => rfl
      | i64_popcnt => rfl
      | f32_abs => rfl
      | f32_neg => rfl
      | f32_ceil => rfl
      | f32_floor => rfl
      | f32_trunc => rfl
      | f32_nearest => rfl
      | f32_sqrt => rfl
      | f64_abs => rfl
      | f64_neg => rfl
      | f64_ceil => rfl
      | f64_floor => rfl
      | f64_trunc => rfl
      | f64_nearest => rfl
      | f64_sqrt => rfl
      | i32_wrap_i64 => rfl
      | i32_trunc_f32_s => rfl
      | i32_trunc_f32_u => rfl
      | i32_trunc_f64_s => rfl
      | i32_trunc_f64_u => rfl
      | i64_extend_i32_s => rfl
      | i64_extend_i32_u => rfl
      | i64_trunc_f32_s => rfl
      | i64_trunc_f32_u => rfl
      | i64_trunc_f64_s => rfl
      | i64_trunc_f64_u => rfl
      | f32_convert_i32_s => rfl
      | f32_convert_i32_u => rfl
      | f32_convert_i64_s => rfl
      | f32_convert_i64_u => rfl
      | f32_demote_f64 => rfl
      | f64_convert_i32_s => rfl
      | f64_convert_i32_u => rfl
      | f64_convert_i64_s => rfl
      | f64_convert_i64_u => rfl
      | f64_promote_f32 => rfl
      | i32_reinterpret_f32 => rfl
      | i64_reinterpret_f64 => rfl
      | f32_reinterpret_i32 => rfl
      | f64_reinterpret_i64 => rfl
    | memory hook arg =>
      cases hook with
      | i32_load => rfl
      | i64_load => rfl
      | f32_load => rfl
      | f64_load => rfl
      | i32_load8_s => rfl
      | i32_load8_u => rfl
      | i32_load16_s => rfl
      | i32_load16_u => rfl
      | i64_load8_s => rfl
      | i64_load8_u => rfl
      | i64_load16_s => rfl
      | i64_load16_u => rfl
      | i64_load32_s => rfl
      | i64_load32_u => rfl
      | i32_store => rfl
      | i64_store => rfl
      | f32_store => rfl
      | f64_store => rfl
      | i32_store8 => rfl
      | i32_store16 => rfl
      | i64_store8 => rfl
      | i64_store16 => rfl
      | i64_store32 => rfl


end Itasca.Visitor
