(** * Translating extracted types to WasmCert types

    The Aeneas extraction has its own copies of the Wasm types (types_ValueType_t,
    opiter_BlockType_t, ...). These map them onto WasmCert-Coq's.

    Definitions only; no proofs. *)

Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.Nnat.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Import Veriwasm.Aeneas_Specs.

From Wasm Require Import datatypes type_checker operations typing.
From mathcomp Require Import ssreflect ssrbool eqtype seq.
From compcert Require Import Integers.
(* Last, so that an unqualified [Byte] is Coq's rather than CompCert's; see the
   same note in [Spec_Module.v]. *)
Require Import Coq.Strings.Byte.


Definition translate_vt_v (vt : types_ValueType_t) : value_type :=
  match vt with
  | Types_ValueType_I32 => T_num T_i32
  | Types_ValueType_I64 => T_num T_i64
  | Types_ValueType_F32 => T_num T_f32
  | Types_ValueType_F64 => T_num T_f64
  end.

(** Every extracted value type is one of WasmCert's *number* types, so no
    translated operand can be [T_bot]. That is what closes the one gap between
    the two sides: WasmCert's [consume] accepts a pop whose operand subtypes the
    expected type and [T_bot] subtypes everything, while the Rust compares value
    types for equality. An operand of unknown type is [StackType::Bot], which
    has no [ValueType] inside it. *)
Lemma translate_vt_v_not_bot : forall vt, translate_vt_v vt <> T_bot.
Proof. intros vt. destruct vt; discriminate. Qed.

(** VeriWasm stacks grow rightward (last = top), WasmCert leftward
    (head = top), so every type list is reversed on the way across. *)
Definition translate_typelist (l : list types_ValueType_t) : list value_type :=
  rev (map translate_vt_v l).

Definition translate_ft (ft : types_FuncType_t) : function_type :=
  Tf (translate_typelist (proj1_sig ft.(types_FuncType_params)))
     (translate_typelist (proj1_sig ft.(types_FuncType_results))).

(** The same function type with both lists left as the binary format writes
    them. [translate_ft] is this one reversed on both sides, which is the shape
    [context_reverse] consumes and therefore the shape the body proof's
    agreement clauses are stated in; a module's [mod_types] holds this one. *)
Definition translate_functype (ft : types_FuncType_t) : function_type :=
  Tf (List.map translate_vt_v (proj1_sig ft.(types_FuncType_params)))
     (List.map translate_vt_v (proj1_sig ft.(types_FuncType_results))).

Definition translate_bt (bt : opiter_BlockType_t) : block_type :=
  match bt with
  | Opiter_BlockType_Empty => BT_valtype None
  | Opiter_BlockType_Value vt => BT_valtype (Some (translate_vt_v vt))
  end.

Definition translate_mut (m : types_Mut_t) : mutability :=
  match m with
  | Types_Mut_Const => MUT_const
  | Types_Mut_Var => MUT_var
  end.

Definition translate_limits (l : limits_Limits_t) : limits :=
  {| lim_min := Z.to_N (to_Z l.(limits_Limits_min));
     lim_max := option_map (fun x => Z.to_N (to_Z x)) l.(limits_Limits_max) |}.

Definition translate_memtype (m : types_MemType_t) : memory_type :=
  translate_limits m.(types_MemType_limits).

Definition translate_tabletype (t : types_TableType_t) : table_type :=
  {| tt_limits := translate_limits t.(types_TableType_limits);
     tt_elem_type := T_funcref |}.

Definition translate_globaltype (g : types_GlobalType_t) : global_type :=
  {| tg_mut := translate_mut g.(types_GlobalType_mutability);
     tg_t := translate_vt_v g.(types_GlobalType_valtype) |}.

(** The four index spaces an import can ask for and an export can name, which
    is what [module::import_types] and [module::export_types] report. *)
Definition translate_externtype (t : types_ExternType_t) : extern_type :=
  match t with
  | Types_ExternType_Func ft => ET_func (translate_functype ft)
  | Types_ExternType_Table t => ET_table (translate_tabletype t)
  | Types_ExternType_Memory mt => ET_mem (translate_memtype mt)
  | Types_ExternType_Global gt => ET_global (translate_globaltype gt)
  end.

Definition translate_externtypes (v : alloc_vec_Vec types_ExternType_t)
  : list extern_type := List.map translate_externtype (vec_list v).

(** WasmCert's [name] is a list of Coq's [Byte.byte], and a data segment's
    contents a list of CompCert's, so a byte the decoder copied out crosses
    into WasmCert two different ways. Both are total on the values a [u8] can
    hold; the [None] arm of [Byte.of_N] is unreachable and the default is
    never looked at. *)
Definition translate_name_byte (b : u8) : Byte.byte :=
  match Byte.of_N (Z.to_N (to_Z b)) with
  | Some x => x
  | None => Byte.x00
  end.

Definition translate_name (v : alloc_vec_Vec u8) : name :=
  List.map translate_name_byte (vec_list v).

Definition translate_data_byte (b : u8) : Integers.byte :=
  Integers.Byte.repr (to_Z b).

Definition translate_data_bytes (v : alloc_vec_Vec u8) : list Integers.byte :=
  List.map translate_data_byte (vec_list v).
