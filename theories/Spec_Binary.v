(** * Binary format specification for Wasm 1.0 operators

    A hand transcription of the W3C WebAssembly 1.0 specification, sections
    5.2.2 (integers), 5.3.1 (value types), 5.3.3 (block types) and 5.4
    (instructions). It is not derived from any implementation.

    THIS FILE IS A TRUST ITEM. The correspondence proof shows that the Rust
    decoder agrees with these rules, so a transcription error here is an error
    in the result. It is deliberately written to be checked line by line
    against the specification document, and deliberately contains no proofs
    about programs.

    WasmCert-Coq cannot serve this role. Its [binary_format_spec.v] declares
    [repr_unsigned] and [repr_module] with zero constructors and comments out
    its only lemma; [binary_format_parser.v] is an executable parser with no
    correctness theorem attached.

    Bytes are [Z] in [0, 256). Every relation consumes a prefix and yields the
    remainder, so [repr_x input value rest] reads "input = enc(value) ++ rest".

    Scope: every Wasm 1.0 operator. Recovering the instruction tree from a flat
    operator stream is deliberately absent; it belongs with the simulation
    invariant, not with the byte format. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
From Wasm Require Import datatypes numerics.
From compcert Require Import Floats Integers.

Open Scope Z_scope.

(* ================================================================== *)
(** ** Flat operators                                                  *)
(* ================================================================== *)

(** A single operator as it appears in the byte stream. Structured
    instructions cannot be decoded in one step because their bodies are not
    yet known, so [block] and [loop] carry only their block type and [end] is
    an operator in its own right. Everything else maps one-to-one onto a
    WasmCert [basic_instruction], including [br], whose constructor takes no
    body. *)
Inductive flat_op : Type :=
| FO_plain : basic_instruction -> flat_op
| FO_block : block_type -> flat_op
| FO_loop  : block_type -> flat_op
| FO_if    : block_type -> flat_op
| FO_else
| FO_end.

(* ================================================================== *)
(** ** 5.2.2 Integers                                                  *)
(* ================================================================== *)

(** Spec 5.2.2:

      uN ::= n:byte           => n                    (if n < 2^7 and n < 2^N)
           | n:byte m:u(N-7)  => 2^7 * m + (n - 2^7)   (if n >= 2^7 and N > 7)

    The [n < 2^bits] guard on the last byte and the [7 < bits] guard on
    continuation together bound the encoding at [ceil(bits/7)] bytes and stop
    the final byte from carrying more payload than [bits] has room for. For
    [bits = 32] that is at most five bytes with the fifth below 16.

    Non-minimal encodings are accepted, matching the spec: [[0x80; 0x00]] is a
    valid encoding of 0. *)
Inductive repr_uN : nat -> list Z -> Z -> list Z -> Prop :=
| repr_uN_last : forall bits b rest,
    0 <= b < 128 ->
    b < 2 ^ Z.of_nat bits ->
    repr_uN bits (b :: rest) b rest
| repr_uN_more : forall bits b more m rest,
    128 <= b < 256 ->
    (7 < bits)%nat ->
    repr_uN (bits - 7) more m rest ->
    repr_uN bits (b :: more) (128 * m + (b - 128)) rest.

(** Spec 5.2.2:

      sN ::= n:byte           => n                    (if n < 2^6 and n < 2^(N-1))
           | n:byte           => n - 2^7              (if 2^6 <= n < 2^7
                                                        and n >= 2^7 - 2^(N-1))
           | n:byte m:s(N-7)  => 2^7 * m + (n - 2^7)   (if n >= 2^7 and N > 7) *)
Inductive repr_sN : nat -> list Z -> Z -> list Z -> Prop :=
| repr_sN_pos : forall bits b rest,
    0 <= b < 64 ->
    b < 2 ^ (Z.of_nat bits - 1) ->
    repr_sN bits (b :: rest) b rest
| repr_sN_neg : forall bits b rest,
    64 <= b < 128 ->
    128 - 2 ^ (Z.of_nat bits - 1) <= b ->
    repr_sN bits (b :: rest) (b - 128) rest
| repr_sN_more : forall bits b more m rest,
    128 <= b < 256 ->
    (7 < bits)%nat ->
    repr_sN (bits - 7) more m rest ->
    repr_sN bits (b :: more) (128 * m + (b - 128)) rest.

Definition repr_u32 (bs : list Z) (v : Z) (rest : list Z) : Prop :=
  repr_uN 32 bs v rest.

Definition repr_s32 (bs : list Z) (v : Z) (rest : list Z) : Prop :=
  repr_sN 32 bs v rest.

(* ================================================================== *)
(** ** 5.1.3 Vectors                                                   *)
(* ================================================================== *)

(** Spec 5.1.3:

      vec(B) ::= n:u32 (x:B)^n => x^n

    Instantiated at [labelidx], which is the only vector immediate Wasm 1.0 has:
    it appears once, as [br_table]'s. [repr_u32_rep n] is the [(x:B)^n] half. *)
Inductive repr_u32_rep : nat -> list Z -> list Z -> list Z -> Prop :=
| repr_u32_rep_nil : forall bs, repr_u32_rep 0 bs [] bs
| repr_u32_rep_cons : forall n bs x mid xs rest,
    repr_u32 bs x mid ->
    repr_u32_rep n mid xs rest ->
    repr_u32_rep (S n) bs (x :: xs) rest.

Inductive repr_vec_u32 : list Z -> list Z -> list Z -> Prop :=
| repr_vec_u32_intro : forall bs n mid xs rest,
    repr_u32 bs n mid ->
    repr_u32_rep (Z.to_nat n) mid xs rest ->
    repr_vec_u32 bs xs rest.

(* ================================================================== *)
(** ** 5.2.3 Floating-point                                            *)
(* ================================================================== *)

(** Spec 5.2.3:

      fN ::= b*:byte^(N/8) => float_N of those bytes

    that is, exactly [N/8] bytes holding the IEEE 754 encoding, least
    significant first. The value is the bit pattern; turning it into a float is
    spec 4.2.3's [float_N], which is CompCert's [of_bits] below. *)
Inductive repr_bytes_le : nat -> list Z -> Z -> list Z -> Prop :=
| repr_bytes_le_nil : forall bs, repr_bytes_le 0 bs 0 bs
| repr_bytes_le_cons : forall n b more m rest,
    0 <= b < 256 ->
    repr_bytes_le n more m rest ->
    repr_bytes_le (S n) (b :: more) (b + 256 * m) rest.

(* ================================================================== *)
(** ** 5.3.1 Value types, 5.3.3 Block types                            *)
(* ================================================================== *)

(** Spec 5.3.1. Wasm 1.0 has only number types. *)
Definition valtype_spec (b : Z) : option value_type :=
  if Z.eqb b 127 then Some (T_num T_i32)        (* 0x7F *)
  else if Z.eqb b 126 then Some (T_num T_i64)   (* 0x7E *)
  else if Z.eqb b 125 then Some (T_num T_f32)   (* 0x7D *)
  else if Z.eqb b 124 then Some (T_num T_f64)   (* 0x7C *)
  else None.

(** Spec 5.3.3, restricted to Wasm 1.0: a block type is either empty or a
    single value type, in one byte. The typeidx form arrived with
    multi-value. *)
Definition blocktype_spec (b : Z) : option block_type :=
  if Z.eqb b 64 then Some (BT_valtype None)     (* 0x40 *)
  else match valtype_spec b with
       | Some vt => Some (BT_valtype (Some vt))
       | None => None
       end.

(* ================================================================== *)
(** ** 5.4.6 Memory instructions: memarg                               *)
(* ================================================================== *)

(** Spec 5.4.6: memarg ::= a:u32 o:u32.

    The alignment constraint [a <= natural] is a validation rule (spec 3.3.7),
    not a decoding rule, so it is deliberately not imposed here. *)
Inductive repr_memarg : list Z -> Z * Z -> list Z -> Prop :=
| repr_memarg_intro : forall bs a mid o rest,
    repr_u32 bs a mid ->
    repr_u32 mid o rest ->
    repr_memarg bs (a, o) rest.

(* ================================================================== *)
(** ** 5.4 The opcode table                                            *)
(* ================================================================== *)

(** The operators whose only immediate is a u32 index. Which instruction the
    index becomes is a row of [idx_instr] below rather than a shape of its own,
    so that adding one is a line in each table and no new rule. *)
Inductive idx_op : Type :=
| IO_br
| IO_br_if
| IO_call
| IO_local_get
| IO_local_set
| IO_local_tee
| IO_global_get
| IO_global_set.

Definition idx_instr (io : idx_op) (x : N) : basic_instruction :=
  match io with
  | IO_br => BI_br x
  | IO_br_if => BI_br_if x
  | IO_call => BI_call x
  | IO_local_get => BI_local_get x
  | IO_local_set => BI_local_set x
  | IO_local_tee => BI_local_tee x
  | IO_global_get => BI_global_get x
  | IO_global_set => BI_global_set x
  end.

(** The two integer [const] operators differ only in the width of the immediate
    and in which constructor the value lands in, so they share a shape and a rule.
    Spec 5.4.5 writes them [0x41 n:i32] and [0x42 n:i64], and spec 5.2.2 defines
    [iN] as [sN]. Both are plain functions of the number type, so the shape stays
    first order and two shapes for the same byte are still equal by injectivity. *)
Definition const_bits (nt : number_type) : nat :=
  match nt with
  | T_i64 => 64
  | _ => 32
  end.

Definition const_val (nt : number_type) (z : Z) : value_num :=
  match nt with
  | T_i64 => VAL_int64 (Wasm_int.Int64.repr z)
  | _ => VAL_int32 (Wasm_int.Int32.repr z)
  end.

(** The two floating-point [const] operators, the same way: spec 5.4.5 writes
    them [0x43 z:f32] and [0x44 z:f64], so the shape carries only the number type
    and the rule reads [N/8] bytes. [fconst_val] is spec 4.2.3's [float_N],
    which CompCert already has as [of_bits]. *)
Definition fconst_bytes (nt : number_type) : nat :=
  match nt with
  | T_f64 => 8
  | _ => 4
  end.

Definition fconst_val (nt : number_type) (bits : Z) : value_num :=
  match nt with
  | T_f64 => VAL_float64 (Float.of_bits (Int64.repr bits))
  | _ => VAL_float32 (Float32.of_bits (Int.repr bits))
  end.

(** The shape of an operator's encoding: which immediates follow the opcode
    byte, and for operators with no immediates, which instruction it is.

    Splitting the table out as a total function rather than writing one
    relation rule per opcode is what keeps determinism cheap: two shapes for
    the same byte are equal by injectivity, so no pairwise reasoning across
    opcodes is needed. *)
Inductive op_shape : Type :=
| Sh_nullary : basic_instruction -> op_shape
| Sh_end : op_shape
| Sh_block : op_shape
| Sh_loop : op_shape
| Sh_if : op_shape
| Sh_else : op_shape
| Sh_const : number_type -> op_shape
| Sh_fconst : number_type -> op_shape
| Sh_reserved : basic_instruction -> op_shape
| Sh_br_table : op_shape
| Sh_call_indirect : op_shape
| Sh_idx : idx_op -> op_shape
| Sh_load : number_type -> option (packed_type * sx) -> op_shape
| Sh_store : number_type -> option packed_type -> op_shape.

(** Abbreviations for the three numeric shapes, so that each row of the table
    below fits on one line. They are notations rather than definitions, so the
    table's rows are still literally [Sh_nullary] applications. *)
Local Notation Sh_un t op := (Sh_nullary (BI_unop t op)).
Local Notation Sh_test t op := (Sh_nullary (BI_testop t op)).
Local Notation Sh_cvt t2 op t1 s := (Sh_nullary (BI_cvtop t2 op t1 s)).
Local Notation Sh_bin t op := (Sh_nullary (BI_binop t op)).
Local Notation Sh_rel t op := (Sh_nullary (BI_relop t op)).

(** Spec 5.4's opcode table, one line per row. *)
Definition op_spec (b : Z) : option op_shape :=
  (* 5.4.1 Control instructions *)
  if Z.eqb b        0 then Some (Sh_nullary BI_unreachable)         (* 0x00 *)
  else if Z.eqb b   1 then Some (Sh_nullary BI_nop)                 (* 0x01 *)
  else if Z.eqb b   2 then Some Sh_block                            (* 0x02 *)
  else if Z.eqb b   3 then Some Sh_loop                             (* 0x03 *)
  else if Z.eqb b   4 then Some Sh_if                               (* 0x04 *)
  else if Z.eqb b   5 then Some Sh_else                             (* 0x05 *)
  else if Z.eqb b  11 then Some Sh_end                              (* 0x0B *)
  else if Z.eqb b  12 then Some (Sh_idx IO_br)                       (* 0x0C *)
  else if Z.eqb b  13 then Some (Sh_idx IO_br_if)                    (* 0x0D *)
  else if Z.eqb b  14 then Some Sh_br_table                          (* 0x0E *)
  else if Z.eqb b  15 then Some (Sh_nullary BI_return)               (* 0x0F *)
  else if Z.eqb b  16 then Some (Sh_idx IO_call)                     (* 0x10 *)
  else if Z.eqb b  17 then Some Sh_call_indirect                     (* 0x11 *)
  (* 5.4.3 Parametric instructions *)
  else if Z.eqb b  26 then Some (Sh_nullary BI_drop)                (* 0x1A *)
  else if Z.eqb b  27 then Some (Sh_nullary (BI_select None))       (* 0x1B *)
  (* 5.4.4 Variable instructions *)
  else if Z.eqb b  32 then Some (Sh_idx IO_local_get)               (* 0x20 *)
  else if Z.eqb b  33 then Some (Sh_idx IO_local_set)               (* 0x21 *)
  else if Z.eqb b  34 then Some (Sh_idx IO_local_tee)               (* 0x22 *)
  else if Z.eqb b  35 then Some (Sh_idx IO_global_get)              (* 0x23 *)
  else if Z.eqb b  36 then Some (Sh_idx IO_global_set)              (* 0x24 *)
  (* 5.4.6 Memory instructions: loads *)
  else if Z.eqb b  40 then Some (Sh_load T_i32 None)                (* 0x28 *)
  else if Z.eqb b  41 then Some (Sh_load T_i64 None)                (* 0x29 *)
  else if Z.eqb b  42 then Some (Sh_load T_f32 None)                (* 0x2A *)
  else if Z.eqb b  43 then Some (Sh_load T_f64 None)                (* 0x2B *)
  else if Z.eqb b  44 then Some (Sh_load T_i32 (Some (Tp_i8,  SX_S)))  (* 0x2C *)
  else if Z.eqb b  45 then Some (Sh_load T_i32 (Some (Tp_i8,  SX_U)))  (* 0x2D *)
  else if Z.eqb b  46 then Some (Sh_load T_i32 (Some (Tp_i16, SX_S)))  (* 0x2E *)
  else if Z.eqb b  47 then Some (Sh_load T_i32 (Some (Tp_i16, SX_U)))  (* 0x2F *)
  else if Z.eqb b  48 then Some (Sh_load T_i64 (Some (Tp_i8,  SX_S)))  (* 0x30 *)
  else if Z.eqb b  49 then Some (Sh_load T_i64 (Some (Tp_i8,  SX_U)))  (* 0x31 *)
  else if Z.eqb b  50 then Some (Sh_load T_i64 (Some (Tp_i16, SX_S)))  (* 0x32 *)
  else if Z.eqb b  51 then Some (Sh_load T_i64 (Some (Tp_i16, SX_U)))  (* 0x33 *)
  else if Z.eqb b  52 then Some (Sh_load T_i64 (Some (Tp_i32, SX_S)))  (* 0x34 *)
  else if Z.eqb b  53 then Some (Sh_load T_i64 (Some (Tp_i32, SX_U)))  (* 0x35 *)
  (* 5.4.6 Memory instructions: stores *)
  else if Z.eqb b  54 then Some (Sh_store T_i32 None)               (* 0x36 *)
  else if Z.eqb b  55 then Some (Sh_store T_i64 None)               (* 0x37 *)
  else if Z.eqb b  56 then Some (Sh_store T_f32 None)               (* 0x38 *)
  else if Z.eqb b  57 then Some (Sh_store T_f64 None)               (* 0x39 *)
  else if Z.eqb b  58 then Some (Sh_store T_i32 (Some Tp_i8))       (* 0x3A *)
  else if Z.eqb b  59 then Some (Sh_store T_i32 (Some Tp_i16))      (* 0x3B *)
  else if Z.eqb b  60 then Some (Sh_store T_i64 (Some Tp_i8))       (* 0x3C *)
  else if Z.eqb b  61 then Some (Sh_store T_i64 (Some Tp_i16))      (* 0x3D *)
  else if Z.eqb b  62 then Some (Sh_store T_i64 (Some Tp_i32))      (* 0x3E *)
  (* 5.4.6 Memory instructions: memory.size and memory.grow, each with the
     reserved zero byte the specification writes out as a literal *)
  else if Z.eqb b  63 then Some (Sh_reserved BI_memory_size)        (* 0x3F 0x00 *)
  else if Z.eqb b  64 then Some (Sh_reserved BI_memory_grow)        (* 0x40 0x00 *)
  (* 5.4.5 Numeric instructions *)
  else if Z.eqb b  65 then Some (Sh_const T_i32)                    (* 0x41 *)
  else if Z.eqb b  66 then Some (Sh_const T_i64)                    (* 0x42 *)
  else if Z.eqb b  67 then Some (Sh_fconst T_f32)                   (* 0x43 *)
  else if Z.eqb b  68 then Some (Sh_fconst T_f64)                   (* 0x44 *)
  (* 5.4.5 Numeric instructions: eqz, 0x45 and 0x50 *)
  else if Z.eqb b  69 then Some (Sh_test T_i32 TO_eqz)
  else if Z.eqb b  80 then Some (Sh_test T_i64 TO_eqz)
  (* 5.4.5 comparisons, 0x46-0x4F, 0x51-0x5A, 0x5B-0x60, 0x61-0x66 *)
  else if Z.eqb b  70 then Some (Sh_rel T_i32 (Relop_i ROI_eq))
  else if Z.eqb b  71 then Some (Sh_rel T_i32 (Relop_i ROI_ne))
  else if Z.eqb b  72 then Some (Sh_rel T_i32 (Relop_i (ROI_lt SX_S)))
  else if Z.eqb b  73 then Some (Sh_rel T_i32 (Relop_i (ROI_lt SX_U)))
  else if Z.eqb b  74 then Some (Sh_rel T_i32 (Relop_i (ROI_gt SX_S)))
  else if Z.eqb b  75 then Some (Sh_rel T_i32 (Relop_i (ROI_gt SX_U)))
  else if Z.eqb b  76 then Some (Sh_rel T_i32 (Relop_i (ROI_le SX_S)))
  else if Z.eqb b  77 then Some (Sh_rel T_i32 (Relop_i (ROI_le SX_U)))
  else if Z.eqb b  78 then Some (Sh_rel T_i32 (Relop_i (ROI_ge SX_S)))
  else if Z.eqb b  79 then Some (Sh_rel T_i32 (Relop_i (ROI_ge SX_U)))
  else if Z.eqb b  81 then Some (Sh_rel T_i64 (Relop_i ROI_eq))
  else if Z.eqb b  82 then Some (Sh_rel T_i64 (Relop_i ROI_ne))
  else if Z.eqb b  83 then Some (Sh_rel T_i64 (Relop_i (ROI_lt SX_S)))
  else if Z.eqb b  84 then Some (Sh_rel T_i64 (Relop_i (ROI_lt SX_U)))
  else if Z.eqb b  85 then Some (Sh_rel T_i64 (Relop_i (ROI_gt SX_S)))
  else if Z.eqb b  86 then Some (Sh_rel T_i64 (Relop_i (ROI_gt SX_U)))
  else if Z.eqb b  87 then Some (Sh_rel T_i64 (Relop_i (ROI_le SX_S)))
  else if Z.eqb b  88 then Some (Sh_rel T_i64 (Relop_i (ROI_le SX_U)))
  else if Z.eqb b  89 then Some (Sh_rel T_i64 (Relop_i (ROI_ge SX_S)))
  else if Z.eqb b  90 then Some (Sh_rel T_i64 (Relop_i (ROI_ge SX_U)))
  else if Z.eqb b  91 then Some (Sh_rel T_f32 (Relop_f ROF_eq))
  else if Z.eqb b  92 then Some (Sh_rel T_f32 (Relop_f ROF_ne))
  else if Z.eqb b  93 then Some (Sh_rel T_f32 (Relop_f ROF_lt))
  else if Z.eqb b  94 then Some (Sh_rel T_f32 (Relop_f ROF_gt))
  else if Z.eqb b  95 then Some (Sh_rel T_f32 (Relop_f ROF_le))
  else if Z.eqb b  96 then Some (Sh_rel T_f32 (Relop_f ROF_ge))
  else if Z.eqb b  97 then Some (Sh_rel T_f64 (Relop_f ROF_eq))
  else if Z.eqb b  98 then Some (Sh_rel T_f64 (Relop_f ROF_ne))
  else if Z.eqb b  99 then Some (Sh_rel T_f64 (Relop_f ROF_lt))
  else if Z.eqb b 100 then Some (Sh_rel T_f64 (Relop_f ROF_gt))
  else if Z.eqb b 101 then Some (Sh_rel T_f64 (Relop_f ROF_le))
  else if Z.eqb b 102 then Some (Sh_rel T_f64 (Relop_f ROF_ge))
  (* 5.4.5 binary, 0x6A-0x78, 0x7C-0x8A, 0x92-0x98, 0xA0-0xA6 *)
  else if Z.eqb b 106 then Some (Sh_bin T_i32 (Binop_i BOI_add))
  else if Z.eqb b 107 then Some (Sh_bin T_i32 (Binop_i BOI_sub))
  else if Z.eqb b 108 then Some (Sh_bin T_i32 (Binop_i BOI_mul))
  else if Z.eqb b 109 then Some (Sh_bin T_i32 (Binop_i (BOI_div SX_S)))
  else if Z.eqb b 110 then Some (Sh_bin T_i32 (Binop_i (BOI_div SX_U)))
  else if Z.eqb b 111 then Some (Sh_bin T_i32 (Binop_i (BOI_rem SX_S)))
  else if Z.eqb b 112 then Some (Sh_bin T_i32 (Binop_i (BOI_rem SX_U)))
  else if Z.eqb b 113 then Some (Sh_bin T_i32 (Binop_i BOI_and))
  else if Z.eqb b 114 then Some (Sh_bin T_i32 (Binop_i BOI_or))
  else if Z.eqb b 115 then Some (Sh_bin T_i32 (Binop_i BOI_xor))
  else if Z.eqb b 116 then Some (Sh_bin T_i32 (Binop_i BOI_shl))
  else if Z.eqb b 117 then Some (Sh_bin T_i32 (Binop_i (BOI_shr SX_S)))
  else if Z.eqb b 118 then Some (Sh_bin T_i32 (Binop_i (BOI_shr SX_U)))
  else if Z.eqb b 119 then Some (Sh_bin T_i32 (Binop_i BOI_rotl))
  else if Z.eqb b 120 then Some (Sh_bin T_i32 (Binop_i BOI_rotr))
  else if Z.eqb b 124 then Some (Sh_bin T_i64 (Binop_i BOI_add))
  else if Z.eqb b 125 then Some (Sh_bin T_i64 (Binop_i BOI_sub))
  else if Z.eqb b 126 then Some (Sh_bin T_i64 (Binop_i BOI_mul))
  else if Z.eqb b 127 then Some (Sh_bin T_i64 (Binop_i (BOI_div SX_S)))
  else if Z.eqb b 128 then Some (Sh_bin T_i64 (Binop_i (BOI_div SX_U)))
  else if Z.eqb b 129 then Some (Sh_bin T_i64 (Binop_i (BOI_rem SX_S)))
  else if Z.eqb b 130 then Some (Sh_bin T_i64 (Binop_i (BOI_rem SX_U)))
  else if Z.eqb b 131 then Some (Sh_bin T_i64 (Binop_i BOI_and))
  else if Z.eqb b 132 then Some (Sh_bin T_i64 (Binop_i BOI_or))
  else if Z.eqb b 133 then Some (Sh_bin T_i64 (Binop_i BOI_xor))
  else if Z.eqb b 134 then Some (Sh_bin T_i64 (Binop_i BOI_shl))
  else if Z.eqb b 135 then Some (Sh_bin T_i64 (Binop_i (BOI_shr SX_S)))
  else if Z.eqb b 136 then Some (Sh_bin T_i64 (Binop_i (BOI_shr SX_U)))
  else if Z.eqb b 137 then Some (Sh_bin T_i64 (Binop_i BOI_rotl))
  else if Z.eqb b 138 then Some (Sh_bin T_i64 (Binop_i BOI_rotr))
  else if Z.eqb b 146 then Some (Sh_bin T_f32 (Binop_f BOF_add))
  else if Z.eqb b 147 then Some (Sh_bin T_f32 (Binop_f BOF_sub))
  else if Z.eqb b 148 then Some (Sh_bin T_f32 (Binop_f BOF_mul))
  else if Z.eqb b 149 then Some (Sh_bin T_f32 (Binop_f BOF_div))
  else if Z.eqb b 150 then Some (Sh_bin T_f32 (Binop_f BOF_min))
  else if Z.eqb b 151 then Some (Sh_bin T_f32 (Binop_f BOF_max))
  else if Z.eqb b 152 then Some (Sh_bin T_f32 (Binop_f BOF_copysign))
  else if Z.eqb b 160 then Some (Sh_bin T_f64 (Binop_f BOF_add))
  else if Z.eqb b 161 then Some (Sh_bin T_f64 (Binop_f BOF_sub))
  else if Z.eqb b 162 then Some (Sh_bin T_f64 (Binop_f BOF_mul))
  else if Z.eqb b 163 then Some (Sh_bin T_f64 (Binop_f BOF_div))
  else if Z.eqb b 164 then Some (Sh_bin T_f64 (Binop_f BOF_min))
  else if Z.eqb b 165 then Some (Sh_bin T_f64 (Binop_f BOF_max))
  else if Z.eqb b 166 then Some (Sh_bin T_f64 (Binop_f BOF_copysign))
  (* 5.4.5 integer unary, 0x67-0x69 and 0x79-0x7B *)
  else if Z.eqb b 103 then Some (Sh_un T_i32 (Unop_i UOI_clz))
  else if Z.eqb b 104 then Some (Sh_un T_i32 (Unop_i UOI_ctz))
  else if Z.eqb b 105 then Some (Sh_un T_i32 (Unop_i UOI_popcnt))
  else if Z.eqb b 121 then Some (Sh_un T_i64 (Unop_i UOI_clz))
  else if Z.eqb b 122 then Some (Sh_un T_i64 (Unop_i UOI_ctz))
  else if Z.eqb b 123 then Some (Sh_un T_i64 (Unop_i UOI_popcnt))
  (* 5.4.5 float unary, 0x8B-0x91 and 0x99-0x9F *)
  else if Z.eqb b 139 then Some (Sh_un T_f32 (Unop_f UOF_abs))
  else if Z.eqb b 140 then Some (Sh_un T_f32 (Unop_f UOF_neg))
  else if Z.eqb b 141 then Some (Sh_un T_f32 (Unop_f UOF_ceil))
  else if Z.eqb b 142 then Some (Sh_un T_f32 (Unop_f UOF_floor))
  else if Z.eqb b 143 then Some (Sh_un T_f32 (Unop_f UOF_trunc))
  else if Z.eqb b 144 then Some (Sh_un T_f32 (Unop_f UOF_nearest))
  else if Z.eqb b 145 then Some (Sh_un T_f32 (Unop_f UOF_sqrt))
  else if Z.eqb b 153 then Some (Sh_un T_f64 (Unop_f UOF_abs))
  else if Z.eqb b 154 then Some (Sh_un T_f64 (Unop_f UOF_neg))
  else if Z.eqb b 155 then Some (Sh_un T_f64 (Unop_f UOF_ceil))
  else if Z.eqb b 156 then Some (Sh_un T_f64 (Unop_f UOF_floor))
  else if Z.eqb b 157 then Some (Sh_un T_f64 (Unop_f UOF_trunc))
  else if Z.eqb b 158 then Some (Sh_un T_f64 (Unop_f UOF_nearest))
  else if Z.eqb b 159 then Some (Sh_un T_f64 (Unop_f UOF_sqrt))
  (* 5.4.5 conversions, 0xA7-0xBF *)
  else if Z.eqb b 167 then Some (Sh_cvt T_i32 CVO_wrap T_i64 None)
  else if Z.eqb b 168 then Some (Sh_cvt T_i32 CVO_trunc T_f32 (Some SX_S))
  else if Z.eqb b 169 then Some (Sh_cvt T_i32 CVO_trunc T_f32 (Some SX_U))
  else if Z.eqb b 170 then Some (Sh_cvt T_i32 CVO_trunc T_f64 (Some SX_S))
  else if Z.eqb b 171 then Some (Sh_cvt T_i32 CVO_trunc T_f64 (Some SX_U))
  else if Z.eqb b 172 then Some (Sh_cvt T_i64 CVO_extend T_i32 (Some SX_S))
  else if Z.eqb b 173 then Some (Sh_cvt T_i64 CVO_extend T_i32 (Some SX_U))
  else if Z.eqb b 174 then Some (Sh_cvt T_i64 CVO_trunc T_f32 (Some SX_S))
  else if Z.eqb b 175 then Some (Sh_cvt T_i64 CVO_trunc T_f32 (Some SX_U))
  else if Z.eqb b 176 then Some (Sh_cvt T_i64 CVO_trunc T_f64 (Some SX_S))
  else if Z.eqb b 177 then Some (Sh_cvt T_i64 CVO_trunc T_f64 (Some SX_U))
  else if Z.eqb b 178 then Some (Sh_cvt T_f32 CVO_convert T_i32 (Some SX_S))
  else if Z.eqb b 179 then Some (Sh_cvt T_f32 CVO_convert T_i32 (Some SX_U))
  else if Z.eqb b 180 then Some (Sh_cvt T_f32 CVO_convert T_i64 (Some SX_S))
  else if Z.eqb b 181 then Some (Sh_cvt T_f32 CVO_convert T_i64 (Some SX_U))
  else if Z.eqb b 182 then Some (Sh_cvt T_f32 CVO_demote T_f64 None)
  else if Z.eqb b 183 then Some (Sh_cvt T_f64 CVO_convert T_i32 (Some SX_S))
  else if Z.eqb b 184 then Some (Sh_cvt T_f64 CVO_convert T_i32 (Some SX_U))
  else if Z.eqb b 185 then Some (Sh_cvt T_f64 CVO_convert T_i64 (Some SX_S))
  else if Z.eqb b 186 then Some (Sh_cvt T_f64 CVO_convert T_i64 (Some SX_U))
  else if Z.eqb b 187 then Some (Sh_cvt T_f64 CVO_promote T_f32 None)
  else if Z.eqb b 188 then Some (Sh_cvt T_i32 CVO_reinterpret T_f32 None)
  else if Z.eqb b 189 then Some (Sh_cvt T_i64 CVO_reinterpret T_f64 None)
  else if Z.eqb b 190 then Some (Sh_cvt T_f32 CVO_reinterpret T_i32 None)
  else if Z.eqb b 191 then Some (Sh_cvt T_f64 CVO_reinterpret T_i64 None)
  else None.

(* ================================================================== *)
(** ** 5.4 Instructions                                                *)
(* ================================================================== *)

(** One rule per shape. The opcode byte selects the shape via [op_spec]; the
    shape says which immediates follow. *)
Inductive repr_op : list Z -> flat_op -> list Z -> Prop :=
| repr_op_nullary : forall b be rest,
    op_spec b = Some (Sh_nullary be) ->
    repr_op (b :: rest) (FO_plain be) rest
| repr_op_end : forall b rest,
    op_spec b = Some Sh_end ->
    repr_op (b :: rest) FO_end rest
| repr_op_block : forall b bt_byte bt rest,
    op_spec b = Some Sh_block ->
    blocktype_spec bt_byte = Some bt ->
    repr_op (b :: bt_byte :: rest) (FO_block bt) rest
| repr_op_loop : forall b bt_byte bt rest,
    op_spec b = Some Sh_loop ->
    blocktype_spec bt_byte = Some bt ->
    repr_op (b :: bt_byte :: rest) (FO_loop bt) rest
| repr_op_if : forall b bt_byte bt rest,
    op_spec b = Some Sh_if ->
    blocktype_spec bt_byte = Some bt ->
    repr_op (b :: bt_byte :: rest) (FO_if bt) rest
| repr_op_else : forall b rest,
    op_spec b = Some Sh_else ->
    repr_op (b :: rest) FO_else rest
| repr_op_reserved : forall b be rest,
    op_spec b = Some (Sh_reserved be) ->
    repr_op (b :: 0 :: rest) (FO_plain be) rest
| repr_op_const : forall b nt z bs rest,
    op_spec b = Some (Sh_const nt) ->
    repr_sN (const_bits nt) bs z rest ->
    repr_op (b :: bs) (FO_plain (BI_const_num (const_val nt z))) rest
| repr_op_fconst : forall b nt bits bs rest,
    op_spec b = Some (Sh_fconst nt) ->
    repr_bytes_le (fconst_bytes nt) bs bits rest ->
    repr_op (b :: bs) (FO_plain (BI_const_num (fconst_val nt bits))) rest
| repr_op_idx : forall b io x bs rest,
    op_spec b = Some (Sh_idx io) ->
    repr_u32 bs x rest ->
    repr_op (b :: bs) (FO_plain (idx_instr io (Z.to_N x))) rest
| repr_op_load : forall b nt tp a o bs rest,
    op_spec b = Some (Sh_load nt tp) ->
    repr_memarg bs (a, o) rest ->
    repr_op (b :: bs) (FO_plain (BI_load nt tp (Z.to_N a) (Z.to_N o))) rest
| repr_op_store : forall b nt tp a o bs rest,
    op_spec b = Some (Sh_store nt tp) ->
    repr_memarg bs (a, o) rest ->
    repr_op (b :: bs) (FO_plain (BI_store nt tp (Z.to_N a) (Z.to_N o))) rest
(** Spec 5.4.1: [0x0E l*:vec(labelidx) l_N:labelidx]. The only operator with a
    vector immediate. *)
| repr_op_br_table : forall b ls bs mid x rest,
    op_spec b = Some Sh_br_table ->
    repr_vec_u32 bs ls mid ->
    repr_u32 mid x rest ->
    repr_op (b :: bs)
            (FO_plain (BI_br_table (List.map Z.to_N ls) (Z.to_N x))) rest
(** Spec 5.4.1: [0x11 y:typeidx x:tableidx]. Wasm 1.0 has one table, so the
    table index is a literal zero, and the instruction's table index is 0. The
    remainder of the type index's encoding is what carries it. *)
| repr_op_call_indirect : forall b y bs rest,
    op_spec b = Some Sh_call_indirect ->
    repr_u32 bs y (0 :: rest) ->
    repr_op (b :: bs) (FO_plain (BI_call_indirect 0%N (Z.to_N y))) rest.

(** A flat operator sequence. Structuring it into nested instructions is the
    simulation invariant's job. *)
Inductive repr_ops : list Z -> list flat_op -> list Z -> Prop :=
| repr_ops_nil : forall bs, repr_ops bs [] bs
| repr_ops_cons : forall bs op mid ops rest,
    repr_op bs op mid ->
    repr_ops mid ops rest ->
    repr_ops bs (op :: ops) rest.

(* ================================================================== *)
(** ** Inversion                                                       *)
(* ================================================================== *)

(** Case analysis on a derivation, as a disjunction. The completeness direction
    needs to take a derivation apart, and [inversion]'s generated names and
    equation order shift with the shape of the index, which makes proofs that
    depend on them brittle. These state the cases once. *)
Lemma repr_memarg_inv : forall bs a o rest,
  repr_memarg bs (a, o) rest ->
  exists mid, repr_u32 bs a mid /\ repr_u32 mid o rest.
Proof.
  (* the index is a pair, which [destruct] will not unify, so invert *)
  intros bs a o rest H. inversion H. subst.
  eexists. split; eassumption.
Qed.

Lemma repr_uN_inv : forall bits bs v rest,
  repr_uN bits bs v rest ->
  (exists b r, bs = b :: r /\ v = b /\ rest = r
               /\ 0 <= b < 128 /\ b < 2 ^ Z.of_nat bits)
  \/ (exists b more m, bs = b :: more /\ v = 128 * m + (b - 128)
               /\ 128 <= b < 256 /\ (7 < bits)%nat
               /\ repr_uN (bits - 7)%nat more m rest).
Proof.
  intros bits bs v rest H.
  destruct H as [bits b r Hlo Hhi | bits b more m r Hlo Hb7 Hsub].
  - left. exists b, r. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [exact Hlo | exact Hhi].
  - right. exists b, more, m. split; [reflexivity|]. split; [reflexivity|].
    split; [exact Hlo|]. split; [exact Hb7 | exact Hsub].
Qed.

Lemma repr_bytes_le_inv : forall n bs v rest,
  repr_bytes_le n bs v rest ->
  (n = 0%nat /\ v = 0 /\ rest = bs)
  \/ (exists k b more m, n = S k /\ bs = b :: more /\ v = b + 256 * m
                 /\ 0 <= b < 256 /\ repr_bytes_le k more m rest).
Proof.
  intros n bs v rest H.
  destruct H as [bs | n b more m r Hb Hsub].
  - left. split; [reflexivity|]. split; reflexivity.
  - right. exists n, b, more, m. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Hb | exact Hsub].
Qed.

Lemma repr_sN_inv : forall bits bs v rest,
  repr_sN bits bs v rest ->
  (exists b r, bs = b :: r /\ v = b /\ rest = r
               /\ 0 <= b < 64 /\ b < 2 ^ (Z.of_nat bits - 1))
  \/ (exists b r, bs = b :: r /\ v = b - 128 /\ rest = r
               /\ 64 <= b < 128 /\ 128 - 2 ^ (Z.of_nat bits - 1) <= b)
  \/ (exists b more m, bs = b :: more /\ v = 128 * m + (b - 128)
               /\ 128 <= b < 256 /\ (7 < bits)%nat
               /\ repr_sN (bits - 7)%nat more m rest).
Proof.
  intros bits bs v rest H.
  destruct H as [bits b r Hlo Hhi | bits b r Hlo Hhi
                | bits b more m r Hlo Hb7 Hsub].
  - left. exists b, r. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [exact Hlo | exact Hhi].
  - right. left. exists b, r. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [exact Hlo | exact Hhi].
  - right. right. exists b, more, m. split; [reflexivity|].
    split; [reflexivity|]. split; [exact Hlo|].
    split; [exact Hb7 | exact Hsub].
Qed.

(* ================================================================== *)
(** ** Determinism                                                     *)
(* ================================================================== *)

(** Needed for the completeness direction of the decoder correspondence: if the
    Rust decoder produces an operator, no other operator is admissible for
    those bytes. *)

Lemma repr_uN_det : forall bits bs v1 r1 v2 r2,
  repr_uN bits bs v1 r1 -> repr_uN bits bs v2 r2 -> v1 = v2 /\ r1 = r2.
Proof.
  intros bits bs v1 r1 v2 r2 H1. revert v2 r2.
  induction H1 as [bits b rest Hlo Hhi | bits b more m rest Hlo Hbits Hsub IH];
    intros v2 r2 H2.
  - inversion H2; subst; [split; reflexivity | lia].
  - (* Drop [Hsub] so the [match] below cannot pick it instead of the
       sub-derivation [inversion] produces. *)
    clear Hsub. inversion H2; subst; [lia |].
    match goal with
    | [ H : repr_uN (bits - 7) more _ _ |- _ ] =>
        destruct (IH _ _ H) as [-> ->]
    end.
    split; reflexivity.
Qed.

Lemma repr_sN_det : forall bits bs v1 r1 v2 r2,
  repr_sN bits bs v1 r1 -> repr_sN bits bs v2 r2 -> v1 = v2 /\ r1 = r2.
Proof.
  intros bits bs v1 r1 v2 r2 H1. revert v2 r2.
  induction H1 as [bits b rest Hlo Hhi | bits b rest Hlo Hhi
                  | bits b more m rest Hlo Hbits Hsub IH];
    intros v2 r2 H2.
  - inversion H2; subst; [split; reflexivity | lia | lia].
  - inversion H2; subst; [lia | split; reflexivity | lia].
  - clear Hsub. inversion H2; subst; [lia | lia |].
    match goal with
    | [ H : repr_sN (bits - 7) more _ _ |- _ ] =>
        destruct (IH _ _ H) as [-> ->]
    end.
    split; reflexivity.
Qed.

Lemma repr_bytes_le_det : forall n bs v1 r1 v2 r2,
  repr_bytes_le n bs v1 r1 -> repr_bytes_le n bs v2 r2 -> v1 = v2 /\ r1 = r2.
Proof.
  intros n bs v1 r1 v2 r2 H1. revert v2 r2.
  induction H1 as [bs | n b more m rest Hb Hsub IH]; intros v2 r2 H2.
  - inversion H2; subst; split; reflexivity.
  - clear Hsub. inversion H2; subst.
    match goal with
    | [ H : repr_bytes_le n more _ _ |- _ ] => destruct (IH _ _ H) as [-> ->]
    end.
    split; reflexivity.
Qed.

(** [n] bytes hold a number below [256 ^ n], which is what makes the narrowing
    cast in the four-byte reader safe. *)
Lemma repr_bytes_le_bound : forall n bs v rest,
  repr_bytes_le n bs v rest -> 0 <= v < 256 ^ Z.of_nat n.
Proof.
  intros n bs v rest H.
  induction H as [bs | n b more m rest Hb Hsub IH].
  - cbn. lia.
  - assert (Hstep : 256 ^ Z.of_nat (S n) = 256 ^ Z.of_nat n * 256).
    { rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia. ring. }
    rewrite Hstep. lia.
Qed.

Lemma repr_u32_det : forall bs v1 r1 v2 r2,
  repr_u32 bs v1 r1 -> repr_u32 bs v2 r2 -> v1 = v2 /\ r1 = r2.
Proof. unfold repr_u32. intros. eapply repr_uN_det; eassumption. Qed.

Lemma repr_u32_rep_det : forall n bs xs1 r1 xs2 r2,
  repr_u32_rep n bs xs1 r1 -> repr_u32_rep n bs xs2 r2 -> xs1 = xs2 /\ r1 = r2.
Proof.
  intros n bs xs1 r1 xs2 r2 H1. revert xs2 r2.
  induction H1 as [bs | n bs x mid xs rest Hx Hxs IH]; intros xs2 r2 H2.
  - inversion H2; subst. split; reflexivity.
  - clear Hxs. inversion H2; subst.
    match goal with
    | [ Ha : repr_u32 bs _ _ |- _ ] =>
        destruct (repr_u32_det _ _ _ _ _ Hx Ha) as [-> ->]
    end.
    match goal with
    | [ H : repr_u32_rep n _ _ _ |- _ ] => destruct (IH _ _ H) as [-> ->]
    end.
    split; reflexivity.
Qed.

(** Every encoding consumes at least one byte, so a vector's count cannot exceed
    the bytes that follow it: a truncated table is a decode failure rather than a
    short one. *)
Lemma repr_uN_shorter : forall bits bs v rest,
  repr_uN bits bs v rest -> (List.length rest < List.length bs)%nat.
Proof. intros bits bs v rest H. induction H; cbn; lia. Qed.

Lemma repr_u32_rep_length : forall n bs xs rest,
  repr_u32_rep n bs xs rest -> (n <= List.length bs)%nat.
Proof.
  intros n bs xs rest H.
  induction H as [bs | n bs x mid xs rest Hx Hrep IH]; [apply Nat.le_0_l|].
  pose proof (repr_uN_shorter _ _ _ _ Hx). cbn. lia.
Qed.

(** The count is a u32 and so determined by the bytes, and the count determines
    how many indices follow. *)
Lemma repr_vec_u32_det : forall bs xs1 r1 xs2 r2,
  repr_vec_u32 bs xs1 r1 -> repr_vec_u32 bs xs2 r2 -> xs1 = xs2 /\ r1 = r2.
Proof.
  intros bs xs1 r1 xs2 r2 H1 H2.
  inversion H1 as [bs0 n1 mid1 xs1' r1' Hn1 Hrep1]; subst.
  inversion H2 as [bs0 n2 mid2 xs2' r2' Hn2 Hrep2]; subst.
  destruct (repr_u32_det _ _ _ _ _ Hn1 Hn2) as [-> ->].
  apply (repr_u32_rep_det _ _ _ _ _ _ Hrep1 Hrep2).
Qed.

Lemma repr_memarg_det : forall bs m1 r1 m2 r2,
  repr_memarg bs m1 r1 -> repr_memarg bs m2 r2 -> m1 = m2 /\ r1 = r2.
Proof.
  intros bs m1 r1 m2 r2 H1 H2.
  inversion H1; inversion H2; subst.
  match goal with
  | [ Ha : repr_u32 ?bs _ _, Hb : repr_u32 ?bs _ _ |- _ ] =>
      destruct (repr_u32_det _ _ _ _ _ Ha Hb) as [-> ->]
  end.
  match goal with
  | [ Ha : repr_u32 ?bs _ _, Hb : repr_u32 ?bs _ _ |- _ ] =>
      destruct (repr_u32_det _ _ _ _ _ Ha Hb) as [-> ->]
  end.
  split; reflexivity.
Qed.

(** Collapse two table lookups on the same byte. Mismatched shapes die by
    injectivity on [op_shape], which is what removes the need to compare
    opcodes pairwise. *)
Ltac collapse_spec :=
  repeat match goal with
  | [ Ha : op_spec ?b = Some _, Hb : op_spec ?b = Some _ |- _ ] =>
      rewrite Ha in Hb; inversion Hb; subst; clear Ha
  | [ Ha : blocktype_spec ?b = Some _, Hb : blocktype_spec ?b = Some _ |- _ ] =>
      rewrite Ha in Hb; inversion Hb; subst; clear Ha
  end.

Lemma repr_op_det : forall bs op1 r1 op2 r2,
  repr_op bs op1 r1 -> repr_op bs op2 r2 -> op1 = op2 /\ r1 = r2.
Proof.
  intros bs op1 r1 op2 r2 H1 H2.
  (* [subst] after each inversion, not once at the end: otherwise the two
     derivations keep separate names for the opcode byte and [collapse_spec]
     cannot see that the table was consulted twice on the same input. *)
  inversion H1; subst; inversion H2; subst; collapse_spec;
    try (split; reflexivity).
  (* What survives are the shapes carrying immediates: the index operators, the
     two [const]s, load and store. Resolve each by its immediate's determinism,
     without depending on the order [inversion] happens to leave the goals in. *)
  all: first
    [ (* call_indirect: the remainder is [0 :: rest], so peel the literal off *)
      match goal with
      | [ Ha : repr_u32 ?bs _ (0 :: _), Hb : repr_u32 ?bs _ (0 :: _) |- _ ] =>
          destruct (repr_u32_det _ _ _ _ _ Ha Hb) as [-> Hrest];
          injection Hrest as ->
      end
    | match goal with
      | [ Ha : repr_u32 ?bs _ _, Hb : repr_u32 ?bs _ _ |- _ ] =>
          destruct (repr_u32_det _ _ _ _ _ Ha Hb) as [-> ->]
      end
    | match goal with
      | [ Ha : repr_sN ?n ?bs _ _, Hb : repr_sN ?n ?bs _ _ |- _ ] =>
          destruct (repr_sN_det _ _ _ _ _ _ Ha Hb) as [-> ->]
      end
    | match goal with
      | [ Ha : repr_bytes_le ?n ?bs _ _, Hb : repr_bytes_le ?n ?bs _ _ |- _ ] =>
          destruct (repr_bytes_le_det _ _ _ _ _ _ Ha Hb) as [-> ->]
      end
    | match goal with
      | [ Ha : repr_memarg ?bs _ _, Hb : repr_memarg ?bs _ _ |- _ ] =>
          destruct (repr_memarg_det _ _ _ _ _ Ha Hb) as [Hm ->];
          inversion Hm; subst
      end
    | (* br_table: the vector first, which pins the remainder the default
         label is read from *)
      match goal with
      | [ Ha : repr_vec_u32 ?bs _ _, Hb : repr_vec_u32 ?bs _ _ |- _ ] =>
          destruct (repr_vec_u32_det _ _ _ _ _ Ha Hb) as [-> ->]
      end;
      match goal with
      | [ Ha : repr_u32 ?m _ _, Hb : repr_u32 ?m _ _ |- _ ] =>
          destruct (repr_u32_det _ _ _ _ _ Ha Hb) as [-> ->]
      end ].
  all: split; reflexivity.
Qed.

Lemma repr_op_nonempty : forall bs op rest, repr_op bs op rest -> bs <> [].
Proof. intros bs op rest H. inversion H; discriminate. Qed.

(** [repr_ops] on its own is ambiguous, since the empty sequence consumes
    nothing from any input. Pinning the remainder to [[]] makes it a function:
    that is the form the top-level theorem needs, where the operator stream has
    to account for the whole body.

    The remainders are variables constrained by hypotheses rather than written
    as [[]] in the conclusion, because [induction] cannot propagate a concrete
    index through the derivation. *)
Lemma repr_ops_det : forall bs ops1 r1 ops2 r2,
  repr_ops bs ops1 r1 -> repr_ops bs ops2 r2 -> r1 = [] -> r2 = [] ->
  ops1 = ops2.
Proof.
  intros bs ops1 r1 ops2 r2 H1. revert ops2 r2.
  induction H1 as [bs | bs op mid ops rest Hop Hops IH];
    intros ops2 r2 H2 Hr1 Hr2; subst.
  - inversion H2; subst; [reflexivity |].
    match goal with
    | [ H : repr_op [] _ _ |- _ ] => apply repr_op_nonempty in H; contradiction
    end.
  - inversion H2; subst.
    + match goal with
      | [ H : repr_op [] _ _ |- _ ] => apply repr_op_nonempty in H; contradiction
      end.
    + match goal with
      | [ Ha : repr_op ?b _ _, Hb : repr_op ?b _ _ |- _ ] =>
          destruct (repr_op_det _ _ _ _ _ Ha Hb) as [-> ->]
      end.
      f_equal. eapply IH; [eassumption | reflexivity | reflexivity].
Qed.

(** The operator stream extends at the *end*, which is the direction a streaming
    validator grows it: each iteration appends the operator it just read. The
    inductive definition prepends, so this is stated once here rather than
    rederived in the loop invariant. *)
Lemma repr_ops_snoc : forall bs ops mid op rest,
  repr_ops bs ops mid -> repr_op mid op rest ->
  repr_ops bs (ops ++ [op]) rest.
Proof.
  intros bs ops mid op rest H. revert op rest.
  induction H as [bs | bs op0 mid0 ops rest0 Hop Hops IH]; intros op rest Hlast.
  - simpl. apply repr_ops_cons with (mid := rest); [exact Hlast |].
    apply repr_ops_nil.
  - simpl. apply repr_ops_cons with (mid := mid0); [exact Hop |].
    apply IH. exact Hlast.
Qed.

(* ================================================================== *)
(** ** Reading a prefix                                                *)
(* ================================================================== *)

(** Every rule consumes a prefix of its input and does not look past it. That
    is the second thing this transcription has to get right, and determinism
    does not imply it: a rule that peeked at the bytes after the ones it
    consumed could still be deterministic, and would make a section's contents
    mean something different read on their own from what they mean read inside
    the module. [Spec_Module.repr_section] states a section's contents relation
    over the section's bytes alone, so it is exactly this that lets a decoder
    run over the whole input and still land in that rule.

    The split and the reuse are one property because they are always proved
    together: an induction that produces the split produces the other stream's
    derivation in the same step. *)

Definition reads_prefix {A} (R : list Z -> A -> list Z -> Prop) : Prop :=
  forall bs x rest, R bs x rest ->
    exists pre, bs = pre ++ rest /\ forall rest', R (pre ++ rest') x rest'.

(** A rule that consumes exactly one byte, which most of them do. *)
Lemma prefix_one : forall {A} (R : list Z -> A -> list Z -> Prop) b x rest,
  (forall r, R (b :: r) x r) ->
  exists pre, b :: rest = pre ++ rest /\ forall rest', R (pre ++ rest') x rest'.
Proof. intros A R b x rest H. exists [b]. split; [reflexivity | exact H]. Qed.

Lemma repr_uN_prefix : forall bits, reads_prefix (repr_uN bits).
Proof.
  intros bits bs x rest H.
  induction H as [bits b rest Hb Hlt | bits b more m rest Hb Hbits Hrec IH].
  - apply prefix_one. intros r. apply repr_uN_last; assumption.
  - destruct IH as [pre [Heq Hall]]. exists (b :: pre). split.
    + cbn. rewrite Heq. reflexivity.
    + intros rest'. cbn. apply repr_uN_more; try assumption. apply Hall.
Qed.

Lemma repr_sN_prefix : forall bits, reads_prefix (repr_sN bits).
Proof.
  intros bits bs x rest H.
  induction H as [bits b rest Hb Hlt | bits b rest Hb Hge
                 | bits b more m rest Hb Hbits Hrec IH].
  - apply prefix_one. intros r. apply repr_sN_pos; assumption.
  - apply prefix_one. intros r. apply repr_sN_neg; assumption.
  - destruct IH as [pre [Heq Hall]]. exists (b :: pre). split.
    + cbn. rewrite Heq. reflexivity.
    + intros rest'. cbn. apply repr_sN_more; try assumption. apply Hall.
Qed.

Lemma repr_u32_prefix : reads_prefix repr_u32.
Proof. exact (repr_uN_prefix 32). Qed.

Lemma repr_bytes_le_prefix : forall n, reads_prefix (repr_bytes_le n).
Proof.
  intros n bs x rest H.
  induction H as [bs | n b more m rest Hb Hrec IH].
  - exists []. split; [reflexivity|]. intros rest'. apply repr_bytes_le_nil.
  - destruct IH as [pre [Heq Hall]]. exists (b :: pre). split.
    + cbn. rewrite Heq. reflexivity.
    + intros rest'. cbn. apply repr_bytes_le_cons; [exact Hb | apply Hall].
Qed.

Lemma repr_u32_rep_prefix : forall n, reads_prefix (repr_u32_rep n).
Proof.
  intros n bs xs rest H.
  induction H as [bs | n bs x mid xs rest Hx Hrec IH].
  - exists []. split; [reflexivity|]. intros rest'. apply repr_u32_rep_nil.
  - destruct (repr_u32_prefix _ _ _ Hx) as [pre1 [Heq1 Hall1]].
    destruct IH as [pre2 [Heq2 Hall2]].
    exists (pre1 ++ pre2). split.
    + rewrite Heq1. rewrite Heq2. rewrite <- app_assoc. reflexivity.
    + intros rest'. rewrite <- app_assoc.
      apply repr_u32_rep_cons with (mid := pre2 ++ rest');
        [apply Hall1 | apply Hall2].
Qed.

Lemma repr_vec_u32_prefix : reads_prefix repr_vec_u32.
Proof.
  intros bs xs rest H. inversion H as [bs0 n mid xs0 rest0 Hn Hrep]; subst.
  destruct (repr_u32_prefix _ _ _ Hn) as [pre1 [Heq1 Hall1]].
  destruct (repr_u32_rep_prefix _ _ _ _ Hrep) as [pre2 [Heq2 Hall2]].
  exists (pre1 ++ pre2). split.
  - rewrite Heq1. rewrite Heq2. rewrite <- app_assoc. reflexivity.
  - intros rest'. rewrite <- app_assoc.
    apply repr_vec_u32_intro with (n := n) (mid := pre2 ++ rest');
      [apply Hall1 | apply Hall2].
Qed.

Lemma repr_memarg_prefix : reads_prefix repr_memarg.
Proof.
  intros bs x rest H. inversion H as [bs0 a mid o rest0 Ha Ho]; subst.
  destruct (repr_u32_prefix _ _ _ Ha) as [pre1 [Heq1 Hall1]].
  destruct (repr_u32_prefix _ _ _ Ho) as [pre2 [Heq2 Hall2]].
  exists (pre1 ++ pre2). split.
  - rewrite Heq1. rewrite Heq2. rewrite <- app_assoc. reflexivity.
  - intros rest'. rewrite <- app_assoc.
    apply repr_memarg_intro with (mid := pre2 ++ rest');
      [apply Hall1 | apply Hall2].
Qed.

(** An operator: the opcode byte, then whatever its shape reads. Fourteen
    rules, and each is the opcode in front of one of the readers above. *)
Lemma repr_op_prefix : reads_prefix repr_op.
Proof.
  intros bs op rest H.
  destruct H as [ b be rest Hs | b rest Hs
                | b bt_byte bt rest Hs Hb | b bt_byte bt rest Hs Hb
                | b bt_byte bt rest Hs Hb | b rest Hs
                | b be rest Hs
                | b nt z bs0 rest Hs Hv | b nt bits bs0 rest Hs Hv
                | b io x bs0 rest Hs Hv
                | b nt tp a o bs0 rest Hs Hv | b nt tp a o bs0 rest Hs Hv
                | b ls bs0 mid x rest Hs Hv Hx
                | b y bs0 rest Hs Hv ].
  (* the one-byte and two-byte shapes *)
  1,2,6: apply prefix_one; intros r;
         solve [ apply repr_op_nullary; exact Hs
               | apply repr_op_end; exact Hs
               | apply repr_op_else; exact Hs ].
  1,2,3: exists [b; bt_byte]; split; [reflexivity|]; intros rest'; cbn;
         solve [ apply repr_op_block; assumption
               | apply repr_op_loop; assumption
               | apply repr_op_if; assumption ].
  - exists [b; 0]. split; [reflexivity|]. intros rest'. cbn.
    apply repr_op_reserved. exact Hs.
  (* the shapes with one immediate *)
  - destruct (repr_sN_prefix _ _ _ _ Hv) as [pre [Heq Hall]].
    exists (b :: pre). split; [cbn; rewrite Heq; reflexivity|].
    intros rest'. cbn. apply repr_op_const; [exact Hs | apply Hall].
  - destruct (repr_bytes_le_prefix _ _ _ _ Hv) as [pre [Heq Hall]].
    exists (b :: pre). split; [cbn; rewrite Heq; reflexivity|].
    intros rest'. cbn. apply repr_op_fconst; [exact Hs | apply Hall].
  - destruct (repr_u32_prefix _ _ _ Hv) as [pre [Heq Hall]].
    exists (b :: pre). split; [cbn; rewrite Heq; reflexivity|].
    intros rest'. cbn. apply repr_op_idx; [exact Hs | apply Hall].
  - destruct (repr_memarg_prefix _ _ _ Hv) as [pre [Heq Hall]].
    exists (b :: pre). split; [cbn; rewrite Heq; reflexivity|].
    intros rest'. cbn. apply repr_op_load; [exact Hs | apply Hall].
  - destruct (repr_memarg_prefix _ _ _ Hv) as [pre [Heq Hall]].
    exists (b :: pre). split; [cbn; rewrite Heq; reflexivity|].
    intros rest'. cbn. apply repr_op_store; [exact Hs | apply Hall].
  (* [br_table]'s vector and its default label *)
  - destruct (repr_vec_u32_prefix _ _ _ Hv) as [pre1 [Heq1 Hall1]].
    destruct (repr_u32_prefix _ _ _ Hx) as [pre2 [Heq2 Hall2]].
    exists (b :: pre1 ++ pre2). split.
    + cbn. rewrite Heq1. rewrite Heq2. rewrite <- app_assoc. reflexivity.
    + intros rest'. cbn. rewrite <- app_assoc.
      apply repr_op_br_table with (mid := pre2 ++ rest');
        [exact Hs | apply Hall1 | apply Hall2].
  (* [call_indirect]'s trailing zero is inside the type index's remainder *)
  - destruct (repr_u32_prefix _ _ _ Hv) as [pre [Heq Hall]].
    exists (b :: pre ++ [0]). split.
    + cbn. rewrite Heq. rewrite <- app_assoc. reflexivity.
    + intros rest'. cbn. rewrite <- app_assoc.
      apply repr_op_call_indirect; [exact Hs | apply Hall].
Qed.

Lemma repr_ops_prefix_read : reads_prefix repr_ops.
Proof.
  intros bs ops rest H.
  induction H as [bs | bs op mid ops rest Hop Hrec IH].
  - exists []. split; [reflexivity|]. intros rest'. apply repr_ops_nil.
  - destruct (repr_op_prefix _ _ _ Hop) as [pre1 [Heq1 Hall1]].
    destruct IH as [pre2 [Heq2 Hall2]].
    exists (pre1 ++ pre2). split.
    + rewrite Heq1. rewrite Heq2. rewrite <- app_assoc. reflexivity.
    + intros rest'. rewrite <- app_assoc.
      apply repr_ops_cons with (mid := pre2 ++ rest');
        [apply Hall1 | apply Hall2].
Qed.

(* ================================================================== *)
(** ** Transcription cross-checks                                      *)
(* ================================================================== *)

(** Concrete decodings, checked against the specification by hand. These are
    the audit for this file: if a table row or a guard is mistyped, one of
    these stops holding. *)

(** The guards mention [2 ^ Z.of_nat bits]. [lia] does not know [Z.pow], and
    [vm_compute] reduces the comparison itself to [Lt = Lt], which [lia] cannot
    read either. So replace each power by its literal value, then use [lia]. *)
Ltac crunch_pow :=
  repeat match goal with
  | [ |- context [2 ^ ?e] ] =>
      let v := eval vm_compute in (2 ^ e) in change (2 ^ e) with v
  end; lia.

(** Peel a concrete byte list apart. [inversion_clear] rather than [inversion]
    so the spent hypotheses do not pile up and confuse the next match. *)
Ltac reject_leb :=
  repeat match goal with
  | [ H : repr_uN _ (_ :: _) _ _ |- _ ] => inversion_clear H
  end; solve [crunch_pow | discriminate].

Ltac leb_more := eapply repr_uN_more; [lia | lia | ].
Ltac leb_last := apply repr_uN_last; [lia | crunch_pow].

Example u32_zero : repr_u32 [0] 0 [].
Proof. unfold repr_u32. leb_last. Qed.

Example u32_127 : repr_u32 [127] 127 [].
Proof. unfold repr_u32. leb_last. Qed.

Example u32_128 : repr_u32 [128; 1] 128 [].
Proof.
  unfold repr_u32. replace 128 with (128 * 1 + (128 - 128)) by lia.
  leb_more. leb_last.
Qed.

(** Spec 5.2.2's worked example: 0xE5 0x8E 0x26 encodes 624485. *)
Example u32_624485 : repr_u32 [229; 142; 38] 624485 [].
Proof.
  unfold repr_u32.
  replace 624485 with (128 * (128 * 38 + (142 - 128)) + (229 - 128)) by lia.
  leb_more. leb_more. leb_last.
Qed.

(* Named for the value it encodes, not [u32_max]: that is a Primitives
   constant, and an Example of the same name shadows it downstream. *)
Example u32_at_max : repr_u32 [255; 255; 255; 255; 15] 4294967295 [].
Proof.
  unfold repr_u32.
  replace 4294967295 with
    (128 * (128 * (128 * (128 * 15 + (255 - 128)) + (255 - 128))
            + (255 - 128)) + (255 - 128)) by lia.
  leb_more. leb_more. leb_more. leb_more. leb_last.
Qed.

(** A sixth byte is unreachable: [repr_uN] runs out of [bits] first. *)
Example u32_six_bytes_rejected :
  forall v rest, ~ repr_u32 [128; 128; 128; 128; 128; 0] v rest.
Proof. intros v rest H. unfold repr_u32 in H. reject_leb. Qed.

(** The fifth byte carries only four bits of a u32. *)
Example u32_fifth_byte_overflow_rejected :
  forall v rest, ~ repr_u32 [128; 128; 128; 128; 16] v rest.
Proof. intros v rest H. unfold repr_u32 in H. reject_leb. Qed.

Example s32_minus_one : repr_s32 [127] (-1) [].
Proof.
  unfold repr_s32. replace (-1) with (127 - 128) by lia.
  apply repr_sN_neg; [lia | crunch_pow].
Qed.

Example s32_sixty_three : repr_s32 [63] 63 [].
Proof. unfold repr_s32. apply repr_sN_pos; [lia | crunch_pow]. Qed.

Example s32_minus_sixty_four : repr_s32 [64] (-64) [].
Proof.
  unfold repr_s32. replace (-64) with (64 - 128) by lia.
  apply repr_sN_neg; [lia | crunch_pow].
Qed.

Example op_nop : repr_op [1] (FO_plain BI_nop) [].
Proof. apply repr_op_nullary. reflexivity. Qed.

Example op_unreachable : repr_op [0] (FO_plain BI_unreachable) [].
Proof. apply repr_op_nullary. reflexivity. Qed.

Example op_end : repr_op [11] FO_end [].
Proof. apply repr_op_end. reflexivity. Qed.

Example op_i32_add : repr_op [106] (FO_plain (BI_binop T_i32 (Binop_i BOI_add))) [].
Proof. apply repr_op_nullary. reflexivity. Qed.

(** 0x1B has no immediate in Wasm 1.0: the typed form [0x1C t*:vec(valtype)]
    arrived with reference types. *)
Example op_select : repr_op [27] (FO_plain (BI_select None)) [].
Proof. apply repr_op_nullary. reflexivity. Qed.

(** The two [const] operators, one row each, sharing a rule. [i64.const] takes ten
    bytes at most, the tenth carrying the single bit left. *)
Example op_i32_const_one :
  repr_op [65; 1] (FO_plain (BI_const_num (VAL_int32 (Wasm_int.Int32.repr 1)))) [].
Proof.
  apply repr_op_const with (nt := T_i32) (z := 1); [reflexivity |].
  cbn [const_bits]. apply repr_sN_pos; [lia | crunch_pow].
Qed.

(** 1.0f32 is 0x3F800000 and 1.0f64 is 0x3FF0000000000000, least significant
    byte first. *)
Ltac le_bytes := repeat (apply repr_bytes_le_cons; [lia|]); apply repr_bytes_le_nil.

Example op_f32_const_one :
  repr_op [67; 0; 0; 128; 63]
    (FO_plain (BI_const_num (VAL_float32 (Float32.of_bits (Int.repr 1065353216)))))
    [].
Proof.
  apply repr_op_fconst with (nt := T_f32) (bits := 1065353216); [reflexivity |].
  cbn [fconst_bytes].
  replace 1065353216 with (0 + 256 * (0 + 256 * (128 + 256 * (63 + 256 * 0))))
    by lia.
  le_bytes.
Qed.

Example op_f64_const_one :
  repr_op [68; 0; 0; 0; 0; 0; 0; 240; 63]
    (FO_plain (BI_const_num
                 (VAL_float64 (Float.of_bits (Int64.repr 4607182418800017408)))))
    [].
Proof.
  apply repr_op_fconst with (nt := T_f64) (bits := 4607182418800017408);
    [reflexivity |].
  cbn [fconst_bytes].
  replace 4607182418800017408
    with (0 + 256 * (0 + 256 * (0 + 256 * (0 + 256 * (0 + 256 * (0 + 256
           * (240 + 256 * (63 + 256 * 0)))))))) by lia.
  le_bytes.
Qed.

Example op_i64_const_minus_one :
  repr_op [66; 127] (FO_plain (BI_const_num (VAL_int64 (Wasm_int.Int64.repr (-1))))) [].
Proof.
  apply repr_op_const with (nt := T_i64) (z := (-1)); [reflexivity |].
  cbn [const_bits]. replace (-1) with (127 - 128) by lia.
  apply repr_sN_neg; [lia | crunch_pow].
Qed.

Example op_select_typed_rejected : forall op rest, ~ repr_op [28] op rest.
Proof. intros op rest H. inversion H; discriminate. Qed.

(** The numeric block. One example per shape, plus the two boundaries of the
    conversion range. *)
Example op_i32_clz :
  repr_op [103] (FO_plain (BI_unop T_i32 (Unop_i UOI_clz))) [].
Proof. apply repr_op_nullary. reflexivity. Qed.

Example op_i32_eqz : repr_op [69] (FO_plain (BI_testop T_i32 TO_eqz)) [].
Proof. apply repr_op_nullary. reflexivity. Qed.

Example op_f64_sqrt :
  repr_op [159] (FO_plain (BI_unop T_f64 (Unop_f UOF_sqrt))) [].
Proof. apply repr_op_nullary. reflexivity. Qed.

Example op_i32_wrap_i64 :
  repr_op [167] (FO_plain (BI_cvtop T_i32 CVO_wrap T_i64 None)) [].
Proof. apply repr_op_nullary. reflexivity. Qed.

Example op_i32_trunc_f32_u :
  repr_op [169] (FO_plain (BI_cvtop T_i32 CVO_trunc T_f32 (Some SX_U))) [].
Proof. apply repr_op_nullary. reflexivity. Qed.

Example op_f64_reinterpret_i64 :
  repr_op [191] (FO_plain (BI_cvtop T_f64 CVO_reinterpret T_i64 None)) [].
Proof. apply repr_op_nullary. reflexivity. Qed.

Example op_i32_sub : repr_op [107] (FO_plain (BI_binop T_i32 (Binop_i BOI_sub))) [].
Proof. apply repr_op_nullary. reflexivity. Qed.

Example op_i64_rotr : repr_op [138] (FO_plain (BI_binop T_i64 (Binop_i BOI_rotr))) [].
Proof. apply repr_op_nullary. reflexivity. Qed.

Example op_f32_min : repr_op [150] (FO_plain (BI_binop T_f32 (Binop_f BOF_min))) [].
Proof. apply repr_op_nullary. reflexivity. Qed.

Example op_i32_lt_u :
  repr_op [73] (FO_plain (BI_relop T_i32 (Relop_i (ROI_lt SX_U)))) [].
Proof. apply repr_op_nullary. reflexivity. Qed.

Example op_f64_ge : repr_op [102] (FO_plain (BI_relop T_f64 (Relop_f ROF_ge))) [].
Proof. apply repr_op_nullary. reflexivity. Qed.

(** 0xC0 is [i32.extend8_s], from the sign-extension proposal rather than
    Wasm 1.0, so the table stops at 0xBF. *)
Example op_extend8_s_rejected : forall op rest, ~ repr_op [192] op rest.
Proof. intros op rest H. inversion H; discriminate. Qed.

Example op_block_i32 :
  repr_op [2; 127] (FO_block (BT_valtype (Some (T_num T_i32)))) [].
Proof. apply repr_op_block; reflexivity. Qed.

Example op_block_empty : repr_op [2; 64] (FO_block (BT_valtype None)) [].
Proof. apply repr_op_block; reflexivity. Qed.

Example op_loop_i64 :
  repr_op [3; 126] (FO_loop (BT_valtype (Some (T_num T_i64)))) [].
Proof. apply repr_op_loop; reflexivity. Qed.

Example op_br_zero : repr_op [12; 0] (FO_plain (BI_br 0%N)) [].
Proof.
  apply repr_op_idx with (io := IO_br) (x := 0); [reflexivity |].
  unfold repr_u32. leb_last.
Qed.

(** The vector immediate, at both of its ends: an empty table is the count byte
    and the default label, and a two-entry one is the count, the two entries and
    the default. *)
Ltac vec_last := apply repr_u32_rep_nil.
Ltac vec_more := eapply repr_u32_rep_cons; [unfold repr_u32; leb_last |].

Example op_br_table_empty :
  repr_op [14; 0; 3] (FO_plain (BI_br_table [] 3%N)) [].
Proof.
  eapply repr_op_br_table with (ls := []) (x := 3); [reflexivity | | ].
  - eapply repr_vec_u32_intro with (n := 0); [unfold repr_u32; leb_last |].
    cbn [Z.to_nat]. vec_last.
  - unfold repr_u32. leb_last.
Qed.

Example op_br_table_two :
  repr_op [14; 2; 0; 1; 2] (FO_plain (BI_br_table [0%N; 1%N] 2%N)) [].
Proof.
  eapply repr_op_br_table with (ls := [0; 1]) (x := 2); [reflexivity | | ].
  - eapply repr_vec_u32_intro with (n := 2); [unfold repr_u32; leb_last |].
    cbn [Z.to_nat]. vec_more. vec_more. vec_last.
  - unfold repr_u32. leb_last.
Qed.

(** A count larger than the entries that follow has no derivation. *)
Example op_br_table_short_rejected : forall op rest,
  ~ repr_op [14; 3; 0; 1] op rest.
Proof.
  intros op rest H. inversion H; subst; try discriminate.
  match goal with
  | [ Hv : repr_vec_u32 _ _ _ |- _ ] => inversion Hv; subst
  end.
  match goal with
  | [ Hn : repr_u32 [3; 0; 1] _ _ |- _ ] =>
      unfold repr_u32 in Hn; inversion Hn; subst; [|crunch_pow]
  end.
  match goal with
  | [ Hr : repr_u32_rep _ _ _ _ |- _ ] =>
      apply repr_u32_rep_length in Hr; cbn in Hr; lia
  end.
Qed.

(** align 2, offset 0: the natural alignment for i32.load. *)
Example op_i32_load : repr_op [40; 2; 0] (FO_plain (BI_load T_i32 None 2%N 0%N)) [].
Proof.
  apply repr_op_load with (a := 2) (o := 0); [reflexivity |].
  eapply repr_memarg_intro; unfold repr_u32; leb_last.
Qed.

Example op_i64_load8_s :
  repr_op [48; 0; 0] (FO_plain (BI_load T_i64 (Some (Tp_i8, SX_S)) 0%N 0%N)) [].
Proof.
  apply repr_op_load with (a := 0) (o := 0); [reflexivity |].
  eapply repr_memarg_intro; unfold repr_u32; leb_last.
Qed.

Example op_i32_store16 :
  repr_op [59; 1; 4] (FO_plain (BI_store T_i32 (Some Tp_i16) 1%N 4%N)) [].
Proof.
  apply repr_op_store with (a := 1) (o := 4); [reflexivity |].
  eapply repr_memarg_intro; unfold repr_u32; leb_last.
Qed.

Example op_local_get_zero : repr_op [32; 0] (FO_plain (BI_local_get 0%N)) [].
Proof.
  apply repr_op_idx with (io := IO_local_get) (x := 0); [reflexivity |].
  unfold repr_u32. leb_last.
Qed.

Example op_local_tee_three : repr_op [34; 3] (FO_plain (BI_local_tee 3%N)) [].
Proof.
  apply repr_op_idx with (io := IO_local_tee) (x := 3); [reflexivity |].
  unfold repr_u32. leb_last.
Qed.

Example op_memory_size : repr_op [63; 0] (FO_plain BI_memory_size) [].
Proof. apply repr_op_reserved. reflexivity. Qed.

(** The reserved byte is a literal, so a non-zero one has no derivation. *)
Example op_memory_size_nonzero_rejected : forall op rest,
  ~ repr_op [63; 1] op rest.
Proof. intros op rest H. inversion H; discriminate. Qed.

Example op_global_set_one : repr_op [36; 1] (FO_plain (BI_global_set 1%N)) [].
Proof.
  apply repr_op_idx with (io := IO_global_set) (x := 1); [reflexivity |].
  unfold repr_u32. leb_last.
Qed.

Example op_call_two : repr_op [16; 2] (FO_plain (BI_call 2%N)) [].
Proof.
  apply repr_op_idx with (io := IO_call) (x := 2); [reflexivity |].
  unfold repr_u32. leb_last.
Qed.

(** The table index is a literal zero, so it is part of the encoding rather than
    an immediate, and a non-zero one has no derivation. *)
Example op_call_indirect_zero :
  repr_op [17; 0; 0] (FO_plain (BI_call_indirect 0%N 0%N)) [].
Proof.
  apply repr_op_call_indirect with (y := 0); [reflexivity |].
  unfold repr_u32. leb_last.
Qed.

Example op_call_indirect_nonzero_table_rejected : forall op rest,
  ~ repr_op [17; 0; 1] op rest.
Proof.
  intros op rest H. inversion H; subst; try discriminate.
  match goal with
  | [ H : repr_u32 _ _ _ |- _ ] => unfold repr_u32 in H; reject_leb
  end.
Qed.

(** 0xFE is not assigned in Wasm 1.0. *)
Example op_unassigned_rejected : forall op rest, ~ repr_op [254] op rest.
Proof. intros op rest H. inversion H; discriminate. Qed.

(** A short operator sequence: i32.const 1, i32.const 2, i32.add, end. *)
Example ops_const_add_end :
  repr_ops [65; 1; 65; 2; 106; 11]
    [FO_plain (BI_const_num (VAL_int32 (Wasm_int.Int32.repr 1)));
     FO_plain (BI_const_num (VAL_int32 (Wasm_int.Int32.repr 2)));
     FO_plain (BI_binop T_i32 (Binop_i BOI_add));
     FO_end] [].
Proof.
  eapply repr_ops_cons.
  { apply repr_op_const with (nt := T_i32) (z := 1); [reflexivity |].
    cbn [const_bits]. apply repr_sN_pos; [lia | crunch_pow]. }
  eapply repr_ops_cons.
  { apply repr_op_const with (nt := T_i32) (z := 2); [reflexivity |].
    cbn [const_bits]. apply repr_sN_pos; [lia | crunch_pow]. }
  eapply repr_ops_cons.
  { apply repr_op_nullary. reflexivity. }
  eapply repr_ops_cons.
  { apply repr_op_end. reflexivity. }
  apply repr_ops_nil.
Qed.
