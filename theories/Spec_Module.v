(** * Binary format specification for Wasm 1.0 modules

    A hand transcription of the W3C WebAssembly 1.0 specification, sections
    5.1.3 (vectors), 5.2.4 (names), 5.3 (types) and 5.5 (modules). It is not
    derived from any implementation.

    THIS FILE IS A TRUST ITEM, for the same reason [Spec_Binary.v] is: the
    correspondence proof shows that the Rust agrees with these rules, so a
    transcription error here is an error in the result. It is deliberately
    written to be checked line by line against the specification document, and
    deliberately contains no proofs about programs. WasmCert-Coq cannot serve
    this role: its [binary_format_spec.v] declares [repr_module] as an inductive
    with zero constructors.

    [Spec_Binary.v] covers instructions and [Spec_Expr.v] covers expressions.
    This file covers everything around them, and depends on those two and on
    WasmCert's datatypes. It does not depend on the extraction.

    Bytes are [Z] in [0, 256). Every relation consumes a prefix and yields the
    remainder, so [repr_x input value rest] reads "input = enc(value) ++ rest".

    ** The value these rules produce

    WasmCert-Coq's [module] is Wasm 2.0-shaped, so a Wasm 1.0 module is a
    particular kind of 2.0 module rather than a different type. Two places
    where the encoding and the value therefore differ in shape, both forced:

    - An element segment's [x*:vec(funcidx)] becomes [modelem_init] as one
      singleton expression [[BI_ref_func x]] per index, with mode
      [ME_active tableidx offset] and [modelem_type] [T_funcref]. The 2.0 type
      has no way to say "a vector of function indices".
    - A data segment's [x:memidx] becomes the mode [MD_active x offset].

    That embedding is not free: [BI_ref_func x] is well typed only when [x] is
    in the context's [tc_refs], which [module_typing] fills from
    [module_filter_funcidx], which collects exactly the indices appearing in
    element segments. The two line up, and [ex_wasm10_module] at the end of this
    file is a worked example: its bytes decode by these rules, and the module
    they decode to is accepted by [module_type_checker].

    No divergence from [module.rs] is known. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
From compcert Require Import Integers.
(* [instantiation_func] is only here for the embedding cross-checks at the end
   of the file; none of the rules depend on it. *)
From Wasm Require Import datatypes numerics instantiation_spec instantiation_func.
Require Import Itasca.Spec_Binary.
Require Import Itasca.Spec_Expr.
(* Last, so that an unqualified [Byte] is Coq's. WasmCert uses two byte types:
   a [name] is a list of Coq's [Byte.byte], while a data segment's contents are
   a list of CompCert's [Integers.byte]. They need separate correspondences. *)
Require Import Coq.Strings.Byte.

Open Scope Z_scope.

(* ================================================================== *)
(** ** 5.1.3 Vectors, over any element                                 *)
(* ================================================================== *)

(** Spec 5.1.3:

      vec(B) ::= n:u32 (x:B)^n => x^n

    [Spec_Binary.v] has this at its one Wasm 1.0 instruction-level
    instantiation, [labelidx]. A module needs it at nine more, so here it is
    parameterised by the element relation. [repr_rep n] is the [(x:B)^n] half. *)

Inductive repr_rep {A : Type} (R : list Z -> A -> list Z -> Prop)
  : nat -> list Z -> list A -> list Z -> Prop :=
| repr_rep_nil : forall bs,
    repr_rep R 0 bs [] bs
| repr_rep_cons : forall n bs x mid xs rest,
    R bs x mid ->
    repr_rep R n mid xs rest ->
    repr_rep R (S n) bs (x :: xs) rest.

Inductive repr_vec {A : Type} (R : list Z -> A -> list Z -> Prop)
  : list Z -> list A -> list Z -> Prop :=
| repr_vec_intro : forall bs n mid xs rest,
    repr_u32 bs n mid ->
    repr_rep R (Z.to_nat n) mid xs rest ->
    repr_vec R bs xs rest.

(** A single byte, so that [vec(byte)] is [repr_vec repr_byte]. *)
Inductive repr_byte : list Z -> Z -> list Z -> Prop :=
| repr_byte_intro : forall b rest,
    0 <= b < 256 ->
    repr_byte (b :: rest) b rest.

(* ================================================================== *)
(** ** 5.2.4 Names                                                     *)
(* ================================================================== *)

(** Spec 5.2.4:

      name ::= b*:vec(byte) => name   if utf8(name) = b*

    The side condition is what [utf8_valid] transcribes: Unicode's table of
    well-formed UTF-8 byte sequences, which is also what rules out overlong
    encodings and the surrogate range. The ranges below are that table, and
    [module.rs]'s [utf8_sequence_len] is the same table again. *)

Inductive utf8_valid : list Z -> Prop :=
| utf8_nil :
    utf8_valid []
| utf8_one : forall b rest,
    0 <= b <= 127 ->
    utf8_valid rest ->
    utf8_valid (b :: rest)
| utf8_two : forall b1 b2 rest,
    194 <= b1 <= 223 -> 128 <= b2 <= 191 ->
    utf8_valid rest ->
    utf8_valid (b1 :: b2 :: rest)
| utf8_three_e0 : forall b2 b3 rest,
    160 <= b2 <= 191 -> 128 <= b3 <= 191 ->
    utf8_valid rest ->
    utf8_valid (224 :: b2 :: b3 :: rest)
| utf8_three_mid : forall b1 b2 b3 rest,
    225 <= b1 <= 236 -> 128 <= b2 <= 191 -> 128 <= b3 <= 191 ->
    utf8_valid rest ->
    utf8_valid (b1 :: b2 :: b3 :: rest)
| utf8_three_ed : forall b2 b3 rest,
    128 <= b2 <= 159 -> 128 <= b3 <= 191 ->
    utf8_valid rest ->
    utf8_valid (237 :: b2 :: b3 :: rest)
| utf8_three_high : forall b1 b2 b3 rest,
    238 <= b1 <= 239 -> 128 <= b2 <= 191 -> 128 <= b3 <= 191 ->
    utf8_valid rest ->
    utf8_valid (b1 :: b2 :: b3 :: rest)
| utf8_four_f0 : forall b2 b3 b4 rest,
    144 <= b2 <= 191 -> 128 <= b3 <= 191 -> 128 <= b4 <= 191 ->
    utf8_valid rest ->
    utf8_valid (240 :: b2 :: b3 :: b4 :: rest)
| utf8_four_mid : forall b1 b2 b3 b4 rest,
    241 <= b1 <= 243 -> 128 <= b2 <= 191 -> 128 <= b3 <= 191 -> 128 <= b4 <= 191 ->
    utf8_valid rest ->
    utf8_valid (b1 :: b2 :: b3 :: b4 :: rest)
| utf8_four_f4 : forall b2 b3 b4 rest,
    128 <= b2 <= 143 -> 128 <= b3 <= 191 -> 128 <= b4 <= 191 ->
    utf8_valid rest ->
    utf8_valid (244 :: b2 :: b3 :: b4 :: rest).

(** The byte stream here is [list Z]. A [name] is a list of Coq's [Byte.byte];
    a data segment's contents are a list of CompCert's [Integers.byte]. Two
    pointwise correspondences, one for each. *)
Definition name_byte_is (z : Z) (b : Byte.byte) : Prop := Z.to_N z = Byte.to_N b.

Definition data_byte_is (z : Z) (b : Integers.byte) : Prop :=
  Integers.Byte.unsigned b = z.

Inductive repr_bytevec : list Z -> list Integers.byte -> list Z -> Prop :=
| repr_bytevec_intro : forall bs zs bys rest,
    repr_vec repr_byte bs zs rest ->
    Forall2 data_byte_is zs bys ->
    repr_bytevec bs bys rest.

Inductive repr_name : list Z -> name -> list Z -> Prop :=
| repr_name_intro : forall bs zs nm rest,
    repr_vec repr_byte bs zs rest ->
    Forall2 name_byte_is zs nm ->
    utf8_valid zs ->
    repr_name bs nm rest.

(* ================================================================== *)
(** ** 5.3 Types                                                       *)
(* ================================================================== *)

(** Spec 5.3.1, via [Spec_Binary.valtype_spec]: Wasm 1.0 has only the four
    number types. *)
Inductive repr_valtype : list Z -> value_type -> list Z -> Prop :=
| repr_valtype_intro : forall b vt rest,
    valtype_spec b = Some vt ->
    repr_valtype (b :: rest) vt rest.

(** Spec 5.3.2: [resulttype ::= t*:vec(valtype)]. *)
Definition repr_resulttype := repr_vec repr_valtype.

(** Spec 5.3.3: [functype ::= 0x60 rt1:resulttype rt2:resulttype].

    Wasm 1.0's "at most one result" is a validation rule, not a decoding one,
    so it is deliberately not imposed here. *)
Inductive repr_functype : list Z -> function_type -> list Z -> Prop :=
| repr_functype_intro : forall p0 p1 t1 t2 rest,
    repr_resulttype p0 t1 p1 ->
    repr_resulttype p1 t2 rest ->
    repr_functype (96 :: p0) (Tf t1 t2) rest.

(** Spec 5.3.4:

      limits ::= 0x00 n:u32       => {min n, max epsilon}
               | 0x01 n:u32 m:u32 => {min n, max m}

    Whether the bounds are in range is spec 3.2.3, a validation rule. *)
Inductive repr_limits : list Z -> limits -> list Z -> Prop :=
| repr_limits_open : forall p0 n rest,
    repr_u32 p0 n rest ->
    repr_limits (0 :: p0) {| lim_min := Z.to_N n; lim_max := None |} rest
| repr_limits_closed : forall p0 n p1 m rest,
    repr_u32 p0 n p1 ->
    repr_u32 p1 m rest ->
    repr_limits (1 :: p0) {| lim_min := Z.to_N n; lim_max := Some (Z.to_N m) |} rest.

(** Spec 5.3.5: [memtype ::= lim:limits]. *)
Definition repr_memtype := repr_limits.

(** Spec 5.3.6 and 5.3.7: [tabletype ::= et:elemtype lim:limits] and
    [elemtype ::= 0x70]. Wasm 1.0's only element type is [funcref]. *)
Inductive repr_tabletype : list Z -> table_type -> list Z -> Prop :=
| repr_tabletype_intro : forall p0 lim rest,
    repr_limits p0 lim rest ->
    repr_tabletype (112 :: p0)
      {| tt_limits := lim; tt_elem_type := T_funcref |} rest.

(** Spec 5.3.8: [globaltype ::= t:valtype m:mut], [mut ::= 0x00 | 0x01]. *)
Inductive repr_mut : list Z -> mutability -> list Z -> Prop :=
| repr_mut_const : forall rest, repr_mut (0 :: rest) MUT_const rest
| repr_mut_var : forall rest, repr_mut (1 :: rest) MUT_var rest.

Inductive repr_globaltype : list Z -> global_type -> list Z -> Prop :=
| repr_globaltype_intro : forall bs t p1 m rest,
    repr_valtype bs t p1 ->
    repr_mut p1 m rest ->
    repr_globaltype bs {| tg_mut := m; tg_t := t |} rest.

(** Indices (spec 5.5.1) are all [u32], and WasmCert's are all [N]. *)
Inductive repr_idx : list Z -> N -> list Z -> Prop :=
| repr_idx_intro : forall bs x rest,
    repr_u32 bs x rest ->
    repr_idx bs (Z.to_N x) rest.

(* ================================================================== *)
(** ** 5.5.2 Sections                                                  *)
(* ================================================================== *)

(** Spec 5.5.2:

      section_N(B) ::= N:byte size:u32 cont:B  (if size = ||B||)
                     | epsilon

    The size is the byte length of the contents, which is stated here by
    splitting the remaining input: the contents are exactly [content], its
    length is the declared size, and the contents relation consumes all of it
    and stops. A section cannot therefore be read past its own end. *)
Inductive repr_section {A : Type} (id : Z) (R : list Z -> A -> list Z -> Prop)
  : list Z -> A -> list Z -> Prop :=
| repr_section_intro : forall p0 size content x rest,
    repr_u32 p0 size (content ++ rest) ->
    Z.of_nat (List.length content) = size ->
    R content x [] ->
    repr_section id R (id :: p0) x rest.

(** The [epsilon] alternative. A section that is absent contributes the empty
    vector, or [None] for the start section.

    The absent case requires the input not to begin with this section's id,
    which is what makes the choice between the two forced by the bytes rather
    than free: without it, an empty section and no section would be two
    readings of the same input. *)
Definition begins_with (id : Z) (bs : list Z) : Prop :=
  exists more, bs = id :: more.

Inductive repr_optsec {A : Type} (id : Z) (R : list Z -> A -> list Z -> Prop)
                      (absent : A)
  : list Z -> A -> list Z -> Prop :=
| repr_optsec_present : forall bs x rest,
    repr_section id R bs x rest ->
    repr_optsec id R absent bs x rest
| repr_optsec_absent : forall bs,
    ~ begins_with id bs ->
    repr_optsec id R absent bs absent bs.

(** Spec 5.5.3: [customsec ::= section_0(custom)], [custom ::= nm:name b*:byte*].

    The trailing bytes are unconstrained and simply fill out the section, which
    is why the contents relation below accepts any remainder after the name.
    Custom sections may appear between any two other sections, so every position
    in the module rule is preceded by a run of them. *)
Definition repr_custom (bs : list Z) (_ : unit) (rest : list Z) : Prop :=
  exists nm mid, repr_name bs nm mid /\ rest = [].

Inductive repr_customs : list Z -> list Z -> Prop :=
| repr_customs_done : forall bs,
    ~ begins_with 0 bs ->
    repr_customs bs bs
| repr_customs_more : forall bs mid rest,
    repr_section 0 repr_custom bs tt mid ->
    repr_customs mid rest ->
    repr_customs bs rest.

(* ================================================================== *)
(** ** 5.5.5 Imports                                                   *)
(* ================================================================== *)

(** Spec 5.5.5:

      import     ::= mod:name nm:name d:importdesc
      importdesc ::= 0x00 x:typeidx | 0x01 tt:tabletype
                   | 0x02 mt:memtype | 0x03 gt:globaltype *)
Inductive repr_importdesc : list Z -> module_import_desc -> list Z -> Prop :=
| repr_importdesc_func : forall p0 x rest,
    repr_idx p0 x rest -> repr_importdesc (0 :: p0) (MID_func x) rest
| repr_importdesc_table : forall p0 tt rest,
    repr_tabletype p0 tt rest -> repr_importdesc (1 :: p0) (MID_table tt) rest
| repr_importdesc_mem : forall p0 mt rest,
    repr_memtype p0 mt rest -> repr_importdesc (2 :: p0) (MID_mem mt) rest
| repr_importdesc_global : forall p0 gt rest,
    repr_globaltype p0 gt rest -> repr_importdesc (3 :: p0) (MID_global gt) rest.

Inductive repr_import : list Z -> module_import -> list Z -> Prop :=
| repr_import_intro : forall bs md p1 nm p2 d rest,
    repr_name bs md p1 ->
    repr_name p1 nm p2 ->
    repr_importdesc p2 d rest ->
    repr_import bs {| imp_module := md; imp_name := nm; imp_desc := d |} rest.

(* ================================================================== *)
(** ** 5.5.7 to 5.5.9 Tables, memories and globals                     *)
(* ================================================================== *)

(** Spec 5.5.7: [table ::= tt:tabletype]. *)
Inductive repr_table : list Z -> module_table -> list Z -> Prop :=
| repr_table_intro : forall bs tt rest,
    repr_tabletype bs tt rest ->
    repr_table bs {| modtab_type := tt |} rest.

(** Spec 5.5.8: [mem ::= mt:memtype]. *)
Inductive repr_mem : list Z -> module_mem -> list Z -> Prop :=
| repr_mem_intro : forall bs mt rest,
    repr_memtype bs mt rest ->
    repr_mem bs {| modmem_type := mt |} rest.

(** Spec 5.5.9: [global ::= gt:globaltype e:expr]. That the expression is
    constant is spec 3.4.4, a validation rule. *)
Inductive repr_global : list Z -> module_global -> list Z -> Prop :=
| repr_global_intro : forall bs gt p1 e rest,
    repr_globaltype bs gt p1 ->
    repr_expr p1 e rest ->
    repr_global bs {| modglob_type := gt; modglob_init := e |} rest.

(* ================================================================== *)
(** ** 5.5.10 Exports                                                  *)
(* ================================================================== *)

(** Spec 5.5.10:

      export     ::= nm:name d:exportdesc
      exportdesc ::= 0x00 x:funcidx | 0x01 x:tableidx
                   | 0x02 x:memidx  | 0x03 x:globalidx *)
Inductive repr_exportdesc : list Z -> module_export_desc -> list Z -> Prop :=
| repr_exportdesc_func : forall p0 x rest,
    repr_idx p0 x rest -> repr_exportdesc (0 :: p0) (MED_func x) rest
| repr_exportdesc_table : forall p0 x rest,
    repr_idx p0 x rest -> repr_exportdesc (1 :: p0) (MED_table x) rest
| repr_exportdesc_mem : forall p0 x rest,
    repr_idx p0 x rest -> repr_exportdesc (2 :: p0) (MED_mem x) rest
| repr_exportdesc_global : forall p0 x rest,
    repr_idx p0 x rest -> repr_exportdesc (3 :: p0) (MED_global x) rest.

Inductive repr_export : list Z -> module_export -> list Z -> Prop :=
| repr_export_intro : forall bs nm p1 d rest,
    repr_name bs nm p1 ->
    repr_exportdesc p1 d rest ->
    repr_export bs {| modexp_name := nm; modexp_desc := d |} rest.

(* ================================================================== *)
(** ** 5.5.11 Start                                                    *)
(* ================================================================== *)

(** Spec 5.5.11: [start ::= x:funcidx], and [startsec] is optional, so the
    contents relation produces the [option] directly. *)
Definition repr_start (bs : list Z) (s : option module_start) (rest : list Z)
  : Prop :=
  exists x, repr_idx bs x rest /\ s = Some {| modstart_func := x |}.

(* ================================================================== *)
(** ** 5.5.12 Element segments                                         *)
(* ================================================================== *)

(** Spec 5.5.12, Wasm 1.0's single form:

      elem ::= x:tableidx e:expr y*:vec(funcidx)

    The 2.0 shape this lands in is described at the top of this file: the
    index vector becomes one [ref.func] expression each, and the table index
    and offset become the segment's mode. *)
Inductive repr_elem : list Z -> module_element -> list Z -> Prop :=
| repr_elem_intro : forall bs x p1 e p2 ys rest,
    repr_idx bs x p1 ->
    repr_expr p1 e p2 ->
    repr_vec repr_idx p2 ys rest ->
    repr_elem bs
      {| modelem_type := T_funcref;
         modelem_init := List.map (fun y => [BI_ref_func y]) ys;
         modelem_mode := ME_active x e |} rest.

(* ================================================================== *)
(** ** 5.5.13 Code                                                     *)
(* ================================================================== *)

(** Spec 5.5.13:

      code   ::= size:u32 code:func  (if size = ||func||)
      func   ::= t*:vec(locals) e:expr
      locals ::= n:u32 t:valtype     => t^n

    The size prefix is framed the same way a section is, so a code entry
    cannot be read past its own end either. *)
Inductive repr_locals : list Z -> list value_type -> list Z -> Prop :=
| repr_locals_intro : forall bs n p1 t rest,
    repr_u32 bs n p1 ->
    repr_valtype p1 t rest ->
    repr_locals bs (List.repeat t (Z.to_nat n)) rest.

Inductive repr_func : list Z -> list value_type * expr -> list Z -> Prop :=
| repr_func_intro : forall bs gs p1 e rest,
    repr_vec repr_locals bs gs p1 ->
    repr_expr p1 e rest ->
    repr_func bs (List.concat gs, e) rest.

Inductive repr_code : list Z -> list value_type * expr -> list Z -> Prop :=
| repr_code_intro : forall bs size content c rest,
    repr_u32 bs size (content ++ rest) ->
    Z.of_nat (List.length content) = size ->
    repr_func content c [] ->
    repr_code bs c rest.

(** Spec 5.5.16 pairs the function section's [typeidx^n] with the code
    section's [code^n], which also says the two have the same length. *)
Inductive funcs_of : list N -> list (list value_type * expr) -> list module_func
                     -> Prop :=
| funcs_of_nil : funcs_of [] [] []
| funcs_of_cons : forall x xs lcls e cs fs,
    funcs_of xs cs fs ->
    funcs_of (x :: xs) ((lcls, e) :: cs)
      ({| modfunc_type := x; modfunc_locals := lcls; modfunc_body := e |} :: fs).

(* ================================================================== *)
(** ** 5.5.14 Data segments                                            *)
(* ================================================================== *)

(** Spec 5.5.14, Wasm 1.0's single form:

      data ::= x:memidx e:expr b*:vec(byte) *)
Inductive repr_data : list Z -> module_data -> list Z -> Prop :=
| repr_data_intro : forall bs x p1 e p2 bys rest,
    repr_idx bs x p1 ->
    repr_expr p1 e p2 ->
    repr_bytevec p2 bys rest ->
    repr_data bs
      {| moddata_init := bys; moddata_mode := MD_active x e |} rest.

(* ================================================================== *)
(** ** 5.5.16 Modules                                                  *)
(* ================================================================== *)

(** Spec 5.5.16:

      magic   ::= 0x00 0x61 0x73 0x6D
      version ::= 0x01 0x00 0x00 0x00 *)
Definition repr_magic_version (bs rest : list Z) : Prop :=
  bs = 0 :: 97 :: 115 :: 109 :: 1 :: 0 :: 0 :: 0 :: rest.

(** Spec 5.5.16 writes every section as [customsec* Xsec], and every [Xsec] is
    optional. That pairing is what one line of the module production actually
    is, so it gets a name. *)
Definition repr_padded {A : Type} (id : Z) (R : list Z -> A -> list Z -> Prop)
                       (absent : A)
                       (bs : list Z) (x : A) (rest : list Z) : Prop :=
  exists mid, repr_customs bs mid /\ repr_optsec id R absent mid x rest.

(** Spec 5.5.16, the module itself: magic, version, then each section in id
    order, with a final run of custom sections after the data section.

    Read the premises top to bottom and they are the specification's production
    line for line. *)
Inductive repr_module : list Z -> module -> Prop :=
| repr_module_intro : forall bs
    p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11
    tfs imps tidxs tabs mems globs exps st els codes datas fs,
    repr_magic_version bs p0 ->
    repr_padded 1  (repr_vec repr_functype) [] p0  tfs   p1  ->
    repr_padded 2  (repr_vec repr_import)   [] p1  imps  p2  ->
    repr_padded 3  (repr_vec repr_idx)      [] p2  tidxs p3  ->
    repr_padded 4  (repr_vec repr_table)    [] p3  tabs  p4  ->
    repr_padded 5  (repr_vec repr_mem)      [] p4  mems  p5  ->
    repr_padded 6  (repr_vec repr_global)   [] p5  globs p6  ->
    repr_padded 7  (repr_vec repr_export)   [] p6  exps  p7  ->
    repr_padded 8  repr_start             None p7  st    p8  ->
    repr_padded 9  (repr_vec repr_elem)     [] p8  els   p9  ->
    repr_padded 10 (repr_vec repr_code)     [] p9  codes p10 ->
    repr_padded 11 (repr_vec repr_data)     [] p10 datas p11 ->
    repr_customs p11 [] ->
    funcs_of tidxs codes fs ->
    repr_module bs
      {| mod_types   := tfs;
         mod_funcs   := fs;
         mod_tables  := tabs;
         mod_mems    := mems;
         mod_globals := globs;
         mod_elems   := els;
         mod_datas   := datas;
         mod_start   := st;
         mod_imports := imps;
         mod_exports := exps |}.

(* ================================================================== *)
(** ** Determinism                                                     *)
(* ================================================================== *)

(** A byte string has at most one reading. This is the audit of the file: an
    ambiguous transcription would be one where two different modules could
    claim the same encoding, and nothing downstream could tell them apart.

    Two rules carry the whole argument, and both would be easy to get wrong.
    [repr_section] pins the contents down by length, so a section's extent is
    determined by its size prefix rather than by how far its contents happen to
    read. [repr_optsec]'s absent case requires the input not to begin with that
    section's id, without which an empty section and no section would be two
    readings of the same bytes. [Spec_Binary.repr_ops_det] and
    [Spec_Expr.repr_expr_det] do the same job one level down. *)

Definition det {A : Type} (R : list Z -> A -> list Z -> Prop) : Prop :=
  forall bs x1 r1 x2 r2, R bs x1 r1 -> R bs x2 r2 -> x1 = x2 /\ r1 = r2.

Ltac det_step L :=
  match goal with
  | [ Ha : ?R ?bs ?x1 ?r1, Hb : ?R ?bs ?x2 ?r2 |- _ ] =>
      destruct (L _ _ _ _ _ Ha Hb) as [-> ->]
  end.


(** *** The generic combinators *)

Lemma repr_byte_det : det repr_byte.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  inversion H1; subst; inversion H2; subst; split; reflexivity.
Qed.

Lemma repr_rep_det : forall A (R : list Z -> A -> list Z -> Prop),
  det R ->
  forall n bs xs1 r1 xs2 r2,
    repr_rep R n bs xs1 r1 -> repr_rep R n bs xs2 r2 -> xs1 = xs2 /\ r1 = r2.
Proof.
  intros A R HR n. induction n as [|n IH]; intros bs xs1 r1 xs2 r2 H1 H2.
  - inversion H1; subst. inversion H2; subst. split; reflexivity.
  - inversion H1 as [|n1 bs1 y1 mid1 ys1 rest1 Hy1 Hrep1]; subst.
    inversion H2 as [|n2 bs2 y2 mid2 ys2 rest2 Hy2 Hrep2]; subst.
    destruct (HR _ _ _ _ _ Hy1 Hy2) as [-> ->].
    destruct (IH _ _ _ _ _ Hrep1 Hrep2) as [-> ->].
    split; reflexivity.
Qed.

Lemma repr_vec_det : forall A (R : list Z -> A -> list Z -> Prop),
  det R -> det (repr_vec R).
Proof.
  intros A R HR bs xs1 r1 xs2 r2 H1 H2.
  inversion H1 as [bs1 n1 mid1 zs1 rest1 Hn1 Hrep1]; subst.
  inversion H2 as [bs2 n2 mid2 zs2 rest2 Hn2 Hrep2]; subst.
  destruct (repr_u32_det _ _ _ _ _ Hn1 Hn2) as [-> ->].
  exact (repr_rep_det _ _ HR _ _ _ _ _ _ Hrep1 Hrep2).
Qed.

(** *** Bytes and names *)

(** Both byte types are determined by the number they carry: [Byte.of_to_N]
    and CompCert's [Byte.repr_unsigned] are the two round trips. *)
Lemma name_byte_is_det : forall z b1 b2,
  name_byte_is z b1 -> name_byte_is z b2 -> b1 = b2.
Proof.
  intros z b1 b2 H1 H2. unfold name_byte_is in *.
  assert (Byte.to_N b1 = Byte.to_N b2) as Heq by (rewrite <- H1, <- H2; reflexivity).
  pose proof (Byte.of_to_N b1) as Hb1.
  rewrite Heq in Hb1. rewrite (Byte.of_to_N b2) in Hb1.
  injection Hb1 as Hb1. symmetry. exact Hb1.
Qed.

Lemma data_byte_is_det : forall z b1 b2,
  data_byte_is z b1 -> data_byte_is z b2 -> b1 = b2.
Proof.
  intros z b1 b2 H1 H2. unfold data_byte_is in *.
  rewrite <- (Integers.Byte.repr_unsigned b1).
  rewrite <- (Integers.Byte.repr_unsigned b2).
  rewrite H1, H2. reflexivity.
Qed.

Lemma forall2_det : forall A (P : Z -> A -> Prop),
  (forall z a1 a2, P z a1 -> P z a2 -> a1 = a2) ->
  forall zs l1 l2, Forall2 P zs l1 -> Forall2 P zs l2 -> l1 = l2.
Proof.
  intros A P HP zs. induction zs as [|z zs IH]; intros l1 l2 H1 H2.
  - inversion H1; inversion H2; reflexivity.
  - inversion H1 as [|z1 a1 zs1 l1' Ha1 Hl1]; subst.
    inversion H2 as [|z2 a2 zs2 l2' Ha2 Hl2]; subst.
    rewrite (HP _ _ _ Ha1 Ha2). rewrite (IH _ _ Hl1 Hl2). reflexivity.
Qed.

Lemma repr_bytevec_det : det repr_bytevec.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  inversion H1 as [bs1 zs1 bys1 rest1 Hv1 Hf1]; subst.
  inversion H2 as [bs2 zs2 bys2 rest2 Hv2 Hf2]; subst.
  destruct (repr_vec_det _ _ repr_byte_det _ _ _ _ _ Hv1 Hv2) as [-> ->].
  split; [|reflexivity].
  exact (forall2_det _ _ data_byte_is_det _ _ _ Hf1 Hf2).
Qed.

Lemma repr_name_det : det repr_name.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  inversion H1 as [bs1 zs1 nm1 rest1 Hv1 Hf1 Hu1]; subst.
  inversion H2 as [bs2 zs2 nm2 rest2 Hv2 Hf2 Hu2]; subst.
  destruct (repr_vec_det _ _ repr_byte_det _ _ _ _ _ Hv1 Hv2) as [-> ->].
  split; [|reflexivity].
  exact (forall2_det _ _ name_byte_is_det _ _ _ Hf1 Hf2).
Qed.

(** *** Types *)

Lemma repr_valtype_det : det repr_valtype.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  inversion H1; subst; inversion H2; subst.
  match goal with
  | [ Ha : valtype_spec ?b = Some ?u, Hb : valtype_spec ?b = Some ?v |- _ ] =>
      rewrite Ha in Hb; injection Hb as ->
  end.
  split; reflexivity.
Qed.

Lemma repr_resulttype_det : det repr_resulttype.
Proof. exact (repr_vec_det _ _ repr_valtype_det). Qed.

Lemma repr_functype_det : det repr_functype.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  inversion H1 as [q0 q1 a1 b1 rest1 Ha1 Hb1]; subst.
  inversion H2 as [q0' q1' a2 b2 rest2 Ha2 Hb2]; subst.
  destruct (repr_resulttype_det _ _ _ _ _ Ha1 Ha2) as [-> ->].
  destruct (repr_resulttype_det _ _ _ _ _ Hb1 Hb2) as [-> ->].
  split; reflexivity.
Qed.

Lemma repr_limits_det : det repr_limits.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  inversion H1; subst; inversion H2; subst; try discriminate;
    repeat det_step repr_u32_det; split; reflexivity.
Qed.

Lemma repr_memtype_det : det repr_memtype.
Proof. exact repr_limits_det. Qed.

Lemma repr_tabletype_det : det repr_tabletype.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  inversion H1; subst; inversion H2; subst.
  det_step repr_limits_det. split; reflexivity.
Qed.

Lemma repr_mut_det : det repr_mut.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  inversion H1; subst; inversion H2; subst; split; reflexivity.
Qed.

Lemma repr_globaltype_det : det repr_globaltype.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  inversion H1 as [bs1 t1 q1 m1 rest1 Ht1 Hm1]; subst.
  inversion H2 as [bs2 t2 q2 m2 rest2 Ht2 Hm2]; subst.
  destruct (repr_valtype_det _ _ _ _ _ Ht1 Ht2) as [-> ->].
  destruct (repr_mut_det _ _ _ _ _ Hm1 Hm2) as [-> ->].
  split; reflexivity.
Qed.

Lemma repr_idx_det : det repr_idx.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  inversion H1; subst; inversion H2; subst.
  det_step repr_u32_det. split; reflexivity.
Qed.

(** *** Sections *)

(** Two splits of the same list at the same length are the same split. This is
    what turns [repr_section]'s length premise into "the contents are pinned
    down". *)
Lemma app_split_det : forall (l1 r1 l2 r2 : list Z),
  l1 ++ r1 = l2 ++ r2 ->
  List.length l1 = List.length l2 ->
  l1 = l2 /\ r1 = r2.
Proof.
  induction l1 as [|a l1 IH]; intros r1 l2 r2 Heq Hlen.
  - destruct l2; [split; [reflexivity | exact Heq] | discriminate].
  - destruct l2 as [|b l2]; [discriminate|].
    injection Heq as -> Heq. injection Hlen as Hlen.
    destruct (IH _ _ _ Heq Hlen) as [-> ->]. split; reflexivity.
Qed.

Lemma repr_section_det : forall A (id : Z) (R : list Z -> A -> list Z -> Prop),
  det R -> det (repr_section id R).
Proof.
  intros A id R HR bs x1 r1 x2 r2 H1 H2.
  inversion H1 as [q0 s1 c1 y1 rest1 Hn1 Hl1 Hc1]; subst.
  inversion H2 as [q0' s2 c2 y2 rest2 Hn2 Hl2 Hc2]; subst.
  destruct (repr_u32_det _ _ _ _ _ Hn1 Hn2) as [Hs Happ].
  assert (List.length c1 = List.length c2) as Hlen by lia.
  destruct (app_split_det _ _ _ _ Happ Hlen) as [-> ->].
  destruct (HR _ _ _ _ _ Hc1 Hc2) as [-> _].
  split; reflexivity.
Qed.

Lemma repr_optsec_det : forall A (id : Z) (R : list Z -> A -> list Z -> Prop)
                               (absent : A),
  det R -> det (repr_optsec id R absent).
Proof.
  intros A id R absent HR bs x1 r1 x2 r2 H1 H2.
  (* A present section begins with its id, which the absent case forbids. *)
  inversion H1 as [bs1 y1 rest1 Hs1 | bs1 Hn1]; subst;
    inversion H2 as [bs2 y2 rest2 Hs2 | bs2 Hn2]; subst.
  - exact (repr_section_det _ _ _ HR _ _ _ _ _ Hs1 Hs2).
  - inversion Hs1; subst. exfalso. apply Hn2. eexists. reflexivity.
  - inversion Hs2; subst. exfalso. apply Hn1. eexists. reflexivity.
  - split; reflexivity.
Qed.

Lemma repr_custom_det : det repr_custom.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  destruct x1, x2.
  destruct H1 as [nm1 [mid1 [_ ->]]]. destruct H2 as [nm2 [mid2 [_ ->]]].
  split; reflexivity.
Qed.

Lemma repr_customs_det : forall bs r1 r2,
  repr_customs bs r1 -> repr_customs bs r2 -> r1 = r2.
Proof.
  intros bs r1 r2 H1. revert r2.
  induction H1 as [bs Hn | bs mid1 rest1 Hs1 Hc1 IH]; intros r2 H2.
  - inversion H2 as [bs2 Hn2 | bs2 mid2 rest2 Hs2 Hc2]; subst;
      [reflexivity|].
    inversion Hs2; subst. exfalso. apply Hn. eexists. reflexivity.
  - inversion H2 as [bs2 Hn2 | bs2 mid2 rest2 Hs2 Hc2]; subst.
    + inversion Hs1; subst. exfalso. apply Hn2. eexists. reflexivity.
    + destruct (repr_section_det _ _ _ repr_custom_det _ _ _ _ _ Hs1 Hs2)
        as [_ ->].
      exact (IH _ Hc2).
Qed.

Lemma repr_padded_det : forall A (id : Z) (R : list Z -> A -> list Z -> Prop)
                               (absent : A),
  det R -> det (repr_padded id R absent).
Proof.
  intros A id R absent HR bs x1 r1 x2 r2 [m1 [Hc1 Ho1]] [m2 [Hc2 Ho2]].
  rewrite (repr_customs_det _ _ _ Hc1 Hc2) in Ho1.
  exact (repr_optsec_det _ _ _ _ HR _ _ _ _ _ Ho1 Ho2).
Qed.

(** The module's chain, one section at a time. The lemma's arguments come out
    of the match rather than being written down, because [repr_padded]'s
    element type is only determined by the relation. An [Ltac] body resolves
    bare identifiers when it is defined, so this has to come after
    [repr_padded_det] rather than with the other tactics.

    It looks for two hypotheses of the same shape, so it declines to pair one
    with itself; when the relation it is handed does not fit the pair it found,
    [match goal] backtracks to the next pair. *)
Ltac det_padded L :=
  match goal with
  | [ Ha : repr_padded ?id ?R ?ab ?bs ?x1 ?r1,
      Hb : repr_padded ?id ?R ?ab ?bs ?x2 ?r2 |- _ ] =>
      tryif constr_eq Ha Hb then fail else
      destruct (repr_padded_det _ id R ab L _ _ _ _ _ Ha Hb) as [-> ->]
  end.

(** *** The sections' contents *)

Lemma repr_importdesc_det : det repr_importdesc.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  inversion H1; subst; inversion H2; subst; try discriminate;
    first [ det_step repr_idx_det
          | det_step repr_tabletype_det
          | det_step repr_memtype_det
          | det_step repr_globaltype_det ];
    split; reflexivity.
Qed.

Lemma repr_import_det : det repr_import.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  inversion H1 as [bs1 md1 q1 nm1 q1' d1 rest1 Hm1 Hn1 Hd1]; subst.
  inversion H2 as [bs2 md2 q2 nm2 q2' d2 rest2 Hm2 Hn2 Hd2]; subst.
  destruct (repr_name_det _ _ _ _ _ Hm1 Hm2) as [-> ->].
  destruct (repr_name_det _ _ _ _ _ Hn1 Hn2) as [-> ->].
  destruct (repr_importdesc_det _ _ _ _ _ Hd1 Hd2) as [-> ->].
  split; reflexivity.
Qed.

Lemma repr_table_det : det repr_table.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  inversion H1; subst; inversion H2; subst.
  det_step repr_tabletype_det. split; reflexivity.
Qed.

Lemma repr_mem_det : det repr_mem.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  inversion H1; subst; inversion H2; subst.
  det_step repr_memtype_det. split; reflexivity.
Qed.

(** Everything from here down goes through an expression, and an expression is
    self-delimiting rather than length-prefixed: the reader stops at the [end]
    that closes it. [Spec_Expr.repr_expr_det_rest] is what says that stopping
    place is unique even when bytes follow, which a global's initialiser and a
    segment's offset both need. *)
Definition expr_det : det repr_expr := repr_expr_det_rest.

Lemma repr_global_det : det repr_global.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  inversion H1 as [bs1 gt1 q1 e1 rest1 Hg1 He1]; subst.
  inversion H2 as [bs2 gt2 q2 e2 rest2 Hg2 He2]; subst.
  destruct (repr_globaltype_det _ _ _ _ _ Hg1 Hg2) as [-> ->].
  destruct (expr_det _ _ _ _ _ He1 He2) as [-> ->].
  split; reflexivity.
Qed.

Lemma repr_exportdesc_det : det repr_exportdesc.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  inversion H1; subst; inversion H2; subst; try discriminate;
    det_step repr_idx_det; split; reflexivity.
Qed.

Lemma repr_export_det : det repr_export.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  inversion H1 as [bs1 nm1 q1 d1 rest1 Hn1 Hd1]; subst.
  inversion H2 as [bs2 nm2 q2 d2 rest2 Hn2 Hd2]; subst.
  destruct (repr_name_det _ _ _ _ _ Hn1 Hn2) as [-> ->].
  destruct (repr_exportdesc_det _ _ _ _ _ Hd1 Hd2) as [-> ->].
  split; reflexivity.
Qed.

Lemma repr_start_det : det repr_start.
Proof.
  intros bs x1 r1 x2 r2 [y1 [Hy1 ->]] [y2 [Hy2 ->]].
  destruct (repr_idx_det _ _ _ _ _ Hy1 Hy2) as [-> ->].
  split; reflexivity.
Qed.

Lemma repr_elem_det : det repr_elem.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  inversion H1 as [bs1 y1 q1 e1 q1' ys1 rest1 Hy1 He1 Hv1]; subst.
  inversion H2 as [bs2 y2 q2 e2 q2' ys2 rest2 Hy2 He2 Hv2]; subst.
  destruct (repr_idx_det _ _ _ _ _ Hy1 Hy2) as [-> ->].
  destruct (expr_det _ _ _ _ _ He1 He2) as [-> ->].
  destruct (repr_vec_det _ _ repr_idx_det _ _ _ _ _ Hv1 Hv2) as [-> ->].
  split; reflexivity.
Qed.

Lemma repr_locals_det : det repr_locals.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  inversion H1 as [bs1 n1 q1 t1 rest1 Hn1 Ht1]; subst.
  inversion H2 as [bs2 n2 q2 t2 rest2 Hn2 Ht2]; subst.
  destruct (repr_u32_det _ _ _ _ _ Hn1 Hn2) as [-> ->].
  destruct (repr_valtype_det _ _ _ _ _ Ht1 Ht2) as [-> ->].
  split; reflexivity.
Qed.

Lemma repr_func_det : det repr_func.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  inversion H1 as [bs1 gs1 q1 e1 rest1 Hg1 He1]; subst.
  inversion H2 as [bs2 gs2 q2 e2 rest2 Hg2 He2]; subst.
  destruct (repr_vec_det _ _ repr_locals_det _ _ _ _ _ Hg1 Hg2) as [-> ->].
  destruct (expr_det _ _ _ _ _ He1 He2) as [-> ->].
  split; reflexivity.
Qed.

Lemma repr_code_det : det repr_code.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  inversion H1 as [bs1 s1 c1 y1 rest1 Hn1 Hl1 Hf1]; subst.
  inversion H2 as [bs2 s2 c2 y2 rest2 Hn2 Hl2 Hf2]; subst.
  destruct (repr_u32_det _ _ _ _ _ Hn1 Hn2) as [Hs Happ].
  assert (List.length c1 = List.length c2) as Hlen by lia.
  destruct (app_split_det _ _ _ _ Happ Hlen) as [-> ->].
  destruct (repr_func_det _ _ _ _ _ Hf1 Hf2) as [-> _].
  split; reflexivity.
Qed.

Lemma repr_data_det : det repr_data.
Proof.
  intros bs x1 r1 x2 r2 H1 H2.
  inversion H1 as [bs1 y1 q1 e1 q1' by1 rest1 Hy1 He1 Hb1]; subst.
  inversion H2 as [bs2 y2 q2 e2 q2' by2 rest2 Hy2 He2 Hb2]; subst.
  destruct (repr_idx_det _ _ _ _ _ Hy1 Hy2) as [-> ->].
  destruct (expr_det _ _ _ _ _ He1 He2) as [-> ->].
  destruct (repr_bytevec_det _ _ _ _ _ Hb1 Hb2) as [-> ->].
  split; reflexivity.
Qed.

Lemma repr_magic_version_det : forall bs r1 r2,
  repr_magic_version bs r1 -> repr_magic_version bs r2 -> r1 = r2.
Proof.
  unfold repr_magic_version. intros bs r1 r2 -> H.
  injection H. auto.
Qed.

Lemma funcs_of_det : forall xs cs fs1 fs2,
  funcs_of xs cs fs1 -> funcs_of xs cs fs2 -> fs1 = fs2.
Proof.
  intros xs cs fs1 fs2 H1. revert fs2.
  induction H1 as [| x xs' lcls e cs' fs' H1 IH]; intros fs2 H2.
  - inversion H2; reflexivity.
  - inversion H2 as [| x2 xs2 lcls2 e2 cs2 fs2' H2']; subst.
    rewrite (IH _ H2'). reflexivity.
Qed.

(** The theorem. Every premise of [repr_module_intro] is deterministic, so the
    positions and the values march in step from the magic number to the end. *)
Theorem repr_module_det : forall bs m1 m2,
  repr_module bs m1 -> repr_module bs m2 -> m1 = m2.
Proof.
  intros bs m1 m2 H1 H2.
  destruct H1. destruct H2.
  match goal with
  | [ Ha : repr_magic_version ?b ?u, Hb : repr_magic_version ?b ?v |- _ ] =>
      rewrite (repr_magic_version_det _ _ _ Ha Hb) in *
  end.
  det_padded (repr_vec_det _ _ repr_functype_det).
  det_padded (repr_vec_det _ _ repr_import_det).
  det_padded (repr_vec_det _ _ repr_idx_det).
  det_padded (repr_vec_det _ _ repr_table_det).
  det_padded (repr_vec_det _ _ repr_mem_det).
  det_padded (repr_vec_det _ _ repr_global_det).
  det_padded (repr_vec_det _ _ repr_export_det).
  det_padded repr_start_det.
  det_padded (repr_vec_det _ _ repr_elem_det).
  det_padded (repr_vec_det _ _ repr_code_det).
  det_padded (repr_vec_det _ _ repr_data_det).
  match goal with
  | [ Ha : funcs_of ?x ?c ?f1, Hb : funcs_of ?x ?c ?f2 |- _ ] =>
      rewrite (funcs_of_det _ _ _ _ Ha Hb)
  end.
  reflexivity.
Qed.

(* ================================================================== *)
(** ** Reading a prefix                                                *)
(* ================================================================== *)

(** The companion to determinism, and the property [repr_section] needs to be
    usable: every rule consumes a prefix of its input and does not look past
    it. [Spec_Binary.reads_prefix] states it, and the note there says why
    determinism does not imply it.

    Only the relations that appear as a *section's contents* need it, because
    that is the one place a rule is stated over a shorter stream than the one
    it was read out of. [repr_optsec] deliberately does not have it, and
    cannot: its absent case is a statement about what follows. *)

Lemma repr_rep_prefix : forall A (R : list Z -> A -> list Z -> Prop),
  reads_prefix R -> forall n, reads_prefix (repr_rep R n).
Proof.
  intros A R HR n bs xs rest H.
  induction H as [bs | n bs x mid xs rest Hx Hrec IH].
  - exists []. split; [reflexivity|]. intros rest'. apply repr_rep_nil.
  - destruct (HR _ _ _ Hx) as [pre1 [Heq1 Hall1]].
    destruct IH as [pre2 [Heq2 Hall2]].
    exists (pre1 ++ pre2). split.
    + rewrite Heq1. rewrite Heq2. rewrite <- app_assoc. reflexivity.
    + intros rest'. rewrite <- app_assoc.
      apply repr_rep_cons with (mid := pre2 ++ rest');
        [apply Hall1 | apply Hall2].
Qed.

Lemma repr_vec_prefix : forall A (R : list Z -> A -> list Z -> Prop),
  reads_prefix R -> reads_prefix (repr_vec R).
Proof.
  intros A R HR bs xs rest H.
  inversion H as [bs0 n mid xs0 rest0 Hn Hrep]; subst.
  destruct (repr_u32_prefix _ _ _ Hn) as [pre1 [Heq1 Hall1]].
  destruct (repr_rep_prefix _ _ HR _ _ _ _ Hrep) as [pre2 [Heq2 Hall2]].
  exists (pre1 ++ pre2). split.
  - rewrite Heq1. rewrite Heq2. rewrite <- app_assoc. reflexivity.
  - intros rest'. rewrite <- app_assoc.
    apply repr_vec_intro with (n := n) (mid := pre2 ++ rest');
      [apply Hall1 | apply Hall2].
Qed.

(** A one-byte rule, which most of the type rules are. *)
Ltac prefix_byte b ctor :=
  exists [b]; split; [reflexivity|]; intros rest'; cbn; apply ctor;
  assumption.

Lemma repr_byte_prefix : reads_prefix repr_byte.
Proof.
  intros bs x rest H. inversion H; subst.
  prefix_byte x repr_byte_intro.
Qed.

Lemma repr_valtype_prefix : reads_prefix repr_valtype.
Proof.
  intros bs x rest H. inversion H as [b vt rest0 Hspec]; subst.
  prefix_byte b repr_valtype_intro.
Qed.

Lemma repr_resulttype_prefix : reads_prefix repr_resulttype.
Proof. exact (repr_vec_prefix _ _ repr_valtype_prefix). Qed.

Lemma repr_functype_prefix : reads_prefix repr_functype.
Proof.
  intros bs x rest H. inversion H as [p0 p1 t1 t2 rest0 H1 H2]; subst.
  destruct (repr_resulttype_prefix _ _ _ H1) as [pre1 [Heq1 Hall1]].
  destruct (repr_resulttype_prefix _ _ _ H2) as [pre2 [Heq2 Hall2]].
  exists (96 :: pre1 ++ pre2). split.
  - cbn. rewrite Heq1. rewrite Heq2. rewrite <- app_assoc. reflexivity.
  - intros rest'. cbn. rewrite <- app_assoc.
    apply repr_functype_intro with (p1 := pre2 ++ rest');
      [apply Hall1 | apply Hall2].
Qed.

Lemma repr_limits_prefix : reads_prefix repr_limits.
Proof.
  intros bs x rest H.
  inversion H as [p0 n rest0 Hn | p0 n p1 m rest0 Hn Hm]; subst.
  - destruct (repr_u32_prefix _ _ _ Hn) as [pre [Heq Hall]].
    exists (0 :: pre). split; [cbn; rewrite Heq; reflexivity|].
    intros rest'. cbn. apply repr_limits_open. apply Hall.
  - destruct (repr_u32_prefix _ _ _ Hn) as [pre1 [Heq1 Hall1]].
    destruct (repr_u32_prefix _ _ _ Hm) as [pre2 [Heq2 Hall2]].
    exists (1 :: pre1 ++ pre2). split.
    + cbn. rewrite Heq1. rewrite Heq2. rewrite <- app_assoc. reflexivity.
    + intros rest'. cbn. rewrite <- app_assoc.
      apply repr_limits_closed with (p1 := pre2 ++ rest');
        [apply Hall1 | apply Hall2].
Qed.

Lemma repr_memtype_prefix : reads_prefix repr_memtype.
Proof. exact repr_limits_prefix. Qed.

Lemma repr_tabletype_prefix : reads_prefix repr_tabletype.
Proof.
  intros bs x rest H. inversion H as [p0 lim rest0 Hlim]; subst.
  destruct (repr_limits_prefix _ _ _ Hlim) as [pre [Heq Hall]].
  exists (112 :: pre). split; [cbn; rewrite Heq; reflexivity|].
  intros rest'. cbn. apply repr_tabletype_intro. apply Hall.
Qed.

Lemma repr_mut_prefix : reads_prefix repr_mut.
Proof.
  intros bs x rest H. inversion H; subst.
  - prefix_byte 0 repr_mut_const.
  - prefix_byte 1 repr_mut_var.
Qed.

Lemma repr_globaltype_prefix : reads_prefix repr_globaltype.
Proof.
  intros bs x rest H. inversion H as [bs0 t p1 m rest0 Ht Hm]; subst.
  destruct (repr_valtype_prefix _ _ _ Ht) as [pre1 [Heq1 Hall1]].
  destruct (repr_mut_prefix _ _ _ Hm) as [pre2 [Heq2 Hall2]].
  exists (pre1 ++ pre2). split.
  - rewrite Heq1. rewrite Heq2. rewrite <- app_assoc. reflexivity.
  - intros rest'. rewrite <- app_assoc.
    apply repr_globaltype_intro with (p1 := pre2 ++ rest');
      [apply Hall1 | apply Hall2].
Qed.

Lemma repr_idx_prefix : reads_prefix repr_idx.
Proof.
  intros bs x rest H. inversion H as [bs0 y rest0 Hy]; subst.
  destruct (repr_u32_prefix _ _ _ Hy) as [pre [Heq Hall]].
  exists pre. split; [exact Heq|].
  intros rest'. apply repr_idx_intro. apply Hall.
Qed.

(** A name and a byte vector are both [vec(byte)] with a side condition on the
    bytes, and neither side condition mentions the remainder. *)
Lemma repr_name_prefix : reads_prefix repr_name.
Proof.
  intros bs nm rest H. inversion H as [bs0 zs nm0 rest0 Hv Hf Hu]; subst.
  destruct (repr_vec_prefix _ _ repr_byte_prefix _ _ _ Hv)
    as [pre [Heq Hall]].
  exists pre. split; [exact Heq|].
  intros rest'. apply repr_name_intro with (zs := zs);
    [apply Hall | exact Hf | exact Hu].
Qed.

Lemma repr_bytevec_prefix : reads_prefix repr_bytevec.
Proof.
  intros bs bys rest H. inversion H as [bs0 zs bys0 rest0 Hv Hf]; subst.
  destruct (repr_vec_prefix _ _ repr_byte_prefix _ _ _ Hv)
    as [pre [Heq Hall]].
  exists pre. split; [exact Heq|].
  intros rest'. apply repr_bytevec_intro with (zs := zs);
    [apply Hall | exact Hf].
Qed.

Lemma repr_importdesc_prefix : reads_prefix repr_importdesc.
Proof.
  intros bs d rest H.
  inversion H as [p0 x rest0 Hd | p0 tt0 rest0 Hd
                 | p0 mt rest0 Hd | p0 gt rest0 Hd]; subst.
  - destruct (repr_idx_prefix _ _ _ Hd) as [pre [Heq Hall]].
    exists (0 :: pre). split; [cbn; rewrite Heq; reflexivity|].
    intros rest'. cbn. apply repr_importdesc_func. apply Hall.
  - destruct (repr_tabletype_prefix _ _ _ Hd) as [pre [Heq Hall]].
    exists (1 :: pre). split; [cbn; rewrite Heq; reflexivity|].
    intros rest'. cbn. apply repr_importdesc_table. apply Hall.
  - destruct (repr_memtype_prefix _ _ _ Hd) as [pre [Heq Hall]].
    exists (2 :: pre). split; [cbn; rewrite Heq; reflexivity|].
    intros rest'. cbn. apply repr_importdesc_mem. apply Hall.
  - destruct (repr_globaltype_prefix _ _ _ Hd) as [pre [Heq Hall]].
    exists (3 :: pre). split; [cbn; rewrite Heq; reflexivity|].
    intros rest'. cbn. apply repr_importdesc_global. apply Hall.
Qed.

Lemma repr_import_prefix : reads_prefix repr_import.
Proof.
  intros bs im rest H.
  inversion H as [bs0 md p1 nm p2 d rest0 Hmd Hnm Hd]; subst.
  destruct (repr_name_prefix _ _ _ Hmd) as [pre1 [Heq1 Hall1]].
  destruct (repr_name_prefix _ _ _ Hnm) as [pre2 [Heq2 Hall2]].
  destruct (repr_importdesc_prefix _ _ _ Hd) as [pre3 [Heq3 Hall3]].
  exists (pre1 ++ pre2 ++ pre3). split.
  - rewrite Heq1. rewrite Heq2. rewrite Heq3.
    repeat rewrite <- app_assoc. reflexivity.
  - intros rest'. repeat rewrite <- app_assoc.
    apply repr_import_intro with (p1 := pre2 ++ pre3 ++ rest')
                            (p2 := pre3 ++ rest').
    + apply Hall1.
    + apply Hall2.
    + apply Hall3.
Qed.

Lemma repr_table_prefix : reads_prefix repr_table.
Proof.
  intros bs t rest H. inversion H as [bs0 tt0 rest0 Ht]; subst.
  destruct (repr_tabletype_prefix _ _ _ Ht) as [pre [Heq Hall]].
  exists pre. split; [exact Heq|].
  intros rest'. apply repr_table_intro. apply Hall.
Qed.

Lemma repr_mem_prefix : reads_prefix repr_mem.
Proof.
  intros bs m rest H. inversion H as [bs0 mt rest0 Hm]; subst.
  destruct (repr_memtype_prefix _ _ _ Hm) as [pre [Heq Hall]].
  exists pre. split; [exact Heq|].
  intros rest'. apply repr_mem_intro. apply Hall.
Qed.

Lemma repr_global_prefix : reads_prefix repr_global.
Proof.
  intros bs g rest H. inversion H as [bs0 gt p1 e rest0 Hgt He]; subst.
  destruct (repr_globaltype_prefix _ _ _ Hgt) as [pre1 [Heq1 Hall1]].
  destruct (repr_expr_prefix _ _ _ He) as [pre2 [Heq2 Hall2]].
  exists (pre1 ++ pre2). split.
  - rewrite Heq1. rewrite Heq2. rewrite <- app_assoc. reflexivity.
  - intros rest'. rewrite <- app_assoc.
    apply repr_global_intro with (p1 := pre2 ++ rest');
      [apply Hall1 | apply Hall2].
Qed.

Lemma repr_exportdesc_prefix : reads_prefix repr_exportdesc.
Proof.
  intros bs d rest H.
  inversion H as [p0 x rest0 Hd | p0 x rest0 Hd
                 | p0 x rest0 Hd | p0 x rest0 Hd]; subst.
  1: destruct (repr_idx_prefix _ _ _ Hd) as [pre [Heq Hall]];
     exists (0 :: pre); split; [cbn; rewrite Heq; reflexivity|];
     intros rest'; cbn; apply repr_exportdesc_func; apply Hall.
  1: destruct (repr_idx_prefix _ _ _ Hd) as [pre [Heq Hall]];
     exists (1 :: pre); split; [cbn; rewrite Heq; reflexivity|];
     intros rest'; cbn; apply repr_exportdesc_table; apply Hall.
  1: destruct (repr_idx_prefix _ _ _ Hd) as [pre [Heq Hall]];
     exists (2 :: pre); split; [cbn; rewrite Heq; reflexivity|];
     intros rest'; cbn; apply repr_exportdesc_mem; apply Hall.
  1: destruct (repr_idx_prefix _ _ _ Hd) as [pre [Heq Hall]];
     exists (3 :: pre); split; [cbn; rewrite Heq; reflexivity|];
     intros rest'; cbn; apply repr_exportdesc_global; apply Hall.
Qed.

Lemma repr_export_prefix : reads_prefix repr_export.
Proof.
  intros bs ex rest H. inversion H as [bs0 nm p1 d rest0 Hnm Hd]; subst.
  destruct (repr_name_prefix _ _ _ Hnm) as [pre1 [Heq1 Hall1]].
  destruct (repr_exportdesc_prefix _ _ _ Hd) as [pre2 [Heq2 Hall2]].
  exists (pre1 ++ pre2). split.
  - rewrite Heq1. rewrite Heq2. rewrite <- app_assoc. reflexivity.
  - intros rest'. rewrite <- app_assoc.
    apply repr_export_intro with (p1 := pre2 ++ rest');
      [apply Hall1 | apply Hall2].
Qed.

Lemma repr_start_prefix : reads_prefix repr_start.
Proof.
  intros bs s rest [x [Hx ->]].
  destruct (repr_idx_prefix _ _ _ Hx) as [pre [Heq Hall]].
  exists pre. split; [exact Heq|].
  intros rest'. exists x. split; [apply Hall | reflexivity].
Qed.

Lemma repr_elem_prefix : reads_prefix repr_elem.
Proof.
  intros bs el rest H.
  inversion H as [bs0 x p1 e p2 ys rest0 Hx He Hys]; subst.
  destruct (repr_idx_prefix _ _ _ Hx) as [pre1 [Heq1 Hall1]].
  destruct (repr_expr_prefix _ _ _ He) as [pre2 [Heq2 Hall2]].
  destruct (repr_vec_prefix _ _ repr_idx_prefix _ _ _ Hys)
    as [pre3 [Heq3 Hall3]].
  exists (pre1 ++ pre2 ++ pre3). split.
  - rewrite Heq1. rewrite Heq2. rewrite Heq3.
    repeat rewrite <- app_assoc. reflexivity.
  - intros rest'. repeat rewrite <- app_assoc.
    apply repr_elem_intro with (p1 := pre2 ++ pre3 ++ rest')
                          (p2 := pre3 ++ rest').
    + apply Hall1.
    + apply Hall2.
    + apply Hall3.
Qed.

Lemma repr_locals_prefix : reads_prefix repr_locals.
Proof.
  intros bs ts rest H. inversion H as [bs0 n p1 t rest0 Hn Ht]; subst.
  destruct (repr_u32_prefix _ _ _ Hn) as [pre1 [Heq1 Hall1]].
  destruct (repr_valtype_prefix _ _ _ Ht) as [pre2 [Heq2 Hall2]].
  exists (pre1 ++ pre2). split.
  - rewrite Heq1. rewrite Heq2. rewrite <- app_assoc. reflexivity.
  - intros rest'. rewrite <- app_assoc.
    apply repr_locals_intro with (p1 := pre2 ++ rest');
      [apply Hall1 | apply Hall2].
Qed.

(** A code entry is framed the way a section is, and the framing is where the
    prefix comes from: the size prefix reads up to the contents, and the
    contents are pinned by their length. *)
Lemma repr_code_prefix : reads_prefix repr_code.
Proof.
  intros bs c rest H.
  inversion H as [bs0 size content c0 rest0 Hn Hlen Hf]; subst.
  destruct (repr_u32_prefix _ _ _ Hn) as [pre [Heq Hall]].
  exists (pre ++ content). split.
  - rewrite Heq. rewrite <- app_assoc. reflexivity.
  - intros rest'. rewrite <- app_assoc.
    (* [subst] used the length premise, so the size is spelt out here *)
    apply repr_code_intro with (size := Z.of_nat (List.length content))
                               (content := content);
      [apply Hall | reflexivity | exact Hf].
Qed.

Lemma repr_data_prefix : reads_prefix repr_data.
Proof.
  intros bs d rest H.
  inversion H as [bs0 x p1 e p2 bys rest0 Hx He Hb]; subst.
  destruct (repr_idx_prefix _ _ _ Hx) as [pre1 [Heq1 Hall1]].
  destruct (repr_expr_prefix _ _ _ He) as [pre2 [Heq2 Hall2]].
  destruct (repr_bytevec_prefix _ _ _ Hb) as [pre3 [Heq3 Hall3]].
  exists (pre1 ++ pre2 ++ pre3). split.
  - rewrite Heq1. rewrite Heq2. rewrite Heq3.
    repeat rewrite <- app_assoc. reflexivity.
  - intros rest'. repeat rewrite <- app_assoc.
    apply repr_data_intro with (p1 := pre2 ++ pre3 ++ rest')
                          (p2 := pre3 ++ rest').
    + apply Hall1.
    + apply Hall2.
    + apply Hall3.
Qed.

(* ================================================================== *)
(** ** Transcription cross-checks                                      *)
(* ================================================================== *)

(** Concrete decodings, checked against the specification by hand. These are
    not proofs about the validator; they are here so that a transcription
    error has a chance of showing up as a failing example rather than as a
    silently wrong rule. [Spec_Binary.v] carries the same kind of table for
    instructions. *)

(** [leb_last], [leb_more] and [crunch_pow] come from [Spec_Binary.v]. *)
Ltac dec_u32 := unfold repr_u32; leb_last.
Ltac dec_valtype := apply repr_valtype_intro; reflexivity.

(** No section of this id starts here, which is the side condition on every
    absent section and on the end of a run of custom sections. *)
Ltac no_more := intros [more Hm]; discriminate.

(** One line of the module production: an empty run of custom sections, then
    either the section or its absence. [present] takes the section's contents,
    which is what pins the split [repr_section] asks for. *)
Ltac absent :=
  eexists; split;
  [ apply repr_customs_done; no_more | apply repr_optsec_absent; no_more ].

Ltac present c :=
  eexists; split;
  [ apply repr_customs_done; no_more
  | apply repr_optsec_present;
    eapply repr_section_intro with (content := c);
    [ dec_u32 | reflexivity | ] ].

(** An index, and vectors of nought and one element. The index has to be given
    because the rule produces [Z.to_N x]. *)
Ltac dec_idx x := apply (repr_idx_intro _ x); dec_u32.

Ltac vec0 := eapply repr_vec_intro with (n := 0); [dec_u32 | apply repr_rep_nil].

Ltac vec1 := eapply repr_vec_intro with (n := 1); [dec_u32 | cbn];
             eapply repr_rep_cons; [| apply repr_rep_nil].

(** The empty module: magic and version and nothing else. Spec 5.5.16's
    smallest well-formed input. Eleven absent sections and twelve empty runs
    of custom sections, which is the framing exercised end to end. *)
Example ex_empty_module :
  repr_module [0; 97; 115; 109; 1; 0; 0; 0]
    {| mod_types := []; mod_funcs := []; mod_tables := []; mod_mems := [];
       mod_globals := []; mod_elems := []; mod_datas := []; mod_start := None;
       mod_imports := []; mod_exports := [] |}.
Proof.
  eapply repr_module_intro; try reflexivity.
  all: first [ apply funcs_of_nil | apply repr_customs_done; no_more | absent ].
Qed.

(** 5.3.4: [0x00 0x01] is the open limits with minimum one, and
    [0x01 0x01 0x02] is the closed one from one to two. *)
Example ex_limits_open :
  repr_limits [0; 1] {| lim_min := 1%N; lim_max := None |} [].
Proof. apply (repr_limits_open [1] 1 []). dec_u32. Qed.

Example ex_limits_closed :
  repr_limits [1; 1; 2] {| lim_min := 1%N; lim_max := Some 2%N |} [].
Proof. apply (repr_limits_closed [1; 2] 1 [2] 2 []); dec_u32. Qed.

(** 5.3.6: [0x70 0x00 0x01] is a table of at least one [funcref]. *)
Example ex_tabletype :
  repr_tabletype [112; 0; 1]
    {| tt_limits := {| lim_min := 1%N; lim_max := None |};
       tt_elem_type := T_funcref |} [].
Proof. apply repr_tabletype_intro. apply ex_limits_open. Qed.

(** 5.3.8: [0x7F 0x01] is a mutable i32 global, [0x7F 0x00] an immutable one. *)
Example ex_globaltype_var :
  repr_globaltype [127; 1] {| tg_mut := MUT_var; tg_t := T_num T_i32 |} [].
Proof.
  eapply repr_globaltype_intro; [dec_valtype | apply repr_mut_var].
Qed.

Example ex_globaltype_const :
  repr_globaltype [127; 0] {| tg_mut := MUT_const; tg_t := T_num T_i32 |} [].
Proof.
  eapply repr_globaltype_intro; [dec_valtype | apply repr_mut_const].
Qed.

(** 5.3.3: [0x60 0x01 0x7F 0x01 0x7E] is [[i32] -> [i64]]. *)
Example ex_functype :
  repr_functype [96; 1; 127; 1; 126]
    (Tf [T_num T_i32] [T_num T_i64]) [].
Proof.
  apply repr_functype_intro with (p1 := [1; 126]); vec1; dec_valtype.
Qed.

(** 5.4.9: the empty expression is the single byte [0x0B]. *)
Lemma ex_expr_empty : repr_expr [11] [] [].
Proof.
  exists [FO_end]. split; [apply else_sugar_refl|].
  eapply repr_ops_cons; [|apply repr_ops_nil].
  apply repr_op_end. reflexivity.
Qed.

(** 5.5.13: [0x02 0x00 0x0B] is a code entry of two bytes holding no locals and
    the empty expression. The size prefix has to agree with the contents, which
    is the point of the example. *)
Example ex_code_empty :
  repr_code [2; 0; 11] ([], []) [].
Proof.
  apply repr_code_intro with (size := 2) (content := [0; 11]).
  - dec_u32.
  - reflexivity.
  - apply repr_func_intro with (gs := []) (p1 := [11]).
    + vec0.
    + apply ex_expr_empty.
Qed.

(** 5.5.13 again, with locals: [0x01 0x02 0x7F] declares two i32 locals in one
    group, so [locals ::= n:u32 t:valtype => t^n] has to repeat the type. *)
Example ex_code_locals :
  repr_code [4; 1; 2; 127; 11] ([T_num T_i32; T_num T_i32], []) [].
Proof.
  apply repr_code_intro with (size := 4) (content := [1; 2; 127; 11]).
  - dec_u32.
  - reflexivity.
  - apply repr_func_intro
      with (gs := [[T_num T_i32; T_num T_i32]]) (p1 := [11]).
    + vec1. apply repr_locals_intro with (n := 2) (p1 := [127; 11]);
        [dec_u32 | dec_valtype].
    + apply ex_expr_empty.
Qed.

(** 5.2.4: the two-byte name "hi". *)
Example ex_name_hi :
  repr_name [2; 104; 105] [Byte.x68; Byte.x69] [].
Proof.
  apply repr_name_intro with (zs := [104; 105]).
  - eapply repr_vec_intro with (n := 2); [dec_u32|].
    cbn. eapply repr_rep_cons; [constructor; lia|].
    eapply repr_rep_cons; [constructor; lia | apply repr_rep_nil].
  - repeat constructor.
  - apply utf8_one; [lia|]. apply utf8_one; [lia|]. apply utf8_nil.
Qed.

(** 5.2.4's side condition has teeth: [0xC0 0x80] is the overlong encoding of
    U+0000, which is a byte sequence but not a name. The two-byte range starts
    at [0xC2] precisely to exclude it. *)
Example ex_utf8_rejects_overlong : ~ utf8_valid [192; 128].
Proof. intros H; inversion H; lia. Qed.

(** And the surrogate range: [0xED 0xA0 0x80] would be U+D800. *)
Example ex_utf8_rejects_surrogate : ~ utf8_valid [237; 160; 128].
Proof. intros H; inversion H; lia. Qed.

(** While the three-byte sequence just below it is fine: U+D7FF. *)
Example ex_utf8_accepts_d7ff : utf8_valid [237; 159; 191].
Proof. apply utf8_three_ed; [lia | lia | apply utf8_nil]. Qed.

(* ================================================================== *)
(** ** The 1.0-into-2.0 embedding                                      *)
(* ================================================================== *)

(** The header describes how a 1.0 element segment lands in the 2.0 [module]
    type. That reshaping is the second thing this file has to get right, and it
    is not something determinism can catch: a wrong but self-consistent
    embedding would still be deterministic, and would simply produce modules
    the 2.0 type system rejects. So it is checked against the type system
    instead, on a module small enough to read and large enough to exercise the
    reshaping.

    One function of type [[] -> []], one table, and one element segment putting
    that function in the table. This is the smallest 1.0 module in which a
    [funcidx] vector appears at all, so it is the smallest one where the
    embedding does any work.

    The segment's function index is a parameter so that the two checks below
    differ in exactly one place. *)
Definition ex_wasm10_module (y : N) : module :=
  {| mod_types   := [Tf [] []];
     mod_funcs   := [{| modfunc_type := 0%N; modfunc_locals := [];
                        modfunc_body := [] |}];
     mod_tables  := [{| modtab_type :=
                          {| tt_limits := {| lim_min := 1%N; lim_max := None |};
                             tt_elem_type := T_funcref |} |}];
     mod_mems    := [];
     mod_globals := [];
     mod_elems   := [{| modelem_type := T_funcref;
                        modelem_init := [[BI_ref_func y]];
                        modelem_mode :=
                          ME_active 0%N
                            [BI_const_num (VAL_int32 (Wasm_int.Int32.repr 0))] |}];
     mod_datas   := [];
     mod_start   := None;
     mod_imports := [];
     mod_exports := [] |}.

(** The bytes, section by section:

      00 61 73 6D 01 00 00 00     magic, version
      01 04  01 60 00 00          type:     one [] -> []
      03 02  01 00                function: one, of type 0
      04 04  01 70 00 01          table:    one funcref table, min 1
      09 07  01 00 41 00 0B 01 00 element:  table 0, offset i32.const 0, [0]
      0A 04  01 02 00 0B          code:     one entry, no locals, empty body

    Six present sections and five absent ones, so the framing and the
    not-this-id side condition are both exercised at every position. *)
Example ex_wasm10_decode :
  repr_module
    [0; 97; 115; 109; 1; 0; 0; 0;
     1; 4; 1; 96; 0; 0;
     3; 2; 1; 0;
     4; 4; 1; 112; 0; 1;
     9; 7; 1; 0; 65; 0; 11; 1; 0;
     10; 4; 1; 2; 0; 11]
    (ex_wasm10_module 0).
Proof.
  unfold ex_wasm10_module.
  eapply repr_module_intro.
  - reflexivity.
  - present [1; 96; 0; 0].
    vec1. apply repr_functype_intro with (p1 := [0]); vec0.
  - absent.
  - present [1; 0].
    vec1. dec_idx 0.
  - present [1; 112; 0; 1].
    vec1. apply repr_table_intro. apply ex_tabletype.
  - absent.
  - absent.
  - absent.
  - absent.
  - present [1; 0; 65; 0; 11; 1; 0].
    vec1. apply repr_elem_intro
            with (ys := [0%N]) (p1 := [65; 0; 11; 1; 0]) (p2 := [1; 0]).
    + dec_idx 0.
    + exists [FO_plain (BI_const_num (VAL_int32 (Wasm_int.Int32.repr 0))); FO_end].
      split; [apply else_sugar_refl|].
      eapply repr_ops_cons.
      * apply repr_op_const with (nt := T_i32) (z := 0); [reflexivity|].
        cbn [const_bits]. apply repr_sN_pos; [lia | crunch_pow].
      * eapply repr_ops_cons; [apply repr_op_end; reflexivity | apply repr_ops_nil].
    + vec1. dec_idx 0.
  - present [1; 2; 0; 11].
    vec1. apply repr_code_intro with (size := 2) (content := [0; 11]).
    + dec_u32.
    + reflexivity.
    + apply repr_func_intro with (gs := []) (e := []) (p1 := [11]).
      * vec0.
      * apply ex_expr_empty.
  - absent.
  - apply repr_customs_done; no_more.
  - apply funcs_of_cons, funcs_of_nil.
Qed.

(** [module_type_checker] is host-parameterised because it lives in a section
    with the rest of the executable instantiation. Its result does not depend on
    the host, so an abstract instance is enough to compute with. *)
Section Embedding.

Context `{ho: host}.

(** The module the bytes above decode to is a well-typed 2.0 module. In
    particular [BI_ref_func 0] typechecks, which needs [0] to be in [tc_refs],
    which [module_filter_funcidx] puts there because the element segment
    mentions it. Nothing else in a 1.0 module can produce a [BI_ref_func], so
    that is the whole of the obligation the embedding creates. *)
Example ex_wasm10_typechecks :
  module_type_checker (ex_wasm10_module 0) = Some ([], []).
Proof. vm_compute. reflexivity. Qed.

(** And it has teeth: naming a function that does not exist is rejected. The
    index reaches the type system as [BI_ref_func 99], whose rule looks it up in
    [tc_funcs] first. An embedding that dropped the indices on the floor would
    pass the check above and fail this one. *)
Example ex_wasm10_bad_funcidx :
  module_type_checker (ex_wasm10_module 99) = None.
Proof. vm_compute. reflexivity. Qed.

End Embedding.
