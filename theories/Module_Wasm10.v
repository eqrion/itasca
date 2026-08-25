(** * The Wasm 1.0 side conditions, from the type checker

    [Module_Complete.validate_module_complete] says the validator accepts every
    module binary satisfying [module_wasm10]. This file discharges that premise
    from WasmCert's own [module_type_checker], leaving only what Wasm 1.0
    restricts and Wasm 2.0 does not: one result per function type, one table,
    one memory. That is [module_1_0], and it is three lines.

    The work splits in two, and the split is the point.

    Everything the *type system* decides is one of [module_type_checker]'s
    thirteen obligations read backwards, and the map is the same one
    [Module_Typing.v] uses in the other direction. Each is short: the checker
    succeeded, so every lookup it made is a range fact and every boolean it
    tested is a check the validator also makes.

    Everything the *encoding* decides comes off [repr_module_fit], which is why
    the derivation is a premise here. Three premises of [module_wasm10] are of
    that kind and no amount of typing supplies them: an initialiser is one
    instruction the binary format has an opcode for, an element segment is
    active with [ref.func] entries, and a local is one of the four number
    types.

    The one argument with content is spec 3.4.10's: a constant expression typed
    [[] -> [t]] has exactly one instruction in it, because every constant
    instruction pushes one value and consumes none. That is what lets
    [decode_const_expr] be a one-instruction reader rather than a mode of
    [opiter]. *)

Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Import Itasca.Aeneas_Specs.
Require Import Itasca.Translate.
Require Import Itasca.Spec_Binary.
Require Import Itasca.Spec_Expr.
Require Import Itasca.Spec_Module.
Require Import Itasca.OpIter_Decode.
Require Import Itasca.OpIter_Complete.
Require Import Itasca.Module_NoPanic.
Require Import Itasca.Module_Sound.
Require Import Itasca.Module_Typing.
Require Import Itasca.Module_Complete.

From Wasm Require Import datatypes datatypes_properties list_extra
                         operations typing type_checker
                         instantiation_spec instantiation_func.
Require Import Itasca.Wasm_Bridge.

Local Open Scope list_scope.
Open Scope Z_scope.

(* ================================================================== *)
(** ** How wide a LEB128 immediate can be                              *)
(* ================================================================== *)

(** The format's own bound on what a [uN] or an [sN] can hold, which is what
    turns a value the derivation names into a scalar the extraction can hold.
    [repr_bytes_le_bound] is already in [Spec_Binary.v]; these two are its
    twins for the two LEB128 readers. *)
Lemma repr_uN_bound : forall bits bs v rest,
  repr_uN bits bs v rest -> 0 <= v < 2 ^ Z.of_nat bits.
Proof.
  intros bits bs v rest H.
  induction H as [bits b rest Hb Hlt | bits b more m rest Hb H7 Hsub IH];
    [lia|].
  assert (Hstep : 2 ^ Z.of_nat bits = 128 * 2 ^ Z.of_nat (bits - 7)).
  { rewrite Nat2Z.inj_sub by lia. cbn [Z.of_nat].
    replace (Z.of_nat bits) with (7 + (Z.of_nat bits - 7)) at 1 by lia.
    rewrite Z.pow_add_r by lia. reflexivity. }
  lia.
Qed.

Lemma repr_sN_bound : forall bits bs v rest,
  repr_sN bits bs v rest ->
  - (2 ^ (Z.of_nat bits - 1)) <= v < 2 ^ (Z.of_nat bits - 1).
Proof.
  intros bits bs v rest H.
  induction H as [bits b rest Hb Hlt | bits b rest Hb Hge
                 | bits b more m rest Hb H7 Hsub IH].
  - pose proof (Z.pow_nonneg 2 (Z.of_nat bits - 1) (ltac:(lia))). lia.
  - pose proof (Z.pow_nonneg 2 (Z.of_nat bits - 1) (ltac:(lia))). lia.
  - assert (Hstep : 2 ^ (Z.of_nat bits - 1)
                    = 128 * 2 ^ (Z.of_nat (bits - 7) - 1)).
    { rewrite Nat2Z.inj_sub by lia. cbn [Z.of_nat].
      replace (Z.of_nat bits - 1) with (7 + (Z.of_nat bits - 7 - 1)) at 1
        by lia.
      rewrite Z.pow_add_r by lia. reflexivity. }
    lia.
Qed.

(** Building the scalar the extraction holds from the value the derivation
    names. The bounds are the reader's own, so every one of these is the
    format's [uN]/[sN]/byte-run bound read as a range. *)
Lemma scalar_of_Z : forall ty z,
  scalar_min ty <= z <= scalar_max ty -> exists s : scalar ty, to_Z s = z.
Proof.
  intros ty z H. destruct (mk_scalar_ok_of_bounds ty z H) as [s [_ Hs]].
  exists s. exact Hs.
Qed.

Lemma i32_min_val : scalar_min I32 = -2147483648. Proof. reflexivity. Qed.
Lemma i32_max_val : scalar_max I32 = 2147483647. Proof. reflexivity. Qed.
Lemma i64_min_val : scalar_min I64 = -9223372036854775808.
Proof. reflexivity. Qed.
Lemma i64_max_val : scalar_max I64 = 9223372036854775807.
Proof. reflexivity. Qed.
Lemma u32_min_val : scalar_min U32 = 0. Proof. reflexivity. Qed.
Lemma u32_max_val' : scalar_max U32 = 4294967295. Proof. reflexivity. Qed.
Lemma u64_min_val : scalar_min U64 = 0. Proof. reflexivity. Qed.
Lemma u64_max_val : scalar_max U64 = 18446744073709551615.
Proof. reflexivity. Qed.

Ltac in_bounds :=
  first [ rewrite i32_min_val; rewrite i32_max_val
        | rewrite i64_min_val; rewrite i64_max_val
        | rewrite u32_min_val; rewrite u32_max_val'
        | rewrite u64_min_val; rewrite u64_max_val ]; lia.

(* ================================================================== *)
(** ** The extracted constant a derivation names                       *)
(* ================================================================== *)

(** [const_ok] existentially quantifies an extracted [ConstExpr], because that
    is what [decode_const_expr] hands back and what the section lemmas compare
    against. Nothing in the type system can supply one: the witness is a
    *format* fact, and this is where it is read off the derivation. *)
Definition const_witness (e : expr) : Prop :=
  exists ce, e = [translate_const_expr ce].

Lemma const_num_witness : forall bs v rest,
  repr_expr bs [BI_const_num v] rest -> const_witness [BI_const_num v].
Proof.
  intros bs v rest H.
  destruct (repr_expr_single_inv _ _ _ H (ltac:(reflexivity)))
    as [mid [Hop1 _]].
  destruct (repr_op_const_inv _ _ _ Hop1) as [b [bs' [_ Hcs]]].
  destruct Hcs as [[_ [z [Hz Hval]]]
                  |[[_ [z [Hz Hval]]]
                  |[[_ [w [Hw Hval]]] | [_ [w [Hw Hval]]]]]].
  - pose proof (repr_sN_bound 32 _ _ _ Hz) as Hb. vm_compute Z.pow in Hb.
    destruct (scalar_of_Z I32 z (ltac:(in_bounds))) as [x Hx].
    exists (Types_ConstExpr_I32 x). cbn [translate_const_expr]. rewrite Hx.
    rewrite Hval. reflexivity.
  - pose proof (repr_sN_bound 64 _ _ _ Hz) as Hb. vm_compute Z.pow in Hb.
    destruct (scalar_of_Z I64 z (ltac:(in_bounds))) as [x Hx].
    exists (Types_ConstExpr_I64 x). cbn [translate_const_expr]. rewrite Hx.
    rewrite Hval. reflexivity.
  - pose proof (repr_bytes_le_bound 4 _ _ _ Hw) as Hb. vm_compute Z.pow in Hb.
    destruct (scalar_of_Z U32 w (ltac:(in_bounds))) as [x Hx].
    exists (Types_ConstExpr_F32 x). cbn [translate_const_expr]. rewrite Hx.
    rewrite Hval. reflexivity.
  - pose proof (repr_bytes_le_bound 8 _ _ _ Hw) as Hb. vm_compute Z.pow in Hb.
    destruct (scalar_of_Z U64 w (ltac:(in_bounds))) as [x Hx].
    exists (Types_ConstExpr_F64 x). cbn [translate_const_expr]. rewrite Hx.
    rewrite Hval. reflexivity.
Qed.

Lemma global_get_witness : forall bs x rest,
  repr_expr bs [BI_global_get x] rest -> const_witness [BI_global_get x].
Proof.
  intros bs x rest H.
  destruct (repr_expr_single_inv _ _ _ H (ltac:(reflexivity)))
    as [mid [Hop1 _]].
  destruct (repr_op_global_get_inv _ _ _ Hop1) as [bs' [z [_ [Hz Hxz]]]].
  pose proof (repr_uN_bound 32 _ _ _ Hz) as Hb. vm_compute Z.pow in Hb.
  destruct (scalar_of_Z U32 z (ltac:(in_bounds))) as [i Hi].
  exists (Types_ConstExpr_GlobalGet i). cbn [translate_const_expr].
  unfold translate_idx. rewrite Hi. rewrite Hxz. reflexivity.
Qed.

(* ================================================================== *)
(** ** What the format derivation says about each entry               *)
(* ================================================================== *)

(** The three premises of [module_wasm10] that the type system cannot supply,
    because they are about what the *encoding* can write rather than about what
    the type system accepts: an initialiser is one instruction the binary format
    has an opcode for, an element segment is active with [ref.func] entries, and
    a local is one of the four number types. All three come off the module's own
    derivation, which is why the derivation is a premise here. *)
Definition encodable (e : expr) : Prop := exists bs rest, repr_expr bs e rest.

Definition global_encodable (g : module_global) : Prop :=
  (exists vt, tg_t g.(modglob_type) = translate_vt_v vt)
  /\ encodable g.(modglob_init).

Definition elem_encodable (el : module_element) : Prop :=
  exists x e ys,
    el.(modelem_mode) = ME_active x e
    /\ encodable e
    /\ el.(modelem_init) = List.map (fun y => [BI_ref_func y]) ys.

Definition data_encodable (d : module_data) : Prop :=
  exists x e, d.(moddata_mode) = MD_active x e /\ encodable e.

Definition locals_encodable (ls : list value_type) : Prop :=
  exists ds, ls = List.map translate_vt_v ds.

Definition import_encodable (im : module_import) : Prop :=
  match im.(imp_desc) with
  | MID_global g => exists vt, tg_t g = translate_vt_v vt
  | _ => True
  end.

Definition module_encodable (m : module) : Prop :=
  List.Forall import_encodable (mod_imports m)
  /\ List.Forall global_encodable (mod_globals m)
  /\ List.Forall elem_encodable (mod_elems m)
  /\ List.Forall data_encodable (mod_datas m)
  /\ List.Forall (fun f => locals_encodable f.(modfunc_locals)) (mod_funcs m).

(** One line of the module, entry by entry. Both cases give it: a present
    section by walking its [repr_rep], an absent one because the list is
    empty. *)
Lemma repr_rep_forall : forall A (R : list Z -> A -> list Z -> Prop)
                               (P : A -> Prop) n bs xs rest,
  (forall b x r, R b x r -> P x) ->
  repr_rep R n bs xs rest -> List.Forall P xs.
Proof.
  intros A R P n bs xs rest HP Hrep.
  induction Hrep as [bs | n bs x mid xs rest Hx Hrec IH];
    [apply List.Forall_nil|].
  apply List.Forall_cons; [exact (HP _ _ _ Hx) | exact IH].
Qed.

Lemma repr_padded_forall : forall A (R : list Z -> A -> list Z -> Prop)
                                  (P : A -> Prop) id bs xs rest,
  (forall b x r, R b x r -> P x) ->
  repr_padded id (repr_vec R) [] bs xs rest -> List.Forall P xs.
Proof.
  intros A R P id bs xs rest HP [mid [_ Ho]].
  destruct (repr_optsec_inv _ _ _ _ _ _ _ Ho) as [Hpres|[_ [-> _]]];
    [|apply List.Forall_nil].
  destruct (repr_section_inv _ _ _ _ _ _ Hpres) as [p0 [sz [ct [_ [_ [_ HR]]]]]].
  destruct (repr_vec_inv _ _ _ _ _ HR) as [n [m1 [_ Hrep]]].
  exact (repr_rep_forall _ R P _ _ _ _ HP Hrep).
Qed.

Lemma valtype_encodable : forall bs t rest,
  repr_valtype bs t rest -> exists vt, t = translate_vt_v vt.
Proof.
  intros bs t rest H. destruct (repr_valtype_inv _ _ _ H) as [b [_ Hspec]].
  unfold valtype_spec in Hspec.
  destruct (Z.eqb b 127); [injection Hspec as <-;
                           exists Types_ValueType_I32; reflexivity|].
  destruct (Z.eqb b 126); [injection Hspec as <-;
                           exists Types_ValueType_I64; reflexivity|].
  destruct (Z.eqb b 125); [injection Hspec as <-;
                           exists Types_ValueType_F32; reflexivity|].
  destruct (Z.eqb b 124); [injection Hspec as <-;
                           exists Types_ValueType_F64; reflexivity|].
  discriminate.
Qed.

Lemma repr_import_encodable : forall bs im rest,
  repr_import bs im rest -> import_encodable im.
Proof.
  intros bs im rest H.
  destruct (repr_import_inv _ _ _ H) as [md [m1 [nm [m2 [d [_ [_ [Hd ->]]]]]]]].
  unfold import_encodable. cbn [imp_desc].
  destruct (repr_importdesc_inv _ _ _ Hd)
    as [[p0 [x [_ [_ ->]]]]|[[p0 [t [_ [_ ->]]]]
       |[[p0 [mm [_ [_ ->]]]]|[p0 [g [_ [Hg ->]]]]]]]; try exact I.
  destruct (repr_globaltype_inv _ _ _ Hg) as [t [m3 [mu [Hvt [_ ->]]]]].
  cbn [tg_t]. exact (valtype_encodable _ _ _ Hvt).
Qed.

Lemma repr_global_encodable : forall bs g rest,
  repr_global bs g rest -> global_encodable g.
Proof.
  intros bs g rest H.
  destruct (repr_global_inv _ _ _ H) as [gt [mid [e [Hgt [He ->]]]]].
  destruct (repr_globaltype_inv _ _ _ Hgt) as [t [m1 [mu [Hvt [_ ->]]]]].
  split; [exact (valtype_encodable _ _ _ Hvt) | exists mid, rest; exact He].
Qed.

Lemma repr_elem_encodable : forall bs el rest,
  repr_elem bs el rest -> elem_encodable el.
Proof.
  intros bs el rest H.
  destruct (repr_elem_inv _ _ _ H) as [x [m1 [e [m2 [ys [_ [He [_ ->]]]]]]]].
  exists x, e, ys. split; [reflexivity|].
  split; [exists m1, m2; exact He | reflexivity].
Qed.

Lemma repr_data_encodable : forall bs d rest,
  repr_data bs d rest -> data_encodable d.
Proof.
  intros bs d rest H.
  destruct (repr_data_inv _ _ _ H) as [x [m1 [e [m2 [bys [_ [He [_ ->]]]]]]]].
  exists x, e. split; [reflexivity | exists m1, m2; exact He].
Qed.

Lemma repr_locals_encodable : forall bs g rest,
  repr_locals bs g rest -> locals_encodable g.
Proof.
  intros bs g rest H.
  destruct (repr_locals_inv _ _ _ H) as [n [mid [t [_ [Hvt ->]]]]].
  destruct (valtype_encodable _ _ _ Hvt) as [vt ->].
  exists (List.repeat vt (Z.to_nat n)).
  rewrite List.map_repeat. reflexivity.
Qed.

Lemma locals_encodable_concat : forall gs,
  List.Forall locals_encodable gs -> locals_encodable (List.concat gs).
Proof.
  intros gs H. induction H as [|g gs [ds Hg] _ [dss Hgs]];
    [exists []; reflexivity|].
  exists (ds ++ dss). cbn [List.concat]. rewrite List.map_app.
  rewrite Hg. rewrite Hgs. reflexivity.
Qed.

Lemma repr_code_encodable : forall bs c rest,
  repr_code bs c rest -> locals_encodable (fst c).
Proof.
  intros bs c rest H.
  destruct (repr_code_inv _ _ _ H) as [size [content [_ [_ Hfunc]]]].
  destruct (repr_func_inv _ _ _ Hfunc) as [gs [mid [e [Hgs [_ ->]]]]].
  cbn [fst].
  destruct (repr_vec_inv _ _ _ _ _ Hgs) as [n [m1 [_ Hrep]]].
  apply locals_encodable_concat.
  exact (repr_rep_forall _ repr_locals _ _ _ _ _ repr_locals_encodable Hrep).
Qed.

Lemma codes_fit_locals : forall bs cs rest,
  codes_fit bs cs rest -> List.Forall (fun c => locals_encodable (fst c)) cs.
Proof.
  intros bs cs rest H.
  induction H as [bs | bs c mid cs rest Hc _ _ _ IH];
    [apply List.Forall_nil|].
  apply List.Forall_cons; [exact (repr_code_encodable _ _ _ Hc) | exact IH].
Qed.

Lemma repr_module_fit_encodable : forall bs m,
  repr_module_fit bs m -> module_encodable m.
Proof.
  intros bs m H. inversion H as [bs0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
                                 tfs imps tidxs tabs mems globs exps st els
                                 codes datas fs Hmagic L1 L2 L3 L4 L5 L6 L7 L8
                                 L9 L10 L11 Htr Hfuncs]; subst.
  destruct (funcs_of_parts _ _ _ Hfuncs) as [_ Hcodes].
  split; [|split; [|split; [|split]]];
    cbn [mod_imports mod_globals mod_elems mod_datas mod_funcs].
  - exact (repr_padded_forall _ repr_import _ 2 _ _ _ repr_import_encodable L2).
  - exact (repr_padded_forall _ repr_global _ 6 _ _ _ repr_global_encodable L6).
  - exact (repr_padded_forall _ repr_elem _ 9 _ _ _ repr_elem_encodable L9).
  - exact (repr_padded_forall _ repr_data _ 11 _ _ _ repr_data_encodable L11).
  - (* the code line is framed by [repr_vec_fit], and the entries pair with the
       module's functions by [funcs_of] *)
    assert (Hcs : List.Forall (fun c => locals_encodable (fst c)) codes).
    { destruct L10 as [mid [_ Ho]].
      destruct (repr_optsec_inv _ _ _ _ _ _ _ Ho) as [Hpres|[_ [-> _]]];
        [|apply List.Forall_nil].
      destruct (repr_section_inv _ _ _ _ _ _ Hpres)
        as [p0 [sz [ct [_ [_ [_ [n [m1 [_ [_ Hfit]]]]]]]]]].
      exact (codes_fit_locals _ _ _ Hfit). }
    rewrite Hcodes in Hcs.
    rewrite List.Forall_map in Hcs. exact Hcs.
Qed.

(* ================================================================== *)
(** ** A constant expression typed [[] -> [t]] is one instruction      *)
(* ================================================================== *)

(** Spec 3.4.10 restricts an initialiser to constant instructions and 3.4.4
    types it [[] -> [t]]. Every constant instruction pushes exactly one value
    and consumes none, so the checker's stack after [n] of them is [n] deep,
    and agreeing with a one-element result type forces [n = 1]. That is the
    whole argument, and it is what lets a dedicated one-instruction reader stand
    in for a general constant-expression mode. *)
Lemma const_single_produce : forall C ct be ct',
  const_expr C be = true ->
  check_single C (Some ct) be = Some ct' ->
  exists t, ct' = Build_checker_type (t :: ct.(CT_type)) ct.(CT_unr).
Proof.
  intros C ct be ct' Hce Hchk. destruct ct as [ts unr].
  destruct be; try discriminate Hce;
    cbn [check_single type_update consume produce CT_type CT_unr] in Hchk.
  - (* i32.const and friends *)
    injection Hchk as <-. eexists. reflexivity.
  - injection Hchk as <-. eexists. reflexivity.
  - injection Hchk as <-. eexists. reflexivity.
  - (* ref.func *)
    destruct (lookup_N (tc_funcs C) f) as [tf|]; [|discriminate].
    (* the [tc_refs] membership is mathcomp's [\in], which cannot be named
       without its notations; take it off the goal instead *)
    match type of Hchk with
    | context [if ?b then _ else _] => destruct b; [|discriminate]
    end.
    injection Hchk as <-. eexists. reflexivity.
  - (* global.get *)
    destruct (lookup_N (tc_globals C) g) as [gt|]; [|discriminate].
    injection Hchk as <-. eexists. reflexivity.
Qed.

Lemma const_fold_shape : forall C es ts unr ct,
  const_exprs C es = true ->
  List.fold_left (check_single C) es (Some (Build_checker_type ts unr))
    = Some ct ->
  exists us, ct = Build_checker_type (us ++ ts) unr
             /\ List.length us = List.length es.
Proof.
  intros C es. induction es as [|be es IH]; intros ts unr ct Hall Hfold.
  - cbn in Hfold. injection Hfold as <-. exists []. split; reflexivity.
  - unfold const_exprs in Hall. cbn [seq.all] in Hall.
    apply Bool.andb_true_iff in Hall. destruct Hall as [Hbe Hes].
    cbn [List.fold_left] in Hfold.
    destruct (check_single C (Some (Build_checker_type ts unr)) be)
      as [ct1|] eqn:Hc;
      [|rewrite fold_check_single_none in Hfold; discriminate].
    destruct (const_single_produce C (Build_checker_type ts unr) be ct1 Hbe Hc)
      as [t Ht].
    cbn [CT_type CT_unr] in Ht. subst ct1.
    destruct (IH (t :: ts) unr ct Hes Hfold) as [us [-> Hlen]].
    exists (us ++ [t]). split.
    + rewrite <- app_assoc. reflexivity.
    + rewrite List.app_length. cbn [List.length]. lia.
Qed.

Lemma const_exprs_one : forall C es t,
  const_exprs C es = true ->
  b_e_type_checker_aux C es (Tf [] [t]) = true ->
  exists be, es = [be].
Proof.
  intros C es t Hall Hchk. unfold b_e_type_checker_aux in Hchk.
  destruct (List.fold_left (check_single C) es
              (Some (Build_checker_type [] false))) as [ct|] eqn:Hfold;
    [|discriminate].
  destruct (const_fold_shape C es [] false ct Hall Hfold) as [us [-> Hlen]].
  unfold c_types_agree in Hchk. cbn [CT_unr CT_type] in Hchk.
  rewrite app_nil_r in Hchk.
  pose proof (all2_length _ _ _ _ _ Hchk) as Hlen1.
  cbn [List.length] in Hlen1. rewrite Hlen1 in Hlen.
  destruct es as [|be [|be' es]]; try (cbn in Hlen; lia).
  exists be. reflexivity.
Qed.

(** Which instruction it is. Only two of the five constant instructions can
    have a number type, and the other three are ruled out by their result type
    alone. *)
Lemma value_subtyping_eq : forall t1 t2,
  value_subtyping t1 t2 = true -> t1 = t2 \/ t1 = T_bot.
Proof.
  intros t1 t2 H. unfold value_subtyping in H.
  apply Bool.orb_true_iff in H. destruct H as [H|H];
    [left | right]; exact (eqb_eq _ _ _ H).
Qed.

Lemma agree_one : forall t1 t2,
  c_types_agree (Build_checker_type [t1] false) [t2] = true ->
  t1 = t2 \/ t1 = T_bot.
Proof.
  intros t1 t2 H. unfold c_types_agree in H. cbn [CT_unr CT_type] in H.
  unfold values_subtyping in H. cbn [seq.all2] in H.
  apply Bool.andb_true_iff in H.
  exact (value_subtyping_eq _ _ (proj1 H)).
Qed.

Lemma const_num_shape : forall C be nt,
  const_expr C be = true ->
  b_e_type_checker_aux C [be] (Tf [] [T_num nt]) = true ->
  (exists v, be = BI_const_num v /\ typeof_num v = nt)
  \/ (exists i gt, be = BI_global_get i
                   /\ lookup_N C.(tc_globals) i = Some gt
                   /\ tg_mut gt = MUT_const
                   /\ (tg_t gt = T_num nt \/ tg_t gt = T_bot)).
Proof.
  intros C be nt Hce Hchk. unfold b_e_type_checker_aux in Hchk.
  cbn [List.fold_left] in Hchk.
  destruct be; try discriminate Hce;
    cbn [check_single type_update consume produce CT_type CT_unr] in Hchk.
  - (* i32.const and friends *)
    destruct (agree_one _ _ Hchk) as [Heq|Heq]; [|discriminate].
    injection Heq as <-. left. exists v. split; reflexivity.
  - (* v128.const *)
    destruct (agree_one _ _ Hchk) as [Heq|Heq]; discriminate.
  - (* ref.null *)
    destruct (agree_one _ _ Hchk) as [Heq|Heq]; discriminate.
  - (* ref.func *)
    destruct (lookup_N (tc_funcs C) f) as [tf|]; [|discriminate].
    match type of Hchk with
    | context [if ?b then _ else _] => destruct b; [|discriminate]
    end.
    destruct (agree_one _ _ Hchk) as [Heq|Heq]; discriminate.
  - (* global.get *)
    (* the one arm [T_bot] survives: nothing here says a global's declared
       type is a real one, and it is the format that rules it out *)
    destruct (lookup_N (tc_globals C) g) as [gt|] eqn:Hg; [|discriminate].
    right. exists g, gt. split; [reflexivity|]. split; [exact Hg|].
    cbn [const_expr] in Hce. rewrite Hg in Hce.
    split; [exact (eqb_eq _ _ _ Hce) | exact (agree_one _ _ Hchk)].
Qed.

Lemma ref_func_range : forall C y t,
  b_e_type_checker_aux C [BI_ref_func y] (Tf [] [T_ref t]) = true ->
  exists tf, lookup_N C.(tc_funcs) y = Some tf.
Proof.
  intros C y t Hchk. unfold b_e_type_checker_aux in Hchk.
  cbn [List.fold_left check_single] in Hchk.
  destruct (lookup_N (tc_funcs C) y) as [tf|] eqn:Hy; [|discriminate].
  exists tf. reflexivity.
Qed.

(** [b_e_type_checker] reverses the context and both halves of the type; at
    [Tf [] [t]] the reversal is the identity, and [const_exprs] reads only
    [tc_globals], which [context_reverse] leaves alone. *)
Lemma b_e_type_checker_one : forall C es t,
  b_e_type_checker C es (Tf [] [t])
    = b_e_type_checker_aux (context_reverse C) es (Tf [] [t]).
Proof. reflexivity. Qed.

Lemma const_expr_reverse : forall C be,
  const_expr (context_reverse C) be = const_expr C be.
Proof. intros C be. destruct be; reflexivity. Qed.

Lemma const_exprs_reverse : forall C es,
  const_exprs (context_reverse C) es = const_exprs C es.
Proof.
  intros C es. unfold const_exprs. induction es as [|be es IH]; [reflexivity|].
  cbn [seq.all]. rewrite const_expr_reverse. rewrite IH. reflexivity.
Qed.

(* ================================================================== *)
(** ** The checker's prepasses, read backwards                        *)
(* ================================================================== *)

(** [those] over a [map] is a [Forall2] saying every lookup succeeded, which is
    the only thing the three prepasses are used for here. *)
Lemma those_map_inv : forall A B (f : A -> option B) l ys,
  those (List.map f l) = Some ys ->
  List.Forall2 (fun x y => f x = Some y) l ys.
Proof.
  intros A B f l. induction l as [|x l IH]; intros ys H;
    rewrite <- those_those0 in H.
  - cbn in H. injection H as <-. apply Forall2_nil.
  - cbn [List.map those0] in H.
    destruct (f x) as [y|] eqn:Hfx; [|discriminate].
    destruct (those0 (List.map f l)) as [ys'|] eqn:Hrest; [|discriminate].
    cbn [option_map] in H. injection H as <-.
    apply Forall2_cons; [exact Hfx|].
    apply IH. rewrite <- those_those0. exact Hrest.
Qed.

Lemma nth_error_lt : forall A (l : list A) n x,
  List.nth_error l n = Some x -> (n < List.length l)%nat.
Proof.
  intros A l n x H. apply List.nth_error_Some. rewrite H. discriminate.
Qed.

(** Spec 5.5.5's descriptors, and what each of the four index spaces gets from
    them. The same [flat_map] on both sides, one import at a time. *)
Lemma imports_typer_inv : forall tfs imps impts,
  module_imports_typer tfs imps = Some impts ->
  List.Forall (fun im => spec_importdesc_wasm10 tfs im.(imp_desc)) imps
  /\ ext_t_funcs impts = spec_resolve tfs (spec_imported_fidxs imps)
  /\ ext_t_tables impts = spec_imported_tables imps
  /\ ext_t_mems impts = spec_imported_mems imps
  /\ ext_t_globals impts = spec_imported_globals imps.
Proof.
  intros tfs imps impts H. unfold module_imports_typer in H.
  apply those_map_inv in H.
  induction H as [|im t imps impts Hd _ IH];
    [split; [apply List.Forall_nil|]; repeat split; reflexivity|].
  destruct IH as [Hall [Hf [Ht [Hm Hg]]]].
  destruct im as [md nm [x|tt|mm|gg]];
    cbn [module_import_desc_typer imp_desc] in Hd.
  - destruct (lookup_N tfs x) as [ft|] eqn:Hx; [|discriminate].
    cbn [option_map] in Hd. injection Hd as <-.
    unfold lookup_N in Hx.
    split; [apply List.Forall_cons;
            [exact (nth_error_lt _ _ _ _ Hx) | exact Hall]|].
    split; [cbn [ext_t_funcs seq.pmap ssrfun.oapp spec_imported_fidxs
                 spec_resolve List.flat_map imp_desc List.app];
            rewrite Hx; rewrite Hf; reflexivity|].
    split; [exact Ht|]. split; [exact Hm | exact Hg].
  - destruct (tabletype_valid tt) eqn:Hv; [|discriminate].
    injection Hd as <-.
    split; [apply List.Forall_cons; [exact Hv | exact Hall]|].
    split; [exact Hf|].
    split; [cbn [ext_t_tables seq.pmap ssrfun.oapp spec_imported_tables
                 List.flat_map imp_desc List.app];
            rewrite Ht; reflexivity|].
    split; [exact Hm | exact Hg].
  - destruct (memtype_valid mm) eqn:Hv; [|discriminate].
    injection Hd as <-.
    split; [apply List.Forall_cons; [exact Hv | exact Hall]|].
    split; [exact Hf|]. split; [exact Ht|].
    split; [cbn [ext_t_mems seq.pmap ssrfun.oapp spec_imported_mems
                 List.flat_map imp_desc List.app];
            rewrite Hm; reflexivity | exact Hg].
  - injection Hd as <-.
    split; [apply List.Forall_cons; [exact I | exact Hall]|].
    split; [exact Hf|]. split; [exact Ht|]. split; [exact Hm|].
    cbn [ext_t_globals seq.pmap ssrfun.oapp spec_imported_globals
         List.flat_map imp_desc List.app].
    rewrite Hg. reflexivity.
Qed.

Lemma spec_resolve_cons : forall tfs x xs,
  spec_resolve tfs (x :: xs)
    = (match List.nth_error tfs (N.to_nat x) with
       | Some ft => [ft]
       | None => []
       end) ++ spec_resolve tfs xs.
Proof. reflexivity. Qed.

Lemma gather_f_inv : forall tfs fs fts,
  gather_m_f_types tfs fs = Some fts ->
  List.Forall (fun f => (N.to_nat f.(modfunc_type) < List.length tfs)%nat) fs
  /\ spec_resolve tfs (List.map modfunc_type fs) = fts.
Proof.
  intros tfs fs fts H. unfold gather_m_f_types in H.
  apply those_map_inv in H.
  induction H as [|f ft fs fts Hd _ IH];
    [split; [apply List.Forall_nil | reflexivity]|].
  destruct IH as [Hall Hres]. unfold gather_m_f_type, lookup_N in Hd.
  split; [apply List.Forall_cons; [exact (nth_error_lt _ _ _ _ Hd) | exact Hall]|].
  cbn [List.map]. rewrite spec_resolve_cons. rewrite Hd. cbn [List.app].
  rewrite Hres. reflexivity.
Qed.

(* ================================================================== *)
(** ** An initialiser the checker accepts is one the decoder reads     *)
(* ================================================================== *)

Definition gt_encodable (gt : global_type) : Prop :=
  exists vt, tg_t gt = translate_vt_v vt.

Lemma gt_encodable_imported : forall imps,
  List.Forall import_encodable imps ->
  List.Forall gt_encodable (spec_imported_globals imps).
Proof.
  intros imps H. unfold spec_imported_globals.
  induction H as [|im imps Him _ IH]; [apply List.Forall_nil|].
  cbn [List.flat_map]. apply List.Forall_app. split; [|exact IH].
  unfold import_encodable in Him. destruct im.(imp_desc);
    try apply List.Forall_nil.
  apply List.Forall_cons; [exact Him | apply List.Forall_nil].
Qed.

Lemma translate_vt_v_not_bot : forall vt, translate_vt_v vt <> T_bot.
Proof. intros [| | |]; discriminate. Qed.

Lemma translate_vt_v_num : forall vt, exists nt, translate_vt_v vt = T_num nt.
Proof. intros [| | |]; eexists; reflexivity. Qed.

(** The join. The type checker says the initialiser is one constant
    instruction of a known shape; the format derivation says which extracted
    constant writes it; together they are [spec_const_ok], which is what the
    global, element and data sections' completeness lemmas consume. *)
Lemma spec_const_ok_of_check : forall C gts nimp vt e,
  tc_globals C = gts ->
  Z.of_nat (List.length gts) = nimp ->
  List.Forall gt_encodable gts ->
  encodable e ->
  const_exprs C e = true ->
  b_e_type_checker C e (Tf [] [translate_vt_v vt]) = true ->
  spec_const_ok gts nimp (translate_vt_v vt) e.
Proof.
  intros C gts nimp vt e Hg Hn Hgts [bs [rest Hexpr]] Hce Hchk.
  rewrite b_e_type_checker_one in Hchk.
  rewrite <- const_exprs_reverse in Hce.
  destruct (const_exprs_one _ _ _ Hce Hchk) as [be ->].
  unfold const_exprs in Hce. cbn [seq.all] in Hce.
  apply Bool.andb_true_iff in Hce. destruct Hce as [Hbe _].
  destruct (translate_vt_v_num vt) as [nt Hnt]. rewrite Hnt in Hchk.
  destruct (const_num_shape _ _ _ Hbe Hchk)
    as [[v [-> Htv]]|[i [gt [-> [Hlk [Hmut Hty]]]]]].
  1: { (* a numeric constant: the derivation names the immediate *)
    destruct (const_num_witness _ _ _ Hexpr) as [ce Hce].
    exists ce, vt. split; [exact Hce|]. split; [reflexivity|].
    destruct ce as [z|z|w|w|x]; cbn [translate_const_expr] in Hce;
      [| | | |discriminate Hce].
    all: injection Hce as ->;
         cbn [const_val fconst_val typeof_num] in Htv; subst nt;
         destruct vt; cbn [translate_vt_v] in Hnt; try discriminate Hnt;
         reflexivity. }
  (* [global.get]: the index resolves inside the imported prefix *)
    cbn [context_reverse tc_globals] in Hlk. rewrite Hg in Hlk.
    assert (Hgt : tg_t gt = translate_vt_v vt).
    { destruct Hty as [Hty|Hbot].
      - rewrite Hty. rewrite Hnt. reflexivity.
      - exfalso.
        rewrite List.Forall_forall in Hgts.
        destruct (Hgts gt (List.nth_error_In _ _ Hlk)) as [vt0 Hvt0].
        rewrite Hbot in Hvt0. exact (translate_vt_v_not_bot vt0 (eq_sym Hvt0)). }
    destruct (global_get_witness _ _ _ Hexpr) as [ce Hce].
    exists ce, vt. split; [exact Hce|]. split; [reflexivity|].
    destruct ce as [z|z|w|w|x]; cbn [translate_const_expr] in Hce;
      [discriminate Hce|discriminate Hce|discriminate Hce|discriminate Hce|].
    injection Hce as Hce. cbn [spec_const_expr_ok].
    exists gt.
    assert (Hidx : N.to_nat i = Z.to_nat (to_Z x))
      by (rewrite Hce; apply N_to_nat_Z_to_N).
    unfold lookup_N in Hlk. rewrite Hidx in Hlk.
    split; [exact Hlk|]. split; [exact Hmut|]. split; [exact Hgt|].
    pose proof (nth_error_lt _ _ _ _ Hlk) as Hlt.
    pose proof (u32_nonneg x).
    apply Nat2Z.inj_lt in Hlt. rewrite Z2Nat.id in Hlt by lia. lia.
Qed.

(* ================================================================== *)
(** ** The Wasm 1.0 restrictions, and nothing else                     *)
(* ================================================================== *)

(** What the type checker cannot supply, because Wasm 2.0 does not ask for it:
    one result per function type, one table, one memory. Everything else in
    [module_wasm10] is one of [module_type_checker]'s own obligations read
    backwards, or a fact about the encoding that [repr_module_fit] carries. *)
Definition module_1_0 (m : module) : Prop :=
  List.Forall functype_wasm10 (mod_types m)
  /\ Z.of_nat (List.length (spec_imported_tables (mod_imports m)))
       + Z.of_nat (List.length (mod_tables m)) <= 1
  /\ Z.of_nat (List.length (spec_imported_mems (mod_imports m)))
       + Z.of_nat (List.length (mod_mems m)) <= 1.

Lemma name_bytes_inj : forall a b : name, name_bytes a = name_bytes b -> a = b.
Proof.
  intros a. unfold name_bytes.
  induction a as [|x a IH]; intros [|y b] H; cbn [List.map] in H;
    try discriminate; [reflexivity|].
  injection H as Hh Ht. f_equal; [|exact (IH b Ht)].
  apply N2Z.inj in Hh.
  pose proof (Byte.of_to_N x) as Hx. rewrite Hh in Hx.
  rewrite (Byte.of_to_N y) in Hx. injection Hx as <-. reflexivity.
Qed.

Lemma nodup_names_of_unique : forall exps,
  export_name_unique exps = true ->
  List.NoDup (List.map (fun e => name_bytes e.(modexp_name)) exps).
Proof.
  intros exps H. unfold export_name_unique in H.
  apply eqb_eq in H.
  assert (Hnd : List.NoDup (seq.map modexp_name exps))
    by (rewrite <- H; apply List.NoDup_nodup).
  rewrite seq_map_eq in Hnd.
  apply (nodup_map_of _ _ _ modexp_name
           (fun e => name_bytes e.(modexp_name)) exps); [|exact Hnd].
  intros x y Hxy. exact (name_bytes_inj _ _ Hxy).
Qed.

(* ================================================================== *)
(** ** Each obligation, read backwards                                *)
(* ================================================================== *)

(** One lemma per section, stated over the context the checker built rather
    than over the module, so that the assembly only has to say which context
    that was. *)
Lemma gather_m_g_types_eq : forall gs,
  gather_m_g_types gs = List.map modglob_type gs.
Proof. intros gs. unfold gather_m_g_types. rewrite seq_map_eq. reflexivity. Qed.

Lemma global_checker_inv : forall C g,
  module_global_type_checker C g = true ->
  global_encodable g ->
  List.Forall gt_encodable (tc_globals C) ->
  spec_const_ok (tc_globals C) (Z.of_nat (List.length (tc_globals C)))
    (tg_t g.(modglob_type)) g.(modglob_init).
Proof.
  intros C [tg init] Hck [[vt Hvt] Henc] Hgts.
  cbn [modglob_type modglob_init] in *.
  unfold module_global_type_checker in Hck. cbn beta iota in Hck.
  apply Bool.andb_true_iff in Hck. destruct Hck as [Hce Hbt].
  rewrite Hvt. rewrite Hvt in Hbt.
  exact (spec_const_ok_of_check C _ _ vt init eq_refl eq_refl Hgts Henc Hce
           Hbt).
Qed.

Lemma data_checker_inv : forall C d,
  module_data_type_checker C d = true ->
  data_encodable d ->
  List.Forall gt_encodable (tc_globals C) ->
  exists x e,
    d.(moddata_mode) = MD_active x e
    /\ (N.to_nat x < List.length C.(tc_mems))%nat
    /\ spec_const_ok (tc_globals C) (Z.of_nat (List.length (tc_globals C)))
         (T_num T_i32) e.
Proof.
  intros C [init dmode] Hck [x [e [Hmode Henc]]] Hgts.
  cbn [moddata_mode] in *. subst dmode.
  unfold module_data_type_checker in Hck. cbn beta iota in Hck.
  cbn [module_data_mode_checker] in Hck.
  destruct (lookup_N (tc_mems C) x) as [mt|] eqn:Hm; [|discriminate].
  apply Bool.andb_true_iff in Hck. destruct Hck as [Hbt Hce].
  exists x, e. split; [reflexivity|].
  unfold lookup_N in Hm.
  split; [exact (nth_error_lt _ _ _ _ Hm)|].
  exact (spec_const_ok_of_check C _ _ Types_ValueType_I32 e eq_refl eq_refl
           Hgts Henc Hce Hbt).
Qed.

Lemma elem_checker_inv : forall C el,
  module_elem_type_checker C el = true ->
  elem_encodable el ->
  List.Forall gt_encodable (tc_globals C) ->
  exists x e ys,
    el.(modelem_mode) = ME_active x e
    /\ (N.to_nat x < List.length C.(tc_tables))%nat
    /\ spec_const_ok (tc_globals C) (Z.of_nat (List.length (tc_globals C)))
         (T_num T_i32) e
    /\ el.(modelem_init) = List.map (fun y => [BI_ref_func y]) ys
    /\ List.Forall (fun y => (N.to_nat y < List.length C.(tc_funcs))%nat) ys.
Proof.
  intros C [t inits emode] Hck [x [e [ys [Hmode [Henc Hinits]]]]] Hgts.
  cbn [modelem_mode modelem_init] in *. subst emode. subst inits.
  unfold module_elem_type_checker in Hck. cbn beta iota in Hck.
  apply Bool.andb_true_iff in Hck. destruct Hck as [Hck Hmc].
  apply Bool.andb_true_iff in Hck. destruct Hck as [_ Hty].
  cbn [module_elem_mode_checker] in Hmc.
  destruct (lookup_N (tc_tables C) x) as [tab|] eqn:Ht; [|discriminate].
  apply Bool.andb_true_iff in Hmc. destruct Hmc as [Hmc Hce].
  apply Bool.andb_true_iff in Hmc. destruct Hmc as [_ Hbt].
  exists x, e, ys. split; [reflexivity|].
  unfold lookup_N in Ht.
  split; [exact (nth_error_lt _ _ _ _ Ht)|].
  split; [exact (spec_const_ok_of_check C _ _ Types_ValueType_I32 e eq_refl
                   eq_refl Hgts Henc Hce Hbt)|].
  split; [reflexivity|].
  apply Forall_of_all in Hty. rewrite List.Forall_map in Hty.
  revert Hty. apply List.Forall_impl. intros y Hy.
  rewrite b_e_type_checker_one in Hy.
  destruct (ref_func_range _ _ _ Hy) as [tf Hlk].
  cbn [context_reverse tc_funcs] in Hlk. unfold lookup_N in Hlk.
  pose proof (nth_error_lt _ _ _ _ Hlk) as Hlt.
  rewrite seq_map_eq in Hlt. rewrite List.map_length in Hlt. exact Hlt.
Qed.

Definition func_ctx (C : t_context) (tn tm t_locs : list value_type)
  : t_context :=
  {| tc_types := C.(tc_types); tc_funcs := C.(tc_funcs);
     tc_globals := C.(tc_globals); tc_tables := C.(tc_tables);
     tc_mems := C.(tc_mems); tc_elems := C.(tc_elems);
     tc_datas := C.(tc_datas);
     tc_locals := List.app C.(tc_locals) (List.app tn t_locs);
     tc_labels := tm :: C.(tc_labels); tc_return := Some tm;
     tc_refs := C.(tc_refs) |}.

Lemma func_checker_inv : forall C f,
  module_func_type_checker C f = true ->
  exists tn tm,
    List.nth_error C.(tc_types) (N.to_nat f.(modfunc_type)) = Some (Tf tn tm)
    /\ b_e_type_checker (func_ctx C tn tm f.(modfunc_locals))
         f.(modfunc_body) (Tf [] tm) = true.
Proof.
  intros C [i t_locs b_es] Hck.
  cbn [modfunc_type modfunc_locals modfunc_body].
  unfold module_func_type_checker in Hck. cbn beta iota in Hck.
  destruct (lookup_N (tc_types C) i) as [[tn tm]|] eqn:Hl; [|discriminate].
  apply Bool.andb_true_iff in Hck. destruct Hck as [Hbt _].
  exists tn, tm. unfold lookup_N in Hl. split; [exact Hl | exact Hbt].
Qed.

Lemma forall2_of_forall_map : forall A B C (g : A -> B) (h : A -> C)
                                     (P : B -> C -> Prop) l,
  List.Forall (fun x => P (g x) (h x)) l ->
  List.Forall2 P (List.map g l) (List.map h l).
Proof.
  intros A B C g h P l H. induction H; [apply Forall2_nil|].
  cbn [List.map]. apply Forall2_cons; assumption.
Qed.

Lemma exports_typer_inv : forall C exps expts,
  module_exports_typer C exps = Some expts ->
  List.Forall
    (fun e => match e.(modexp_desc) with
              | MED_func x => (N.to_nat x < List.length C.(tc_funcs))%nat
              | MED_table x => (N.to_nat x < List.length C.(tc_tables))%nat
              | MED_mem x => (N.to_nat x < List.length C.(tc_mems))%nat
              | MED_global x => (N.to_nat x < List.length C.(tc_globals))%nat
              end) exps.
Proof.
  intros C exps expts H. unfold module_exports_typer in H.
  apply those_map_inv in H.
  induction H as [|e t exps expts Hd _ IH]; [apply List.Forall_nil|].
  apply List.Forall_cons; [|exact IH].
  unfold module_export_typer in Hd. destruct e.(modexp_desc) as [x|x|x|x];
    (destruct (lookup_N _ x) as [v|] eqn:Hl; [|discriminate]);
    unfold lookup_N in Hl; exact (nth_error_lt _ _ _ _ Hl).
Qed.

Lemma start_checker_inv : forall C s,
  module_start_type_checker C s = true ->
  List.nth_error C.(tc_funcs) (N.to_nat s.(modstart_func)) = Some (Tf [] []).
Proof.
  intros C s H. unfold module_start_type_checker, module_start_typing in H.
  destruct (lookup_N (tc_funcs C) s.(modstart_func)) as [tf|] eqn:Hl;
    [|discriminate].
  unfold lookup_N in Hl. rewrite Hl. f_equal. exact (eqb_eq _ _ _ H).
Qed.

(** Every obligation of [module_type_checker], read backwards. The two
    contexts it builds are named [c] and [c'] here as they are on the soundness
    side, and each clause of [module_wasm10] comes from the obligation with the
    same name -- except the three the format supplies and the three Wasm 1.0
    restrictions. *)
Theorem module_wasm10_of_checker : forall bs m t_imps t_exps,
  repr_module_fit bs m ->
  module_type_checker m = Some (t_imps, t_exps) ->
  module_1_0 m ->
  module_wasm10 m.
Proof.
  intros bs m t_imps t_exps Hrepr Hchk H10.
  destruct (repr_module_fit_encodable _ _ Hrepr) as [Eim [Egl [Eel [Eda Efn]]]].
  destruct H10 as [W1 [Wtab Wmem]].
  destruct m as [tfs fs ts ms gs els ds i_opt imps exps].
  cbn [mod_types mod_funcs mod_tables mod_mems mod_globals mod_elems
       mod_datas mod_start mod_imports mod_exports] in *.
  unfold module_type_checker in Hchk. cbn beta iota zeta in Hchk.
  destruct (gather_m_f_types tfs fs) as [fts|] eqn:Hgf;
    destruct (module_imports_typer tfs imps) as [impts|] eqn:Hit;
    cbn beta iota zeta in Hchk; try discriminate.
  destruct (imports_typer_inv _ _ _ Hit) as [Him [Hif [Hitab [Himem Hig]]]].
  destruct (gather_f_inv _ _ _ Hgf) as [Hfr Hfres].
  repeat rewrite seq_cat_eq in Hchk. repeat rewrite seq_map_eq in Hchk.
  match type of Hchk with
  | context [gather_m_e_types ?tt els] =>
      destruct (gather_m_e_types tt els) as [rts|] eqn:Hge
  end; cbn beta iota zeta in Hchk; try discriminate.
  match type of Hchk with
  | context [gather_m_d_types ?mm ds] =>
      destruct (gather_m_d_types mm ds) as [dts|] eqn:Hgd
  end; cbn beta iota zeta in Hchk; try discriminate.
  match type of Hchk with
  | context [if ?b then _ else _] => destruct b eqn:Hall; [|discriminate]
  end.
  destruct (module_exports_typer _ exps) as [expts|] eqn:Hex; [|discriminate].
  clear Hchk.
  apply Bool.andb_true_iff in Hall. destruct Hall as [Hall Hun].
  apply Bool.andb_true_iff in Hall. destruct Hall as [Hall Hst].
  apply Bool.andb_true_iff in Hall. destruct Hall as [Hall Hda].
  apply Bool.andb_true_iff in Hall. destruct Hall as [Hall Hel].
  apply Bool.andb_true_iff in Hall. destruct Hall as [Hall Hgl].
  apply Bool.andb_true_iff in Hall. destruct Hall as [Hall Hme].
  apply Bool.andb_true_iff in Hall. destruct Hall as [Hfu Hta].
  match type of Hfu with
  | context [module_func_type_checker ?cc] => set (c := cc) in *
  end.
  match type of Hgl with
  | context [module_global_type_checker ?cc] => set (c' := cc) in *
  end.
  match goal with |- module_wasm10 ?mm => set (M := mm) in * end.
  unfold module_wasm10. set (es := es_of M) in *.
  (* the four index spaces, as the checker built them *)
  assert (Hcf : tc_funcs c = ext_t_funcs impts ++ fts) by reflexivity.
  assert (Hct : tc_tables c = ext_t_tables impts ++ List.map modtab_type ts)
    by reflexivity.
  assert (Hcm : tc_mems c = ext_t_mems impts ++ List.map modmem_type ms)
    by reflexivity.
  assert (Hcg : tc_globals c = ext_t_globals impts ++ gather_m_g_types gs)
    by reflexivity.
  assert (Hc't : tc_tables c' = tc_tables c) by reflexivity.
  assert (Hc'f : tc_funcs c' = tc_funcs c) by reflexivity.
  assert (Hc'g : tc_globals c' = spec_imported_globals imps)
    by (change (tc_globals c') with (ext_t_globals impts); exact Hig).
  assert (Hgts : List.Forall gt_encodable (tc_globals c'))
    by (rewrite Hc'g; exact (gt_encodable_imported _ Eim)).
  assert (Hfun : all_funcs es = ext_t_funcs impts ++ fts).
  { change (all_funcs es)
      with (spec_resolve tfs
              (spec_imported_fidxs imps ++ List.map modfunc_type fs)).
    rewrite spec_resolve_app. rewrite Hif. rewrite Hfres. reflexivity. }
  assert (Htabs : all_tabtypes es
                  = ext_t_tables impts ++ List.map modtab_type ts).
  { change (all_tabtypes es)
      with (spec_imported_tables imps ++ List.map modtab_type ts).
    rewrite Hitab. reflexivity. }
  assert (Hmems : all_memtypes es
                  = ext_t_mems impts ++ List.map modmem_type ms).
  { change (all_memtypes es)
      with (spec_imported_mems imps ++ List.map modmem_type ms).
    rewrite Himem. reflexivity. }
  assert (Hglobs : all_globtypes es
                   = ext_t_globals impts ++ gather_m_g_types gs).
  { change (all_globtypes es)
      with (spec_imported_globals imps ++ List.map modglob_type gs).
    rewrite Hig. try rewrite gather_m_g_types_eq. reflexivity. }
  assert (Hnimp : spec_nimp_globals es = Z.of_nat (List.length (tc_globals c')))
    by (rewrite Hc'g; reflexivity).
  split; [|split].
  - (* the nine environment lines *)
    unfold env_wasm10. repeat split.
    + exact W1.
    + exact Him.
    + change (es_tidxs es) with (List.map modfunc_type fs).
      apply List.Forall_map. exact Hfr.
    + exact (Forall_of_all _ _ _ Hta).
    + exact (Forall_of_all _ _ _ Hme).
    + exact Wtab.
    + exact Wmem.
    + (* the global section's initialisers *)
      change (spec_imported_globals (es_imps es))
        with (spec_imported_globals imps).
      rewrite Hnimp. rewrite <- Hc'g.
      change (es_globs es) with gs.
      pose proof (Forall_of_all _ _ _ Hgl) as Hg2.
      rewrite List.Forall_forall in Hg2. rewrite List.Forall_forall in Egl.
      apply List.Forall_forall. intros g Hin.
      exact (global_checker_inv c' g (Hg2 g Hin) (Egl g Hin) Hgts).
    + exact (nodup_names_of_unique _ Hun).
    + (* the export descriptors *)
      pose proof (exports_typer_inv _ _ _ Hex) as Hexp.
      rewrite Hcf, Hct, Hcm, Hcg in Hexp.
      change (es_exps es) with exps.
      revert Hexp. apply List.Forall_impl. intros e He.
      unfold spec_exportdesc_wasm10.
      rewrite Hfun, Htabs, Hmems, Hglobs. exact He.
    + (* the start function *)
      intros st Hs. change (es_start es) with i_opt in Hs.
      rewrite Hs in Hst. cbn [pred_option] in Hst.
      rewrite Hfun. rewrite <- Hcf. exact (start_checker_inv c st Hst).
    + (* the element segments *)
      change (es_els es) with els.
      pose proof (Forall_of_all _ _ _ Hel) as He2.
      rewrite List.Forall_forall in He2. rewrite List.Forall_forall in Eel.
      apply List.Forall_forall. intros el Hin.
      destruct (elem_checker_inv c' el (He2 el Hin) (Eel el Hin) Hgts)
        as [x [e [ys [Hmode [Hxr [Hce [Hinit Hys]]]]]]].
      unfold spec_element_wasm10. rewrite Hmode. rewrite Hinit. split.
      * split.
        -- rewrite Htabs. rewrite <- Hct. rewrite <- Hc't. exact Hxr.
        -- change (spec_imported_globals (es_imps es))
             with (spec_imported_globals imps).
           rewrite Hnimp. rewrite <- Hc'g. exact Hce.
      * apply List.Forall_map. revert Hys. apply List.Forall_impl.
        intros y Hy. exists y. split; [reflexivity|].
        rewrite Hfun. rewrite <- Hcf. rewrite <- Hc'f. exact Hy.
  - (* the data segments *)
    change (mod_datas M) with ds.
    pose proof (Forall_of_all _ _ _ Hda) as Hd2.
    rewrite List.Forall_forall in Hd2. rewrite List.Forall_forall in Eda.
    apply List.Forall_forall. intros d Hin.
    destruct (data_checker_inv c' d (Hd2 d Hin) (Eda d Hin) Hgts)
      as [x [e [Hmode [Hxr Hce]]]].
    unfold spec_data_wasm10. rewrite Hmode. split.
    + rewrite Hmems. change (tc_mems c') with (tc_mems c). rewrite <- Hcm.
      exact Hxr.
    + change (spec_imported_globals (es_imps es))
        with (spec_imported_globals imps).
      rewrite Hnimp. rewrite <- Hc'g. exact Hce.
  - (* the code entries, at the module's own three index spaces *)
    exists (tc_elems c), (tc_datas c), (tc_refs c).
    change (List.map modfunc_type (mod_funcs M))
      with (List.map modfunc_type fs).
    change (codes_of M)
      with (List.map (fun f => (f.(modfunc_locals), f.(modfunc_body))) fs).
    apply forall2_of_forall_map.
    pose proof (Forall_of_all _ _ _ Hfu) as Hf2.
    rewrite List.Forall_forall in Hf2. rewrite List.Forall_forall in Efn.
    apply List.Forall_forall. intros f Hin.
    destruct (func_checker_inv c f (Hf2 f Hin)) as [tn [tm [Hnth Hbt]]].
    exists (Tf tn tm). cbn [fst snd].
    split; [exact Hnth|]. split; [exact (Efn f Hin)|].
    assert (Hctx : spec_func_context (tc_elems c) (tc_datas c) (tc_refs c) es
                     (Tf tn tm) f.(modfunc_locals)
                   = func_ctx c tn tm f.(modfunc_locals)).
    { unfold spec_func_context, func_ctx.
      rewrite Hfun, Htabs, Hmems, Hglobs.
      rewrite <- Hcf. rewrite <- Hct. rewrite <- Hcm. rewrite <- Hcg.
      reflexivity. }
    rewrite Hctx. exact Hbt.
Qed.

(* ================================================================== *)
(** ** No false rejects, against the type checker                      *)
(* ================================================================== *)

(** The end of the completeness chain, and the twin of
    [Module_Typing.validate_module_typed]: the validator accepts every Wasm 1.0
    module binary WasmCert's own module type checker accepts.

    It is stated against [module_type_checker] rather than [module_typing] for
    the same reason [validate_body_complete] is stated against
    [b_e_type_checker_aux]: WasmCert proves the checker sound, not complete, so
    the checker is the stronger of the two premises and the one a caller can
    actually decide.

    The two extern-type lists the caller supplied are the ones the accepting run
    reports, which is the completeness-side half of the relationship
    [Module_Typing.validate_module_typed] states. What identifies them is
    [Spec_Module.repr_module_det]: the bytes decode to one module only, so the
    module the run decoded is the caller's [m] and the checker's verdict on it
    is the caller's pair. *)
Theorem validate_module_typechecked : forall data m t_imps t_exps,
  dlen data <= module_bytes ->
  repr_module_fit (byte_list data) m ->
  module_type_checker m = Some (t_imps, t_exps) ->
  module_1_0 m ->
  exists vm imps exps,
    module_validate_module data = Ok (Core_result_Result_Ok vm)
    /\ module_import_types vm.(module_ValidatedModule_env)
         = Ok (Core_result_Result_Ok imps)
    /\ module_export_types vm.(module_ValidatedModule_env)
         = Ok (Core_result_Result_Ok exps)
    /\ translate_externtypes imps = t_imps
    /\ translate_externtypes exps = t_exps.
Proof.
  intros data m t_imps t_exps Hmod Hrepr Hchk H10.
  destruct (validate_module_complete data m Hmod Hrepr
              (module_wasm10_of_checker _ _ _ _ Hrepr Hchk H10)) as [vm Hvm].
  destruct (validate_module_checked _ _ Hvm)
    as [m' [imps [exps [Hm' [Himps [Hexps [_ [_ Hchk']]]]]]]].
  assert (Hsame : m' = m)
    by (apply (repr_module_det (byte_list data) m' m Hm');
        exact (repr_module_fit_module _ _ Hrepr)).
  subst m'.
  rewrite Hchk in Hchk'. injection Hchk' as Hi He.
  exists vm. exists imps. exists exps.
  split; [exact Hvm|]. split; [exact Himps|]. split; [exact Hexps|].
  split; [symmetry; exact Hi | symmetry; exact He].
Qed.
