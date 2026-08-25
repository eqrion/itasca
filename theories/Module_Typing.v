(** * An accepted module is well typed

    The second half of module soundness. [Module_Sound.validate_module_parts]
    says an accepting run means the input is a Wasm 1.0 module binary, and says
    which module it is: [module_of env fs tabs mems datas], built out of the
    environment the run produced. This file works up to

      module_type_checker (module_of ...) = Some (t_imps, t_exps)

    which [instantiation_spec.module_type_checker_sound] turns into
    [module_typing]. Going through the checker rather than proving
    [module_typing] directly is the single biggest saving available.

    [module_type_checker] is thirteen obligations and each has a counterpart in
    [module.rs]. Almost every one of them needs a fact about the *environment*
    rather than about one decoder, which is what [Module_Sound]'s
    [decode_env_preserves] invariants and [validate_module_parts]' field
    equations are for. [module_of_type_checker] discharges all thirteen;
    [validate_module_typed] at the end of the file is the theorem. *)

Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Import Itasca.Aeneas_Specs.
Require Import Itasca.Translate.
Require Import Itasca.OpIter_Decode.
Require Import Itasca.Spec_Module.
Require Import Itasca.Module_Sound.
Require Import Itasca.Module_Externs.

From Wasm Require Import datatypes datatypes_properties list_extra
                         operations typing type_checker
                         instantiation_spec instantiation_func
                         interp_instantiate_sound.
Require Import Itasca.Wasm_Bridge.

Local Open Scope list_scope.

(** [Forall] on the extracted side, [all] on WasmCert's. Every obligation that
    is a per-entry check crosses here. *)
Lemma forall_all_map : forall A B (f : A -> B) (p : B -> bool) (l : list A),
  List.Forall (fun x => p (f x) = true) l -> seq.all p (List.map f l) = true.
Proof.
  intros A B f p l Hall. induction l as [|x l IH]; [reflexivity|].
  inversion Hall as [|x' l' Hx Hl]; subst.
  cbn [List.map seq.all]. rewrite Hx. cbn [andb]. apply IH. exact Hl.
Qed.

(** A suffix of a list the environment invariant holds of. *)
Lemma forall_suffix : forall A (P : A -> Prop) pre suf l,
  l = pre ++ suf -> List.Forall P l -> List.Forall P suf.
Proof.
  intros A P pre suf l Heq Hall. rewrite Heq in Hall.
  apply (proj2 (proj1 (List.Forall_app _ _ _) Hall)).
Qed.

(** *** [module_table_type_checker] and [module_mem_type_checker]

    Both are spec 3.2.1 on the type the module *defines*, and both come out of
    [env_limits_valid]: every entry of the index space was checked where it was
    decoded, and what the module defines is the suffix of that space the import
    section did not write. *)
Lemma module_of_tables_ok : forall env tabs c,
  env_limits_valid env ->
  vec_list env.(env_Env_table_types)
    = imported_tables (vec_list env.(env_Env_imports)) ++ tabs ->
  seq.all (module_table_type_checker c)
    (List.map translate_table tabs) = true.
Proof.
  intros env tabs c [_ [Hvt _]] Hsplit.
  apply forall_all_map.
  apply (forall_suffix _ _ _ _ _ Hsplit Hvt).
Qed.

Lemma module_of_mems_ok : forall env mems c,
  env_limits_valid env ->
  vec_list env.(env_Env_mem_types)
    = imported_mems (vec_list env.(env_Env_imports)) ++ mems ->
  seq.all (module_mem_type_checker c)
    (List.map translate_mem mems) = true.
Proof.
  intros env mems c [_ [_ Hvm]] Hsplit.
  apply forall_all_map.
  apply (forall_suffix _ _ _ _ _ Hsplit Hvm).
Qed.

(* ================================================================== *)
(** ** Resolving a type index                                         *)
(* ================================================================== *)

(** [lookup_N] is [nth_error] at an [N], and a type index reaches it through
    [translate_idx]. The two conversions to [nat] agree, which is the whole
    content. *)
Lemma lookup_N_resolved : forall tys idx ft,
  List.nth_error tys (Z.to_nat (to_Z idx)) = Some ft ->
  lookup_N (List.map translate_functype tys) (translate_idx idx)
    = Some (translate_functype ft).
Proof.
  intros tys idx ft H. unfold lookup_N, translate_idx.
  rewrite Z_N_nat. apply List.map_nth_error. exact H.
Qed.

Lemma resolved_types_cons_some : forall tys idx xs ft,
  List.nth_error tys (Z.to_nat (to_Z idx)) = Some ft ->
  resolved_types tys (idx :: xs)
    = translate_functype ft :: resolved_types tys xs.
Proof.
  intros tys idx xs ft H. unfold resolved_types.
  cbn [List.flat_map]. rewrite H. reflexivity.
Qed.

(* ================================================================== *)
(** ** [module_imports_typer]                                          *)
(* ================================================================== *)

(** The checker makes [import_externs] of the import list. The three arms that
    carry a type outright are decided by spec 3.2.1, which is
    [env_limits_valid]; the function arm is a type-index lookup, which is
    [idx_in_range]. *)
Lemma module_imports_typer_ok : forall tys imps,
  List.Forall import_valid imps ->
  List.Forall (idx_in_range tys) (imported_func_idxs imps) ->
  module_imports_typer (List.map translate_functype tys)
                       (List.map translate_import imps)
    = Some (import_externs tys imps).
Proof.
  intros tys imps. unfold module_imports_typer.
  rewrite <- those_those0.
  induction imps as [|im imps IH]; intros Hval Hrange; [reflexivity|].
  inversion Hval as [|x l Hv Hvl]; subst.
  unfold import_valid in Hv.
  cbn [imported_func_idxs List.flat_map] in Hrange.
  (* [module_imports_typer] maps with mathcomp's [map], not [List.map] *)
  cbn [List.map seq.map those0 import_externs List.flat_map].
  unfold translate_import at 1. cbn [imp_desc]. unfold translate_importdesc.
  destruct im.(env_Import_desc) as [idx|t|m|g] eqn:Hd.
  - (* a function: the index has to resolve *)
    cbn [List.app] in Hrange.
    inversion Hrange as [|y l Hy Hyl]; subst.
    unfold idx_in_range in Hy.
    destruct (List.nth_error tys (Z.to_nat (to_Z idx))) as [ft|] eqn:Hnth;
      [|exfalso; apply Hy; reflexivity].
    cbn [module_import_desc_typer].
    rewrite (lookup_N_resolved _ _ _ Hnth). cbn [option_map].
    rewrite (IH Hvl Hyl). reflexivity.
  - (* a table and a memory carry their type, and it was checked *)
    cbn [List.app] in Hrange. cbn [module_import_desc_typer].
    rewrite Hv. rewrite (IH Hvl Hrange). reflexivity.
  - cbn [List.app] in Hrange. cbn [module_import_desc_typer].
    rewrite Hv. rewrite (IH Hvl Hrange). reflexivity.
  - (* a global has nothing to check *)
    cbn [List.app] in Hrange. cbn [module_import_desc_typer].
    rewrite (IH Hvl Hrange). reflexivity.
Qed.

(* ================================================================== *)
(** ** [gather_m_f_types]                                              *)
(* ================================================================== *)

(** The function section's indices, resolved. [funcs_of] pairs them with the
    code entries, so the [modfunc_type] the checker looks up is the index the
    decoder already resolved. *)
Lemma gather_m_f_types_ok : forall tys xs codes fs,
  funcs_of (List.map translate_idx xs) codes fs ->
  List.Forall (idx_in_range tys) xs ->
  gather_m_f_types (List.map translate_functype tys) fs
    = Some (resolved_types tys xs).
Proof.
  intros tys.
  (* stated over [those0], the structural twin of [those], so that the
     induction has something to compute with *)
  assert (Haux : forall xs codes fs,
            funcs_of (List.map translate_idx xs) codes fs ->
            List.Forall (idx_in_range tys) xs ->
            those0 (seq.map (gather_m_f_type (List.map translate_functype tys))
                            fs)
              = Some (resolved_types tys xs)).
  { induction xs as [|idx xs IH]; intros codes fs Hfs Hrange.
    - inversion Hfs. reflexivity.
    - cbn [List.map] in Hfs.
      inversion Hfs as [|x xs' lcls e cs fs' Hrest]; subst.
      inversion Hrange as [|y l Hy Hyl]; subst.
      unfold idx_in_range in Hy.
      destruct (List.nth_error tys (Z.to_nat (to_Z idx))) as [ft|] eqn:Hnth;
        [|exfalso; apply Hy; reflexivity].
      cbn [seq.map those0]. unfold gather_m_f_type at 1.
      cbn [modfunc_type].
      rewrite (lookup_N_resolved _ _ _ Hnth).
      rewrite (IH cs fs' Hrest Hyl). cbn [option_map].
      rewrite (resolved_types_cons_some _ _ _ _ Hnth). reflexivity. }
  intros xs codes fs Hfs Hrange. unfold gather_m_f_types.
  rewrite <- those_those0. apply (Haux xs codes fs Hfs Hrange).
Qed.

(* ================================================================== *)
(** ** The index spaces the checker builds                             *)
(* ================================================================== *)

(** [module_type_checker] puts the context's index spaces together as
    "what the imports gave, then what the module defines": [ifts ++ fts],
    [its ++ map modtab_type ts], [ims ++ map modmem_type ms]. Ours are single
    vectors with the imported entries in front, so the two agree exactly when
    the split is where [import_spaces] says it is. *)
Lemma pmap_app : forall A B (f : A -> option B) l1 l2,
  seq.pmap f (l1 ++ l2) = seq.pmap f l1 ++ seq.pmap f l2.
Proof.
  intros A B f l1 l2. induction l1 as [|x l1 IH]; [reflexivity|].
  cbn [List.app seq.pmap ssrfun.oapp]. destruct (f x); cbn [List.app];
    rewrite IH; reflexivity.
Qed.

Lemma ext_t_funcs_app : forall a b,
  ext_t_funcs (a ++ b) = ext_t_funcs a ++ ext_t_funcs b.
Proof. intros a b. apply pmap_app. Qed.

Lemma ext_t_tables_app : forall a b,
  ext_t_tables (a ++ b) = ext_t_tables a ++ ext_t_tables b.
Proof. intros a b. apply pmap_app. Qed.

Lemma ext_t_mems_app : forall a b,
  ext_t_mems (a ++ b) = ext_t_mems a ++ ext_t_mems b.
Proof. intros a b. apply pmap_app. Qed.

Lemma ext_t_globals_app : forall a b,
  ext_t_globals (a ++ b) = ext_t_globals a ++ ext_t_globals b.
Proof. intros a b. apply pmap_app. Qed.

(** One import at a time: with the descriptor a constructor both sides
    compute, which is why the import record is destructed rather than its
    field. *)
Lemma ext_t_funcs_imports : forall tys imps,
  ext_t_funcs (import_externs tys imps)
    = resolved_types tys (imported_func_idxs imps).
Proof.
  intros tys imps. induction imps as [|im imps IH]; [reflexivity|].
  rewrite import_externs_cons. rewrite ext_t_funcs_app. rewrite IH.
  destruct im as [md nm [idx|t|m|g]]; [|reflexivity|reflexivity|reflexivity].
  unfold import_externs, resolved_types, imported_func_idxs. cbn [List.flat_map env_Import_desc app].
  destruct (List.nth_error tys (Z.to_nat (to_Z idx))); reflexivity.
Qed.

Lemma ext_t_tables_imports : forall tys imps,
  ext_t_tables (import_externs tys imps)
    = List.map translate_tabletype (imported_tables imps).
Proof.
  intros tys imps. induction imps as [|im imps IH]; [reflexivity|].
  rewrite import_externs_cons. rewrite ext_t_tables_app. rewrite IH.
  destruct im as [md nm [idx|t|m|g]]; [|reflexivity|reflexivity|reflexivity].
  unfold import_externs, imported_tables. cbn [List.flat_map env_Import_desc app].
  destruct (List.nth_error tys (Z.to_nat (to_Z idx))); reflexivity.
Qed.

Lemma ext_t_mems_imports : forall tys imps,
  ext_t_mems (import_externs tys imps)
    = List.map translate_memtype (imported_mems imps).
Proof.
  intros tys imps. induction imps as [|im imps IH]; [reflexivity|].
  rewrite import_externs_cons. rewrite ext_t_mems_app. rewrite IH.
  destruct im as [md nm [idx|t|m|g]]; [|reflexivity|reflexivity|reflexivity].
  unfold import_externs, imported_mems. cbn [List.flat_map env_Import_desc app].
  destruct (List.nth_error tys (Z.to_nat (to_Z idx))); reflexivity.
Qed.

Lemma ext_t_globals_imports : forall tys imps,
  ext_t_globals (import_externs tys imps)
    = List.map translate_globaltype (imported_globals imps).
Proof.
  intros tys imps. induction imps as [|im imps IH]; [reflexivity|].
  rewrite import_externs_cons. rewrite ext_t_globals_app. rewrite IH.
  destruct im as [md nm [idx|t|m|g]]; [|reflexivity|reflexivity|reflexivity].
  unfold import_externs, imported_globals. cbn [List.flat_map env_Import_desc app].
  destruct (List.nth_error tys (Z.to_nat (to_Z idx))); reflexivity.
Qed.

(** The three spaces, each the environment's own vector, given where the
    import section's entries end. *)
Lemma checker_tc_funcs : forall env,
  env_func_space env (imported_func_idxs (vec_list env.(env_Env_imports))
                      ++ vec_list env.(env_Env_func_type_indices)) ->
  ext_t_funcs (import_externs (vec_list env.(env_Env_types))
                              (vec_list env.(env_Env_imports)))
    ++ resolved_types (vec_list env.(env_Env_types))
         (vec_list env.(env_Env_func_type_indices))
    = List.map translate_functype (vec_list env.(env_Env_func_types)).
Proof.
  intros env [Hmap _]. rewrite ext_t_funcs_imports.
  rewrite <- resolved_types_app. symmetry. exact Hmap.
Qed.

Lemma checker_tc_tables : forall env tabs,
  vec_list env.(env_Env_table_types)
    = imported_tables (vec_list env.(env_Env_imports)) ++ tabs ->
  ext_t_tables (import_externs (vec_list env.(env_Env_types))
                               (vec_list env.(env_Env_imports)))
    ++ List.map modtab_type (List.map translate_table tabs)
    = List.map translate_tabletype (vec_list env.(env_Env_table_types)).
Proof.
  intros env tabs Hsplit. rewrite ext_t_tables_imports. rewrite Hsplit.
  rewrite List.map_app. rewrite List.map_map. reflexivity.
Qed.

Lemma checker_tc_mems : forall env mems,
  vec_list env.(env_Env_mem_types)
    = imported_mems (vec_list env.(env_Env_imports)) ++ mems ->
  ext_t_mems (import_externs (vec_list env.(env_Env_types))
                             (vec_list env.(env_Env_imports)))
    ++ List.map modmem_type (List.map translate_mem mems)
    = List.map translate_memtype (vec_list env.(env_Env_mem_types)).
Proof.
  intros env mems Hsplit. rewrite ext_t_mems_imports. rewrite Hsplit.
  rewrite List.map_app. rewrite List.map_map. reflexivity.
Qed.

Lemma checker_tc_globals : forall env globs,
  vec_list env.(env_Env_global_types)
    = imported_globals (vec_list env.(env_Env_imports))
      ++ List.map (fun g => g.(env_Global_gtype)) globs ->
  ext_t_globals (import_externs (vec_list env.(env_Env_types))
                                (vec_list env.(env_Env_imports)))
    ++ gather_m_g_types (List.map translate_global globs)
    = List.map translate_globaltype (vec_list env.(env_Env_global_types)).
Proof.
  intros env globs Hsplit. rewrite ext_t_globals_imports. rewrite Hsplit.
  rewrite List.map_app. unfold gather_m_g_types.
  rewrite List.map_map. rewrite List.map_map. reflexivity.
Qed.

(* ================================================================== *)
(** ** Constant expressions                                           *)
(* ================================================================== *)

(** Spec 3.3.7 in the checker's terms. The four literal arms compute; the
    [global.get] arm is a lookup in [tc_globals], which for the context the
    module's initialisers are checked in holds the imported globals and
    nothing else -- which is why the decoder had to report that the index sits
    in that prefix. *)
Lemma const_expr_typed : forall env c t e,
  tc_globals c = List.map translate_globaltype
                   (imported_globals (vec_list env.(env_Env_imports))) ->
  vec_list env.(env_Env_global_types)
    = imported_globals (vec_list env.(env_Env_imports))
      ++ List.map (fun g => g.(env_Global_gtype))
           (vec_list env.(env_Env_globals)) ->
  to_Z env.(env_Env_num_imported_globals)
    = Z.of_nat (List.length
        (imported_globals (vec_list env.(env_Env_imports)))) ->
  const_expr_ok env t e ->
  const_exprs c [translate_const_expr e] = true
  /\ b_e_type_checker c [translate_const_expr e]
       (Tf [] [translate_vt_v t]) = true.
Proof.
  intros env c t e Hc Hsplit Hnig H.
  destruct e as [v|v|b|b|x]; cbn [translate_const_expr];
    [ cbn [const_expr_ok] in H; subst t; split; reflexivity
    | cbn [const_expr_ok] in H; subst t; split; reflexivity
    | cbn [const_expr_ok] in H; subst t; split; reflexivity
    | cbn [const_expr_ok] in H; subst t; split; reflexivity
    | ].
  (* [global.get]: the index is inside the imported prefix *)
  destruct H as [gt [Hnth [Hmut [Hty Hlt]]]].
  assert (Hpre : List.nth_error
                   (imported_globals (vec_list env.(env_Env_imports)))
                   (Z.to_nat (to_Z x)) = Some gt).
  { rewrite Hsplit in Hnth. rewrite List.nth_error_app1 in Hnth;
      [exact Hnth|].
    apply Nat2Z.inj_lt. rewrite Z2Nat.id by (pose proof (u32_nonneg x); lia).
    lia. }
  assert (Hlk : lookup_N (tc_globals c) (translate_idx x)
                = Some (translate_globaltype gt)).
  { rewrite Hc. unfold lookup_N, translate_idx. rewrite Z_N_nat.
    apply List.map_nth_error. exact Hpre. }
  unfold translate_idx in Hlk.
  split.
  - unfold const_exprs. cbn [seq.all const_expr]. rewrite Hlk.
    unfold translate_globaltype. cbn [tg_mut andb].
    rewrite Hmut. cbn [translate_mut]. rewrite eqb_refl_true. reflexivity.
  - unfold b_e_type_checker. cbn [b_e_type_checker_aux].
    cbn [List.fold_left seq.foldl check_single context_reverse tc_globals].
    rewrite Hlk. rewrite <- Hty.
    unfold translate_globaltype. cbn [tg_t].
    destruct (types_GlobalType_valtype gt); reflexivity.
Qed.

(* ================================================================== *)
(** ** Small bridges                                                   *)
(* ================================================================== *)

Lemma seq_cat_eq : forall A (a b : list A), seq.cat a b = a ++ b.
Proof.
  intros A a b. induction a as [|x a IH]; [reflexivity|].
  cbn [seq.cat List.app]. rewrite IH. reflexivity.
Qed.

Lemma seq_map_eq : forall A B (f : A -> B) (l : list A),
  seq.map f l = List.map f l.
Proof.
  intros A B f l. induction l as [|x l IH]; [reflexivity|].
  cbn [seq.map List.map]. rewrite IH. reflexivity.
Qed.

(** Wasm 1.0's value types all have a default, which is
    [module_func_type_checker]'s last conjunct. *)
Lemma default_vals_num : forall ts,
  List.Forall (fun t => exists nt, t = T_num nt) ts -> default_vals ts <> None.
Proof.
  intros ts. unfold default_vals. rewrite <- those_those0.
  induction ts as [|t ts IH]; intros Hall; [discriminate|].
  inversion Hall as [|h l Ht Hl]; subst. destruct Ht as [nt ->].
  cbn [seq.map those0 default_val].
  destruct (those0 (seq.map default_val ts)) as [vs|] eqn:E.
  - cbn [option_map]. discriminate.
  - exfalso. exact (IH Hl eq_refl).
Qed.

Lemma default_vals_map : forall l,
  default_vals (List.map translate_vt_v l) <> None.
Proof.
  intros l. apply default_vals_num.
  induction l as [|v l IH]; [apply List.Forall_nil|].
  cbn [List.map]. apply List.Forall_cons; [|exact IH].
  destruct v; [exists T_i32|exists T_i64|exists T_f32|exists T_f64];
    reflexivity.
Qed.

(** [translate_name] is injective on the byte strings a name can hold, which
    is what carries the decoder's "no two exports share a byte string" to
    WasmCert's [export_name_unique]. *)
Lemma translate_name_byte_inj : forall a b : u8,
  translate_name_byte a = translate_name_byte b -> to_Z a = to_Z b.
Proof.
  intros a b H. unfold translate_name_byte in H.
  pose proof (u8_bounds a) as Ha. pose proof (u8_bounds b) as Hb.
  destruct (Byte.of_N (Z.to_N (to_Z a))) as [x|] eqn:Hx.
  2: { exfalso. apply Byte.of_N_None_iff in Hx.
       apply N2Z.inj_lt in Hx. rewrite Z2N.id in Hx by lia. cbn in Hx. lia. }
  destruct (Byte.of_N (Z.to_N (to_Z b))) as [y|] eqn:Hy.
  2: { exfalso. apply Byte.of_N_None_iff in Hy.
       apply N2Z.inj_lt in Hy. rewrite Z2N.id in Hy by lia. cbn in Hy. lia. }
  cbn in H. subst y.
  apply Byte.to_of_N in Hx. apply Byte.to_of_N in Hy.
  rewrite Hx in Hy. apply (f_equal Z.of_N) in Hy.
  rewrite Z2N.id in Hy by lia. rewrite Z2N.id in Hy by lia.
  exact Hy.
Qed.

Lemma translate_name_inj : forall a b,
  translate_name a = translate_name b -> byte_list a = byte_list b.
Proof.
  intros a b. unfold translate_name, byte_list.
  generalize (vec_list a) as la. generalize (vec_list b) as lb.
  intros lb la. revert lb.
  induction la as [|x la IH]; intros lb H; destruct lb as [|y lb];
    cbn [List.map] in *; try discriminate; [reflexivity|].
  injection H as Hhd Htl.
  rewrite (translate_name_byte_inj _ _ Hhd). rewrite (IH lb Htl). reflexivity.
Qed.

Lemma nodup_map_of : forall A B C (f : A -> B) (g : A -> C) (l : list A),
  (forall x y, g x = g y -> f x = f y) ->
  List.NoDup (List.map f l) -> List.NoDup (List.map g l).
Proof.
  intros A B C f g l Hinj. induction l as [|x l IH]; intros H;
    [apply List.NoDup_nil|].
  cbn [List.map] in *. inversion H as [|h t Hnin Hnd]; subst.
  apply List.NoDup_cons; [|apply IH; exact Hnd].
  intros Hin. apply Hnin. apply List.in_map_iff in Hin.
  destruct Hin as [y [Hgy Hiny]]. apply List.in_map_iff.
  exists y. split; [symmetry; apply Hinj; symmetry; exact Hgy | exact Hiny].
Qed.

Lemma export_name_unique_ok : forall exps,
  List.NoDup (List.map export_name exps) ->
  export_name_unique (List.map translate_export exps) = true.
Proof.
  intros exps H. unfold export_name_unique.
  assert (Hnd : List.NoDup
                  (seq.map modexp_name (List.map translate_export exps))).
  { rewrite seq_map_eq. rewrite List.map_map.
    apply (nodup_map_of _ _ _ export_name
             (fun e => modexp_name (translate_export e)) exps);
      [| exact H].
    intros x y Hxy. unfold export_name.
    apply translate_name_inj. exact Hxy. }
  rewrite (List.nodup_fixed_point _ Hnd). apply eqb_refl_true.
Qed.

(* ================================================================== *)
(** ** The element and data segments' prepass                          *)
(* ================================================================== *)

(** [gather_m_e_types] and [gather_m_d_types] are the two lookups the checker
    makes before it builds its context: an active element segment names a
    table and an active data segment names a memory. In Wasm 1.0 both indices
    were checked as the section was decoded, and the segment's reference type
    is [T_funcref] on both sides. *)
Lemma lookup_N_map : forall A B (f : A -> B) l (x : scalar U32) v,
  List.nth_error l (Z.to_nat (to_Z x)) = Some v ->
  lookup_N (List.map f l) (translate_idx x) = Some (f v).
Proof.
  intros A B f l x v H. unfold lookup_N, translate_idx.
  rewrite Z_N_nat. apply List.map_nth_error. exact H.
Qed.

Lemma lookup_N_seq_map : forall A B (f : A -> B) l n v,
  lookup_N l n = Some v -> lookup_N (seq.map f l) n = Some (f v).
Proof.
  intros A B f l n v H. unfold lookup_N in *. rewrite seq_map_eq.
  apply List.map_nth_error. exact H.
Qed.

Lemma nth_error_of_lt : forall A (l : list A) (x : scalar U32),
  to_Z x < Z.of_nat (List.length l) ->
  exists v, List.nth_error l (Z.to_nat (to_Z x)) = Some v.
Proof.
  intros A l x H.
  destruct (List.nth_error l (Z.to_nat (to_Z x))) as [v|] eqn:E;
    [exists v; reflexivity|].
  exfalso. apply List.nth_error_None in E.
  apply Nat2Z.inj_le in E. rewrite Z2Nat.id in E
    by (pose proof (u32_nonneg x); lia). lia.
Qed.

Lemma gather_m_e_types_ok : forall env els,
  List.Forall (element_ok env) els ->
  gather_m_e_types
    (List.map translate_tabletype (vec_list env.(env_Env_table_types)))
    (List.map translate_element els)
    = Some (List.map (fun _ => T_funcref) els).
Proof.
  intros env els. unfold gather_m_e_types. rewrite <- those_those0.
  induction els as [|el els IH]; intros Hall; [reflexivity|].
  inversion Hall as [|h t Hel Hels]; subst.
  destruct Hel as [Ht _].
  destruct (nth_error_of_lt _ (vec_list env.(env_Env_table_types))
              el.(env_Element_table_idx) Ht) as [tt0 Hnth].
  cbn [List.map seq.map those0 gather_m_e_type translate_element
       modelem_mode modelem_type].
  rewrite (lookup_N_map _ _ translate_tabletype _ _ _ Hnth).
  cbn [option_map tt_elem_type translate_tabletype].
  rewrite eqb_refl_true.
  rewrite (IH Hels). reflexivity.
Qed.

Lemma gather_m_d_types_ok : forall env ds,
  List.Forall (data_ok env) ds ->
  gather_m_d_types
    (List.map translate_memtype (vec_list env.(env_Env_mem_types)))
    (List.map translate_data ds)
    = Some (List.map (fun _ => tt) ds).
Proof.
  intros env ds. unfold gather_m_d_types. rewrite <- those_those0.
  induction ds as [|d ds IH]; intros Hall; [reflexivity|].
  inversion Hall as [|h t Hd Hds]; subst.
  destruct Hd as [Hm _].
  destruct (nth_error_of_lt _ (vec_list env.(env_Env_mem_types))
              d.(module_Data_memory_idx) Hm) as [mt0 Hnth].
  cbn [List.map seq.map those0 gather_m_d_type translate_data moddata_mode].
  rewrite (lookup_N_map _ _ translate_memtype _ _ _ Hnth).
  cbn [option_map]. rewrite (IH Hds). reflexivity.
Qed.

(* ================================================================== *)
(** ** The function indices an element segment mentions                *)
(* ================================================================== *)

(** [BI_ref_func x] type-checks only if [x] is in the context's [tc_refs],
    which [module_type_checker] fills with [module_filter_funcidx m] -- the
    indices the module's globals and element segments name. A 1.0 element
    segment's initialiser is exactly one [ref.func] per index it writes, so
    every index it writes is in there by construction. *)
Lemma in_module_filter_funcidx : forall m el x,
  List.In el m.(mod_elems) ->
  List.In [BI_ref_func x] el.(modelem_init) ->
  List.In x (module_filter_funcidx m).
Proof.
  intros m el x Hel Hin. unfold module_filter_funcidx.
  apply List.nodup_In. apply List.in_or_app. right.
  unfold module_elems_get_funcidx. apply List.nodup_In.
  apply List.in_concat. exists (module_elem_get_funcidx el). split.
  - apply List.in_map. exact Hel.
  - unfold module_elem_get_funcidx. apply List.nodup_In.
    apply List.in_or_app. left.
    apply List.in_concat. exists (expr_get_funcidx [BI_ref_func x]). split.
    + apply List.in_map. exact Hin.
    + cbn [expr_get_funcidx be_get_funcidx List.map List.concat
           nlist_nodup List.nodup List.in_dec].
      left. reflexivity.
Qed.

(* ================================================================== *)
(** ** The per-entry checks                                            *)
(* ================================================================== *)

(** Each of these takes the context's fields as equations rather than the
    context itself, because [module_type_checker] builds two of them -- [c]
    for the functions, tables, memories, start and exports, [c'] with only the
    imported globals for the initialisers -- and the checks split between
    them. *)

Lemma module_global_type_checker_ok : forall env c' g,
  tc_globals c' = List.map translate_globaltype
                    (imported_globals (vec_list env.(env_Env_imports))) ->
  vec_list env.(env_Env_global_types)
    = imported_globals (vec_list env.(env_Env_imports))
      ++ List.map (fun x => x.(env_Global_gtype))
           (vec_list env.(env_Env_globals)) ->
  to_Z env.(env_Env_num_imported_globals)
    = Z.of_nat (List.length
        (imported_globals (vec_list env.(env_Env_imports)))) ->
  global_ok env g ->
  module_global_type_checker c' (translate_global g) = true.
Proof.
  intros env c' g Hc Hsplit Hnig H.
  destruct (const_expr_typed env c' _ _ Hc Hsplit Hnig H) as [Hconst Hchk].
  unfold module_global_type_checker, translate_global.
  cbn [modglob_type modglob_init].
  rewrite Hconst. cbn [andb].
  unfold translate_globaltype. cbn [tg_t]. exact Hchk.
Qed.

Lemma module_data_type_checker_ok : forall c' d,
  module_data_type_checker c' (translate_data d)
    = module_data_mode_checker c' (MD_active
        (translate_idx d.(module_Data_memory_idx))
        [translate_const_expr d.(module_Data_offset)]).
Proof. intros c' d. reflexivity. Qed.

Lemma module_data_type_checker_true : forall env c' d,
  tc_mems c' = List.map translate_memtype (vec_list env.(env_Env_mem_types)) ->
  tc_globals c' = List.map translate_globaltype
                    (imported_globals (vec_list env.(env_Env_imports))) ->
  vec_list env.(env_Env_global_types)
    = imported_globals (vec_list env.(env_Env_imports))
      ++ List.map (fun x => x.(env_Global_gtype))
           (vec_list env.(env_Env_globals)) ->
  to_Z env.(env_Env_num_imported_globals)
    = Z.of_nat (List.length
        (imported_globals (vec_list env.(env_Env_imports)))) ->
  data_ok env d ->
  module_data_type_checker c' (translate_data d) = true.
Proof.
  intros env c' d Hm Hc Hsplit Hnig [Hidx Hoff].
  rewrite module_data_type_checker_ok.
  destruct (nth_error_of_lt _ (vec_list env.(env_Env_mem_types))
              d.(module_Data_memory_idx) Hidx) as [mt Hnth].
  cbn [module_data_mode_checker].
  rewrite Hm. rewrite (lookup_N_map _ _ translate_memtype _ _ _ Hnth).
  destruct (const_expr_typed env c' Types_ValueType_I32 _ Hc Hsplit Hnig Hoff)
    as [Hconst Hchk].
  cbn [translate_vt_v] in Hchk. rewrite Hchk. rewrite Hconst. reflexivity.
Qed.

Lemma module_elem_type_checker_ok : forall env c' m el,
  tc_tables c' = List.map translate_tabletype
                   (vec_list env.(env_Env_table_types)) ->
  tc_funcs c' = List.map translate_functype
                  (vec_list env.(env_Env_func_types)) ->
  tc_globals c' = List.map translate_globaltype
                    (imported_globals (vec_list env.(env_Env_imports))) ->
  tc_refs c' = module_filter_funcidx m ->
  List.In (translate_element el) m.(mod_elems) ->
  vec_list env.(env_Env_global_types)
    = imported_globals (vec_list env.(env_Env_imports))
      ++ List.map (fun x => x.(env_Global_gtype))
           (vec_list env.(env_Env_globals)) ->
  to_Z env.(env_Env_num_imported_globals)
    = Z.of_nat (List.length
        (imported_globals (vec_list env.(env_Env_imports)))) ->
  element_ok env el ->
  module_elem_type_checker c' (translate_element el) = true.
Proof.
  intros env c' m el Ht Hf Hg Hr Hin Hsplit Hnig [Htidx [Hoff Hinit]].
  unfold module_elem_type_checker, translate_element.
  cbn [modelem_type modelem_init modelem_mode].
  (* every [ref.func] is constant, and types at [[] -> [funcref]] *)
  assert (Hall1 : seq.all (const_exprs c')
                    (List.map (fun y => [BI_ref_func (translate_idx y)])
                       (vec_list el.(env_Element_init))) = true).
  { apply all_of_Forall. apply List.Forall_forall. intros es Hes.
    apply List.in_map_iff in Hes. destruct Hes as [y [<- _]]. reflexivity. }
  rewrite Hall1. cbn [andb].
  assert (Hall2 : seq.all
                    (fun es => b_e_type_checker c' es
                                 (Tf [] [T_ref T_funcref]))
                    (List.map (fun y => [BI_ref_func (translate_idx y)])
                       (vec_list el.(env_Element_init))) = true).
  { apply all_of_Forall. apply List.Forall_forall. intros es Hes.
    apply List.in_map_iff in Hes. destruct Hes as [y [<- Hy]].
    rewrite List.Forall_forall in Hinit.
    destruct (nth_error_of_lt _ (vec_list env.(env_Env_func_types)) y
                (Hinit y Hy)) as [ft Hnth].
    unfold b_e_type_checker.
    cbn [b_e_type_checker_aux List.fold_left seq.foldl check_single
         context_reverse tc_funcs tc_refs].
    rewrite Hf.
    rewrite (lookup_N_seq_map _ _ rev_tf _ _ _
               (lookup_N_map _ _ translate_functype _ _ _ Hnth)).
    rewrite Hr.
    pose proof (mem_of_In datatypes_properties.u32_eqType (translate_idx y)
                  (module_filter_funcidx m)
                  (in_module_filter_funcidx m (translate_element el)
                     (translate_idx y) Hin
                     (ltac:(cbn [translate_element modelem_init];
                            apply List.in_map_iff; exists y;
                            split; [reflexivity | exact Hy])))) as Hmem.
    (* the membership test and the lemma's are the same boolean up to the
       instances Coq chose for each *)
    match goal with
    | |- context [if ?b then _ else _] => destruct b eqn:Emem
    end;
      [ reflexivity
      | exfalso; exact (Bool.diff_true_false (eq_trans (eq_sym Hmem) Emem)) ].
  }
  rewrite Hall2. cbn [andb].
  (* the mode: the table index, the offset expression *)
  cbn [module_elem_mode_checker].
  destruct (nth_error_of_lt _ (vec_list env.(env_Env_table_types))
              el.(env_Element_table_idx) Htidx) as [tt0 Hnth].
  rewrite Ht. rewrite (lookup_N_map _ _ translate_tabletype _ _ _ Hnth).
  cbn [tt_elem_type translate_tabletype]. rewrite eqb_refl_true.
  cbn [andb].
  destruct (const_expr_typed env c' Types_ValueType_I32 _ Hg Hsplit Hnig Hoff)
    as [Hconst Hchk].
  cbn [translate_vt_v] in Hchk. rewrite Hchk. rewrite Hconst. reflexivity.
Qed.

Lemma module_start_type_checker_ok : forall env c st,
  tc_funcs c = List.map translate_functype
                 (vec_list env.(env_Env_func_types)) ->
  start_ok env ->
  env.(env_Env_start) = st ->
  pred_option (module_start_type_checker c) (translate_start st) = true.
Proof.
  intros env c st Hf H Hst. unfold start_ok in H. rewrite Hst in H.
  destruct st as [x|]; [|reflexivity].
  destruct H as [ft [Hnth [Hps Hrs]]].
  unfold translate_start. cbn [option_map pred_option].
  unfold module_start_type_checker, module_start_typing.
  cbn [modstart_func].
  rewrite Hf. rewrite (lookup_N_map _ _ translate_functype _ _ _ Hnth).
  unfold vec_list in Hps, Hrs.
  unfold translate_functype. rewrite Hps. rewrite Hrs.
  cbn [List.map]. apply eqb_refl_true.
Qed.

(* ================================================================== *)
(** ** [module_exports_typer]                                          *)
(* ================================================================== *)

(** And [export_externs] of the export list. An export names an index space
    entry, so unlike an import it carries no type of its own and every arm is a
    lookup; [export_desc_ok] is what makes all four of them succeed.

    Naming both lists rather than producing witnesses is what lets
    [validate_module_typed] say the import and export types WasmCert's type
    system assigns are the ones [module::import_types] and
    [module::export_types] return. *)
Lemma module_exports_typer_ok : forall env c exps,
  tc_funcs c = List.map translate_functype
                 (vec_list env.(env_Env_func_types)) ->
  tc_tables c = List.map translate_tabletype
                  (vec_list env.(env_Env_table_types)) ->
  tc_mems c = List.map translate_memtype (vec_list env.(env_Env_mem_types)) ->
  tc_globals c = List.map translate_globaltype
                   (vec_list env.(env_Env_global_types)) ->
  List.Forall (export_desc_ok env) exps ->
  module_exports_typer c (List.map translate_export exps)
    = Some (export_externs env exps).
Proof.
  intros env c exps Hf Ht Hm Hg. unfold module_exports_typer.
  rewrite <- those_those0.
  induction exps as [|e exps IH]; intros Hall; [reflexivity|].
  inversion Hall as [|h t He Hes]; subst.
  cbn [List.map seq.map those0].
  unfold translate_export at 1. cbn [modexp_desc].
  unfold export_desc_ok in He. unfold translate_exportdesc.
  rewrite (IH Hes). cbn [export_externs List.flat_map].
  destruct e.(env_Export_desc) as [x|x|x|x]; cbn [module_export_typer].
  - destruct (nth_error_of_lt _ (vec_list env.(env_Env_func_types)) x He)
      as [v Hnth].
    rewrite Hf. rewrite (lookup_N_map _ _ translate_functype _ _ _ Hnth).
    rewrite Hnth. reflexivity.
  - destruct (nth_error_of_lt _ (vec_list env.(env_Env_table_types)) x He)
      as [v Hnth].
    rewrite Ht. rewrite (lookup_N_map _ _ translate_tabletype _ _ _ Hnth).
    rewrite Hnth. reflexivity.
  - destruct (nth_error_of_lt _ (vec_list env.(env_Env_mem_types)) x He)
      as [v Hnth].
    rewrite Hm. rewrite (lookup_N_map _ _ translate_memtype _ _ _ Hnth).
    rewrite Hnth. reflexivity.
  - destruct (nth_error_of_lt _ (vec_list env.(env_Env_global_types)) x He)
      as [v Hnth].
    rewrite Hg. rewrite (lookup_N_map _ _ translate_globaltype _ _ _ Hnth).
    rewrite Hnth. reflexivity.
Qed.

(* ================================================================== *)
(** ** The code entries                                                *)
(* ================================================================== *)

(** The obligation with content. [code_typed] already says the body checks
    against the type its index names, in the context [func_body_context]
    builds; all that is left is that the checker's own [c'] is that context,
    which it is once the module's index spaces are the environment's. *)
Lemma module_func_type_checker_ok : forall env c,
  tc_types c = List.map translate_functype (vec_list env.(env_Env_types)) ->
  tc_funcs c = List.map translate_functype
                 (vec_list env.(env_Env_func_types)) ->
  tc_tables c = List.map translate_tabletype
                  (vec_list env.(env_Env_table_types)) ->
  tc_mems c = List.map translate_memtype (vec_list env.(env_Env_mem_types)) ->
  tc_globals c = List.map translate_globaltype
                   (vec_list env.(env_Env_global_types)) ->
  tc_locals c = [] ->
  tc_labels c = [] ->
  forall tidxs codes fs,
  funcs_of (List.map translate_idx tidxs) codes fs ->
  List.Forall2 (code_typed env) tidxs codes ->
  seq.all (module_func_type_checker c) fs = true.
Proof.
  intros env c Hty Hfn Htb Hmm Hgl Hloc Hlab tidxs.
  induction tidxs as [|tidx tidxs IH]; intros codes fs Hfuncs Hall.
  - inversion Hall; subst. cbn [List.map] in Hfuncs. inversion Hfuncs; subst.
    reflexivity.
  - inversion Hall as [|x y l1 l2 Hc Hrest]; subst.
    cbn [List.map] in Hfuncs.
    inversion Hfuncs as [|x0 xs0 lcls e cs fs0 Hfs Heq1 Heq2 Heq3]; subst.
    destruct Hc as [ft [Hnth [[ds Hds] Hchk]]].
    cbn [fst snd] in Hds, Hchk.
    cbn [seq.all].
    (* the head entry *)
    assert (Hhead : module_func_type_checker c
                      {| modfunc_type := translate_idx tidx;
                         modfunc_locals := lcls;
                         modfunc_body := e |} = true).
    { unfold module_func_type_checker.
      cbn [modfunc_type modfunc_locals modfunc_body].
      rewrite Hty. rewrite (lookup_N_map _ _ translate_functype _ _ _ Hnth).
      unfold translate_functype at 1.
      rewrite Hloc. rewrite Hlab.
      (* with the index spaces rewritten, the checker's [c'] and
         [func_body_context] are the same record up to [[] ++ _] *)
      rewrite Hfn. rewrite Htb. rewrite Hmm. rewrite Hgl.
      apply Bool.andb_true_iff. split.
      - exact (Hchk (tc_elems c) (tc_datas c) (tc_refs c)).
      - apply neq_true. rewrite Hds. apply default_vals_map. }
    rewrite Hhead. cbn [andb]. apply (IH l2 fs0 Hfs Hrest).
Qed.

(* ================================================================== *)
(** ** The module type checker                                         *)
(* ================================================================== *)

(** All thirteen obligations, for the module an accepting run decoded. The
    hypotheses are exactly what [Module_Sound.validate_module_parts] hands
    back. *)
Theorem module_of_type_checker : forall env fs tabs mems ds codes,
  env_limits_valid env ->
  vec_list env.(env_Env_table_types)
    = imported_tables (vec_list env.(env_Env_imports)) ++ tabs ->
  vec_list env.(env_Env_mem_types)
    = imported_mems (vec_list env.(env_Env_imports)) ++ mems ->
  env_func_space env
    (imported_func_idxs (vec_list env.(env_Env_imports))
     ++ vec_list env.(env_Env_func_type_indices)) ->
  vec_list env.(env_Env_global_types)
    = imported_globals (vec_list env.(env_Env_imports))
      ++ List.map (fun g => g.(env_Global_gtype))
           (vec_list env.(env_Env_globals)) ->
  to_Z env.(env_Env_num_imported_globals)
    = Z.of_nat (List.length
        (imported_globals (vec_list env.(env_Env_imports)))) ->
  List.Forall (element_ok env) (vec_list env.(env_Env_elements)) ->
  start_ok env ->
  exports_distinct env ->
  List.Forall (export_desc_ok env) (vec_list env.(env_Env_exports)) ->
  List.Forall (data_ok env) ds ->
  List.Forall (global_ok env) (vec_list env.(env_Env_globals)) ->
  List.Forall2 (code_typed env) (vec_list env.(env_Env_func_type_indices))
    codes ->
  funcs_of (List.map translate_idx (vec_list env.(env_Env_func_type_indices)))
    codes fs ->
  module_type_checker
    (module_of env fs tabs mems (List.map translate_data ds))
    = Some (import_externs (vec_list env.(env_Env_types))
                           (vec_list env.(env_Env_imports)),
            export_externs env (vec_list env.(env_Env_exports))).
Proof.
  intros env fs tabs mems ds codes Hlim Htab Hmem Hfsp Hgsp Hnig Hels Hstart
         Hdist Hdesc Hdata Hglob Hcodes Hfuncs.
  unfold module_type_checker, module_of.
  cbn [mod_types mod_funcs mod_tables mod_mems mod_globals mod_elems
       mod_datas mod_start mod_imports mod_exports].
  destruct Hfsp as [Hfmap Hfall].
  apply List.Forall_app in Hfall. destruct Hfall as [Hfimp Hfdef].
  rewrite (gather_m_f_types_ok _ _ _ _ Hfuncs Hfdef).
  rewrite (module_imports_typer_ok _ _ (proj1 Hlim) Hfimp).
  repeat rewrite seq_cat_eq. repeat rewrite seq_map_eq.
  rewrite (checker_tc_tables env tabs Htab).
  rewrite (gather_m_e_types_ok env _ Hels). cbn iota.
  repeat rewrite seq_cat_eq. repeat rewrite seq_map_eq.
  rewrite (checker_tc_mems env mems Hmem).
  rewrite (gather_m_d_types_ok env _ Hdata). cbn iota.
  repeat rewrite seq_cat_eq.
  assert (Hfsp : env_func_space env
                   (imported_func_idxs (vec_list env.(env_Env_imports))
                    ++ vec_list env.(env_Env_func_type_indices)))
    by (split; [exact Hfmap | apply List.Forall_app; split; assumption]).
  rewrite (checker_tc_funcs env Hfsp).
  repeat rewrite seq_cat_eq.
  rewrite (checker_tc_globals env _ Hgsp).
  rewrite ext_t_globals_imports.
  (* name the two contexts the checker built *)
  match goal with
  | |- context [seq.all (module_func_type_checker ?cc) fs] => set (c := cc)
  end.
  match goal with
  | |- context [seq.all (module_global_type_checker ?cc) _] => set (c' := cc)
  end.
  (* the seven checks *)
  rewrite (module_func_type_checker_ok env c eq_refl eq_refl eq_refl eq_refl
             eq_refl eq_refl eq_refl _ _ _ Hfuncs Hcodes).
  rewrite (module_of_tables_ok env tabs c Hlim Htab).
  rewrite (module_of_mems_ok env mems c Hlim Hmem).
  rewrite (module_start_type_checker_ok env c _ eq_refl Hstart eq_refl).
  rewrite (export_name_unique_ok _ Hdist).
  assert (Hgl : seq.all (module_global_type_checker c')
                  (List.map translate_global (vec_list env.(env_Env_globals)))
                = true).
  { apply forall_all_map. rewrite List.Forall_forall in Hglob.
    apply List.Forall_forall. intros g Hin.
    apply (module_global_type_checker_ok env c' g eq_refl Hgsp Hnig).
    apply Hglob. exact Hin. }
  rewrite Hgl.
  assert (Hdt : seq.all (module_data_type_checker c')
                  (List.map translate_data ds) = true).
  { apply forall_all_map. rewrite List.Forall_forall in Hdata.
    apply List.Forall_forall. intros d Hin.
    apply (module_data_type_checker_true env c' d eq_refl eq_refl Hgsp Hnig).
    apply Hdata. exact Hin. }
  rewrite Hdt.
  assert (Hel : seq.all (module_elem_type_checker c')
                  (List.map translate_element
                     (vec_list env.(env_Env_elements))) = true).
  { apply forall_all_map. rewrite List.Forall_forall in Hels.
    apply List.Forall_forall. intros el Hin.
    apply (module_elem_type_checker_ok env c' _ el eq_refl eq_refl eq_refl
             eq_refl (ltac:(cbn [mod_elems]; apply List.in_map; exact Hin))
             Hgsp Hnig).
    apply Hels. exact Hin. }
  rewrite Hel. cbn [andb].
  rewrite (module_exports_typer_ok env c (vec_list env.(env_Env_exports))
             eq_refl eq_refl eq_refl eq_refl Hdesc).
  reflexivity.
Qed.

(* ================================================================== *)
(** ** An accepted module is well typed                                *)
(* ================================================================== *)

(** The checker's verdict on the module an accepting run decoded, with both
    extern-type lists named.

    The module is existential -- validation is a single streaming pass that does
    not retain function bodies, so the module the bytes decode to is not a
    function of what the run returns. Its imports and exports are retained,
    though, and that is what the rest of the conclusion is about: the two
    [mod_imports]/[mod_exports] equations say the module WasmCert reads declares
    exactly what the run recorded, in order and with the names, and the pair the
    checker returns is [import_externs] and [export_externs] of the environment
    in the returned [ValidatedModule] rather than a witness.

    [validate_module_typed] below turns the checker's verdict into
    [module_typing]. [Module_Wasm10.validate_module_typechecked] uses the
    equation itself, to identify the two lists a caller supplied with the ones
    the run reports. *)
Theorem validate_module_checked : forall data vm,
  module_validate_module data = Ok (Core_result_Result_Ok vm) ->
  let env := vm.(module_ValidatedModule_env) in
  exists m imps exps,
    repr_module (byte_list data) m
    /\ module_import_types env = Ok (Core_result_Result_Ok imps)
    /\ module_export_types env = Ok (Core_result_Result_Ok exps)
    /\ mod_imports m
         = List.map translate_import (vec_list env.(env_Env_imports))
    /\ mod_exports m
         = List.map translate_export (vec_list env.(env_Env_exports))
    /\ module_type_checker m
         = Some (translate_externtypes imps, translate_externtypes exps).
Proof.
  intros data vm H.
  destruct (validate_module_parts _ _ H)
    as [env [cp [tp [tl [fs [tabs [mems Hrest]]]]]]].
  destruct Hrest as [Hvm Hrest].
  destruct Hrest as [Henv Hrest]. destruct Hrest as [_ Hrest].
  destruct Hrest as [_ Hrest]. destruct Hrest as [Htab Hrest].
  destruct Hrest as [Hmem Hrest]. destruct Hrest as [Hfsp Hrest].
  destruct Hrest as [Hgsp Hrest]. destruct Hrest as [Hnig Hrest].
  destruct Hrest as [Hels Hrest]. destruct Hrest as [Hstart Hrest].
  destruct Hrest as [Hdist Hrest]. destruct Hrest as [Hdesc Hrest].
  destruct Hrest as [Hdata Hrest]. destruct Hrest as [Hglob Hrest].
  destruct Hrest as [[codes [Hcodes Hfuncs]] Hm].
  pose proof (module_of_type_checker env fs tabs mems
                (vec_list tl.(module_Tail_data)) codes
                (decode_env_limits_valid _ _ _ Henv)
                Htab Hmem Hfsp Hgsp Hnig Hels Hstart Hdist Hdesc Hdata Hglob
                Hcodes Hfuncs) as Hchk.
  (* the two accessors succeed, and return the two lists the checker built *)
  destruct Hfsp as [_ Hfall].
  apply List.Forall_app in Hfall. destruct Hfall as [Hfimp _].
  destruct (import_types_externs env Hfimp) as [imps [Himps Hiv]].
  destruct (export_types_externs env Hdesc) as [exps [Hexps Hev]].
  subst vm. cbn [module_ValidatedModule_env]. cbv zeta.
  exists (module_of env fs tabs mems
            (List.map translate_data (vec_list tl.(module_Tail_data)))).
  exists imps. exists exps.
  split; [exact Hm|]. split; [exact Himps|]. split; [exact Hexps|].
  split; [reflexivity|]. split; [reflexivity|].
  rewrite Hiv. rewrite Hev. exact Hchk.
Qed.

(** The second half of module soundness, and the end of the chain: an
    accepting run of [validate_module] means the input is a Wasm 1.0 module
    binary *and* WebAssembly's type system accepts the module it decodes to,
    with the import and export types it assigns being the ones the run reports.

    [module_type_checker_sound] is host-parameterised, so the statement is too;
    nothing in it depends on the host. *)
Section Typed.

Context `{ho: host}.

Theorem validate_module_typed : forall data vm,
  module_validate_module data = Ok (Core_result_Result_Ok vm) ->
  let env := vm.(module_ValidatedModule_env) in
  exists m imps exps,
    repr_module (byte_list data) m
    /\ module_import_types env = Ok (Core_result_Result_Ok imps)
    /\ module_export_types env = Ok (Core_result_Result_Ok exps)
    /\ mod_imports m
         = List.map translate_import (vec_list env.(env_Env_imports))
    /\ mod_exports m
         = List.map translate_export (vec_list env.(env_Env_exports))
    /\ module_typing m (translate_externtypes imps)
                       (translate_externtypes exps).
Proof.
  intros data vm H env.
  destruct (validate_module_checked _ _ H)
    as [m [imps [exps [Hm [Himps [Hexps [Himp [Hexp Hchk]]]]]]]].
  exists m. exists imps. exists exps.
  split; [exact Hm|]. split; [exact Himps|]. split; [exact Hexps|].
  split; [exact Himp|]. split; [exact Hexp|].
  apply module_type_checker_sound. exact Hchk.
Qed.

End Typed.
