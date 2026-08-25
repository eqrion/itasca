(** * The extern types the validator reports

    [module::import_types] and [module::export_types] are what an embedder
    links against: given the environment an accepting run returned, they hand
    back the type of every import the module asks for and of every export it
    provides. This file says what they return, in WasmCert's vocabulary.

    Two definitions and two theorems. [import_externs] and [export_externs] are
    the two lists said directly, as a [flat_map] over the environment's import
    and export vectors; [import_types_externs] and [export_types_externs] say
    the extracted Rust computes exactly them, and never fails doing it. What
    makes the failure arms unreachable is what validation already established:
    every import's type index resolved ([idx_in_range], from
    [env_func_space]), and every export's index was range-checked against its
    index space ([export_desc_ok]).

    [Module_Typing] then proves WasmCert's own [module_imports_typer] and
    [module_exports_typer] return the same two lists, which is what puts the
    Rust values into [validate_module_typed]'s statement. *)

Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Import Itasca.Aeneas_Specs.
Require Import Itasca.Translate.
Require Import Itasca.OpIter_State.
Require Import Itasca.Module_NoPanic.
Require Import Itasca.Module_Sound.

From Wasm Require Import datatypes.

Local Open Scope list_scope.

(* ================================================================== *)
(** ** The two lists                                                   *)
(* ================================================================== *)

(** Spec 3.2.7 for the import section. The three arms that carry a type outright
    give it up directly; the function arm is a type-index lookup, and
    [idx_in_range] is what makes it hit. *)
Definition import_externs (tys : list types_FuncType_t)
                          (imps : list module_Import_t) : list extern_type :=
  List.flat_map
    (fun im => match im.(module_Import_desc) with
               | Module_ImportDesc_Func idx =>
                   match List.nth_error tys (Z.to_nat (to_Z idx)) with
                   | Some ft => [ET_func (translate_functype ft)]
                   | None => []
                   end
               | Module_ImportDesc_Table t => [ET_table (translate_tabletype t)]
               | Module_ImportDesc_Memory m => [ET_mem (translate_memtype m)]
               | Module_ImportDesc_Global g => [ET_global (translate_globaltype g)]
               end)
    imps.

(** The same for the export section. An export names an index space entry, so
    unlike an import it carries no type of its own and all four arms are
    lookups; [export_desc_ok] is what makes them all hit. *)
Definition export_externs (env : module_Env_t)
                          (exps : list module_Export_t) : list extern_type :=
  List.flat_map
    (fun e => match e.(module_Export_desc) with
              | Module_ExportDesc_Func x =>
                  match List.nth_error (vec_list env.(module_Env_func_types))
                          (Z.to_nat (to_Z x)) with
                  | Some ft => [ET_func (translate_functype ft)]
                  | None => []
                  end
              | Module_ExportDesc_Table x =>
                  match List.nth_error (vec_list env.(module_Env_table_types))
                          (Z.to_nat (to_Z x)) with
                  | Some t => [ET_table (translate_tabletype t)]
                  | None => []
                  end
              | Module_ExportDesc_Memory x =>
                  match List.nth_error (vec_list env.(module_Env_mem_types))
                          (Z.to_nat (to_Z x)) with
                  | Some m => [ET_mem (translate_memtype m)]
                  | None => []
                  end
              | Module_ExportDesc_Global x =>
                  match List.nth_error (vec_list env.(module_Env_global_types))
                          (Z.to_nat (to_Z x)) with
                  | Some g => [ET_global (translate_globaltype g)]
                  | None => []
                  end
              end)
    exps.

Lemma import_externs_cons : forall tys im imps,
  import_externs tys (im :: imps)
    = import_externs tys [im] ++ import_externs tys imps.
Proof.
  intros tys im imps. unfold import_externs. cbn [List.flat_map].
  rewrite List.app_nil_r. reflexivity.
Qed.

Lemma export_externs_cons : forall env e exps,
  export_externs env (e :: exps)
    = export_externs env [e] ++ export_externs env exps.
Proof.
  intros env e exps. unfold export_externs. cbn [List.flat_map].
  rewrite List.app_nil_r. reflexivity.
Qed.

(* ================================================================== *)
(** ** What the two loops do                                          *)
(* ================================================================== *)

(** The import list's function arm needs its type index to resolve, and the
    fact that it does is stated over [imported_func_idxs], one entry per
    function import. This turns the list-level statement into the one entry the
    loop is looking at. *)
Lemma in_imported_func_idxs : forall imps im idx,
  List.In im imps ->
  im.(module_Import_desc) = Module_ImportDesc_Func idx ->
  List.In idx (imported_func_idxs imps).
Proof.
  intros imps im idx Hin Hd. unfold imported_func_idxs.
  apply List.in_flat_map. exists im. split; [exact Hin|].
  rewrite Hd. cbn [List.In]. left. reflexivity.
Qed.

(** An index below a vector's length is one its bounds check lets through.
    Every read in the two loops goes past one of these. *)
Lemma lt_len_geb_false : forall {T} (v : alloc_vec_Vec T) (j : usize),
  to_Z j < Z.of_nat (List.length (vec_list v)) ->
  (j s>= alloc_vec_Vec_len v) = false.
Proof.
  intros T v j H. apply scalar_lt_geb_false. rewrite vec_len_spec. exact H.
Qed.

(** [lookup_type] succeeds exactly when the index is in range, and what it
    returns denotes the type section entry there. [Module_Sound.lookup_type_sound]
    is the converse; this is the direction that makes the [?] in [import_types]
    unreachable. *)
Lemma lookup_type_in_range : forall env idx ft',
  List.nth_error (vec_list env.(module_Env_types)) (Z.to_nat (to_Z idx))
    = Some ft' ->
  exists ft,
    module_lookup_type env idx = Ok (Core_result_Result_Ok ft)
    /\ translate_functype ft = translate_functype ft'.
Proof.
  intros env idx ft' Hnth. unfold module_lookup_type.
  destruct (scalar_cast_u32_usize idx) as [i [Hcast Hi]].
  rewrite Hcast. cbn [bind].
  assert (Hn : (Z.to_nat (to_Z idx)
                  < List.length (vec_list env.(module_Env_types)))%nat)
    by (apply List.nth_error_Some; rewrite Hnth; discriminate).
  assert (Hlt : to_Z i
                  < Z.of_nat (List.length (vec_list env.(module_Env_types)))).
  { rewrite Hi. apply Nat2Z.inj_lt in Hn.
    rewrite Z2Nat.id in Hn by (apply u32_nonneg). exact Hn. }
  rewrite (lt_len_geb_false _ _ Hlt).
  rewrite vec_index_spec. rewrite Hi. rewrite Hnth. cbn [bind].
  destruct (copy_func_type_ok ft') as [ft [Hcopy _]].
  rewrite Hcopy. cbn [bind].
  exists ft. split; [reflexivity|]. exact (copy_func_type_same _ _ Hcopy).
Qed.

(** Every [alloc_vec_Vec] carries the length bound in its type, so a vector's
    length is never a reason a [usize] index overflows. *)
Lemma vec_length_le_max : forall {T} (v : alloc_vec_Vec T),
  Z.of_nat (List.length (vec_list v)) <= usize_max.
Proof.
  intros T v. rewrite <- vec_len_spec. apply usize_le_max.
Qed.

Lemma translate_externtypes_push : forall v x v',
  alloc_vec_Vec_push v x = Ok v' ->
  translate_externtypes v'
    = translate_externtypes v ++ [translate_externtype x].
Proof.
  intros v x v' H. unfold translate_externtypes.
  rewrite (vec_push_spec _ _ _ H). apply List.map_app.
Qed.

Lemma import_types_loop_ok : forall m env out i,
  List.Forall (idx_in_range (vec_list env.(module_Env_types)))
    (imported_func_idxs (vec_list env.(module_Env_imports))) ->
  Z.of_nat (List.length (vec_list env.(module_Env_imports))) - to_Z i
    <= Z.of_nat m ->
  Z.of_nat (List.length (vec_list out))
    + (Z.of_nat (List.length (vec_list env.(module_Env_imports))) - to_Z i)
    <= usize_max ->
  exists v,
    module_import_types_loop env out i = Ok (Core_result_Result_Ok v)
    /\ translate_externtypes v
       = translate_externtypes out
         ++ import_externs (vec_list env.(module_Env_types))
              (List.skipn (Z.to_nat (to_Z i))
                 (vec_list env.(module_Env_imports))).
Proof.
  induction m as [|m IH]; intros env out i Hrange Hmeas Hroom;
    pose proof (usize_nonneg i) as Hi0;
    unfold module_import_types_loop; rewrite loop_unfold; cbn beta iota;
    destruct (i s>= alloc_vec_Vec_len env.(module_Env_imports)) eqn:Hge.
  1,3: pose proof (scalar_geb_true_ge _ _ Hge) as Hle;
       rewrite vec_len_spec in Hle;
       exists out; split; [reflexivity|];
       rewrite List.skipn_all2
         by (apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; lia);
       cbn [import_externs List.flat_map]; rewrite List.app_nil_r; reflexivity.
  - exfalso. pose proof (scalar_geb_false_lt _ _ Hge) as Hlt.
    rewrite vec_len_spec in Hlt. cbn in Hmeas. lia.
  - pose proof (scalar_geb_false_lt _ _ Hge) as Hlt.
    rewrite vec_len_spec in Hlt.
    pose proof (vec_length_le_max env.(module_Env_imports)) as Hmax.
    rewrite vec_index_spec.
    destruct (List.nth_error (vec_list env.(module_Env_imports))
                (Z.to_nat (to_Z i))) as [im|] eqn:Hnth.
    2: { exfalso. apply List.nth_error_None in Hnth.
         apply Nat2Z.inj_le in Hnth. rewrite Z2Nat.id in Hnth by lia. lia. }
    cbn [bind].
    rewrite (skipn_nth_error _ _ _ Hnth). rewrite import_externs_cons.
    (* the entry pushed this round, then the recursive call *)
    assert (Hstep : forall x out2 i2,
              alloc_vec_Vec_push out x = Ok out2 ->
              usize_add i 1%usize = Ok i2 ->
              import_externs (vec_list env.(module_Env_types)) [im]
                = [translate_externtype x] ->
              exists v,
                module_import_types_loop env out2 i2
                  = Ok (Core_result_Result_Ok v)
                /\ translate_externtypes v
                   = translate_externtypes out
                     ++ import_externs (vec_list env.(module_Env_types)) [im]
                     ++ import_externs (vec_list env.(module_Env_types))
                          (List.skipn (S (Z.to_nat (to_Z i)))
                             (vec_list env.(module_Env_imports)))).
    { intros x out2 i2 Hpush Hadd Hone.
      pose proof (scalar_add_val _ _ _ 1 Hadd eq_refl) as Hi2.
      destruct (IH env out2 i2 Hrange) as [v [Hv Hlv]].
      - cbn in Hmeas. lia.
      - rewrite (vec_push_spec _ _ _ Hpush). rewrite List.app_length.
        cbn [List.length]. lia.
      - exists v. split; [exact Hv|].
        rewrite Hlv. rewrite (translate_externtypes_push _ _ _ Hpush).
        rewrite Hi2. rewrite Z_to_nat_add1 by lia.
        rewrite <- List.app_assoc. rewrite Hone. reflexivity. }
    destruct im.(module_Import_desc) as [idx|t|mm|g] eqn:Hd.
    + (* a function: the type index resolves *)
      assert (Hin : idx_in_range (vec_list env.(module_Env_types)) idx).
      { rewrite List.Forall_forall in Hrange. apply Hrange.
        exact (in_imported_func_idxs _ _ _ (List.nth_error_In _ _ Hnth) Hd). }
      unfold idx_in_range in Hin.
      destruct (List.nth_error (vec_list env.(module_Env_types))
                  (Z.to_nat (to_Z idx))) as [ft'|] eqn:Hnth';
        [|exfalso; apply Hin; reflexivity].
      destruct (lookup_type_in_range env idx ft' Hnth') as [ft [Hlk Hsame]].
      rewrite Hlk. cbn [bind]. rewrite branch_ok. cbn [bind].
      destruct (vec_push_ok out (Types_ExternType_Func ft) (ltac:(lia)))
        as [out2 Hpush].
      rewrite Hpush. cbn [bind].
      destruct (usize_add_1_ok i (ltac:(lia))) as [i2 [Hadd _]].
      rewrite Hadd. cbn [bind].
      apply (Hstep _ _ _ Hpush Hadd).
      cbn [import_externs List.flat_map List.app]. rewrite Hd.
      rewrite Hnth'. cbn [translate_externtype]. rewrite Hsame. reflexivity.
    + destruct (vec_push_ok out (Types_ExternType_Table t) (ltac:(lia)))
        as [out2 Hpush].
      rewrite Hpush. cbn [bind].
      destruct (usize_add_1_ok i (ltac:(lia))) as [i2 [Hadd _]].
      rewrite Hadd. cbn [bind].
      apply (Hstep _ _ _ Hpush Hadd).
      cbn [import_externs List.flat_map List.app]. rewrite Hd. reflexivity.
    + destruct (vec_push_ok out (Types_ExternType_Memory mm) (ltac:(lia)))
        as [out2 Hpush].
      rewrite Hpush. cbn [bind].
      destruct (usize_add_1_ok i (ltac:(lia))) as [i2 [Hadd _]].
      rewrite Hadd. cbn [bind].
      apply (Hstep _ _ _ Hpush Hadd).
      cbn [import_externs List.flat_map List.app]. rewrite Hd. reflexivity.
    + destruct (vec_push_ok out (Types_ExternType_Global g) (ltac:(lia)))
        as [out2 Hpush].
      rewrite Hpush. cbn [bind].
      destruct (usize_add_1_ok i (ltac:(lia))) as [i2 [Hadd _]].
      rewrite Hadd. cbn [bind].
      apply (Hstep _ _ _ Hpush Hadd).
      cbn [import_externs List.flat_map List.app]. rewrite Hd. reflexivity.
Qed.

Theorem import_types_externs : forall env,
  List.Forall (idx_in_range (vec_list env.(module_Env_types)))
    (imported_func_idxs (vec_list env.(module_Env_imports))) ->
  exists v,
    module_import_types env = Ok (Core_result_Result_Ok v)
    /\ translate_externtypes v
       = import_externs (vec_list env.(module_Env_types))
                        (vec_list env.(module_Env_imports)).
Proof.
  intros env Hrange. unfold module_import_types.
  pose proof (vec_length_le_max env.(module_Env_imports)).
  assert (Hz : to_Z 0%usize = 0) by reflexivity.
  destruct (import_types_loop_ok
              (List.length (vec_list env.(module_Env_imports))) env
              (alloc_vec_Vec_new types_ExternType_t) 0%usize Hrange)
    as [v [Hv Hlv]].
  - lia.
  - cbn [vec_list alloc_vec_Vec_new proj1_sig List.length]. lia.
  - exists v. split; [exact Hv|].
    rewrite Hlv. rewrite Hz.
    cbn [vec_list alloc_vec_Vec_new proj1_sig translate_externtypes
         List.map List.app List.skipn].
    reflexivity.
Qed.

(** The export loop. Each arm is its own bounds check rather than a call to
    [lookup_type], so the four are spelled out; [export_desc_ok] is exactly the
    conjunction of what the four checks need. *)
Lemma export_types_loop_ok : forall m env out i,
  List.Forall (export_desc_ok env) (vec_list env.(module_Env_exports)) ->
  Z.of_nat (List.length (vec_list env.(module_Env_exports))) - to_Z i
    <= Z.of_nat m ->
  Z.of_nat (List.length (vec_list out))
    + (Z.of_nat (List.length (vec_list env.(module_Env_exports))) - to_Z i)
    <= usize_max ->
  exists v,
    module_export_types_loop env out i = Ok (Core_result_Result_Ok v)
    /\ translate_externtypes v
       = translate_externtypes out
         ++ export_externs env
              (List.skipn (Z.to_nat (to_Z i))
                 (vec_list env.(module_Env_exports))).
Proof.
  induction m as [|m IH]; intros env out i Hdesc Hmeas Hroom;
    pose proof (usize_nonneg i) as Hi0;
    unfold module_export_types_loop; rewrite loop_unfold; cbn beta iota;
    destruct (i s>= alloc_vec_Vec_len env.(module_Env_exports)) eqn:Hge.
  1,3: pose proof (scalar_geb_true_ge _ _ Hge) as Hle;
       rewrite vec_len_spec in Hle;
       exists out; split; [reflexivity|];
       rewrite List.skipn_all2
         by (apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; lia);
       cbn [export_externs List.flat_map]; rewrite List.app_nil_r; reflexivity.
  - exfalso. pose proof (scalar_geb_false_lt _ _ Hge) as Hlt.
    rewrite vec_len_spec in Hlt. cbn in Hmeas. lia.
  - pose proof (scalar_geb_false_lt _ _ Hge) as Hlt.
    rewrite vec_len_spec in Hlt.
    pose proof (vec_length_le_max env.(module_Env_exports)) as Hmax.
    rewrite vec_index_spec.
    destruct (List.nth_error (vec_list env.(module_Env_exports))
                (Z.to_nat (to_Z i))) as [e|] eqn:Hnth.
    2: { exfalso. apply List.nth_error_None in Hnth.
         apply Nat2Z.inj_le in Hnth. rewrite Z2Nat.id in Hnth by lia. lia. }
    cbn [bind].
    assert (He : export_desc_ok env e)
      by (rewrite List.Forall_forall in Hdesc; apply Hdesc;
          exact (List.nth_error_In _ _ Hnth)).
    rewrite (skipn_nth_error _ _ _ Hnth). rewrite export_externs_cons.
    assert (Hstep : forall x out2 i2,
              alloc_vec_Vec_push out x = Ok out2 ->
              usize_add i 1%usize = Ok i2 ->
              export_externs env [e] = [translate_externtype x] ->
              exists v,
                module_export_types_loop env out2 i2
                  = Ok (Core_result_Result_Ok v)
                /\ translate_externtypes v
                   = translate_externtypes out
                     ++ export_externs env [e]
                     ++ export_externs env
                          (List.skipn (S (Z.to_nat (to_Z i)))
                             (vec_list env.(module_Env_exports)))).
    { intros x out2 i2 Hpush Hadd Hone.
      pose proof (scalar_add_val _ _ _ 1 Hadd eq_refl) as Hi2.
      destruct (IH env out2 i2 Hdesc) as [v [Hv Hlv]].
      - cbn in Hmeas. lia.
      - rewrite (vec_push_spec _ _ _ Hpush). rewrite List.app_length.
        cbn [List.length]. lia.
      - exists v. split; [exact Hv|].
        rewrite Hlv. rewrite (translate_externtypes_push _ _ _ Hpush).
        rewrite Hi2. rewrite Z_to_nat_add1 by lia.
        rewrite <- List.app_assoc. rewrite Hone. reflexivity. }
    unfold export_desc_ok in He.
    destruct e.(module_Export_desc) as [x|x|x|x] eqn:Hd.
    (* the four arms differ only in which index space they read *)
    + destruct (scalar_cast_u32_usize x) as [j [Hcast Hj]].
      rewrite Hcast. cbn [bind].
      assert (Hjlt : to_Z j < Z.of_nat
                       (List.length (vec_list env.(module_Env_func_types))))
        by (rewrite Hj; exact He).
      rewrite (lt_len_geb_false _ _ Hjlt).
      rewrite vec_index_spec.
      destruct (List.nth_error (vec_list env.(module_Env_func_types))
                  (Z.to_nat (to_Z j))) as [ft0|] eqn:Hnthf.
      2: { exfalso. apply List.nth_error_None in Hnthf.
           apply Nat2Z.inj_le in Hnthf.
           rewrite Z2Nat.id in Hnthf by (apply usize_nonneg). lia. }
      cbn [bind].
      destruct (copy_func_type_ok ft0) as [ft [Hcopy _]].
      rewrite Hcopy. cbn [bind].
      destruct (vec_push_ok out (Types_ExternType_Func ft) (ltac:(lia)))
        as [out2 Hpush].
      rewrite Hpush. cbn [bind].
      destruct (usize_add_1_ok i (ltac:(lia))) as [i2 [Hadd _]].
      rewrite Hadd. cbn [bind].
      apply (Hstep _ _ _ Hpush Hadd).
      cbn [export_externs List.flat_map List.app]. rewrite Hd.
      rewrite <- Hj. rewrite Hnthf. cbn [translate_externtype].
      rewrite (copy_func_type_same _ _ Hcopy). reflexivity.
    + destruct (scalar_cast_u32_usize x) as [j [Hcast Hj]].
      rewrite Hcast. cbn [bind].
      assert (Hjlt : to_Z j < Z.of_nat
                       (List.length (vec_list env.(module_Env_table_types))))
        by (rewrite Hj; exact He).
      rewrite (lt_len_geb_false _ _ Hjlt).
      rewrite vec_index_spec.
      destruct (List.nth_error (vec_list env.(module_Env_table_types))
                  (Z.to_nat (to_Z j))) as [t0|] eqn:Hntht.
      2: { exfalso. apply List.nth_error_None in Hntht.
           apply Nat2Z.inj_le in Hntht.
           rewrite Z2Nat.id in Hntht by (apply usize_nonneg). lia. }
      cbn [bind].
      destruct (vec_push_ok out (Types_ExternType_Table t0) (ltac:(lia)))
        as [out2 Hpush].
      rewrite Hpush. cbn [bind].
      destruct (usize_add_1_ok i (ltac:(lia))) as [i2 [Hadd _]].
      rewrite Hadd. cbn [bind].
      apply (Hstep _ _ _ Hpush Hadd).
      cbn [export_externs List.flat_map List.app]. rewrite Hd.
      rewrite <- Hj. rewrite Hntht. reflexivity.
    + destruct (scalar_cast_u32_usize x) as [j [Hcast Hj]].
      rewrite Hcast. cbn [bind].
      assert (Hjlt : to_Z j < Z.of_nat
                       (List.length (vec_list env.(module_Env_mem_types))))
        by (rewrite Hj; exact He).
      rewrite (lt_len_geb_false _ _ Hjlt).
      rewrite vec_index_spec.
      destruct (List.nth_error (vec_list env.(module_Env_mem_types))
                  (Z.to_nat (to_Z j))) as [m0|] eqn:Hnthm.
      2: { exfalso. apply List.nth_error_None in Hnthm.
           apply Nat2Z.inj_le in Hnthm.
           rewrite Z2Nat.id in Hnthm by (apply usize_nonneg). lia. }
      cbn [bind].
      destruct (vec_push_ok out (Types_ExternType_Memory m0) (ltac:(lia)))
        as [out2 Hpush].
      rewrite Hpush. cbn [bind].
      destruct (usize_add_1_ok i (ltac:(lia))) as [i2 [Hadd _]].
      rewrite Hadd. cbn [bind].
      apply (Hstep _ _ _ Hpush Hadd).
      cbn [export_externs List.flat_map List.app]. rewrite Hd.
      rewrite <- Hj. rewrite Hnthm. reflexivity.
    + destruct (scalar_cast_u32_usize x) as [j [Hcast Hj]].
      rewrite Hcast. cbn [bind].
      assert (Hjlt : to_Z j < Z.of_nat
                       (List.length (vec_list env.(module_Env_global_types))))
        by (rewrite Hj; exact He).
      rewrite (lt_len_geb_false _ _ Hjlt).
      rewrite vec_index_spec.
      destruct (List.nth_error (vec_list env.(module_Env_global_types))
                  (Z.to_nat (to_Z j))) as [g0|] eqn:Hnthg.
      2: { exfalso. apply List.nth_error_None in Hnthg.
           apply Nat2Z.inj_le in Hnthg.
           rewrite Z2Nat.id in Hnthg by (apply usize_nonneg). lia. }
      cbn [bind].
      destruct (vec_push_ok out (Types_ExternType_Global g0) (ltac:(lia)))
        as [out2 Hpush].
      rewrite Hpush. cbn [bind].
      destruct (usize_add_1_ok i (ltac:(lia))) as [i2 [Hadd _]].
      rewrite Hadd. cbn [bind].
      apply (Hstep _ _ _ Hpush Hadd).
      cbn [export_externs List.flat_map List.app]. rewrite Hd.
      rewrite <- Hj. rewrite Hnthg. reflexivity.
Qed.

Theorem export_types_externs : forall env,
  List.Forall (export_desc_ok env) (vec_list env.(module_Env_exports)) ->
  exists v,
    module_export_types env = Ok (Core_result_Result_Ok v)
    /\ translate_externtypes v
       = export_externs env (vec_list env.(module_Env_exports)).
Proof.
  intros env Hdesc. unfold module_export_types.
  pose proof (vec_length_le_max env.(module_Env_exports)).
  assert (Hz : to_Z 0%usize = 0) by reflexivity.
  destruct (export_types_loop_ok
              (List.length (vec_list env.(module_Env_exports))) env
              (alloc_vec_Vec_new types_ExternType_t) 0%usize Hdesc)
    as [v [Hv Hlv]].
  - lia.
  - cbn [vec_list alloc_vec_Vec_new proj1_sig List.length]. lia.
  - exists v. split; [exact Hv|].
    rewrite Hlv. rewrite Hz.
    cbn [vec_list alloc_vec_Vec_new proj1_sig translate_externtypes
         List.map List.app List.skipn].
    reflexivity.
Qed.
