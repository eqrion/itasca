(** * What a driving consumer gets

    [module.rs] splits a module into three parts and gives each one a [_with]
    entry point, so a compiler can decode the environment, dispatch the code
    section's entries to other threads, and decode the tail, hearing about each
    step through its own hooks. Every theorem about that shape lives in
    [Module_Sound.v], [Module_NoPanic.v] and [Module_Complete.v], stated about
    the run the consumer made. This file closes the three gaps between those
    statements and what a consumer can actually put its hands on.

    The first is the one that matters. [Module_Sound.code_hooks_validate] is
    what a consumer that overrides [on_code_entry] owes the walk, and it is a
    claim about [validate_code_entry] -- the do-nothing run. A compiler runs
    [validate_code_entry_with] at its own operator visitor.
    [validate_code_entry_driven] is what turns the one into the other, on top
    of [OpIter_Driven.v].

    The second is the mirror of every [_driven] lemma: a run that the
    do-nothing consumer accepts is one a hooked consumer accepts too, provided
    its hooks do not decline. [Module_Sound.v] proves the [_driven] direction
    because soundness needs it; completeness needs this one, and with both,
    driving a walk changes nothing about its verdict.

    The third is [validate_module]'s own decomposition read backwards.
    [Module_Sound.validate_module_parts] says an accepting whole-module run is
    three accepting parts; [validate_module_of_parts] says three accepting
    parts are an accepting whole-module run, which is what lets a consumer that
    called the three itself inherit [validate_module_repr],
    [validate_module_typed] and the rest rather than have them restated. *)

Require Import Primitives.
Import Primitives.
Require Import Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Import Itasca.Aeneas_Specs.
Require Import Itasca.Translate.
Require Import Itasca.Spec_Module.
Require Import Itasca.OpIter_Visit.
Require Import Itasca.OpIter_Decode.
Require Import Itasca.OpIter_Driven.
Require Import Itasca.Module_NoPanic.
Require Import Itasca.Module_Sound.
Require Import Itasca.Module_Complete.
Require Import Itasca.Module_Typing.

From Wasm Require Import datatypes operations typing instantiation_spec.

Local Open Scope list_scope.
Local Bind Scope list_scope with list.
Open Scope Z_scope.

(* ================================================================== *)
(** ** One code entry                                                  *)
(* ================================================================== *)

(** The frame hook and then the body, both transferred at once. *)
Lemma validate_code_entry_transfer :
  forall V W (inst : code_OpVisitor_t V) (inst' : code_OpVisitor_t W)
         data pos env index v w q' v',
  hooks_accept inst' ->
  module_validate_code_entry_with inst data pos env index v
    = Ok (Core_result_Result_Ok q', v') ->
  exists w', module_validate_code_entry_with inst' data pos env index w
             = Ok (Core_result_Result_Ok q', w').
Proof.
  intros V W inst inst' data pos env index v w q' v' Hacc H.
  unfold module_validate_code_entry_with in H |- *.
  destruct (index s>= alloc_vec_Vec_len env.(module_Env_func_type_indices));
    [discriminate|].
  destruct (reader_read_u32_leb data pos) as [r0|] eqn:Hleb;
    cbn [bind] in H |- *; [|discriminate].
  destruct r0 as [[size p]|e0]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H |- *. cbn [bind] in H |- *.
  destruct (scalar_cast U32 Usize size) as [n|] eqn:Hn;
    cbn [bind] in H |- *; [|discriminate].
  destruct (module_have_bytes data p n) as [r1|] eqn:Hhb;
    cbn [bind] in H |- *; [|discriminate].
  destruct r1 as [u1|e1]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H |- *. cbn [bind] in H |- *.
  destruct (usize_add p n) as [fin|] eqn:Hend;
    cbn [bind] in H |- *; [|discriminate].
  destruct (module_decode_locals data p) as [r2|] eqn:Hloc;
    cbn [bind] in H |- *; [|discriminate].
  destruct r2 as [[declared p1]|e2]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H |- *. cbn [bind] in H |- *.
  destruct (p1 s> fin); [discriminate|].
  destruct (alloc_vec_Vec_index
              (core_slice_index_SliceIndexUsizeSliceInst _)
              env.(module_Env_func_type_indices) index) as [tidx|] eqn:Hti;
    cbn [bind] in H |- *; [|discriminate].
  destruct (scalar_cast U32 Usize tidx) as [t|] eqn:Ht;
    cbn [bind] in H |- *; [|discriminate].
  destruct (t s>= alloc_vec_Vec_len env.(module_Env_types)); [discriminate|].
  destruct (alloc_vec_Vec_index
              (core_slice_index_SliceIndexUsizeSliceInst types_FuncType_t)
              env.(module_Env_types) t) as [ft|] eqn:Hft;
    cbn [bind] in H |- *; [|discriminate].
  destruct (module_build_func_locals
              (alloc_vec_Vec_deref ft.(types_FuncType_params))
              (alloc_vec_Vec_deref declared)) as [locals|] eqn:Hbl;
    cbn [bind] in H |- *; [|discriminate].
  destruct (module_copy_value_types
              (alloc_vec_Vec_deref ft.(types_FuncType_results)))
    as [results|] eqn:Hcv; cbn [bind] in H |- *; [|discriminate].
  destruct (inst.(code_OpVisitor_t_on_function_start) v
              (mkcode_Context_t locals results) tidx p1 fin) as [[r3 v3]|]
    eqn:Hfs; cbn [bind] in H; [|discriminate].
  destruct r3 as [u3|e3]; [|discriminate].
  destruct (frame_hook_accept W inst' w (mkcode_Context_t locals results)
              tidx p1 fin Hacc) as [w3 Hw3].
  rewrite Hw3. cbn [bind].
  destruct (core_slice_index_Slice_index
              (core_slice_index_SliceIndexRangeUsizeSliceInst _) data
              {| core_ops_range_Range_start := p1;
                 core_ops_range_Range_end_ := fin |}) as [body|] eqn:Hsl;
    cbn [bind] in H |- *; [|discriminate].
  destruct (code_validate_body_with inst body env
              (mkcode_Context_t locals results) v3) as [[r4 v4]|] eqn:Hvb;
    cbn [bind] in H; [|discriminate].
  destruct r4 as [u4|e4]; [|discriminate].
  destruct u4.
  destruct (validate_body_with_transfer V W inst inst' body env
              (mkcode_Context_t locals results) v3 w3 v4 Hacc Hvb)
    as [w4 Hw4].
  rewrite Hw4. cbn [bind]. inversion H; subst. eauto.
Qed.

(** What a compiler concludes from its own run of an entry: the do-nothing run
    would have accepted the same bytes at the same position. This is exactly
    the shape of [Module_Sound.code_hooks_validate]'s conclusion, so a consumer
    whose [on_code_entry] returns [Ok] only when its own
    [validate_code_entry_with] did can discharge that obligation with this and
    nothing else. *)
Corollary validate_code_entry_driven :
  forall V (inst : code_OpVisitor_t V) data pos env index v q' v',
  module_validate_code_entry_with inst data pos env index v
    = Ok (Core_result_Result_Ok q', v') ->
  module_validate_code_entry data pos env index
    = Ok (Core_result_Result_Ok q').
Proof.
  intros V inst data pos env index v q' v' H.
  destruct (validate_code_entry_transfer V code_EmptyOpVisitor_t inst
              code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor data pos env index
              v tt q' v' nop_hooks_accept H) as [w' Hw].
  apply code_entry_nop. rewrite Hw. destruct w'. reflexivity.
Qed.

(** And the mirror, which discharges [Module_Complete.code_hooks_accept]: the
    same consumer does not refuse an entry the validator accepts, provided its
    own hooks do not. *)
Corollary validate_code_entry_accepts :
  forall V (inst : code_OpVisitor_t V) data pos env index v q',
  hooks_accept inst ->
  module_validate_code_entry data pos env index
    = Ok (Core_result_Result_Ok q') ->
  exists v', module_validate_code_entry_with inst data pos env index v
             = Ok (Core_result_Result_Ok q', v').
Proof.
  intros V inst data pos env index v q' Hacc H.
  apply (validate_code_entry_transfer code_EmptyOpVisitor_t V
           code_EmptyOpVisitor_Insts_ItascaCodeOpVisitor inst data pos env
           index tt v q' tt Hacc).
  exact (code_entry_nop_inv data pos env index _ H).
Qed.

(* ================================================================== *)
(** ** The three parts                                                 *)
(* ================================================================== *)

(** [Module_Sound.v] proves each part's [_driven] direction, from a hooked run
    to the do-nothing one. These are the same inductions in the other
    direction, and general in both instances so that [_driven] would fall out
    of them too. *)
Lemma validate_env_with_loop_transfer :
  forall m V W (inst : module_ModuleVisitor_t V) (inst' : module_ModuleVisitor_t W)
         data v w env q last_id envf qf v',
  module_hooks_accept inst' ->
  Z.of_nat (List.length (vec_list data)) - to_Z q <= Z.of_nat m ->
  module_validate_env_with_loop inst data v env q last_id
    = Ok (Core_result_Result_Ok (envf, qf), v') ->
  exists w', module_validate_env_with_loop inst' data w env q last_id
             = Ok (Core_result_Result_Ok (envf, qf), w').
Proof.
  induction m as [|m IH];
    intros V W inst inst' data v w env q last_id envf qf v' Hacc Hmeas H;
    unfold module_validate_env_with_loop in H |- *;
    rewrite loop_unfold in H; rewrite loop_unfold; cbn beta iota in H |- *;
    destruct (q s>= slice_len data) eqn:Hge.
  1,3: inversion H; subst; eauto.
  - exfalso. apply scalar_geb_false_lt in Hge.
    rewrite slice_len_spec in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge. rewrite slice_len_spec in Hge.
    destruct (module_read_section_header data q) as [r|] eqn:Hhdr;
      cbn [bind] in H |- *; [|discriminate].
    destruct r as [[[id start] fin]|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H |- *. cbn [bind] in H |- *.
    destruct (read_section_header_step _ _ _ _ _ Hhdr) as [Hqs [Hsf Hfd]].
    rewrite slice_len_spec in Hfd.
    destruct (id s= module_section_custom).
    { destruct (module_decode_custom_section data start fin) as [r1|] eqn:Hcs;
        cbn [bind] in H |- *; [|discriminate].
      destruct r1 as [c|e1]; [|try_err_rw_in H; discriminate].
      rewrite branch_ok in H |- *. cbn [bind] in H |- *.
      destruct (inst.(module_ModuleVisitor_t_on_custom_section) v c)
        as [[rh v1]|] eqn:Hh; cbn [bind] in H; [|discriminate].
      destruct rh as [u|ev]; [|cbn beta iota in H; discriminate].
      cbn beta iota in H.
      destruct (Hacc w c) as [w1 Hw1]. rewrite Hw1. cbn [bind]. cbn beta iota.
      exact (IH V W inst inst' data v1 w1 env fin last_id envf qf v' Hacc
               (ltac:(lia)) H). }
    destruct (id s>= module_section_code).
    { inversion H; subst. eauto. }
    destruct (id s<= last_id); [discriminate|].
    destruct (module_decode_env_section data start id env) as [[r1 env2]|]
      eqn:Hsec; cbn [bind] in H |- *; [|discriminate].
    destruct r1 as [p|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H |- *. cbn [bind] in H |- *.
    destruct (p s<> fin); [discriminate|].
    cbn beta iota in H |- *.
    exact (IH V W inst inst' data v w env2 fin id envf qf v' Hacc
             (ltac:(lia)) H).
Qed.

Lemma validate_env_with_transfer :
  forall V W (inst : module_ModuleVisitor_t V) (inst' : module_ModuleVisitor_t W)
         data v w env qf v',
  module_hooks_accept inst' ->
  module_validate_env_with inst data v
    = Ok (Core_result_Result_Ok (env, qf), v') ->
  exists w', module_validate_env_with inst' data w
             = Ok (Core_result_Result_Ok (env, qf), w').
Proof.
  intros V W inst inst' data v w env qf v' Hacc H.
  unfold module_validate_env_with in H |- *.
  destruct module_Env_new as [env0|] eqn:Hnew; cbn [bind] in H |- *;
    [|discriminate].
  destruct (module_read_header data) as [r|] eqn:Hhdr;
    cbn [bind] in H |- *; [|discriminate].
  destruct r as [p0|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H |- *. cbn [bind] in H |- *.
  exact (validate_env_with_loop_transfer (List.length (vec_list data)) V W inst
           inst' data v w env0 p0 0%u8 env qf v' Hacc
           (ltac:(pose proof (usize_nonneg p0); lia)) H).
Qed.

Corollary validate_env_with_accepts :
  forall V (inst : module_ModuleVisitor_t V) data v env qf,
  module_hooks_accept inst ->
  module_validate_env data = Ok (Core_result_Result_Ok (env, qf)) ->
  exists v', module_validate_env_with inst data v
             = Ok (Core_result_Result_Ok (env, qf), v').
Proof.
  intros V inst data v env qf Hacc H.
  apply (validate_env_with_transfer _ V
           module_EmptyModuleVisitor_Insts_ItascaModuleModuleVisitor inst data
           tt v env qf tt Hacc).
  exact (validate_env_nop_inv data _ H).
Qed.

Lemma validate_tail_with_loop_transfer :
  forall m V W (inst : module_ModuleVisitor_t V) (inst' : module_ModuleVisitor_t W)
         data env v w segments q seen tail v',
  module_hooks_accept inst' ->
  Z.of_nat (List.length (vec_list data)) - to_Z q <= Z.of_nat m ->
  module_validate_tail_with_loop inst data env v segments q seen
    = Ok (Core_result_Result_Ok tail, v') ->
  exists w', module_validate_tail_with_loop inst' data env w segments q seen
             = Ok (Core_result_Result_Ok tail, w').
Proof.
  induction m as [|m IH];
    intros V W inst inst' data env v w segments q seen tail v' Hacc Hmeas H;
    unfold module_validate_tail_with_loop in H |- *;
    rewrite loop_unfold in H; rewrite loop_unfold; cbn beta iota in H |- *;
    destruct (q s>= slice_len data) eqn:Hge.
  1,3: inversion H; subst; eauto.
  - exfalso. apply scalar_geb_false_lt in Hge.
    rewrite slice_len_spec in Hge. cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge. rewrite slice_len_spec in Hge.
    destruct (module_read_section_header data q) as [r|] eqn:Hhdr;
      cbn [bind] in H |- *; [|discriminate].
    destruct r as [[[id start] fin]|e]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H |- *. cbn [bind] in H |- *.
    destruct (read_section_header_step _ _ _ _ _ Hhdr) as [Hqs [Hsf Hfd]].
    rewrite slice_len_spec in Hfd.
    destruct (id s= module_section_custom).
    { destruct (module_decode_custom_section data start fin) as [r1|] eqn:Hcs;
        cbn [bind] in H |- *; [|discriminate].
      destruct r1 as [c|e1]; [|try_err_rw_in H; discriminate].
      rewrite branch_ok in H |- *. cbn [bind] in H |- *.
      destruct (inst.(module_ModuleVisitor_t_on_custom_section) v c)
        as [[rh v1]|] eqn:Hh; cbn [bind] in H; [|discriminate].
      destruct rh as [u|ev]; [|cbn beta iota in H; discriminate].
      cbn beta iota in H.
      destruct (Hacc w c) as [w1 Hw1]. rewrite Hw1. cbn [bind]. cbn beta iota.
      exact (IH V W inst inst' data env v1 w1 segments fin seen tail v' Hacc
               (ltac:(lia)) H). }
    destruct (id s<> module_section_data); [discriminate|].
    destruct seen; [discriminate|].
    destruct (module_decode_data_section data start env) as [r1|] eqn:Hds;
      cbn [bind] in H |- *; [|discriminate].
    destruct r1 as [[decoded p]|e1]; [|try_err_rw_in H; discriminate].
    rewrite branch_ok in H |- *. cbn [bind] in H |- *.
    destruct (p s<> fin); [discriminate|].
    cbn beta iota in H |- *.
    exact (IH V W inst inst' data env v w decoded fin true tail v' Hacc
             (ltac:(lia)) H).
Qed.

Lemma validate_tail_with_transfer :
  forall V W (inst : module_ModuleVisitor_t V) (inst' : module_ModuleVisitor_t W)
         data pos env v w tail v',
  module_hooks_accept inst' ->
  module_validate_tail_with inst data pos env v
    = Ok (Core_result_Result_Ok tail, v') ->
  exists w', module_validate_tail_with inst' data pos env w
             = Ok (Core_result_Result_Ok tail, w').
Proof.
  intros V W inst inst' data pos env v w tail v' Hacc H.
  unfold module_validate_tail_with in H |- *.
  exact (validate_tail_with_loop_transfer (List.length (vec_list data)) V W inst
           inst' data env v w (alloc_vec_Vec_new module_Data_t) pos false tail
           v' Hacc (ltac:(pose proof (usize_nonneg pos); lia)) H).
Qed.

Corollary validate_tail_with_accepts :
  forall V (inst : module_ModuleVisitor_t V) data pos env v tail,
  module_hooks_accept inst ->
  module_validate_tail data pos env = Ok (Core_result_Result_Ok tail) ->
  exists v', module_validate_tail_with inst data pos env v
             = Ok (Core_result_Result_Ok tail, v').
Proof.
  intros V inst data pos env v tail Hacc H.
  apply (validate_tail_with_transfer _ V
           module_EmptyModuleVisitor_Insts_ItascaModuleModuleVisitor inst data
           pos env tt v tail tt Hacc).
  exact (validate_tail_nop_inv data pos env _ H).
Qed.

(** The code section's walk needs both obligations at once: [code_hooks_validate]
    of the run in hand, to know the entry it accepted is one the validator
    accepts, and [code_hooks_accept] of the run being built, to know it accepts
    the same entry. *)
Lemma validate_code_entries_with_loop_transfer :
  forall m V W (inst : module_CodeVisitor_t V) (inst' : module_CodeVisitor_t W)
         data env v w q i q' v',
  code_hooks_validate inst data env ->
  code_hooks_accept inst' data env ->
  Z.of_nat (List.length (vec_list env.(module_Env_func_type_indices)))
    - to_Z i <= Z.of_nat m ->
  module_validate_code_entries_with_loop inst data env v q i
    = Ok (Core_result_Result_Ok q', v') ->
  exists w', module_validate_code_entries_with_loop inst' data env w q i
             = Ok (Core_result_Result_Ok q', w').
Proof.
  induction m as [|m IH];
    intros V W inst inst' data env v w q i q' v' Hval Hacc Hmeas H;
    destruct Hacc as [Hnb Hce];
    unfold module_validate_code_entries_with_loop in H |- *;
    rewrite loop_unfold in H; rewrite loop_unfold; cbn beta iota in H |- *;
    destruct (i s>= alloc_vec_Vec_len env.(module_Env_func_type_indices))
      eqn:Hge.
  1,3: inversion H; subst; eauto.
  - exfalso. apply scalar_geb_false_lt in Hge. rewrite vec_len_spec in Hge.
    cbn in Hmeas. lia.
  - apply scalar_geb_false_lt in Hge. rewrite vec_len_spec in Hge.
    destruct (usize_add q limits_max_leb_bytes) as [qw|] eqn:Hqw;
      cbn [bind] in H |- *; [|discriminate].
    destruct (inst.(module_CodeVisitor_t_on_need_bytes) v qw) as [[rn v1]|]
      eqn:Hn; cbn [bind] in H; [|discriminate].
    destruct rn as [un|en]; [|try_err_rw_in H; cbn beta iota in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (Hnb w qw) as [w1 Hw1].
    rewrite Hw1. cbn [bind]. rewrite branch_ok. cbn [bind].
    destruct (module_code_entry_extent data q) as [rx|] eqn:Hx;
      cbn [bind] in H |- *; [|discriminate].
    destruct rx as [[contents fin]|ex];
      [|try_err_rw_in H; cbn beta iota in H; discriminate].
    rewrite branch_ok in H |- *. cbn [bind] in H |- *.
    destruct (inst.(module_CodeVisitor_t_on_need_bytes) v1 fin) as [[rn2 v2]|]
      eqn:Hn2; cbn [bind] in H; [|discriminate].
    destruct rn2 as [un2|en2];
      [|try_err_rw_in H; cbn beta iota in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct (Hnb w1 fin) as [w2 Hw2].
    rewrite Hw2. cbn [bind]. rewrite branch_ok. cbn [bind].
    destruct (inst.(module_CodeVisitor_t_on_code_entry) v2 data env i q contents
                fin) as [[re v3]|] eqn:He; cbn [bind] in H; [|discriminate].
    destruct re as [ue|ee];
      [|try_err_rw_in H; cbn beta iota in H; discriminate].
    rewrite branch_ok in H. cbn [bind] in H.
    destruct ue.
    destruct (Hval _ _ _ _ _ _ He) as [q1 Hent].
    destruct (Hce w2 i q contents fin q1 Hent) as [w3 Hw3].
    rewrite Hw3. cbn [bind]. rewrite branch_ok. cbn [bind].
    destruct (usize_add i 1%usize) as [i2|] eqn:Hadd;
      cbn [bind] in H |- *; [|discriminate].
    apply (IH V W inst inst' data env v3 w3 fin i2 q' v' Hval
             (conj Hnb Hce)
             (ltac:(pose proof (scalar_add_val _ _ _ 1 Hadd eq_refl);
                    cbn in Hmeas; lia)) H).
Qed.

Lemma validate_code_with_transfer :
  forall V W (inst : module_CodeVisitor_t V) (inst' : module_CodeVisitor_t W)
         data pos env v w q' v',
  code_hooks_validate inst data env ->
  code_hooks_accept inst' data env ->
  module_validate_code_with inst data pos env v
    = Ok (Core_result_Result_Ok q', v') ->
  exists w', module_validate_code_with inst' data pos env w
             = Ok (Core_result_Result_Ok q', w').
Proof.
  intros V W inst inst' data pos env v w q' v' Hval Hacc H.
  pose proof Hacc as Hacc0. destruct Hacc0 as [Hnb _].
  unfold module_validate_code_with in H |- *.
  destruct (usize_add pos limits_max_code_header_bytes) as [pw|] eqn:Hpw;
    cbn [bind] in H |- *; [|discriminate].
  destruct (inst.(module_CodeVisitor_t_on_need_bytes) v pw) as [[rn v1]|]
    eqn:Hn; cbn [bind] in H; [|discriminate].
  destruct rn as [un|en]; [|try_err_rw_in H; cbn beta iota in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (Hnb w pw) as [w1 Hw1].
  rewrite Hw1. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (module_code_section data pos env) as [r|] eqn:Hcs;
    cbn [bind] in H |- *; [|discriminate].
  destruct r as [oc|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H |- *. cbn [bind] in H |- *.
  destruct oc as [cs|]; [|inversion H; subst; eauto].
  unfold module_validate_code_entries_with in H |- *.
  destruct (module_validate_code_entries_with_loop inst data env v1
              cs.(module_CodeSection_entries) 0%usize) as [[r2 v2]|] eqn:Hents;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [q|e2]; [|try_err_rw_in H; cbn beta iota in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (validate_code_entries_with_loop_transfer
              (List.length (vec_list env.(module_Env_func_type_indices)))
              V W inst inst' data env v1 w1 cs.(module_CodeSection_entries)
              0%usize q v2 Hval Hacc
              (ltac:(assert (to_Z 0%usize = 0) by reflexivity; lia)) Hents)
    as [w2 Hw2].
  rewrite Hw2. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (q s<> cs.(module_CodeSection_end)); [discriminate|].
  cbn beta iota in H |- *. inversion H; subst. eauto.
Qed.

Corollary validate_code_with_accepts :
  forall V (inst : module_CodeVisitor_t V) data pos env v q',
  code_hooks_accept inst data env ->
  module_validate_code data pos env = Ok (Core_result_Result_Ok q') ->
  exists v', module_validate_code_with inst data pos env v
             = Ok (Core_result_Result_Ok q', v').
Proof.
  intros V inst data pos env v q' Hacc H.
  apply (validate_code_with_transfer _ V
           module_ValidatingCodeVisitor_Insts_ItascaModuleCodeVisitor inst
           data pos env tt v q' tt (validating_code_hooks_validate data env)
           Hacc).
  exact (validate_code_nop_inv data pos env _ H).
Qed.

(* ================================================================== *)
(** ** The whole module                                                *)
(* ================================================================== *)

(** [Module_Sound.validate_module_parts] read backwards. [validate_module] is
    the three parts in order behind one size check, so this is that check and
    three rewrites; it is here because nothing else says it, and a consumer
    that called the three itself has no other way to reach
    [validate_module_repr] and [validate_module_typed]. *)
Theorem validate_module_of_parts : forall data env code_pos tail_pos tl,
  dlen data <= module_bytes ->
  module_validate_env data = Ok (Core_result_Result_Ok (env, code_pos)) ->
  module_validate_code data code_pos env
    = Ok (Core_result_Result_Ok tail_pos) ->
  module_validate_tail data tail_pos env = Ok (Core_result_Result_Ok tl) ->
  module_validate_module data
    = Ok (Core_result_Result_Ok
            {| module_Module_env := env;
               module_Module_tail := tl |}).
Proof.
  intros data env code_pos tail_pos tl Hlen Henv Hcode Htail.
  unfold module_validate_module.
  destruct (slice_len data s> limits_max_module_bytes) eqn:Hbig.
  { exfalso. apply scalar_gtb_true in Hbig.
    rewrite max_module_bytes_val in Hbig. lia. }
  rewrite Henv. cbn [bind]. rewrite branch_ok. cbn [bind].
  rewrite Hcode. cbn [bind]. rewrite branch_ok. cbn [bind].
  rewrite Htail. cbn [bind]. rewrite branch_ok. cbn [bind]. reflexivity.
Qed.

(** The mirror of [Module_Sound.validate_module_driven]: driving the walk
    changes neither the verdict nor the module it reports, in either
    direction. *)
Theorem validate_module_with_accepts :
  forall V (minst : module_ModuleVisitor_t V) (cinst : module_CodeVisitor_t V)
         data v vm,
  module_hooks_accept minst ->
  (forall env, code_hooks_accept cinst data env) ->
  module_validate_module data = Ok (Core_result_Result_Ok vm) ->
  exists v', module_validate_module_with minst cinst data v
             = Ok (Core_result_Result_Ok vm, v').
Proof.
  intros V minst cinst data v vm Hmacc Hcacc H.
  unfold module_validate_module in H. unfold module_validate_module_with.
  destruct (slice_len data s> limits_max_module_bytes); [discriminate|].
  destruct (module_validate_env data) as [r|] eqn:Henv; cbn [bind] in H;
    [|discriminate].
  destruct r as [[env code_pos]|e]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (validate_env_with_accepts V minst data v env code_pos Hmacc Henv)
    as [v1 Hv1].
  rewrite Hv1. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (module_validate_code data code_pos env) as [r1|] eqn:Hcode;
    cbn [bind] in H; [|discriminate].
  destruct r1 as [tail_pos|e1]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (validate_code_with_accepts V cinst data code_pos env v1 tail_pos
              (Hcacc env) Hcode) as [v2 Hv2].
  rewrite Hv2. cbn [bind]. rewrite branch_ok. cbn [bind].
  destruct (module_validate_tail data tail_pos env) as [r2|] eqn:Htail;
    cbn [bind] in H; [|discriminate].
  destruct r2 as [tl|e2]; [|try_err_rw_in H; discriminate].
  rewrite branch_ok in H. cbn [bind] in H.
  destruct (validate_tail_with_accepts V minst data tail_pos env v2 tl Hmacc
              Htail) as [v3 Hv3].
  rewrite Hv3. cbn [bind]. rewrite branch_ok. cbn [bind].
  inversion H; subst. eauto.
Qed.

(** [Module_NoPanic.validate_module_no_panic] for the driven walk. The size
    check is inside [validate_module_with] as it is inside [validate_module],
    so the only hypotheses are the consumer's own. *)
Theorem validate_module_with_no_panic :
  forall V (minst : module_ModuleVisitor_t V) (cinst : module_CodeVisitor_t V)
         data v,
  module_hooks_total minst ->
  (forall env, code_hooks_total cinst data env) ->
  exists r v', module_validate_module_with minst cinst data v = Ok (r, v').
Proof.
  intros V minst cinst data v Hmt Hct. unfold module_validate_module_with.
  destruct (slice_len data s> limits_max_module_bytes) eqn:Hbig;
    [eauto|].
  apply scalar_gtb_false in Hbig. rewrite max_module_bytes_val in Hbig.
  destruct (validate_env_with_ok V minst v data Hmt Hbig) as [r [v1 [Hr Hpost]]].
  rewrite Hr. cbn [bind]. cbn beta iota.
  destruct r as [[env code_pos]|e]; [|try_err_rw; eauto].
  rewrite branch_ok. cbn [bind].
  destruct (Hpost _ _ (ltac:(reflexivity))) as [Hcp Henv].
  destruct (validate_code_with_ok V cinst data code_pos env v1 (Hct env) Henv
              Hcp Hbig) as [r1 [v2 [Hr1 Hvc]]].
  rewrite Hr1. cbn [bind]. cbn beta iota.
  destruct r1 as [tail_pos|e1]; [|try_err_rw; eauto].
  rewrite branch_ok. cbn [bind].
  destruct (Hvc _ (ltac:(reflexivity))) as [_ Htp].
  destruct (validate_tail_with_ok V minst data tail_pos env v2 Hmt Htp Hbig)
    as [r2 [v3 Hr2]].
  rewrite Hr2. cbn [bind]. cbn beta iota.
  destruct r2 as [tl|e2]; [|try_err_rw; eauto].
  rewrite branch_ok. cbn [bind]. eauto.
Qed.

(** And completeness for it. *)
Corollary validate_module_with_complete :
  forall V (minst : module_ModuleVisitor_t V) (cinst : module_CodeVisitor_t V)
         data v m,
  module_hooks_accept minst ->
  (forall env, code_hooks_accept cinst data env) ->
  dlen data <= module_bytes ->
  repr_module_fit (byte_list data) m ->
  module_wasm10 m ->
  exists vm v', module_validate_module_with minst cinst data v
                = Ok (Core_result_Result_Ok vm, v').
Proof.
  intros V minst cinst data v m Hmacc Hcacc Hlen Hrepr Hw10.
  destruct (validate_module_complete data m Hlen Hrepr Hw10) as [vm Hvm].
  destruct (validate_module_with_accepts V minst cinst data v vm Hmacc Hcacc
              Hvm) as [v' Hv'].
  exists vm, v'. exact Hv'.
Qed.

(** The payoff for a consumer holding the module in pieces: three accepting
    parts mean the bytes are a well-typed Wasm 1.0 module, with the import and
    export types the environment reports. [validate_module_repr],
    [Module_Wasm10.validate_module_typechecked] and the rest transfer the same
    way, through [validate_module_of_parts]. *)
Corollary validate_module_parts_typed : forall data env code_pos tail_pos tl,
  dlen data <= module_bytes ->
  module_validate_env data = Ok (Core_result_Result_Ok (env, code_pos)) ->
  module_validate_code data code_pos env
    = Ok (Core_result_Result_Ok tail_pos) ->
  module_validate_tail data tail_pos env = Ok (Core_result_Result_Ok tl) ->
  exists m imps exps,
    repr_module (byte_list data) m
    /\ module_import_types env = Ok (Core_result_Result_Ok imps)
    /\ module_export_types env = Ok (Core_result_Result_Ok exps)
    /\ mod_imports m = List.map translate_import (vec_list env.(module_Env_imports))
    /\ mod_exports m = List.map translate_export (vec_list env.(module_Env_exports))
    /\ module_typing m (translate_externtypes imps)
                       (translate_externtypes exps).
Proof.
  intros data env code_pos tail_pos tl Hlen Henv Hcode Htail.
  exact (validate_module_typed data _
           (validate_module_of_parts data env code_pos tail_pos tl Hlen Henv
              Hcode Htail)).
Qed.
