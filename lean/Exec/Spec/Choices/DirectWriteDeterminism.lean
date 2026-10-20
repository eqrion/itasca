import Exec.Spec.Choices.MutationUniqueness
import Exec.Spec.Choices.VectorReadUniqueness
import Exec.Spec.MemoryBounds
import Exec.Spec.Choices.ValuePrefixSyntax
/-! Direct state-changing source rules, separated from evaluation contexts.
Each constructor retains the generated rule premises and erases to Step. -/
namespace Exec.Spec
open SpecExt
inductive DirectWrite : config → config → Prop where
  | local_set (z : state) (v_val : val) (x : idx) (var_0 : state) :
    fun_with_local z x v_val var_0 →
    wf_config (config.mk_config z [admininstr_val v_val, admininstr.LOCAL_SET x]) →
    wf_config (config.mk_config var_0 []) →
    DirectWrite (config.mk_config z [admininstr_val v_val, admininstr.LOCAL_SET x]) (config.mk_config var_0 [])
  | global_set (z : state) (v_val : val) (x : idx) (var_0 : state) :
    fun_with_global z x v_val var_0 →
    wf_config (config.mk_config z [admininstr_val v_val, admininstr.GLOBAL_SET x]) →
    wf_config (config.mk_config var_0 []) →
    DirectWrite (config.mk_config z [admininstr_val v_val, admininstr.GLOBAL_SET x]) (config.mk_config var_0 [])
  | table_set_trap (z : state) (i : num_) (v_ref : ref) (x : idx) :
    (proj_num__0 i) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 i))) ≥ (List.length ((fun_table z x).REFS)) →
    wf_config (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr_ref v_ref, admininstr.TABLE_SET x]) →
    wf_config (config.mk_config z [admininstr.TRAP]) →
    DirectWrite (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr_ref v_ref, admininstr.TABLE_SET x]) (config.mk_config z [admininstr.TRAP])
  | table_set_val (z : state) (i : num_) (v_ref : ref) (x : idx) (var_0 : state) :
    (proj_num__0 i) ≠ none →
    fun_with_table z x (proj_uN_0 (Option.get! (proj_num__0 i))) v_ref var_0 →
    (proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_table z x).REFS)) →
    wf_config (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr_ref v_ref, admininstr.TABLE_SET x]) →
    wf_config (config.mk_config var_0 []) →
    DirectWrite (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr_ref v_ref, admininstr.TABLE_SET x]) (config.mk_config var_0 [])
  | elem_drop (z : state) (x : idx) (var_0 : state) :
    fun_with_elem z x [] var_0 →
    wf_config (config.mk_config z [admininstr.ELEM_DROP x]) →
    wf_config (config.mk_config var_0 []) →
    DirectWrite (config.mk_config z [admininstr.ELEM_DROP x]) (config.mk_config var_0 [])
  | store_num_trap (z : state) (i : num_) (nt : numtype) (c : num_) (ao : memarg) :
    (proj_num__0 i) ≠ none →
    (size (valtype_numtype nt)) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat (((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_config (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CONST nt c, admininstr.STORE nt none ao]) →
    wf_config (config.mk_config z [admininstr.TRAP]) →
    wf_uN 32 (uN.mk_uN 0) →
    DirectWrite (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CONST nt c, admininstr.STORE nt none ao]) (config.mk_config z [admininstr.TRAP])
  | store_num_val (z : state) (i : num_) (nt : numtype) (c : num_) (ao : memarg) (b_lst : List byte) (var_0 : state) :
    (proj_num__0 i) ≠ none →
    (size (valtype_numtype nt)) ≠ none →
    fun_with_mem z (uN.mk_uN 0) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (rat_to_nat (((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat))) b_lst var_0 →
    b_lst = (nbytes_ nt c) →
    wf_config (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CONST nt c, admininstr.STORE nt none ao]) →
    wf_config (config.mk_config var_0 []) →
    DirectWrite (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CONST nt c, admininstr.STORE nt none ao]) (config.mk_config var_0 [])
  | store_pack_trap (z : state) (i : num_) (v_Inn : Inn) (c : num_) (v_n : n) (ao : memarg) :
    (proj_num__0 i) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat ((v_n : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_config (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CONST (numtype_Inn v_Inn) c, admininstr.STORE (numtype_Inn v_Inn) (some (sz.mk_sz v_n)) ao]) →
    wf_config (config.mk_config z [admininstr.TRAP]) →
    wf_uN 32 (uN.mk_uN 0) →
    DirectWrite (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CONST (numtype_Inn v_Inn) c, admininstr.STORE (numtype_Inn v_Inn) (some (sz.mk_sz v_n)) ao]) (config.mk_config z [admininstr.TRAP])
  | store_pack_val (z : state) (i : num_) (v_Inn : Inn) (c : num_) (v_n : n) (ao : memarg) (b_lst : List byte) (var_0 : state) :
    (proj_num__0 i) ≠ none →
    fun_with_mem z (uN.mk_uN 0) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (rat_to_nat ((v_n : Rat) / (8 : Rat))) b_lst var_0 →
    (size (valtype_Inn v_Inn)) ≠ none →
    (proj_num__0 c) ≠ none →
    b_lst = (ibytes_ v_n (wrap__ (Option.get! (size (valtype_Inn v_Inn))) v_n (Option.get! (proj_num__0 c)))) →
    wf_config (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CONST (numtype_Inn v_Inn) c, admininstr.STORE (numtype_Inn v_Inn) (some (sz.mk_sz v_n)) ao]) →
    wf_config (config.mk_config var_0 []) →
    DirectWrite (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CONST (numtype_Inn v_Inn) c, admininstr.STORE (numtype_Inn v_Inn) (some (sz.mk_sz v_n)) ao]) (config.mk_config var_0 [])
  | vstore_oob (z : state) (i : num_) (c : vec_) (ao : memarg) :
    (proj_num__0 i) ≠ none →
    (size valtype.V128) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat (((Option.get! (size valtype.V128)) : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_config (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c, admininstr.VSTORE vectype.V128 ao]) →
    wf_config (config.mk_config z [admininstr.TRAP]) →
    wf_uN 32 (uN.mk_uN 0) →
    DirectWrite (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c, admininstr.VSTORE vectype.V128 ao]) (config.mk_config z [admininstr.TRAP])
  | vstore_val (z : state) (i : num_) (c : vec_) (ao : memarg) (b_lst : List byte) (var_0 : state) :
    (proj_num__0 i) ≠ none →
    (size valtype.V128) ≠ none →
    fun_with_mem z (uN.mk_uN 0) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (rat_to_nat (((Option.get! (size valtype.V128)) : Rat) / (8 : Rat))) b_lst var_0 →
    b_lst = (vbytes_ vectype.V128 c) →
    wf_config (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c, admininstr.VSTORE vectype.V128 ao]) →
    wf_config (config.mk_config var_0 []) →
    DirectWrite (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c, admininstr.VSTORE vectype.V128 ao]) (config.mk_config var_0 [])
  | vstore_lane_oob (z : state) (i : num_) (c : vec_) (v_N : N) (ao : memarg) (j : laneidx) :
    (proj_num__0 i) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat ((v_N : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_config (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c, admininstr.VSTORE_LANE vectype.V128 (sz.mk_sz v_N) ao j]) →
    wf_config (config.mk_config z [admininstr.TRAP]) →
    wf_uN 32 (uN.mk_uN 0) →
    DirectWrite (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c, admininstr.VSTORE_LANE vectype.V128 (sz.mk_sz v_N) ao j]) (config.mk_config z [admininstr.TRAP])
  | vstore_lane_val (z : state) (i : num_) (c : vec_) (v_N : N) (ao : memarg) (j : laneidx) (b_lst : List byte) (v_Jnn : Jnn) (v_M : M) (var_0 : state) :
    (proj_num__0 i) ≠ none →
    fun_with_mem z (uN.mk_uN 0) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (rat_to_nat ((v_N : Rat) / (8 : Rat))) b_lst var_0 →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat ((v_N : Rat) / (8 : Rat)))) ≤ (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    v_N = (jsize v_Jnn) →
    (v_M : Rat) = ((128 : Rat) / (v_N : Rat)) →
    (proj_lane__0 ((lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) c)[proj_uN_0 j]!)) ≠ none →
    (proj_uN_0 j) < (List.length (lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) c)) →
    b_lst = (ibytes_ v_N (uN.mk_uN (proj_uN_0 (Option.get! (proj_lane__0 ((lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) c)[proj_uN_0 j]!)))))) →
    wf_config (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c, admininstr.VSTORE_LANE vectype.V128 (sz.mk_sz v_N) ao j]) →
    wf_config (config.mk_config var_0 []) →
    wf_uN 32 (uN.mk_uN 0) →
    wf_uN v_N (uN.mk_uN (proj_uN_0 (Option.get! (proj_lane__0 ((lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) c)[proj_uN_0 j]!))))) →
    DirectWrite (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c, admininstr.VSTORE_LANE vectype.V128 (sz.mk_sz v_N) ao j]) (config.mk_config var_0 [])
  | data_drop (z : state) (x : idx) (var_0 : state) :
    fun_with_data z x [] var_0 →
    wf_config (config.mk_config z [admininstr.DATA_DROP x]) →
    wf_config (config.mk_config var_0 []) →
    DirectWrite (config.mk_config z [admininstr.DATA_DROP x]) (config.mk_config var_0 [])

theorem DirectWrite.erases {before after : config} (source : DirectWrite before after) : Step before after := by
  cases source
  all_goals solve_by_elim (maxDepth := 16) [Step.local_set,Step.global_set,Step.table_set_trap,Step.table_set_val,
    Step.elem_drop,Step.store_num_trap,Step.store_num_val,Step.store_pack_trap,Step.store_pack_val,
    Step.vstore_oob,Step.vstore_val,Step.vstore_lane_oob,Step.vstore_lane_val,Step.data_drop]

private theorem ref_instruction_injective {left right : ref}
    (same : admininstr_ref left=admininstr_ref right) : left=right := by
  cases left <;> cases right <;> simp_all [admininstr_ref]

private theorem integer_type_injective {left right : Inn}
    (same : numtype_Inn left=numtype_Inn right) : left=right := by
  cases left <;> cases right <;> simp_all [numtype_Inn]

private def writeLast (c : config) : Option Nat := (match c with | .mk_config _ code => code).getLast? |>.map admininstr.ctorIdx
set_option maxHeartbeats 2000000 in
theorem DirectWrite.deterministic {before other left right : config}
    (first : DirectWrite before left) (second : DirectWrite other right) (same : before=other) : left=right := by
  have last := congrArg writeLast same
  cases first
  all_goals cases second
  all_goals cases last
  all_goals try injections
  all_goals subst_vars
  all_goals try injections
  all_goals subst_vars
  all_goals try injections
  all_goals subst_vars
  all_goals try injections
  all_goals subst_vars
  all_goals try (with_reducible rfl)
  all_goals try (with_reducible contradiction)
  all_goals try (with_reducible grind only [value_instruction_injective,ref_instruction_injective,
    integer_type_injective,source_with_local_unique,source_with_global_unique,source_with_table_unique,
    source_with_elem_unique,source_with_data_unique,source_with_mem_unique,memory_write_bounds,
    source_jsize_injective])
  case store_num_trap.store_num_val | store_num_val.store_num_trap |
      store_pack_trap.store_pack_val | store_pack_val.store_pack_trap |
      vstore_oob.vstore_val | vstore_val.vstore_oob =>
    have inside := memory_write_bounds (by assumption)
    omega
  case vstore_lane_val.vstore_lane_val =>
    have inj : Function.Injective jsize := fun _ _ h => source_jsize_injective h
    simp only [inj.eq_iff] at *
    subst_vars
    casesm* Jnn
    all_goals norm_num [jsize,lsize,lanetype_Jnn,sizenn,size,valtype_numtype,psize] at *
    all_goals norm_cast at *
    all_goals subst_vars
    all_goals with_reducible grind only [source_with_mem_unique]
end Exec.Spec
