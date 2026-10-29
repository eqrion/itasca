import Itasca.Runtime.SourceMachine.Stateful.TableTyping
import Itasca.Runtime.SourceMachine.Stateful.MemorySize
import Itasca.Runtime.Spec.TableGrowth
import Itasca.Runtime.Spec.MemoryGrowth
namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

def limitMaximum : limits → Option Nat
  | .mk_limits _ maximum => maximum.map proj_uN_0

theorem limits_maximum_bound {type : limits} {bound : Nat} (typed : Limits_ok type bound) :
    ∀ maximum ∈ limitMaximum type, maximum ≤ bound := by
  cases typed with
  | mk_Limits_ok minimum maximum bound low high wf =>
    cases maximum with
    | none => simp [limitMaximum,OMap]
    | some maximum =>
      simpa [limitMaximum,OMap,proj_uN_0] using (high maximum (by simp)).2

theorem limits_grown {old count bound : Nat} {maximum : Option Nat}
    (typed : Limits_ok (.mk_limits (.mk_uN old) (OMap uN.mk_uN maximum)) bound)
    (small : count ≤ bound) (within : Forall (fun limit => count ≤ limit) maximum.toList)
    (wf : wf_limits (.mk_limits (.mk_uN count) (OMap uN.mk_uN maximum))) :
    Limits_ok (.mk_limits (.mk_uN count) (OMap uN.mk_uN maximum)) bound := by
  apply Limits_ok.mk_Limits_ok count maximum bound small _ wf
  intro limit member
  refine ⟨within limit member,?_⟩
  apply limits_maximum_bound typed limit
  cases maximum with
  | none => simp at member
  | some maximum => simpa [limitMaximum,OMap,proj_uN_0,eq_comm] using member

theorem growtable_typed {s : store} {object next : tableinst} {delta : Nat} {value : ref}
    (typed : Tableinst_ok s object object.TYPE)
    (valueTyped : Ref_ok s value (tableElementType object.TYPE))
    (grown : fun_growtable object delta value (some next)) :
    Tableinst_ok s next next.TYPE ∧ Extend_tableinst object next := by
  cases grown with
  | fun_growtable_case_0 _ minimum maximum type refs count source size limit target freshWf oldWf targetWf =>
    subst object
    subst next
    subst count
    cases typed with
    | mk_Tableinst_ok old max type refs typeOk refsOk length storeWf objectWf typeWf =>
      have small : refs.length+delta < 2^32 := by
        cases targetWf with | tableinst_case_ _ _ tableWf =>
        cases tableWf with | tabletype_case_0 _ _ limitsWf =>
        cases limitsWf with | limits_case_0 _ _ minWf _ =>
        cases minWf with | uN_case_0 _ bound => norm_num at bound ⊢; omega
      have wfLimits : wf_limits (.mk_limits (.mk_uN (refs.length+delta)) (OMap uN.mk_uN max)) := by
        cases targetWf; rename_i tableWf; cases tableWf; assumption
      have limitsOk : Limits_ok (.mk_limits (.mk_uN old) (OMap uN.mk_uN max)) (Int.toNat (((2^32):Int)-1)) := by
        cases typeOk; assumption
      have countLimit : Forall (fun maximum => refs.length+delta ≤ maximum) max.toList := by
        cases max <;> simpa [Forall,OMap,proj_uN_0] using limit
      have newLimits := limits_grown limitsOk (count:=refs.length+delta) (by norm_num; omega) countLimit wfLimits
      have newTableWf : wf_tabletype (.mk_tabletype (.mk_limits (.mk_uN (refs.length+delta)) (OMap uN.mk_uN max)) type) :=
        .tabletype_case_0 _ _ wfLimits
      constructor
      · apply Tableinst_ok.mk_Tableinst_ok s (refs.length+delta) max type (refs++List.replicate delta value)
          (.mk_Tabletype_ok _ _ newLimits newTableWf)
        · intro reference member
          rcases List.mem_append.mp member with original | added
          · exact refsOk reference original
          · have same : reference=value := List.eq_of_mem_replicate added
            subst reference
            exact valueTyped
        · simp
        · exact storeWf
        · exact targetWf
        · exact newTableWf
      · exact extend_table_contents old (refs.length+delta) max type refs (refs++List.replicate delta value)
          (by omega) (by simp) objectWf targetWf


theorem growmemory_typed {s : store} {object next : meminst} {delta : Nat}
    (typed : Meminst_ok s object object.TYPE)
    (grown : fun_growmemory object delta (some next)) :
    Meminst_ok s next next.TYPE ∧ Extend_meminst object next := by
  cases grown with
  | fun_growmemory_case_0 _ minimum maximum bytes count source size limit small target freshWf oldWf targetWf =>
    subst object
    subst next
    cases typed with
    | mk_Meminst_ok old max bytes typeOk length storeWf objectWf typeWf =>
      have countEq : count = ((old+delta : Nat) : Rat) := by
        rw [size,length]
        norm_num [Ki,Nat.cast_mul,Nat.cast_add]
      rw [countEq] at limit small freshWf targetWf ⊢
      have natural : rat_to_nat (((old+delta : Nat) : Rat)) = old+delta := by
        simp only [rat_to_nat,Rat.num_natCast,Rat.den_natCast]
        change ((Int.ofNat (old+delta)).tdiv 1).toNat = old+delta
        rw [Int.tdiv_one]
        rfl
      rw [natural] at freshWf targetWf ⊢
      have smallNat : old+delta ≤ 2^16 := by exact_mod_cast small
      have wfLimits : wf_limits (.mk_limits (.mk_uN (old+delta)) (OMap uN.mk_uN max)) := by
        cases targetWf; rename_i memoryWf _; cases memoryWf; assumption
      have limitsOk : Limits_ok (.mk_limits (.mk_uN old) (OMap uN.mk_uN max)) (2^16) := by
        cases typeOk; assumption
      have countLimit : Forall (fun maximum => old+delta ≤ maximum) max.toList := by
        cases max with
        | none => simp [Forall]
        | some max =>
          have one := limit (.mk_uN max) (by simp [OMap])
          have bounded : old+delta ≤ max := by exact_mod_cast one
          simpa [Forall] using bounded
      have newLimits := limits_grown limitsOk smallNat countLimit wfLimits
      have newMemoryWf : wf_memtype (.PAGE (.mk_limits (.mk_uN (old+delta)) (OMap uN.mk_uN max))) :=
        .memtype_case_0 _ wfLimits
      constructor
      · exact .mk_Meminst_ok s (old+delta) max (bytes++List.replicate (delta*(64*Ki)) (.mk_byte 0))
          (.mk_Memtype_ok _ newLimits newMemoryWf)
          (by simp only [List.length_append,List.length_replicate,length,Nat.add_mul])
          storeWf targetWf newMemoryWf
      · exact extend_mem_contents old (old+delta) max bytes (bytes++List.replicate (delta*(64*Ki)) (.mk_byte 0))
          (by omega) (by simp) objectWf targetWf
end Itasca.Runtime.SourceMachine.Stateful
