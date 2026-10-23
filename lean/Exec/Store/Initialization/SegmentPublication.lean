import Exec.Store.Initialization.SegmentCounts
namespace Exec.Store
open Aeneas Aeneas.Std

/-- Old instance maps remain exact. New segment addresses are accounted for by
newly published instance maps; existing payloads may be dropped or modified.
This is an explicit state relation, not a law of arbitrary host callbacks. -/
structure SegmentPublication {M : Type} (before after : runtime.store.Store M) : Prop where
  instances : after.instances.val.take before.instances.length = before.instances.val
  elements : after.elems.length = before.elems.length +
    ((after.instances.val.drop before.instances.length).map fun inst => inst.elems.length).sum
  datas : after.datas.length = before.datas.length +
    ((after.instances.val.drop before.instances.length).map fun inst => inst.datas.length).sum

private theorem sum_retained {T : Type} (measure : T → Nat) {before after : List T}
    (retained : after.take before.length = before) :
    (after.map measure).sum = (before.map measure).sum + ((after.drop before.length).map measure).sum := by
  conv_lhs => rw [←List.take_append_drop before.length after]
  rw [List.map_append,List.sum_append,retained]

private theorem prefix_trans {T : Type} {a b c : List T}
    (ab : b.take a.length = a) (bc : c.take b.length = b) : c.take a.length = a := by
  have lengths := congrArg List.length ab
  simp only [List.length_take] at lengths
  have bound : a.length ≤ b.length := by omega
  calc
    c.take a.length = (c.take b.length).take a.length := by simp [List.take_take,Nat.min_eq_left bound]
    _ = a := by rw [bc,ab]

private theorem suffix_sum {T : Type} (measure : T → Nat) {a b c : List T}
    (ab : b.take a.length = a) (bc : c.take b.length = b) :
    ((c.drop a.length).map measure).sum =
      ((b.drop a.length).map measure).sum + ((c.drop b.length).map measure).sum := by
  have first := sum_retained measure ab
  have second := sum_retained measure bc
  have both := sum_retained measure (prefix_trans ab bc)
  omega

theorem SegmentPublication.refl {M : Type} (store : runtime.store.Store M) :
    SegmentPublication store store := by
  constructor <;> simp

theorem SegmentPublication.trans {M : Type} {a b c : runtime.store.Store M}
    (first : SegmentPublication a b) (second : SegmentPublication b c) : SegmentPublication a c := by
  refine ⟨prefix_trans first.instances second.instances,?_,?_⟩
  · rw [second.elements,first.elements]
    have sums := suffix_sum (fun inst : runtime.store.ModuleInst => inst.elems.length) first.instances second.instances
    change _ = _ + ((c.instances.val.drop a.instances.val.length).map fun inst => inst.elems.length).sum
    rw [sums]
    simp only [alloc.vec.Vec.length]
    omega
  · rw [second.datas,first.datas]
    have sums := suffix_sum (fun inst : runtime.store.ModuleInst => inst.datas.length) first.instances second.instances
    change _ = _ + ((c.instances.val.drop a.instances.val.length).map fun inst => inst.datas.length).sum
    rw [sums]
    simp only [alloc.vec.Vec.length]
    omega

/-- Complete accounting on both sides determines the publication ledger.
In particular, retaining old metadata alone does not assume accounting for
newly introduced segment entries. -/
theorem SegmentPublication.of_accounting {M : Type} {before after : runtime.store.Store M}
    (instances : after.instances.val.take before.instances.length = before.instances.val)
    (old : SegmentAccounting before) (fresh : SegmentAccounting after) : SegmentPublication before after := by
  refine ⟨instances,?_,?_⟩
  · rw [fresh.elements,old.elements]
    exact sum_retained _ instances
  · rw [fresh.datas,old.datas]
    exact sum_retained _ instances

theorem SegmentPublication.accounting {M : Type} {before after : runtime.store.Store M}
    (published : SegmentPublication before after) (old : SegmentAccounting before) : SegmentAccounting after := by
  constructor
  · rw [published.elements,old.elements]
    exact (sum_retained _ published.instances).symm
  · rw [published.datas,old.datas]
    exact (sum_retained _ published.instances).symm

theorem SegmentPublication.element_count {M : Type} {before after : runtime.store.Store M}
    (published : SegmentPublication before after) : before.elems.length ≤ after.elems.length := by
  rw [published.elements]
  omega

theorem SegmentPublication.data_count {M : Type} {before after : runtime.store.Store M}
    (published : SegmentPublication before after) : before.datas.length ≤ after.datas.length := by
  rw [published.datas]
  omega

theorem SegmentPublication.instance_lookup {M : Type} {before after : runtime.store.Store M}
    (published : SegmentPublication before after) {index : Nat} {inst : runtime.store.ModuleInst}
    (found : before.instances.val[index]? = some inst) : after.instances.val[index]? = some inst := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have same := congrArg (fun instances => instances[index]?) published.instances
  simpa only [List.getElem?_take,if_pos bound,found] using same

/-- The former fixed-count relation is the no-publication special case. -/
theorem SegmentCounts.publication {M : Type} {before after : runtime.store.Store M}
    (counts : SegmentCounts before after) (instances : after.instances = before.instances) :
    SegmentPublication before after := by
  constructor
  · simp [instances]
  · simpa [instances] using counts.elements
  · simpa [instances] using counts.datas

theorem SegmentPublication.counts {M : Type} {before after : runtime.store.Store M}
    (published : SegmentPublication before after) (same : after.instances.length = before.instances.length) :
    SegmentCounts before after := by
  constructor
  · simpa only [←same,List.drop_length,List.map_nil,List.sum_nil,Nat.add_zero] using published.elements
  · simpa only [←same,List.drop_length,List.map_nil,List.sum_nil,Nat.add_zero] using published.datas
/-- The additive counts are also exact lengths of the independently decoded
source segment spaces. Their payload contents remain unconstrained. -/
theorem SegmentPublication.decoded_counts {M : Type} {before after : runtime.store.Store M}
    (published : SegmentPublication before after) (view : M → Slice U8)
    (oldCode newCode : CodeInterpretation) :
    (decodeStore view newCode after).ELEMS.length = (decodeStore view oldCode before).ELEMS.length +
      ((after.instances.val.drop before.instances.length).map fun inst => (decodeInstance after inst).ELEMS.length).sum ∧
    (decodeStore view newCode after).DATAS.length = (decodeStore view oldCode before).DATAS.length +
      ((after.instances.val.drop before.instances.length).map fun inst => (decodeInstance after inst).DATAS.length).sum := by
  constructor
  · simpa only [decodeStore,decodeInstance,List.length_map] using published.elements
  · simpa only [decodeStore,decodeInstance,List.length_map] using published.datas

end Exec.Store
