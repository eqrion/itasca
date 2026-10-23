import Exec.Store.Invariant.FunctionStaging
import Exec.Store.Initialization.ElementEffects
import Exec.Store.Initialization.DataEffects
namespace Exec.Store
open Aeneas Aeneas.Std

/-- Addresses issued by append-only preparation, in their actual source order. -/
def AddressOrder (start : Nat) (initial : List Nat) (total : Nat) (addresses : List Nat) : Prop :=
  ∃ count, total = start + count ∧ addresses = initial ++ List.range' start count

theorem AddressOrder.refl (start : Nat) (initial : List Nat) : AddressOrder start initial start initial :=
  ⟨0, by simp, by simp⟩

theorem AddressOrder.append {start total : Nat} {initial addresses : List Nat}
    (ordered : AddressOrder start initial total addresses) :
    AddressOrder start initial (total + 1) (addresses ++ [total]) := by
  obtain ⟨count, rfl, rfl⟩ := ordered
  refine ⟨count + 1, by omega, ?_⟩
  simp only [List.range'_concat, Nat.one_mul, List.append_assoc]

theorem AddressOrder.complete {start total count : Nat} {initial addresses : List Nat}
    (ordered : AddressOrder start initial total addresses)
    (lengths : addresses.length = initial.length + count) :
    total = start + count ∧ addresses = initial ++ List.range' start count := by
  obtain ⟨actual, totalEq, values⟩ := ordered
  have same : actual = count := by simp only [values, List.length_append, List.length_range'] at lengths; omega
  simpa only [same] using And.intro totalEq values

theorem AddressOrder.trans {a b c : Nat} {initial middle final : List Nat}
    (first : AddressOrder a initial b middle) (second : AddressOrder b middle c final) :
    AddressOrder a initial c final := by
  obtain ⟨n, rfl, rfl⟩ := first
  obtain ⟨m, rfl, rfl⟩ := second
  refine ⟨n + m, by omega, ?_⟩
  rw [List.append_assoc]
  congr 1
  simpa only [Nat.one_mul] using (List.range'_append (s := a) (m := n) (n := m) (step := 1))

theorem FunctionStageEffect.address_order {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {instanceIndex index signature out} {start initial}
    (effect : FunctionStageEffect store inst instanceIndex index signature out)
    (ordered : AddressOrder start initial store.funcs.length (inst.funcs.val.map fun address => address.index.val)) :
    AddressOrder start initial out.2.1.funcs.length (out.2.2.funcs.val.map fun address => address.index.val) := by
  rcases effect with ⟨error, rfl⟩ | ⟨functions, addresses, stored, mapped, capacity, rfl⟩
  · exact ordered
  · simpa [stored, mapped] using ordered.append

theorem GlobalStageEffect.address_order {M : Type} {store after : runtime.store.Store M}
    {inst next : runtime.store.ModuleInst} {instIndex : Usize} {start initial}
    (effect : GlobalStageEffect store instIndex inst after)
    (found : store.instances.val[instIndex.val]? = some inst)
    (nextFound : after.instances.val[instIndex.val]? = some next)
    (ordered : AddressOrder start initial store.globals.length (inst.globals.val.map (fun address => address.index.val))) :
    AddressOrder start initial after.globals.length (next.globals.val.map (fun address => address.index.val)) := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    simpa only [same] using ordered
  | appended globals addresses global stored mapped canonical room =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    simpa [stored, mapped] using ordered.append

theorem ElementStageEffect.address_order {M : Type} {store after : runtime.store.Store M}
    {inst next : runtime.store.ModuleInst} {instIndex : Usize} {start initial}
    (effect : ElementStageEffect store instIndex inst after)
    (found : store.instances.val[instIndex.val]? = some inst)
    (nextFound : after.instances.val[instIndex.val]? = some next)
    (ordered : AddressOrder start initial store.elems.length (inst.elems.val.map (UScalar.val))) :
    AddressOrder start initial after.elems.length (next.elems.val.map (UScalar.val)) := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    simpa only [same] using ordered
  | appended elements addresses element stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    simpa [stored, mapped] using ordered.append

theorem DataStageEffect.address_order {M : Type} {store after : runtime.store.Store M}
    {inst next : runtime.store.ModuleInst} {instIndex : Usize} {start initial}
    (effect : DataStageEffect store instIndex inst after)
    (found : store.instances.val[instIndex.val]? = some inst)
    (nextFound : after.instances.val[instIndex.val]? = some next)
    (ordered : AddressOrder start initial store.datas.length (inst.datas.val.map (UScalar.val))) :
    AddressOrder start initial after.datas.length (next.datas.val.map (UScalar.val)) := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    simpa only [same] using ordered
  | appended datas addresses data stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    simpa [stored, mapped] using ordered.append

end Exec.Store
