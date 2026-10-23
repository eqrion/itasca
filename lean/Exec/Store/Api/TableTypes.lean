import Exec.Store.Api.TableStagingLoop
import Exec.Store.Initialization.SegmentTypes

namespace Exec.Store
open Aeneas Aeneas.Std

def TableTypeMap {M : Type} (store : runtime.store.Store M)
    (types : List Itasca.types.TableType) (addresses : List runtime.TableAddr) : Prop :=
  List.Forall₂ (fun ty address => ∃ table, store.tables.val[address.index.val]? = some table ∧ table.ty = ty.elem) types addresses

theorem TableTypeMap.prefix {M : Type} {store after : runtime.store.Store M} {types addresses}
    (matching : TableTypeMap store types addresses) (retained : after.tables.val.take store.tables.length = store.tables.val) :
    TableTypeMap after types addresses := by
  apply matching.imp
  rintro ty address ⟨table, found, equal⟩
  refine ⟨table, ?_, equal⟩
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have lookup := congrArg (fun values : List runtime.store.TableInst => values[address.index.val]?) retained
  simp only [List.getElem?_take, alloc.vec.Vec.length, if_pos bound] at lookup
  exact lookup.trans found

theorem LinkedMaps.table_types {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {module entries inst} (linked : LinkedMaps view store module entries inst) :
    TableTypeMap store (Itasca.ModuleEnv.importedTables entries) inst.tables.val := by
  apply linked.tables.imp
  rintro ty address ⟨owner, table, found, typeEq, limits⟩
  exact ⟨table, found, typeEq⟩

theorem TableStageEffect.table_types {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty out} (effect : TableStageEffect store inst ty out)
    {types : List Itasca.types.TableType} (matching : TableTypeMap store types inst.tables.val)
    (success : out.1 = .Ok ()) : TableTypeMap out.2.1 (types ++ [ty]) out.2.2.tables.val := by
  rcases effect with ⟨error, rfl⟩ | ⟨tables, elements, addresses, count, zeros, appended, mapped, limits, capacity, counter, budget, rfl⟩
  · simp at success
  · have old := matching.prefix (after := {store with tables, table_elements := count}) (by simp [appended])
    change List.Forall₂ _ _ addresses.val
    rw [mapped]
    apply List.rel_append old
    exact .cons ⟨{elements, ty := ty.elem, maximum := ty.limits.max}, by simp [appended], rfl⟩ .nil

theorem TableTypeMap.bindings {M : Type} {store : runtime.store.Store M} {inst : runtime.store.ModuleInst}
    (matching : TableTypeMap store inst.module.module.env.table_types.val inst.tables.val) :
    ∀ (index : Nat) (source : Itasca.types.TableType) (address : runtime.TableAddr) (table : runtime.store.TableInst),
      inst.module.module.env.table_types.val[index]? = some source → inst.tables.val[index]? = some address →
      store.tables.val[address.index.val]? = some table → table.ty = source.elem := by
  intro index source address table sourceFound mapped found
  have left := (List.getElem?_eq_some_iff.mp sourceFound).1
  have right := (List.getElem?_eq_some_iff.mp mapped).1
  have related := matching.get left right
  simp only [List.get_eq_getElem] at related
  have sourceEq := (List.getElem?_eq_some_iff.mp sourceFound).2
  have addressEq := (List.getElem?_eq_some_iff.mp mapped).2
  rw [sourceEq, addressEq] at related
  obtain ⟨actual, actualFound, typed⟩ := related
  have same : actual = table := Option.some.inj (actualFound.symm.trans found)
  simpa only [same] using typed

end Exec.Store
