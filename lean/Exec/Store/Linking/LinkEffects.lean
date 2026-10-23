import Exec.Store.Linking.Link

namespace Exec.Store
open Aeneas Aeneas.Std

/-- A private external handle is either foreign or names an issued object.
Foreign handles remain admitted here because the API reports WrongStore. -/
def ExternalIssued {M : Type} (store : runtime.store.Store M) : runtime.Extern → Prop
  | .Func address => address.store = store.id → address.index.val < store.funcs.length
  | .Table address => address.store = store.id → address.index.val < store.tables.length
  | .Memory address => address.store = store.id → address.index.val < store.memories.length
  | .Global address => address.store = store.id → address.index.val < store.globals.length

/-- Exact structural effect of one successful import. Signature and global
agreement are retained for the initializer and ordinary call invariants. -/
inductive LinkedStep {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (before : runtime.store.ModuleInst) : Itasca.module.ImportDesc → runtime.Extern → runtime.store.ModuleInst → Prop where
  | func (index : U32) (address : runtime.FuncAddr) (addresses : alloc.vec.Vec runtime.FuncAddr)
      (mapped : addresses.val = before.funcs.val ++ [address])
      (owner : address.store = store.id) (issued : address.index.val < store.funcs.length)
      (signature : (store.funcs.val[address.index.val]).signature.val < store.types.length)
      (source : index.val < before.module.module.env.types.length)
      (typeEq : store.types.val[(store.funcs.val[address.index.val]).signature.val] =
        before.module.module.env.types.val[index.val]) :
      LinkedStep view store before (.Func index) (.Func address) {before with funcs := addresses}
  | table (required : Itasca.types.TableType) (address : runtime.TableAddr)
      (addresses : alloc.vec.Vec runtime.TableAddr)
      (mapped : addresses.val = before.tables.val ++ [address])
      (owner : address.store = store.id) (issued : address.index.val < store.tables.length)
      (element : (store.tables.val[address.index.val]).ty = required.elem)
      (limits : LimitsMatch (store.tables.val[address.index.val]).elements.length
        (store.tables.val[address.index.val]).maximum required.limits) :
      LinkedStep view store before (.Table required) (.Table address) {before with tables := addresses}
  | memory (required : Itasca.types.MemType) (address : runtime.MemoryAddr)
      (addresses : alloc.vec.Vec runtime.MemoryAddr)
      (mapped : addresses.val = before.memories.val ++ [address])
      (owner : address.store = store.id) (issued : address.index.val < store.memories.length)
      (limits : LimitsMatch ((view (store.memories.val[address.index.val]).buf).length / 65536)
        (store.memories.val[address.index.val]).maximum required.limits) :
      LinkedStep view store before (.Memory required) (.Memory address) {before with memories := addresses}
  | global (required : Itasca.types.GlobalType) (address : runtime.GlobalAddr)
      (addresses : alloc.vec.Vec runtime.GlobalAddr)
      (mapped : addresses.val = before.globals.val ++ [address])
      (owner : address.store = store.id) (issued : address.index.val < store.globals.length)
      (typeEq : (store.globals.val[address.index.val]).ty = required) :
      LinkedStep view store before (.Global required) (.Global address) {before with globals := addresses}

private theorem instance_ext (a b : runtime.store.ModuleInst)
    (module : a.module = b.module) (types : a.types = b.types)
    (funcs : a.funcs = b.funcs) (tables : a.tables = b.tables)
    (memories : a.memories = b.memories) (globals : a.globals = b.globals)
    (elements : a.elems = b.elems) (data : a.datas = b.datas) : a = b := by
  cases a; cases b; simp_all

/-- Every admitted API import is checked without changing the store. A successful
result exposes only issued addresses and the actual checked type agreements. -/
theorem link_import_effect {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (shape : Shape view store)
    (inst : runtime.store.ModuleInst) (index : Usize) (external : runtime.Extern)
    (bound : index.val < inst.module.module.env.imports.length)
    (typeBound : ∀ idx, inst.module.module.env.imports.val[index.val].desc = .Func idx →
      idx.val < inst.module.module.env.types.length)
    (issued : ExternalIssued store external)
    (mapRoom : match inst.module.module.env.imports.val[index.val].desc with
      | .Func _ => inst.funcs.length < Usize.max
      | .Table _ => inst.tables.length < Usize.max
      | .Memory _ => inst.memories.length < Usize.max
      | .Global _ => inst.globals.length < Usize.max) :
    runtime.store.instantiate.Store.link_import memory store inst index external ⦃ out =>
      out.2.1 = store ∧
      ((∃ error, out.1 = .Err error ∧ out.2.2 = inst) ∨
      (out.1 = .Ok () ∧ LinkedStep view store inst inst.module.module.env.imports.val[index.val].desc
        external out.2.2)) ⦄ := by
  by_cases foreign : ForeignExtern store external
  · apply WP.spec_mono (link_foreign memory store inst index external bound foreign)
    rintro out ⟨error, status, unchanged, same⟩
    exact ⟨unchanged, Or.inl ⟨error, status, same⟩⟩
  by_cases kind : ImportKindMatches inst.module.module.env.imports.val[index.val].desc external
  · cases desc : inst.module.module.env.imports.val[index.val].desc <;> cases external <;>
      simp only [desc, ImportKindMatches] at kind
    all_goals try contradiction
    case Func.Func required address =>
      have owner : address.store = store.id := by simpa only [ForeignExtern, not_not] using foreign
      have addressBound := issued owner
      apply WP.spec_mono (link_function memory view store shape inst index required address bound desc
        (typeBound required desc) owner addressBound (by simpa only [desc] using mapRoom))
      rintro ⟨status, after, result⟩ ⟨unchanged, failure | success⟩
      · exact ⟨unchanged, Or.inl ⟨_, failure⟩⟩
      · rcases success with ⟨ok, mapped, tables, memories, globals, module, types, elements, data, checked⟩
        refine ⟨unchanged, Or.inr ⟨ok, ?_⟩⟩
        have same : result = {inst with funcs := result.funcs} :=
          instance_ext _ _ module types rfl tables memories globals elements data
        rw [same]
        exact .func required address result.funcs mapped owner addressBound
          ((shape.functions _ (List.getElem_mem addressBound)).1) (typeBound required desc) checked
    case Table.Table required address =>
      have owner : address.store = store.id := by simpa only [ForeignExtern, not_not] using foreign
      have addressBound := issued owner
      apply WP.spec_mono (link_table memory store inst index required address bound desc owner addressBound (by simpa only [desc] using mapRoom))
      rintro ⟨status, after, result⟩ ⟨unchanged, failure | success⟩
      · exact ⟨unchanged, Or.inl ⟨_, failure⟩⟩
      · rcases success with ⟨ok, mapped, funcs, memories, globals, module, types, elements, data, checked, limits⟩
        refine ⟨unchanged, Or.inr ⟨ok, ?_⟩⟩
        have same : result = {inst with tables := result.tables} :=
          instance_ext _ _ module types funcs rfl memories globals elements data
        rw [same]
        exact .table required address result.tables mapped owner addressBound checked limits
    case Memory.Memory required address =>
      have owner : address.store = store.id := by simpa only [ForeignExtern, not_not] using foreign
      have addressBound := issued owner
      apply WP.spec_mono (link_memory memory view laws store inst index required address bound desc owner addressBound (by simpa only [desc] using mapRoom))
      rintro ⟨status, after, result⟩ ⟨unchanged, failure | success⟩
      · exact ⟨unchanged, Or.inl ⟨_, failure⟩⟩
      · rcases success with ⟨ok, mapped, funcs, tables, globals, module, types, elements, data, limits⟩
        refine ⟨unchanged, Or.inr ⟨ok, ?_⟩⟩
        have same : result = {inst with memories := result.memories} :=
          instance_ext _ _ module types funcs tables rfl globals elements data
        rw [same]
        exact .memory required address result.memories mapped owner addressBound limits
    case Global.Global required address =>
      have owner : address.store = store.id := by simpa only [ForeignExtern, not_not] using foreign
      have addressBound := issued owner
      apply WP.spec_mono (link_global memory store inst index required address bound desc owner addressBound (by simpa only [desc] using mapRoom))
      rintro ⟨status, after, result⟩ ⟨unchanged, failure | success⟩
      · exact ⟨unchanged, Or.inl ⟨_, failure⟩⟩
      · rcases success with ⟨ok, mapped, funcs, tables, memories, module, types, elements, data, checked⟩
        refine ⟨unchanged, Or.inr ⟨ok, ?_⟩⟩
        have same : result = {inst with globals := result.globals} :=
          instance_ext _ _ module types funcs tables memories rfl elements data
        rw [same]
        exact .global required address result.globals mapped owner addressBound checked
  · apply WP.spec_mono (link_wrong_kind memory store inst index external bound kind)
    rintro out ⟨status, unchanged, same⟩
    exact ⟨unchanged, Or.inl ⟨_, status, same⟩⟩

end Exec.Store
