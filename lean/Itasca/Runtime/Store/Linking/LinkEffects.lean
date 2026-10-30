import Itasca.Runtime.Store.Invariant.TypeEquality
import Itasca.Runtime.Platform.Memory
import Itasca.Runtime.Representation.StoreInvariant
import Itasca.Runtime.Store.Api.Write

/-!
Import linking and its issued-object effect. Per-kind signature/type/limit checks and wrong-kind or foreign-store rejection establish the complete linked-step result.
-/

/-! ## Link -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def LimitsMatch (size : Nat) (maximum : Option U32) (required : Itasca.wasm_types.Limits) : Prop :=
  required.min.val ≤ size ∧ ∀ bound, required.max = some bound →
    ∃ actual, maximum = some actual ∧ actual.val ≤ bound.val

@[step] theorem matches_limits_spec (size : U64) (maximum : Option U32)
    (required : Itasca.wasm_types.Limits) :
    runtime.store.matches_limits size maximum required ⦃ answer =>
      answer = true ↔ LimitsMatch size.val maximum required ⦄ := by
  unfold runtime.store.matches_limits
  step as ⟨minimum, hminimum⟩
  split
  · rename_i hsize
    cases hr : required.max with
    | none => simp [LimitsMatch, hr]; scalar_tac
    | some bound =>
      cases hm : maximum with
      | none => simp [LimitsMatch, hr, hm]
      | some actual =>
        simp [LimitsMatch, hr, hm]
        scalar_tac
  · rename_i hsize
    simp [LimitsMatch]
    scalar_tac

/-- Linking a function uses the actual canonical signature comparison and adds
only the selected issued address to the local instance map. -/
theorem link_function {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (s : runtime.store.Store M) (hs : Shape view s)
    (inst : runtime.store.ModuleInst) (i : Usize) (typeIndex : U32) (address : runtime.FuncAddr)
    (hi : i.val < inst.module.module.env.imports.length)
    (hdesc : inst.module.module.env.imports.val[i.val].desc = .Func typeIndex)
    (htype : typeIndex.val < inst.module.module.env.types.length)
    (haddr : address.store = s.id) (hindex : address.index.val < s.funcs.length)
    (hroom : inst.funcs.length < Usize.max) :
    runtime.store.instantiate.Store.link_import ops s inst i (.Func address) ⦃ answer after result =>
      after = s ∧
      (answer = .Err (.Link .IncompatibleImportType) ∧ result = inst ∨
       answer = .Ok () ∧ result.funcs.val = inst.funcs.val ++ [address] ∧
       result.tables = inst.tables ∧ result.memories = inst.memories ∧
       result.globals = inst.globals ∧ result.module = inst.module ∧
       result.types = inst.types ∧ result.elems = inst.elems ∧ result.datas = inst.datas ∧
       s.types.val[(s.funcs.val[address.index.val]).signature.val]'((hs.functions _ (by simp)).1) =
         inst.module.module.env.types.val[typeIndex.val]) ⦄ := by
  unfold runtime.store.instantiate.Store.link_import
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.imports, bind_ok]
  have hb : i.val < inst.module.module.env.imports.deref.length := by simpa [alloc.vec.Vec.deref] using hi
  step as ⟨entry, hentry⟩
  have hd : entry.desc = .Func typeIndex := by simpa [hentry, alloc.vec.Vec.deref] using hdesc
  rw [hd]
  simp [runtime.store.Store.check, haddr, core.result.Result.Insts.CoreOpsTry.branch]
  step as ⟨function, hfunction⟩
  have hsignature := (hs.functions function (by simp [hfunction])).1
  step as ⟨actual, hactual⟩
  simp only [Itasca.metadata.Env.impl.types, bind_ok]
  step as ⟨index, hcast⟩
  have hind : index.val < inst.module.module.env.types.deref.length := by
    simp [alloc.vec.Vec.deref]
    scalar_tac
  step as ⟨required, hrequired⟩
  step with same_func_type_spec actual required as ⟨same, hsame⟩
  cases same
  · simp
  · have heq : actual = required := hsame.mp rfl
    simp
    step as ⟨functions, hfunctions⟩
    refine Or.inr ⟨hfunctions, ?_⟩
    simpa [hactual, hrequired, hfunction, hcast, alloc.vec.Vec.deref] using heq

/-- Memory imports inspect the current buffer size and declared maximum before
adding the address; neither successful linking nor rejection changes the store. -/
theorem link_memory {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view)
    (s : runtime.store.Store M) (inst : runtime.store.ModuleInst) (i : Usize)
    (required : Itasca.wasm_types.MemType) (address : runtime.MemoryAddr)
    (hi : i.val < inst.module.module.env.imports.length)
    (hdesc : inst.module.module.env.imports.val[i.val].desc = .Memory required)
    (haddr : address.store = s.id) (hindex : address.index.val < s.memories.length)
    (hroom : inst.memories.length < Usize.max) :
    runtime.store.instantiate.Store.link_import ops s inst i (.Memory address) ⦃ answer after result =>
      after = s ∧
      (answer = .Err (.Link .IncompatibleImportType) ∧ result = inst ∨
       answer = .Ok () ∧ result.memories.val = inst.memories.val ++ [address] ∧
       result.funcs = inst.funcs ∧ result.tables = inst.tables ∧
       result.globals = inst.globals ∧ result.module = inst.module ∧
       result.types = inst.types ∧ result.elems = inst.elems ∧ result.datas = inst.datas ∧
       LimitsMatch ((view (s.memories.val[address.index.val]).buf).length / 65536)
         (s.memories.val[address.index.val]).maximum required.limits) ⦄ := by
  unfold runtime.store.instantiate.Store.link_import
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.imports, bind_ok]
  have hb : i.val < inst.module.module.env.imports.deref.length := by simpa [alloc.vec.Vec.deref] using hi
  step as ⟨entry, hentry⟩
  have hd : entry.desc = .Memory required := by simpa [hentry, alloc.vec.Vec.deref] using hdesc
  rw [hd]
  simp [runtime.store.Store.check, haddr, core.result.Result.Insts.CoreOpsTry.branch]
  step as ⟨memory, hmemory⟩
  rw [laws.read]
  simp only [bind_ok]
  step as ⟨pages, hpages⟩
  step as ⟨size, hsize⟩
  step with matches_limits_spec size memory.maximum required.limits as ⟨matched, hmatches⟩
  cases matched
  · simp
  · have hmatch := hmatches.mp rfl
    simp
    step as ⟨memories, hmemories⟩
    refine Or.inr ⟨hmemories, ?_⟩
    simpa [hsize, hpages, hmemory] using hmatch

@[step] theorem value_type_ne (a b : Itasca.wasm_types.ValueType) :
    core.cmp.PartialEq.ne.trait_default wasm_types.ValueType.Insts.CoreCmpPartialEqValueType a b
      ⦃ different => different = true ↔ a ≠ b ⦄ := by
  unfold core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default
  step with value_type_equal a b as ⟨equal, hequal⟩
  cases equal <;> simp_all

@[step] theorem mut_ne (a b : Itasca.wasm_types.Mut) :
    core.cmp.PartialEq.ne.trait_default wasm_types.Mut.Insts.CoreCmpPartialEqMut a b
      ⦃ different => different = true ↔ a ≠ b ⦄ := by
  cases a <;> cases b <;>
    simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, Itasca.wasm_types.Mut.Insts.CoreCmpPartialEqMut.eq]

theorem element_value_type_injective : Function.Injective elementValueType := by
  intro a b h
  cases a <;> cases b <;> simp_all [elementValueType]

/-- Table linking compares both the element type and current size/maximum. -/
theorem link_table {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (inst : runtime.store.ModuleInst) (i : Usize)
    (required : Itasca.wasm_types.TableType) (address : runtime.TableAddr)
    (hi : i.val < inst.module.module.env.imports.length)
    (hdesc : inst.module.module.env.imports.val[i.val].desc = .Table required)
    (haddr : address.store = s.id) (hindex : address.index.val < s.tables.length)
    (hroom : inst.tables.length < Usize.max) :
    runtime.store.instantiate.Store.link_import ops s inst i (.Table address) ⦃ answer after result =>
      after = s ∧
      (answer = .Err (.Link .IncompatibleImportType) ∧ result = inst ∨
       answer = .Ok () ∧ result.tables.val = inst.tables.val ++ [address] ∧
       result.funcs = inst.funcs ∧ result.memories = inst.memories ∧
       result.globals = inst.globals ∧ result.module = inst.module ∧
       result.types = inst.types ∧ result.elems = inst.elems ∧ result.datas = inst.datas ∧
       (s.tables.val[address.index.val]).ty = required.elem ∧
       LimitsMatch (s.tables.val[address.index.val]).elements.length
         (s.tables.val[address.index.val]).maximum required.limits) ⦄ := by
  unfold runtime.store.instantiate.Store.link_import
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.imports, bind_ok]
  have hb : i.val < inst.module.module.env.imports.deref.length := by simpa [alloc.vec.Vec.deref] using hi
  step as ⟨entry, hentry⟩
  have hd : entry.desc = .Table required := by simpa [hentry, alloc.vec.Vec.deref] using hdesc
  rw [hd]
  simp [runtime.store.Store.check, haddr, core.result.Result.Insts.CoreOpsTry.branch]
  step as ⟨table, htable⟩
  step with value_type_ne (elementValueType required.elem) (elementValueType table.ty) as ⟨different, hdifferent⟩
  cases different
  · have htype : table.ty = required.elem := by
      apply element_value_type_injective
      have he : elementValueType required.elem = elementValueType table.ty := by simpa using hdifferent
      exact he.symm
    simp
    step as ⟨size, hsize⟩
    step with matches_limits_spec size table.maximum required.limits as ⟨matched, hmatched⟩
    cases matched
    · simp
    · have hmatch := hmatched.mp rfl
      simp
      step as ⟨tables, htables⟩
      refine Or.inr ⟨htables, ?_, ?_⟩
      · simpa [htable] using htype
      · simpa [hsize, htable] using hmatch
  · simp

/-- Imported globals must agree in both value type and mutability. -/
theorem link_global {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (inst : runtime.store.ModuleInst) (i : Usize)
    (required : Itasca.wasm_types.GlobalType) (address : runtime.GlobalAddr)
    (hi : i.val < inst.module.module.env.imports.length)
    (hdesc : inst.module.module.env.imports.val[i.val].desc = .Global required)
    (haddr : address.store = s.id) (hindex : address.index.val < s.globals.length)
    (hroom : inst.globals.length < Usize.max) :
    runtime.store.instantiate.Store.link_import ops s inst i (.Global address) ⦃ answer after result =>
      after = s ∧
      (answer = .Err (.Link .IncompatibleImportType) ∧ result = inst ∨
       answer = .Ok () ∧ result.globals.val = inst.globals.val ++ [address] ∧
       result.funcs = inst.funcs ∧ result.tables = inst.tables ∧
       result.memories = inst.memories ∧ result.module = inst.module ∧
       result.types = inst.types ∧ result.elems = inst.elems ∧ result.datas = inst.datas ∧
       (s.globals.val[address.index.val]).ty = required) ⦄ := by
  unfold runtime.store.instantiate.Store.link_import
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.imports, bind_ok]
  have hb : i.val < inst.module.module.env.imports.deref.length := by simpa [alloc.vec.Vec.deref] using hi
  step as ⟨entry, hentry⟩
  have hd : entry.desc = .Global required := by simpa [hentry, alloc.vec.Vec.deref] using hdesc
  rw [hd]
  simp [runtime.store.Store.check, haddr, core.result.Result.Insts.CoreOpsTry.branch]
  step as ⟨global, hglobal⟩
  step with value_type_ne global.ty.valtype required.valtype as ⟨different, hdifferent⟩
  cases different
  · have hval : global.ty.valtype = required.valtype := by simpa using hdifferent
    simp
    step with mut_ne global.ty.mutability required.mutability as ⟨differentMut, hmut⟩
    cases differentMut
    · have hmutability : global.ty.mutability = required.mutability := by simpa using hmut
      have htype : global.ty = required := by
        cases hgt : global.ty
        cases required
        simp_all
      simp
      step as ⟨globals, hglobals⟩
      refine Or.inr ⟨hglobals, ?_⟩
      simpa [hglobal] using htype
    · simp
  · simp

/-- The kind test is independent of store addresses and resource contents. -/
def ImportKindMatches : Itasca.metadata.ImportDesc → runtime.Extern → Prop
  | .Func _, .Func _ | .Table _, .Table _ | .Memory _, .Memory _ | .Global _, .Global _ => True
  | _, _ => False

theorem link_wrong_kind {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (inst : runtime.store.ModuleInst) (i : Usize)
    (external : runtime.Extern) (hi : i.val < inst.module.module.env.imports.length)
    (hkind : ¬ ImportKindMatches inst.module.module.env.imports.val[i.val].desc external) :
    runtime.store.instantiate.Store.link_import ops s inst i external ⦃ answer after result =>
      answer = .Err (.Link .IncompatibleImportType) ∧ after = s ∧ result = inst ⦄ := by
  unfold runtime.store.instantiate.Store.link_import
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.imports, bind_ok]
  have hb : i.val < inst.module.module.env.imports.deref.length := by simpa [alloc.vec.Vec.deref] using hi
  step as ⟨entry, hentry⟩
  have hk : ¬ ImportKindMatches entry.desc external := by simpa [hentry, alloc.vec.Vec.deref] using hkind
  cases hd : entry.desc <;> cases external <;> simp [hd, ImportKindMatches] at hk ⊢

def ForeignExtern {M : Type} (s : runtime.store.Store M) : runtime.Extern → Prop
  | .Func a => a.store ≠ s.id
  | .Table a => a.store ≠ s.id
  | .Memory a => a.store ≠ s.id
  | .Global a => a.store ≠ s.id

/-- Foreign handles are rejected before an object index is read. Wrong-kind
imports retain the ordinary incompatible-import error. -/
theorem link_foreign {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (inst : runtime.store.ModuleInst) (i : Usize)
    (external : runtime.Extern) (hi : i.val < inst.module.module.env.imports.length)
    (hforeign : ForeignExtern s external) :
    runtime.store.instantiate.Store.link_import ops s inst i external ⦃ answer after result =>
      ∃ error, answer = .Err error ∧ after = s ∧ result = inst ⦄ := by
  unfold runtime.store.instantiate.Store.link_import
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.imports, bind_ok]
  have hb : i.val < inst.module.module.env.imports.deref.length := by simpa [alloc.vec.Vec.deref] using hi
  step as ⟨entry, hentry⟩
  cases entry.desc <;> cases external <;>
    simp_all [ForeignExtern, runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca.Runtime.Store

end

/-! ## Link Effects -/

section

namespace Itasca.Runtime.Store
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
    (before : runtime.store.ModuleInst) : Itasca.metadata.ImportDesc → runtime.Extern → runtime.store.ModuleInst → Prop where
  | func (index : U32) (address : runtime.FuncAddr) (addresses : alloc.vec.Vec runtime.FuncAddr)
      (mapped : addresses.val = before.funcs.val ++ [address])
      (owner : address.store = store.id) (issued : address.index.val < store.funcs.length)
      (signature : (store.funcs.val[address.index.val]).signature.val < store.types.length)
      (source : index.val < before.module.module.env.types.length)
      (typeEq : store.types.val[(store.funcs.val[address.index.val]).signature.val] =
        before.module.module.env.types.val[index.val]) :
      LinkedStep view store before (.Func index) (.Func address) {before with funcs := addresses}
  | table (required : Itasca.wasm_types.TableType) (address : runtime.TableAddr)
      (addresses : alloc.vec.Vec runtime.TableAddr)
      (mapped : addresses.val = before.tables.val ++ [address])
      (owner : address.store = store.id) (issued : address.index.val < store.tables.length)
      (element : (store.tables.val[address.index.val]).ty = required.elem)
      (limits : LimitsMatch (store.tables.val[address.index.val]).elements.length
        (store.tables.val[address.index.val]).maximum required.limits) :
      LinkedStep view store before (.Table required) (.Table address) {before with tables := addresses}
  | memory (required : Itasca.wasm_types.MemType) (address : runtime.MemoryAddr)
      (addresses : alloc.vec.Vec runtime.MemoryAddr)
      (mapped : addresses.val = before.memories.val ++ [address])
      (owner : address.store = store.id) (issued : address.index.val < store.memories.length)
      (limits : LimitsMatch ((view (store.memories.val[address.index.val]).buf).length / 65536)
        (store.memories.val[address.index.val]).maximum required.limits) :
      LinkedStep view store before (.Memory required) (.Memory address) {before with memories := addresses}
  | global (required : Itasca.wasm_types.GlobalType) (address : runtime.GlobalAddr)
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

end Itasca.Runtime.Store

end
