import Exec.Store.Invariant.TypeEquality
import Exec.Platform.Memory
import Exec.Representation.StoreInvariant
import Exec.Store.Api.Write

namespace Exec.Store
open Aeneas Aeneas.Std

def LimitsMatch (size : Nat) (maximum : Option U32) (required : Itasca.types.Limits) : Prop :=
  required.min.val ≤ size ∧ ∀ bound, required.max = some bound →
    ∃ actual, maximum = some actual ∧ actual.val ≤ bound.val

@[step] theorem matches_limits_spec (size : U64) (maximum : Option U32)
    (required : Itasca.types.Limits) :
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
    (inst : runtime.store.Instance) (i : Usize) (typeIndex : U32) (address : runtime.FuncAddr)
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
       result.types = inst.types ∧ result.elements = inst.elements ∧ result.data = inst.data ∧
       s.types.val[(s.funcs.val[address.index.val]).signature.val]'((hs.functions _ (by simp)).1) =
         inst.module.module.env.types.val[typeIndex.val]) ⦄ := by
  unfold runtime.store.instantiate.Store.link_import
  simp only [runtime.compiler.ExecutableModule.env, module.Module.env,
    Itasca.module.Module.impl.env, module.Env.imports, Itasca.module.Env.impl.imports, bind_ok]
  have hb : i.val < inst.module.module.env.imports.deref.length := by simpa [alloc.vec.Vec.deref] using hi
  step as ⟨entry, hentry⟩
  have hd : entry.desc = .Func typeIndex := by simpa [hentry, alloc.vec.Vec.deref] using hdesc
  rw [hd]
  simp [runtime.store.Store.check, haddr, core.result.Result.Insts.CoreOpsTry.branch]
  step as ⟨function, hfunction⟩
  have hsignature := (hs.functions function (by simp [hfunction])).1
  step as ⟨actual, hactual⟩
  simp only [module.Env.types, Itasca.module.Env.impl.types, bind_ok]
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
    (s : runtime.store.Store M) (inst : runtime.store.Instance) (i : Usize)
    (required : Itasca.types.MemType) (address : runtime.MemoryAddr)
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
       result.types = inst.types ∧ result.elements = inst.elements ∧ result.data = inst.data ∧
       LimitsMatch ((view (s.memories.val[address.index.val]).buf).length / 65536)
         (s.memories.val[address.index.val]).maximum required.limits) ⦄ := by
  unfold runtime.store.instantiate.Store.link_import
  simp only [runtime.compiler.ExecutableModule.env, module.Module.env,
    Itasca.module.Module.impl.env, module.Env.imports, Itasca.module.Env.impl.imports, bind_ok]
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

@[step] theorem value_type_ne (a b : Itasca.types.ValueType) :
    core.cmp.PartialEq.ne.trait_default types.ValueType.Insts.CoreCmpPartialEqValueType a b
      ⦃ different => different = true ↔ a ≠ b ⦄ := by
  unfold core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default
  step with value_type_equal a b as ⟨equal, hequal⟩
  cases equal <;> simp_all

@[step] theorem mut_ne (a b : Itasca.types.Mut) :
    core.cmp.PartialEq.ne.trait_default types.Mut.Insts.CoreCmpPartialEqMut a b
      ⦃ different => different = true ↔ a ≠ b ⦄ := by
  cases a <;> cases b <;>
    simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      types.Mut.Insts.CoreCmpPartialEqMut.eq, Itasca.types.Mut.Insts.CoreCmpPartialEqMut.eq]

theorem elementValueType_injective : Function.Injective elementValueType := by
  intro a b h
  cases a <;> cases b <;> simp_all [elementValueType]

/-- Table linking compares both the element type and current size/maximum. -/
theorem link_table {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (inst : runtime.store.Instance) (i : Usize)
    (required : Itasca.types.TableType) (address : runtime.TableAddr)
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
       result.types = inst.types ∧ result.elements = inst.elements ∧ result.data = inst.data ∧
       (s.tables.val[address.index.val]).ty = required.elem ∧
       LimitsMatch (s.tables.val[address.index.val]).elements.length
         (s.tables.val[address.index.val]).maximum required.limits) ⦄ := by
  unfold runtime.store.instantiate.Store.link_import
  simp only [runtime.compiler.ExecutableModule.env, module.Module.env,
    Itasca.module.Module.impl.env, module.Env.imports, Itasca.module.Env.impl.imports, bind_ok]
  have hb : i.val < inst.module.module.env.imports.deref.length := by simpa [alloc.vec.Vec.deref] using hi
  step as ⟨entry, hentry⟩
  have hd : entry.desc = .Table required := by simpa [hentry, alloc.vec.Vec.deref] using hdesc
  rw [hd]
  simp [runtime.store.Store.check, haddr, core.result.Result.Insts.CoreOpsTry.branch]
  step as ⟨table, htable⟩
  step with value_type_ne (elementValueType required.elem) (elementValueType table.ty) as ⟨different, hdifferent⟩
  cases different
  · have htype : table.ty = required.elem := by
      apply elementValueType_injective
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
    (s : runtime.store.Store M) (inst : runtime.store.Instance) (i : Usize)
    (required : Itasca.types.GlobalType) (address : runtime.GlobalAddr)
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
       result.types = inst.types ∧ result.elements = inst.elements ∧ result.data = inst.data ∧
       (s.globals.val[address.index.val]).ty = required) ⦄ := by
  unfold runtime.store.instantiate.Store.link_import
  simp only [runtime.compiler.ExecutableModule.env, module.Module.env,
    Itasca.module.Module.impl.env, module.Env.imports, Itasca.module.Env.impl.imports, bind_ok]
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
def ImportKindMatches : Itasca.module.ImportDesc → runtime.Extern → Prop
  | .Func _, .Func _ | .Table _, .Table _ | .Memory _, .Memory _ | .Global _, .Global _ => True
  | _, _ => False

theorem link_wrong_kind {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (inst : runtime.store.Instance) (i : Usize)
    (external : runtime.Extern) (hi : i.val < inst.module.module.env.imports.length)
    (hkind : ¬ ImportKindMatches inst.module.module.env.imports.val[i.val].desc external) :
    runtime.store.instantiate.Store.link_import ops s inst i external ⦃ answer after result =>
      answer = .Err (.Link .IncompatibleImportType) ∧ after = s ∧ result = inst ⦄ := by
  unfold runtime.store.instantiate.Store.link_import
  simp only [runtime.compiler.ExecutableModule.env, module.Module.env,
    Itasca.module.Module.impl.env, module.Env.imports, Itasca.module.Env.impl.imports, bind_ok]
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
    (s : runtime.store.Store M) (inst : runtime.store.Instance) (i : Usize)
    (external : runtime.Extern) (hi : i.val < inst.module.module.env.imports.length)
    (hforeign : ForeignExtern s external) :
    runtime.store.instantiate.Store.link_import ops s inst i external ⦃ answer after result =>
      ∃ error, answer = .Err error ∧ after = s ∧ result = inst ⦄ := by
  unfold runtime.store.instantiate.Store.link_import
  simp only [runtime.compiler.ExecutableModule.env, module.Module.env,
    Itasca.module.Module.impl.env, module.Env.imports, Itasca.module.Env.impl.imports, bind_ok]
  have hb : i.val < inst.module.module.env.imports.deref.length := by simpa [alloc.vec.Vec.deref] using hi
  step as ⟨entry, hentry⟩
  cases entry.desc <;> cases external <;>
    simp_all [ForeignExtern, runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Exec.Store
