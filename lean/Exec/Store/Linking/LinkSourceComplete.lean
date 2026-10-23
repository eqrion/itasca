import Exec.Store.Linking.LinkComplete
import Exec.Store.Linking.LinkTypingComplete
import Exec.Store.Linking.ExternalMaps
namespace Exec.Store
open Aeneas Aeneas.Std Itasca

/-- A same-store issued import accepted by generated external typing passes
all actual link checks. The module's declared external type is resolved from
its canonical environment, independently of the runtime comparison. -/
theorem link_import_source_complete {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (code : CodeInterpretation) (store : runtime.store.Store M) (shape : Shape view store)
    (inst : runtime.store.ModuleInst) (index : Usize) (external : runtime.Extern)
    (bound : index.val < inst.module.module.env.imports.length)
    (required : types.ExternType)
    (resolved : ModuleExternals.ImportResolves inst.module.module.env
      inst.module.module.env.imports.val[index.val] required)
    (issued : ExternalIssued store external) (owned : ¬ ForeignExtern store external)
    (typed : Externaddr_ok (decodeStore view code store) (decodeExternal external)
      (ModuleExternals.externalType required))
    (room : match inst.module.module.env.imports.val[index.val].desc with
      | .Func _ => inst.funcs.length < Usize.max
      | .Table _ => inst.tables.length < Usize.max
      | .Memory _ => inst.memories.length < Usize.max
      | .Global _ => inst.globals.length < Usize.max) :
    runtime.store.instantiate.Store.link_import memory store inst index external
      ⦃ answer after _result => after = store ∧ answer = .Ok () ⦄ := by
  have compatible := Spec.externaddr_compatible typed
  cases desc : inst.module.module.env.imports.val[index.val].desc with
  | Func typeIndex =>
    simp only [ModuleExternals.ImportResolves, desc] at resolved
    obtain ⟨typeBound, rfl⟩ := resolved
    cases external with
    | Func address =>
      have owner : address.store = store.id := by simpa only [ForeignExtern, not_not] using owned
      have addressBound := issued owner
      let function := store.funcs.val[address.index.val]
      have functionFound : store.funcs.val[address.index.val]? = some function := List.getElem?_eq_getElem addressBound
      have signatureBound := (shape.functions function (List.mem_of_getElem? functionFound)).1
      have same := source_function_import_signature view code store address function
        store.types.val[function.signature.val] inst.module.module.env.types.val[typeIndex.val]
        functionFound (List.getElem?_eq_getElem signatureBound) typed
      exact link_function_complete memory view store shape inst index typeIndex address bound desc typeBound
        owner addressBound (by simpa [desc] using room) same
    | Table address | Memory address | Global address =>
      simp [decodeExternal, ModuleExternals.externalType, Spec.externalActualType, Spec.ExternalCompatible] at compatible
  | Global requiredGlobal =>
    simp only [ModuleExternals.ImportResolves, desc] at resolved
    subst required
    cases external with
    | Global address =>
      have owner : address.store = store.id := by simpa only [ForeignExtern, not_not] using owned
      have addressBound := issued owner
      have same := source_global_import_type view code store address store.globals.val[address.index.val]
        requiredGlobal (List.getElem?_eq_getElem addressBound) typed
      exact link_global_complete memory store inst index requiredGlobal address bound desc owner addressBound
        (by simpa [desc] using room) same
    | Func address | Table address | Memory address =>
      simp [decodeExternal, ModuleExternals.externalType, Spec.externalActualType, Spec.ExternalCompatible] at compatible
  | Memory requiredMemory =>
    simp only [ModuleExternals.ImportResolves, desc] at resolved
    subst required
    cases external with
    | Memory address =>
      have owner : address.store = store.id := by simpa only [ForeignExtern, not_not] using owned
      have addressBound := issued owner
      have compatibleType :=  source_memory_import_limits view code store address store.memories.val[address.index.val]
        requiredMemory (List.getElem?_eq_getElem addressBound) typed
      exact link_memory_complete memory view laws store inst index requiredMemory address bound desc owner addressBound
        (by simpa [desc] using room) compatibleType
    | Func address | Table address | Global address =>
      simp [decodeExternal, ModuleExternals.externalType, Spec.externalActualType, Spec.ExternalCompatible] at compatible
  | Table requiredTable =>
    simp only [ModuleExternals.ImportResolves, desc] at resolved
    subst required
    cases external with
    | Table address =>
      have owner : address.store = store.id := by simpa only [ForeignExtern, not_not] using owned
      have addressBound := issued owner
      have compatibleType :=  source_table_import_type view code store address store.tables.val[address.index.val]
        requiredTable (List.getElem?_eq_getElem addressBound) typed
      exact link_table_complete memory store inst index requiredTable address bound desc owner addressBound
        (by simpa [desc] using room) compatibleType.1 compatibleType.2
    | Func address | Memory address | Global address =>
      simp [decodeExternal, ModuleExternals.externalType, Spec.externalActualType, Spec.ExternalCompatible] at compatible

/-- Source external typing also excludes mismatched import namespaces. -/
theorem source_import_kind {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (env : Itasca.module.Env) (entry : Itasca.module.Import)
    (required : types.ExternType) (external : runtime.Extern)
    (resolved : ModuleExternals.ImportResolves env entry required)
    (typed : Externaddr_ok (decodeStore view code store) (decodeExternal external)
      (ModuleExternals.externalType required)) : ImportKindMatches entry.desc external := by
  have compatible := Spec.externaddr_compatible typed
  cases desc : entry.desc with
  | Func index =>
    simp only [ModuleExternals.ImportResolves, desc] at resolved
    obtain ⟨bound, rfl⟩ := resolved
    cases external <;> simp_all [ImportKindMatches, decodeExternal, ModuleExternals.externalType,
      Spec.externalActualType, Spec.ExternalCompatible]
  | Table ty | Memory ty | Global ty =>
    simp only [ModuleExternals.ImportResolves, desc] at resolved
    subst required
    cases external <;> simp_all [ImportKindMatches, decodeExternal, ModuleExternals.externalType,
      Spec.externalActualType, Spec.ExternalCompatible]

/-- A foreign handle of the right namespace reports ownership failure, rather
than incompatible-import typing. -/
theorem link_foreign_matching {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (external : runtime.Extern) (bound : index.val < inst.module.module.env.imports.length)
    (foreign : ForeignExtern store external)
    (kind : ImportKindMatches inst.module.module.env.imports.val[index.val].desc external) :
    runtime.store.instantiate.Store.link_import ops store inst index external ⦃ answer after result =>
      answer = .Err .WrongStore ∧ after = store ∧ result = inst ⦄ := by
  unfold runtime.store.instantiate.Store.link_import
  simp only [runtime.compiler.ExecutableModule.env, module.Module.env,
    Itasca.module.Module.impl.env, module.Env.imports, Itasca.module.Env.impl.imports, bind_ok]
  have accessBound : index.val < inst.module.module.env.imports.deref.length := by
    simpa [alloc.vec.Vec.deref] using bound
  step as ⟨entry, found⟩
  have compatible : ImportKindMatches entry.desc external := by
    simpa [found, alloc.vec.Vec.deref] using kind
  cases desc : entry.desc <;> cases external <;>
    simp_all [ImportKindMatches, ForeignExtern, runtime.store.Store.check,
      core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Well-typed imports cannot produce a Link rejection. Foreign handles retain
the existing WrongStore outcome without adding an ownership premise. -/
theorem link_import_source_typed {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (code : CodeInterpretation) (store : runtime.store.Store M) (shape : Shape view store)
    (inst : runtime.store.ModuleInst) (index : Usize) (external : runtime.Extern)
    (bound : index.val < inst.module.module.env.imports.length)
    (required : types.ExternType)
    (resolved : ModuleExternals.ImportResolves inst.module.module.env
      inst.module.module.env.imports.val[index.val] required)
    (issued : ExternalIssued store external)
    (typed : Externaddr_ok (decodeStore view code store) (decodeExternal external)
      (ModuleExternals.externalType required))
    (room : match inst.module.module.env.imports.val[index.val].desc with
      | .Func _ => inst.funcs.length < Usize.max
      | .Table _ => inst.tables.length < Usize.max
      | .Memory _ => inst.memories.length < Usize.max
      | .Global _ => inst.globals.length < Usize.max) :
    runtime.store.instantiate.Store.link_import memory store inst index external
      ⦃ answer after _result => after = store ∧ (answer = .Ok () ∨ answer = .Err .WrongStore) ⦄ := by
  by_cases foreign : ForeignExtern store external
  · have kind := source_import_kind view code store inst.module.module.env
      inst.module.module.env.imports.val[index.val] required external resolved typed
    apply WP.spec_mono (link_foreign_matching memory store inst index external bound foreign kind)
    rintro ⟨answer, after, result⟩ ⟨status, unchanged, identity⟩
    exact ⟨unchanged, Or.inr status⟩
  · apply WP.spec_mono (link_import_source_complete memory view laws code store shape inst index external
      bound required resolved issued foreign typed room)
    rintro ⟨answer, after, result⟩ ⟨unchanged, status⟩
    exact ⟨unchanged, Or.inl status⟩
end Exec.Store
