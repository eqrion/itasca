import Exec.Store.Linking.Link
namespace Exec.Store
open Aeneas Aeneas.Std

theorem link_function_complete {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (s : runtime.store.Store M) (hs : Shape view s)
    (inst : runtime.store.Instance) (i : Usize) (typeIndex : U32) (address : runtime.FuncAddr)
    (hi : i.val < inst.module.module.env.imports.length)
    (hdesc : inst.module.module.env.imports.val[i.val].desc = .Func typeIndex)
    (htype : typeIndex.val < inst.module.module.env.types.length)
    (haddr : address.store = s.id) (hindex : address.index.val < s.funcs.length)
    (hroom : inst.funcs.length < Usize.max)
    (matching : s.types.val[(s.funcs.val[address.index.val]).signature.val]'((hs.functions _ (by simp)).1) = inst.module.module.env.types.val[typeIndex.val]) :
    runtime.store.instantiate.Store.link_import ops s inst i (.Func address) ⦃ answer after _result => after = s ∧ answer = .Ok () ⦄ := by
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
  have expectedSame : actual = required := by
    simpa [hactual, hrequired, hfunction, hcast, alloc.vec.Vec.deref] using matching
  have accepted := hsame.mpr expectedSame
  subst same
  simp
  step

theorem link_memory_complete {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view)
    (s : runtime.store.Store M) (inst : runtime.store.Instance) (i : Usize)
    (required : Itasca.types.MemType) (address : runtime.MemoryAddr)
    (hi : i.val < inst.module.module.env.imports.length)
    (hdesc : inst.module.module.env.imports.val[i.val].desc = .Memory required)
    (haddr : address.store = s.id) (hindex : address.index.val < s.memories.length)
    (hroom : inst.memories.length < Usize.max)
    (matching : LimitsMatch ((view (s.memories.val[address.index.val]).buf).length / 65536) (s.memories.val[address.index.val]).maximum required.limits) :
    runtime.store.instantiate.Store.link_import ops s inst i (.Memory address) ⦃ answer after _result => after = s ∧ answer = .Ok () ⦄ := by
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
  have compatible : LimitsMatch size.val memory.maximum required.limits := by
    simpa [hsize, hpages, hmemory] using matching
  have accepted := hmatches.mpr compatible
  subst matched
  simp
  step

theorem link_table_complete {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (inst : runtime.store.Instance) (i : Usize)
    (required : Itasca.types.TableType) (address : runtime.TableAddr)
    (hi : i.val < inst.module.module.env.imports.length)
    (hdesc : inst.module.module.env.imports.val[i.val].desc = .Table required)
    (haddr : address.store = s.id) (hindex : address.index.val < s.tables.length)
    (hroom : inst.tables.length < Usize.max)
    (sameType : (s.tables.val[address.index.val]).ty = required.elem)
    (matching : LimitsMatch (s.tables.val[address.index.val]).elements.length (s.tables.val[address.index.val]).maximum required.limits) :
    runtime.store.instantiate.Store.link_import ops s inst i (.Table address) ⦃ answer after _result => after = s ∧ answer = .Ok () ⦄ := by
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
  have equal : table.ty = required.elem := by simpa [htable] using sameType
  have acceptedType : different = false := by simpa [equal] using hdifferent
  subst different
  simp
  step as ⟨size, hsize⟩
  step with matches_limits_spec size table.maximum required.limits as ⟨matched, hmatched⟩
  have compatible : LimitsMatch size.val table.maximum required.limits := by simpa [hsize, htable] using matching
  have accepted := hmatched.mpr compatible
  subst matched
  simp
  step

theorem link_global_complete {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (inst : runtime.store.Instance) (i : Usize)
    (required : Itasca.types.GlobalType) (address : runtime.GlobalAddr)
    (hi : i.val < inst.module.module.env.imports.length)
    (hdesc : inst.module.module.env.imports.val[i.val].desc = .Global required)
    (haddr : address.store = s.id) (hindex : address.index.val < s.globals.length)
    (hroom : inst.globals.length < Usize.max)
    (sameType : (s.globals.val[address.index.val]).ty = required) :
    runtime.store.instantiate.Store.link_import ops s inst i (.Global address) ⦃ answer after _result => after = s ∧ answer = .Ok () ⦄ := by
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
  have equal : global.ty = required := by simpa [hglobal] using sameType
  have acceptedType : different = false := by simpa [equal] using hdifferent
  subst different
  simp
  step with mut_ne global.ty.mutability required.mutability as ⟨differentMut, hmut⟩
  have acceptedMut : differentMut = false := by simpa [equal] using hmut
  subst differentMut
  simp
  step

end Exec.Store
