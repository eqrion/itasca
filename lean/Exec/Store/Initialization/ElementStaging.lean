import Exec.Representation.Collection
import Exec.Store.Initialization.ElementLoop
import Exec.Store.Api.GlobalStaging

/-! Staged element initialization evaluates all constants before publishing a
segment. Allocation refusal or an initializer error preserves every old object;
success appends one segment and updates only the new instance's address map. -/
namespace Exec.Store
open Aeneas Aeneas.Std

theorem add_instance_element_staged {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.Instance) (segment : Itasca.module.Element)
    (hprefix : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (certificates : ElementInitializers store inst index segment)
    (bindings : InitializerBindings store inst)
    (room : store.elems.length < Usize.max) (mapRoom : inst.elements.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_element memory hooks floats allocator store platform instIndex index
      ⦃ out => StagedPrefix before out.2.1 ∧ out.2.2 = platform ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_element
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.env, module.Module.env,
    Itasca.module.Module.impl.env, module.Env.elements, Itasca.module.Env.impl.elements, bind_ok]
  step with Exec.Representation.slice_index_given inst.module.module.env.elements.deref index segment
    (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
  subst found
  obtain ⟨reserved, hreserve⟩ := reserve_wrapper_eq allocator law (alloc.vec.Vec.new U64) segment.init.len
  rw [hreserve]
  cases reserved with
  | false =>
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using hprefix
  | true =>
    simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with element_initializers_loop memory hooks floats allocator law store platform instIndex index
      segment.init.len inst segment hi helem (by simp) certificates bindings
      (alloc.vec.Vec.new U64) 0#usize (.Ok ()) (by simp) (by scalar_tac)
      as ⟨after, host, values, status, hs, hp, hvalues⟩
    subst after host
    cases status with
    | Err error =>
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using hprefix
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨reserved, hreserve⟩ := reserve_wrapper_eq allocator law store.elems 1#usize
      rw [hreserve]
      cases reserved with
      | false =>
        simpa [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using hprefix
      | true =>
        simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
        subst found
        step with Exec.Representation.slice_index_given inst.module.module.env.elements.deref index segment
          (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
        subst found
        step as ⟨elements, helements⟩
        have instanceBound : instIndex.val < store.instances.length :=
          (List.getElem?_eq_some_iff.mp hi).1
        step as ⟨old, back, hold, hback⟩
        have old_eq : old = inst := by
          have hread := List.getElem?_eq_getElem instanceBound
          rw [hi] at hread
          exact hold.trans (Option.some.inj hread).symm
        subst old
        step as ⟨addresses, haddresses⟩
        have appended : StagedPrefix store { store with elems := elements } := by
          constructor <;> simp [helements]
        have staged := (hprefix.trans appended).set_fresh_instance instIndex
          { inst with elements := addresses } fresh
        have instanceRead : store.instances.val[instIndex.val] = inst :=
          Option.some.inj ((List.getElem?_eq_getElem instanceBound).symm.trans hi)
        simpa [hback, instanceRead] using And.intro staged (rfl : platform = platform)

end Exec.Store
