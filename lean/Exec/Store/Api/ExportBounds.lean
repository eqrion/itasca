import Exec.Representation.StoreInvariant
import Exec.Store.Preparation.Staging
import Itasca.Module.Env.Basic
import Itasca.Module.Elab.Metadata
namespace Exec.Store
open Aeneas Aeneas.Std

/-- Static export descriptors address the validated namespace and retain
unique source names. Both facts depend only on immutable module metadata. -/
structure ModuleExportBounds (env : Itasca.module.Env) : Prop where
  indices : ∀ entry ∈ env.exports.val, match entry.desc with
    | .Func index => index.val < env.func_types.length
    | .Table index => index.val < env.table_types.length
    | .Memory index => index.val < env.mem_types.length
    | .Global index => index.val < env.global_types.length
  names : (env.exports.val.map (fun entry => Itasca.ModuleBinary.nameOfBytes entry.name.val)).Nodup

/-- Every retained instance has bounded module export descriptors. -/
def ExportBounds {M : Type} (store : runtime.store.Store M) : Prop :=
  ∀ (index : Nat) (inst : runtime.store.ModuleInst), store.instances.val[index]? = some inst → ModuleExportBounds inst.module.module.env

/-- Successful validation supplies export bounds without an API correctness premise. -/
theorem module_export_bounds {env profile} (valid : Itasca.ModuleEnv.Valid env profile) :
    ModuleExportBounds env := by
  constructor
  · intro entry member
    obtain ⟨ty,resolved⟩ := valid.exports entry member
    cases descriptor : entry.desc <;>
      simp only [Itasca.ModuleExternals.ExportResolves,descriptor] at resolved ⊢ <;>
      exact resolved.choose
  · exact Itasca.ModuleElaboration.export_names_distinct valid

/-- Combining retained export descriptors with completed instance map lengths
makes every actual export address lookup safe. -/
theorem export_address_bounds {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} (bounds : ModuleExportBounds inst.module.module.env)
    (shape : InstanceShape store inst) (entry : Itasca.module.Export)
    (member : entry ∈ inst.module.module.env.exports.val) :
    match entry.desc with
    | .Func index => index.val < inst.funcs.length
    | .Table index => index.val < inst.tables.length
    | .Memory index => index.val < inst.memories.length
    | .Global index => index.val < inst.globals.length := by
  obtain ⟨_,functions,tables,memories,globals,_⟩ := shape
  have bounded := bounds.indices entry member
  cases descriptor : entry.desc <;> simp only [descriptor] at bounded ⊢
  · simpa only [functions] using bounded
  · simpa only [tables] using bounded
  · simpa only [memories] using bounded
  · simpa only [globals] using bounded

theorem ExportBounds.instances_eq {M : Type} {before after : runtime.store.Store M}
    (bounds : ExportBounds before) (same : after.instances = before.instances) : ExportBounds after := by
  simpa only [ExportBounds,same] using bounds

theorem ExportBounds.staged {M : Type} {before after : runtime.store.Store M}
    (bounds : ExportBounds before) (retained : StagedPrefix before after)
    (count : after.instances.length ≤ before.instances.length + 1)
    (fresh : ∀ inst, after.instances.val[before.instances.length]? = some inst →
      ModuleExportBounds inst.module.module.env) : ExportBounds after := by
  intro index inst found
  by_cases bound : index < before.instances.length
  · have same := congrArg (fun values : List runtime.store.ModuleInst => values[index]?) retained.instances
    have oldFound : before.instances.val[index]? = some inst := by
      simpa only [List.getElem?_take, if_pos bound, found] using same.symm
    exact bounds index inst oldFound
  · have room := (List.getElem?_eq_some_iff.mp found).1
    change index < after.instances.length at room
    have equal : index = before.instances.length := by omega
    subst index
    exact fresh inst found

theorem new_export_bounds {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (identity : Usize) (limits : runtime.store.StoreLimits) :
    runtime.store.Store.with_identity memory identity limits ⦃ store => ExportBounds store ⦄ := by
  simp [runtime.store.Store.with_identity,WP.spec_ok,ExportBounds,alloc.vec.Vec.new]
end Exec.Store
