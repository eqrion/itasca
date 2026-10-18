import Exec.Theorems.Composition.Certified.CertifiedExecutable
import Exec.Theorems.Instantiation.StartExecutableResolved
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

def TailExecutableSourceResult {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (inst : runtime.store.Instance) (store after : runtime.store.Store M) (identity : runtime.InstanceAddr)
    (initialized : core.result.Result Unit runtime.ExecError)
    (result : core.result.Result runtime.InstanceAddr runtime.ExecError) : Prop :=
  match initialized with
  | .Err error => result = .Err error
  | .Ok _ =>
    (inst.module.module.env.start = none ∧ result = .Ok identity) ∨
    ∃ index address, inst.module.module.env.start = some index ∧
      inst.funcs.val[index.val]? = some address ∧
      (∀ returned, result = .Ok returned → returned = identity ∧
        StepsH (moduleStartConfiguration view code store inst index) []
          ⟨⟨Store.decodeStore view code after, moduleStartFrame store inst⟩, []⟩) ∧
      (∀ error, result = .Err error → SupportedInvocationError
        (moduleStartConfiguration view code store inst index)
        (Store.decodeStore view code after) (moduleStartFrame store inst) error)

/-- An exact decomposition of the actual tail. It retains the successful
initializer, declared start index, map lookup and source-validated signature. -/
theorem instantiate_tail_executable_cases {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (identity : runtime.InstanceAddr)
    (inst : runtime.store.Instance) (bytes : Slice U8) (profile : Itasca.ValidationProfile)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module))
    (found : store.instances.val[identity.index.val]? = some inst)
    (code : Store.CodeInterpretation) (certified : CertifiedExecutableStore view code store)
    (imports : Store.InitializerImports store inst) (types : Store.SegmentTypeBindings store inst)
    (table : Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map Store.decodeFuncType)) :
    ∃ initialized status,
      runtime.instantiate.initialize_segments memory hooks floats allocator store platform identity.index =
        .ok (status, initialized, platform) ∧
      CertifiedExecutableStore view code initialized ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code initialized) ∧
      Store.SegmentObjectMetadata view store initialized ∧
      ((∃ result, Store.instantiate_tail memory hooks floats allocator identity store platform =
          .ok (result, initialized, platform, true) ∧
          (∀ returned, result = .Ok returned → returned = identity) ∧
          TailExecutableSourceResult view code inst initialized initialized identity status result) ∨
       ∃ index address function signature,
         status = .Ok () ∧ inst.module.module.env.start = some index ∧
         inst.funcs.val[index.val]? = some address ∧
         address.store = initialized.id ∧ initialized.funcs.val[address.index.val]? = some function ∧
         initialized.types.val[function.signature.val]? = some signature ∧
         signature.params.val = [] ∧ signature.results.val = [] ∧
         Store.instantiate_tail memory hooks floats allocator identity store platform =
           Store.instantiate_start memory hooks floats allocator identity address initialized platform) := by
  have bindings := certified.shape.initializer_bindings (List.mem_of_getElem? found)
  obtain ⟨witness⟩ := Code.compile_accepted allocator bytes profile limits inst.module accepted
  have valid : Itasca.ModuleEnv.Valid inst.module.module.env inst.module.profile := by
    rw [(witness.initializers law).2.1]
    exact (witness.semantic law).1
  obtain ⟨⟨status, initialized, host⟩, initRun, certifiedAfter, extension, metadata, hostEq⟩ :=
    WP.spec_imp_exists (initialize_segments_certified_supported memory hooks floats allocator view laws law
      store platform identity.index inst bytes profile limits accepted found code certified imports bindings types)
  dsimp only at certifiedAfter extension metadata hostEq
  subst host
  refine ⟨initialized, status, initRun, certifiedAfter, extension, metadata, ?_⟩
  cases status with
  | Err error =>
    apply Or.inl
    refine ⟨.Err error, ?_, by simp, rfl⟩
    simp [Store.instantiate_tail, initRun, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
  | Ok value =>
    cases value
    have afterFound : initialized.instances.val[identity.index.val]? = some inst := by
      rw [metadata.space.instances]; exact found
    obtain ⟨actual, read, same⟩ := WP.spec_imp_exists (Interp.vec_index_given initialized.instances identity.index inst afterFound)
    subst actual
    cases start : inst.module.module.env.start with
    | none =>
      apply Or.inl
      refine ⟨.Ok identity, ?_, by simp, Or.inl ⟨start, rfl⟩⟩
      simp [Store.instantiate_tail, initRun, core.result.Result.Insts.CoreOpsTry.branch, alloc.vec.Vec.index_slice_index,
        read, runtime.compiler.ExecutableModule.env, Exec.module.Module.env, Itasca.module.Module.impl.env,
        Exec.module.Env.start, Itasca.module.Env.impl.start, start]
    | some index =>
      obtain ⟨address, function, signature, mapped, owner, hf, hs, params, results⟩ :=
        Store.start_function_resolves (metadata.space.function_table table) valid index start
      refine Or.inr ⟨index, address, function, signature, rfl, rfl, mapped, owner, hf, hs, params, results, ?_⟩
      let slot := UScalar.cast .Usize index
      have mappedSlot : inst.funcs.val[slot.val]? = some address := by simpa [slot] using mapped
      obtain ⟨actual, addressRun, same⟩ := WP.spec_imp_exists (Interp.vec_index_given inst.funcs slot address mappedSlot)
      subst actual
      dsimp only [slot] at addressRun
      simp only [Store.instantiate_tail, Store.instantiate_start, initRun, lift, bind_ok, uncurry_apply_pair,
        core.result.Result.Insts.CoreOpsTry.branch, runtime.compiler.ExecutableModule.env,
        Exec.module.Module.env, Itasca.module.Module.impl.env, Exec.module.Env.start, Itasca.module.Env.impl.start,
        alloc.vec.Vec.index_slice_index, read, start, bind_tc_ok, addressRun]
      all_goals congr 1

end Exec.Theorems
