import Exec.Store.Instantiation.InstantiateNoStart
import Exec.Store.Initialization.SegmentCodeMetadata

namespace Exec.Store
open Aeneas Aeneas.Std

/-- The exact fresh-execution start invocation remaining in instantiation. -/
def instantiate_start {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (identity : runtime.InstanceAddr) (address : runtime.FuncAddr)
    (store : runtime.store.Store M) (platform : P) :
    Result (core.result.Result runtime.InstanceAddr runtime.ExecError × runtime.store.Store M × P × Bool) := do
  let execution ← runtime.interp.Execution.new
  let arguments ← lift (Array.to_slice (Std.Array.empty runtime.Value))
  let (result, _, after, host, _) ← runtime.interp.invoke_with memory hooks floats allocator
    execution store platform address arguments (alloc.vec.Vec.new runtime.Value)
  let branch ← core.result.Result.Insts.CoreOpsTry.branch result
  match branch with
  | core.ops.control_flow.ControlFlow.Continue _ => .ok (.Ok identity, after, host, true)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let error ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      runtime.InstanceAddr (core.convert.FromSame runtime.ExecError) residual
    .ok (error, after, host, true)

/-- The accepted initializer tail either completes normally or reaches exactly
one source-validated empty-signature start call in a fully shaped store. All
address and signature facts are obtained from the constructed function table. -/
theorem instantiate_tail_start_ready {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (identity : runtime.InstanceAddr)
    (inst : runtime.store.ModuleInst) (bytes : Slice U8) (profile : Itasca.ValidationProfile)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module))
    (found : store.instances.val[identity.index.val]? = some inst)
    (shape : Shape view store) (imports : InitializerImports store inst)
    (types : SegmentTypeBindings store inst)
    (table : Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map decodeFuncType)) :
    ∃ initialized, Shape view initialized ∧ SegmentAddressSpace store initialized ∧
      ((∃ result, instantiate_tail memory hooks floats allocator identity store platform =
        .ok (result, initialized, platform, true)) ∨
       ∃ address function signature,
         address.store = initialized.id ∧ initialized.funcs.val[address.index.val]? = some function ∧
         initialized.types.val[function.signature.val]? = some signature ∧
         signature.params.val = [] ∧ signature.results.val = [] ∧
         instantiate_tail memory hooks floats allocator identity store platform =
           instantiate_start memory hooks floats allocator identity address initialized platform) := by
  have bindings := shape.initializer_bindings (List.mem_of_getElem? found)
  have instanceShape := shape.instances inst (List.mem_of_getElem? found)
  obtain ⟨witness⟩ := Code.compile_accepted allocator bytes profile limits inst.module accepted
  have valid : Itasca.ModuleEnv.Valid inst.module.module.env inst.module.profile := by
    rw [(witness.initializers law).2.1]
    exact (witness.semantic law).1
  have total := initialize_segments_compiled memory hooks floats allocator view laws law
    store platform identity.index inst bytes profile limits accepted found instanceShape imports bindings
  have shaped := initialize_segments_compiled_shape memory hooks floats allocator view laws law
    store platform identity.index inst bytes profile limits accepted found shape imports bindings types
  obtain ⟨⟨result, after, host⟩, initRun, ⟨metadata, sameHost⟩, afterShape, segmentTypes⟩ :=
    WP.spec_imp_exists (segment_specs_and total shaped)
  dsimp only at metadata sameHost afterShape segmentTypes
  subst host
  refine ⟨after, afterShape, metadata, ?_⟩
  cases result with
  | Err error =>
    apply Or.inl
    refine ⟨.Err error, ?_⟩
    simp [instantiate_tail, initRun, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
  | Ok value =>
    have afterFound : after.instances.val[identity.index.val]? = some inst := by rw [metadata.instances]; exact found
    obtain ⟨actual, read, same⟩ := WP.spec_imp_exists (Interp.vec_index_given after.instances identity.index inst afterFound)
    subst actual
    cases start : inst.module.module.env.start with
    | none =>
      apply Or.inl
      refine ⟨.Ok identity, ?_⟩
      simp [instantiate_tail, initRun, core.result.Result.Insts.CoreOpsTry.branch, alloc.vec.Vec.index_slice_index,
        read, runtime.compiler.ExecutableModule.env, Exec.module.Module.env, Itasca.module.Module.impl.env,
        Exec.module.Env.start, Itasca.module.Env.impl.start, start]
    | some index =>
      obtain ⟨address, function, signature, mapped, owned, functionFound, signatureFound, params, results⟩ :=
        start_function_resolves (metadata.function_table table) valid index start
      refine Or.inr ⟨address, function, signature, owned, functionFound, signatureFound, params, results, ?_⟩
      let slot := UScalar.cast .Usize index
      have mappedSlot : inst.funcs.val[slot.val]? = some address := by simpa [slot] using mapped
      obtain ⟨actual, addressRun, same⟩ := WP.spec_imp_exists (Interp.vec_index_given inst.funcs slot address mappedSlot)
      subst actual
      dsimp only [slot] at addressRun
      simp only [instantiate_tail, instantiate_start, initRun, lift, bind_ok, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        runtime.compiler.ExecutableModule.env, Exec.module.Module.env, Itasca.module.Module.impl.env,
        Exec.module.Env.start, Itasca.module.Env.impl.start, alloc.vec.Vec.index_slice_index,
        read, start, bind_tc_ok, addressRun]
      all_goals congr 1

end Exec.Store
