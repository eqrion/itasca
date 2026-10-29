import Itasca.Runtime.Compiler.Module.CompileAssembly
import Itasca.Runtime.Compiler.Local.Relations.Function.Environment
import Itasca.Runtime.Compiler.Module.CompilerDrain
import Itasca.Stream.DriverRun
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Compiler custom-section callbacks preserve every scheduler predicate. -/
theorem compiler_custom_preserves {A : Type} (ops : runtime.platform.Alloc A)
    (P : runtime.compiler.CompileScheduler A → Prop) :
    ModuleTail.PreservesInvariant
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops).moduleModuleVisitorInst P := by
  intro before chunk after accepted prior
  have same : before = after := congrArg Prod.snd (Result.ok_injective accepted)
  simpa only [← same] using prior

/-- Parsing the environment only delivers custom-section notifications, so the
actual compiler scheduler is unchanged before its environment-ready callback. -/
theorem compiler_driver_decoded {A S : Type} (ops : runtime.platform.Alloc A)
    {source : stream.Source S} {id state before after env profile}
    (run : StreamRun.Accepted source
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      id state before after env profile) : run.decoded = before := by
  have region : run.region = before := (Result.ok_injective run.region_call).symm
  have decoded := module.validate_env_with.accepted_invariant
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops).moduleModuleVisitorInst
    (fun scheduler => scheduler = before) (compiler_custom_preserves ops _) run.environment run.region env
    run.environmentLength run.decoded run.decode_environment region
  exact decoded

/-- Code-end, tail parsing/delivery and final worker retirement preserve the
function array and captured tables produced by submission. -/
theorem compiler_driver_after_submission {A S : Type} (ops : runtime.platform.Alloc A)
    {source : stream.Source S} {id state env environmentLength before after profile}
    (run : StreamRun.Remaining source
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      id state env environmentLength before after profile) :
    after = {run.submitted with completed := after.completed, tail := some run.tail} := by
  have ended : run.ended = run.submitted := by
    have same := congrArg Prod.snd (Result.ok_injective run.end_call)
    exact same.symm
  have region : run.region = run.ended := (Result.ok_injective run.region_call).symm
  have decoded := module.validate_tail_with.accepted_invariant
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops).moduleModuleVisitorInst
    (fun scheduler => scheduler = run.region) (compiler_custom_preserves ops _) run.tailBytes 0#usize env
    run.region run.tail run.decodedTail run.decode_tail rfl
  have ready : run.ready = {run.decodedTail with tail := some run.tail} := by
    have same := congrArg Prod.snd (Result.ok_injective run.ready_call)
    exact same.symm
  have drained := compiler_drain_frame ops id run.ready after run.pending run.remaining run.drain_call
  simpa only [ready, decoded, region, ended] using drained

/-- Actual environment preparation supplies the exact canonical signature and
parameter tables and the empty source-indexed result array. -/
theorem compiler_driver_configured {A S : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {source : stream.Source S} {id state before after env profile}
    (run : StreamRun.Accepted source
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      id state before after env profile)
    (emptyTypes : before.signatures.val = []) (emptySlots : before.func_param_slots.val = [])
    (emptyFunctions : before.functions.val = []) :
    SignatureSequence run.remaining.configured.signatures.val env.types.val ∧
      run.remaining.configured.func_param_slots.val.map (fun word => word.val) =
        env.func_types.val.map (fun ft => signatureSlots ft.params.val) ∧
      run.remaining.configured.functions.val = List.replicate env.func_type_indices.val.length none ∧
      run.remaining.configured.code_start = before.code_start := by
  have decoded := compiler_driver_decoded ops run
  have prepared := compiler_environment_ready_sequence ops law run.decoded env
    (by simpa only [decoded] using emptyTypes) (by simpa only [decoded] using emptySlots)
    (by simpa only [decoded] using emptyFunctions)
  have configured := run.remaining.configured_call
  change runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready ops run.decoded env =
    .ok (.Ok run.remaining.config, run.remaining.configured) at configured
  rw [configured, WP.spec_ok] at prepared
  obtain ⟨signatures, widths, functions⟩ := prepared _ rfl
  have frame := compiler_environment_frame ops run.decoded run.remaining.configured env run.remaining.config
    run.remaining.configured_call
  have origin := congrArg (fun fields => fields.2.2) frame
  exact ⟨signatures, widths, functions, by simpa only [schedulerFrame, decoded] using origin⟩
end Itasca.Runtime.Compiler
