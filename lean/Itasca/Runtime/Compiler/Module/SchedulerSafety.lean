import Itasca.Runtime.Compiler.Local.Relations.Function.Environment
import Itasca.Runtime.Compiler.Module.EnvironmentFrame
import Itasca.Runtime.Compiler.Module.SchedulerSubmission

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
open runtime.compiler

/-- The eager scheduler's raw metadata and queue bounds at the next submitted
function index. No successful final module or semantic code certificate is used. -/
structure SchedulerReady {A : Type} (env : module.Env) (cursor : Nat)
    (scheduler : CompileScheduler A) : Prop where
  signatures : SignatureSequence scheduler.signatures.val env.types.val
  functionSlots : scheduler.func_param_slots.val.map (fun word => word.val) =
    env.func_types.val.map (fun ty => signatureSlots ty.params.val)
  functions : scheduler.functions.val.length = env.func_type_indices.val.length
  origin : scheduler.code_start.val ≤ limits.MAX_MODULE_BYTES.val
  queue : scheduler.completed.val.length ≤ cursor
  cursorBound : cursor ≤ env.func_type_indices.val.length

/-- Initial scheduler fields before the environment callback. -/
structure SchedulerInitial {A : Type} (scheduler : CompileScheduler A) : Prop where
  signatures : scheduler.signatures.val = []
  functionSlots : scheduler.func_param_slots.val = []
  functions : scheduler.functions.val = []
  queue : scheduler.completed.val = []
  origin : scheduler.code_start.val ≤ limits.MAX_MODULE_BYTES.val

@[step] theorem compiler_environment_safety {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : CompileScheduler A)
    (env : module.Env) (initial : SchedulerInitial scheduler) :
    CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready ops scheduler env ⦃ out =>
      ∀ config, out.1 = .Ok config → SchedulerReady env 0 out.2 ⦄ := by
  obtain ⟨⟨status,after⟩,run,post⟩ := WP.spec_imp_exists
    (compiler_environment_ready_sequence ops law scheduler env initial.signatures initial.functionSlots initial.functions)
  rw [run]
  apply (WP.spec_ok _).mpr
  intro config accepted
  dsimp only at accepted
  obtain ⟨signatures,slots,functions⟩ := post config accepted
  have unchanged := compiler_environment_frame ops scheduler after env config (by simpa only [accepted] using run)
  have fields : after.completed = scheduler.completed ∧ after.tail = scheduler.tail ∧ after.code_start = scheduler.code_start := by
    simpa [schedulerFrame] using unchanged
  refine ⟨signatures,slots,?_,?_,?_,Nat.zero_le _⟩
  · simp [functions]
  · simpa [fields.2.2] using initial.origin
  · simp [fields.1,initial.queue]

@[step] theorem compiler_poll_safety {A : Type} (ops : runtime.platform.Alloc A)
    (env : module.Env) (cursor : Nat) (scheduler : CompileScheduler A)
    (ready : SchedulerReady env cursor scheduler) :
    CompileScheduler.Insts.ItascaStreamStreamingVisitor.poll_code_batch ops scheduler ⦃ out =>
      ∀ batch, out.1 = .Ok batch → SchedulerReady env cursor out.2 ⦄ := by
  unfold CompileScheduler.Insts.ItascaStreamStreamingVisitor.poll_code_batch
  simp only [alloc.vec.Vec.pop,bind_ok]
  cases present : scheduler.completed.val.getLast? with
  | none => simp [core.option.Option.ok_or]
  | some batch =>
    simp [core.option.Option.ok_or]
    exact ⟨ready.signatures,ready.functionSlots,ready.functions,ready.origin,
      (by dsimp only; rw [alloc.vec.Vec.from_val]; simp only [List.length_dropLast]; have := ready.queue; omega),ready.cursorBound⟩

end Itasca.Runtime.Code
