import Exec.Code.Module.CompileEntry
import Exec.Code.Local.Initializer.InitializerComplete
import Exec.Code.Module.CollectFunctions
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
open Itasca Itasca.ResultFacts

def initialScheduler (A : Type) (limits : runtime.compiler.CompileLimits) (codeStart : Usize) :
    runtime.compiler.CompileScheduler A :=
  { signatures := alloc.vec.Vec.new _, func_param_slots := alloc.vec.Vec.new _,
    completed := alloc.vec.Vec.new _, functions := alloc.vec.Vec.new _, tail := none,
    code_start := codeStart,
    budget := {marker := (), limits, instructions := 0#usize, branches := 0#usize, controls := 0#usize, locals := 0#usize, error := none} }

def uninitializedModule (env : module.Env) (tail : module.Tail) (profile : ValidationProfile)
    (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction) : runtime.compiler.ExecutableModule :=
  { module := {env, tail}, profile, functions, global_initializers := alloc.vec.Vec.new _,
    element_initializers := alloc.vec.Vec.new _, element_offsets := alloc.vec.Vec.new _,
    data_offsets := alloc.vec.Vec.new _, initialization := 0#usize }

/-- A successful public compiler run retains the actual canonical streaming
validation, source-ordered function collection, and initializer-lowering calls. -/
structure CompileWitness {A : Type} (allocator : runtime.platform.Alloc A)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (executable : runtime.compiler.ExecutableModule) where
  codeStart : Usize
  codeEnd : Usize
  initialEnv : module.Env
  env : module.Env
  scheduler : runtime.compiler.CompileScheduler A
  tail : module.Tail
  functions : alloc.vec.Vec runtime.bytecode.CompiledFunction
  pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction)
  collectedBudget : runtime.compiler.Budget A
  finalBudget : runtime.compiler.Budget A
  region : runtime.compiler.code_region bytes = .ok (codeStart, codeEnd)
  initialized : module.Env.new = .ok initialEnv
  validated : stream.validate_streaming runtime.compiler.CompileSource.Insts.ItascaStreamSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator)
    0#u64 profile {bytes, code_start := codeStart, code_end := codeEnd}
    (initialScheduler A limits codeStart) initialEnv = .ok (.Ok (), scheduler, env)
  tailReady : scheduler.tail = some tail
  collected : runtime.compiler.collect_functions allocator scheduler.budget scheduler.functions =
    .ok (.Ok functions, collectedBudget, pending)
  lowered : runtime.compiler.initialize.lower allocator (uninitializedModule env tail profile functions)
    collectedBudget = .ok (.Ok (), executable, finalBudget)

theorem compile_accepted {A : Type} (allocator : runtime.platform.Alloc A)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (executable : runtime.compiler.ExecutableModule)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok executable)) :
    Nonempty (CompileWitness allocator bytes profile limits executable) := by
  unfold runtime.compiler.compile_with at accepted
  dsimp only at accepted
  split at accepted
  · simp at accepted
  · obtain ⟨⟨codeStart, codeEnd⟩, region, rest⟩ := bind_ok_inv _ _ _ accepted
    obtain ⟨initialEnv, initialized, rest⟩ := bind_ok_inv _ _ _ rest
    obtain ⟨⟨result, scheduler, env⟩, validated, rest⟩ := bind_ok_inv _ _ _ rest
    cases result with
    | Err error => cases choice : scheduler.budget.error <;> simp [choice] at rest
    | Ok acceptedUnit =>
      cases acceptedUnit
      simp only [uncurry_apply_pair] at rest
      cases tailReady : scheduler.tail with
      | none => simp [tailReady, core.option.Option.ok_or,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | some tail =>
        simp only [tailReady, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨⟨result, collectedBudget, pending⟩, collected, rest⟩ := bind_ok_inv _ _ _ rest
        cases result with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
        | Ok functions =>
          simp only [uncurry_apply_pair, bind_ok] at rest
          obtain ⟨⟨result, output, finalBudget⟩, lowered, rest⟩ := bind_ok_inv _ _ _ rest
          cases result with
          | Err error => cases choice : finalBudget.error <;> simp [choice] at rest
          | Ok acceptedUnit =>
            cases acceptedUnit
            simp at rest
            subst output
            exact ⟨⟨codeStart, codeEnd, initialEnv, env, scheduler, tail, functions, pending,
              collectedBudget, finalBudget, region, initialized, validated, tailReady, collected, lowered⟩⟩

/-- The actual collection witness fixes the exact order of the defined code. -/
theorem CompileWitness.function_order {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes profile limits executable} (w : CompileWitness allocator bytes profile limits executable)
    (law : Platform.AllocCorrect allocator) : w.scheduler.functions.val = w.functions.val.map some := by
  have collected := collect_functions_spec allocator law w.scheduler.budget w.scheduler.functions
  rw [w.collected, WP.spec_ok] at collected
  exact collected w.functions rfl

/-- Successful initializer lowering preserves the validated module and all
defined functions, and establishes the concrete read-only initializer maps. -/
theorem CompileWitness.initializers {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes profile limits executable} (w : CompileWitness allocator bytes profile limits executable)
    (law : Platform.AllocCorrect allocator) :
    executable.module = ⟨w.env, w.tail⟩ ∧ executable.profile = profile ∧
      executable.functions.val.take w.functions.length = w.functions.val ∧ InitializerMappings executable := by
  exact initializer_lower allocator law (uninitializedModule w.env w.tail profile w.functions) executable
    w.collectedBudget w.finalBudget (by rfl) (by rfl) (by rfl) (by rfl) w.lowered

end Itasca.Runtime.Code
