import Exec.Store.Instantiation.InstantiateWithRecording
import Exec.Platform.RecordingBind
namespace Exec.Store
open Aeneas Aeneas.Std SpecExt

/-- Erasure holds for arbitrary internal inputs and callback behavior. -/
theorem recordedInstantiateStart_erase {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (identity : runtime.InstanceAddr) (address : runtime.FuncAddr)
    (store : runtime.store.Store M) (platform : P) (prior : List HostEvent) :
    (do let (out,_) ← recordedInstantiateStart memory hooks floats allocator identity address store platform prior
        Result.ok out) = instantiate_start memory hooks floats allocator identity address store platform := by
  unfold recordedInstantiateStart instantiate_start
  simp only [runtime.interp.Execution.new,lift,bind_ok,Std.uncurry,Std.bind_assoc]
  apply Platform.Recording.bind_erase_cont _ _ _ _ (Interp.recordedInvokeWith_erase ..)
  rintro ⟨status,exec,after,p,results⟩ trace
  cases status <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,core.convert.FromSame.from]

theorem recordedInstantiateTail_erase {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (identity : runtime.InstanceAddr) (store : runtime.store.Store M) (platform : P)
    (prior : List HostEvent) :
    (do let (out,_) ← recordedInstantiateTail memory hooks floats allocator identity store platform prior
        Result.ok out) = runtime.store.instantiate.Store.commit_instance memory hooks floats allocator store platform identity false := by
  unfold recordedInstantiateTail runtime.store.instantiate.Store.commit_instance
  simp only [Std.bind_assoc,Std.uncurry]
  apply congrArg (Std.bind _)
  funext answer
  rcases answer with ⟨status,after,p⟩
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,core.convert.FromSame.from]
  | Ok unitValue =>
    cases unitValue
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry,Std.bind_assoc]
    apply congrArg (Std.bind _); funext inst
    apply congrArg (Std.bind _); funext env
    apply congrArg (Std.bind _); funext start
    cases start with
    | none => simp only [bind_ok,Std.uncurry]
    | some index =>
      simp only [lift,bind_ok,Std.bind_assoc]
      apply congrArg (Std.bind _); funext address
      rw [recordedInstantiateStart_erase]
      unfold instantiate_start
      simp only [lift,bind_ok,Std.uncurry]
      repeat' first
        | rfl
        | (apply congrArg (Std.bind _); funext answer)
        | (split <;> simp only [bind_ok,Std.uncurry])

theorem recordedInstantiateInner_erase {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P) (committed : Bool) (prior : List HostEvent) :
    (do let (out,_) ← recordedInstantiateInner memory hooks floats allocator store module imports platform committed prior
        Result.ok out) = runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator store module imports platform committed := by
  unfold recordedInstantiateInner runtime.store.instantiate.Store.instantiate_inner
  simp only [Std.bind_assoc]
  apply congrArg (Std.bind _)
  funext prepared
  obtain ⟨result, staged, after⟩ := prepared
  simp only [uncurry_apply_pair]
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,core.convert.FromSame.from]
  | Ok prepared =>
    obtain ⟨identity, items⟩ := prepared
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.bind_assoc]
    apply congrArg (Std.bind _); funext charged
    exact recordedInstantiateTail_erase ..

theorem recordedInstantiateWith_erase {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P) (prior : List HostEvent) :
    (do let (out,_) ← recordedInstantiateWith memory hooks floats allocator store module imports platform prior
        Result.ok out) = runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator store module imports platform := by
  unfold recordedInstantiateWith runtime.store.instantiate.Store.instantiate_with
  simp only [Std.bind_assoc,Std.uncurry]
  apply Platform.Recording.bind_erase_cont _ _ _ _ (recordedInstantiateInner_erase ..)
  rintro ⟨result,after,p,committed⟩ trace
  simp only [Std.bind_assoc,Std.uncurry]
  repeat' first
    | rfl
    | (apply congrArg (Std.bind _); funext answer)
    | (split <;> simp only [Std.bind_assoc,bind_ok,Std.uncurry])
    | (split_ifs <;> simp only [Std.bind_assoc,bind_ok,Std.uncurry])
end Exec.Store
