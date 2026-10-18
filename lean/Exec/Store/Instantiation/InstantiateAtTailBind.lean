import Exec.Store.Instantiation.InstantiateAtTail
namespace Exec.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Continuations commute with the extracted preparation prefix. -/
theorem instantiateInnerAtTail_bind {M P F A R S : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P) (committed : Bool)
    (rejected : (core.result.Result runtime.InstanceAddr runtime.ExecError × runtime.store.Store M × P × Bool) → Result R)
    (tail : runtime.InstanceAddr → runtime.store.Store M → P → Result R)
    (next : R → Result S) :
    Std.bind (instantiateInnerAtTail memory hooks floats allocator store module imports platform committed rejected tail) next =
      instantiateInnerAtTail memory hooks floats allocator store module imports platform committed
        (fun out => Std.bind (rejected out) next) (fun identity store platform => Std.bind (tail identity store platform) next) := by
  unfold instantiateInnerAtTail
  simp only [Std.bind_assoc]
  repeat' first
    | rfl
    | (apply congrArg (Std.bind _); funext answer)
    | (split <;> simp only [Std.bind_assoc,bind_ok,Std.uncurry])
    | (split_ifs <;> simp only [Std.bind_assoc,bind_ok,Std.uncurry])
end Exec.Store
