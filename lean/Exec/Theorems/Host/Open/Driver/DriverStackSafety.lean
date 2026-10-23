import Exec.Theorems.Host.Open.Driver.DriverPrefixes
import Exec.Theorems.Host.Reentrant.CallbackStackSafety
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std

def NoOverflowMode {M : Type} : Mode M → Prop
  | .hostReturn status _ => status≠.Err .StackOverflow
  | _ => True

def NoOverflowOutput {M : Type} : ControlFlow (State M) (Outcome M) → Prop
  | .cont next => NoOverflowMode next.mode
  | .done (.host answer _) => answer.1≠.Err .StackOverflow
  | .done (.invocation _ _) => True

private theorem action_no_overflow {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (program : CallbackActions.Program) (answer : Reply M) (actual : program.run memory allocator store=.ok answer) :
    answer.1≠.Err .StackOverflow := by
  have post := program.correct memory allocator allocation view laws code store held
  rw [actual,WP.spec_ok] at post
  exact post.1.no_overflow

private theorem publish_no_overflow {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (bytes : Slice U8) (profile : Itasca.ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (answer : HostStatus × runtime.store.Store M) (actual : publish memory floats allocator store bytes profile limits=.ok answer) :
    answer.1≠.Err .StackOverflow := by
  have post := publish_effect memory floats allocator correct allocation view laws code store held bytes profile limits
  rw [actual,WP.spec_ok] at post
  obtain ⟨afterCode,effect,kind⟩ := post
  rcases kind with ok|trapped <;> simp_all

private theorem acceptCall_no_overflow {M : Type} (select : Selector) (state : State M)
    (phase : Interp.OpenCall.CallPhase M Unit) (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value) :
    NoOverflowMode (acceptCall select state phase root results).mode := by
  cases phase <;> trivial

/-- Stack exhaustion from nested APIs is mapped to a host trap by this concrete
control language; its checked primitive actions cannot report host overflow. -/
theorem tick_no_overflow {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (state : State M) (held : ExecutableInv view code state.store)
    (safe : NoOverflowMode state.mode) (out : ControlFlow (State M) (Outcome M))
    (actual : tick memory floats allocator select state=.ok out) : NoOverflowOutput out := by
  rcases state with ⟨store,mode,stack,history⟩
  cases mode <;> simp only [NoOverflowMode] at safe
  all_goals unfold tick at actual
  all_goals
    repeat' first
      | (simp only [Std.bind_assoc,bind_ok] at actual)
      | (split at actual)
      | (obtain ⟨value,called,actual⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
         try have actionSafe := action_no_overflow memory allocator allocation view laws code store held _ value called
         try have publicationSafe := publish_no_overflow memory floats allocator correct allocation view laws code store held _ _ _ value called
         cases value
         try simp only [Std.uncurry] at actual)
      | (simp only [Result.ok.injEq] at actual
         cases actual
         simp only [NoOverflowOutput]
         all_goals first
         | exact acceptCall_no_overflow _ _ _ _ _
         | simp_all [NoOverflowMode])

/-- Continuing execution preserves the supported control language's exclusion
of host stack exhaustion at every finite prefix. -/
theorem continuing_no_overflow {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    {count : Nat} {first last : State M}
    (trace : Interp.ContinuingTrace (tick memory floats allocator select) count first last)
    (code : Store.CodeInterpretation) (guard : StateGuard memory view code first) (safe : NoOverflowMode first.mode) :
    NoOverflowMode last.mode := by
  induction trace generalizing code with
  | nil => exact safe
  | next step tail ih =>
    have post:=tick_guard memory floats allocator correct allocation view laws select code _ guard
    rw [step,WP.spec_ok] at post
    obtain ⟨afterCode,effect,fresh⟩:=post
    exact ih afterCode fresh (tick_no_overflow memory floats allocator correct allocation view laws select code _ guard.1 safe _ step)

end Exec.Theorems.OpenReentrantControl
