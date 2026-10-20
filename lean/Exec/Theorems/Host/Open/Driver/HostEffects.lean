import Exec.Theorems.Host.Open.Driver.ReentrantControl
import Exec.Theorems.Host.Reentrant.FiniteReentrantCallbacks
import Exec.Code.Module.CompileTotal
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std
abbrev Effect := @ReentrantCallbacks.Effect

/-- Publication runs normally and retains all checked world effects, including
committed initializer effects on error. No returning host contract is needed
because the operation rejects modules with a start function. -/
theorem publish_effect {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (bytes : Slice U8) (profile : Itasca.ValidationProfile) (limits : runtime.compiler.CompileLimits) :
    publish memory floats allocator store bytes profile limits ⦃ answer=>∃afterCode,
      Effect view code store afterCode answer.2 ∧ (answer.1=.Ok () ∨ answer.1=.Err .Trap) ⦄ := by
  obtain ⟨compiled,actual,_⟩ := WP.spec_imp_exists (Code.compile_with_total allocator allocation bytes profile limits)
  unfold publish
  rw [actual,bind_ok]
  cases compiled with
  | Err error => exact WP.spec.ret ⟨code,.refl held,Or.inr rfl⟩
  | Ok module =>
    simp only []
    split
    · rename_i noStart
      obtain ⟨answer,run,afterCode,effect,externs,source⟩ := WP.spec_imp_exists
        (ReentrantCallbacks.instantiate_no_start_without_callbacks memory (inert memory) floats allocator correct allocation
          (fun _=>WP.spec.ret trivial) view laws code store held module (Slice.new _) (by simp) bytes profile limits actual noStart)
      rw [run,bind_ok]
      have fresh : Effect view code store afterCode answer.2.1 := ⟨effect,by rw [externs]⟩
      cases answer.1 with
      | Ok address => exact WP.spec.ret ⟨afterCode,fresh,Or.inl rfl⟩
      | Err error => exact WP.spec.ret ⟨afterCode,fresh,Or.inr rfl⟩
    · exact WP.spec.ret ⟨code,.refl held,Or.inr rfl⟩

/-- Host-local instructions cannot enter a nested Wasm execution. They may
finish, loop, or perform one checked API action with committed effects. -/
def Local : Instruction → Prop
  | .invoke _ _ _ => False
  | _ => True

def LocalOutcome {M : Type} (host : HostState) (state : State M) : Prop :=
  (∃next,state.mode=.host next ∧ next.identity=host.identity ∧ next.arguments=host.arguments) ∨
  ∃status values,state.mode=.hostReturn status values ∧
    ∀value∈values.val,Store.IssuedValue state.store value

/-- Each host-local tick returns normally and retains the full source-typed
store, raw metadata, old-key interpretation and issued references. This local
proof makes no termination claim about the host graph. -/
theorem host_local_effect {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (select : Selector) (state : State M) (held : ExecutableInv view code state.store)
    (host : HostState) (mode : state.mode=.host host)
    (onlyLocal : ∀instruction,host.code[host.pc]?=some instruction → Local instruction) :
    tick memory floats allocator select state ⦃ out=>∃next afterCode,out=.cont next ∧
      Effect view code state.store afterCode next.store ∧ next.stack=state.stack ∧ next.history=state.history ∧ LocalOutcome host next ⦄ := by
  unfold tick
  rw [mode]
  dsimp only
  cases selected : host.code[host.pc]? with
  | none => exact WP.spec.ret ⟨_,code,rfl,.refl held,rfl,rfl,Or.inr ⟨_,_,rfl,by simp⟩⟩
  | some instruction =>
    cases instruction with
    | trapped => exact WP.spec.ret ⟨_,code,rfl,.refl held,rfl,rfl,Or.inr ⟨_,_,rfl,by simp⟩⟩
    | returned values =>
      exact WP.spec.ret ⟨_,code,rfl,.refl held,rfl,rfl,
        Or.inr ⟨_,_,rfl,(PureCallbacks.Program.returned values).issued state.store⟩⟩
    | jump target => exact WP.spec.ret ⟨_,code,rfl,.refl held,rfl,rfl,Or.inl ⟨_,rfl,rfl,rfl⟩⟩
    | branch condition yes no => exact WP.spec.ret ⟨_,code,rfl,.refl held,rfl,rfl,Or.inl ⟨_,rfl,rfl,rfl⟩⟩
    | returnAction segment =>
      dsimp only
      obtain ⟨answer,actual,source,effect,issued⟩ := WP.spec_imp_exists (segment.correct memory allocator allocation view laws code state.store held)
      rw [actual,bind_ok]
      exact WP.spec.ret ⟨_,code,rfl,⟨⟨(by intro index inst found fn; rfl),effect.invariant,effect.metadata,effect.extension⟩,
        by rw [effect.externs]⟩,rfl,rfl,Or.inr ⟨_,_,rfl,issued⟩⟩
    | action segment next =>
      dsimp only
      obtain ⟨⟨status,after,values⟩,actual,source,effect,issued⟩ := WP.spec_imp_exists
        (segment.correct memory allocator allocation view laws code state.store held)
      rw [actual,bind_ok]
      have fresh : Effect view code state.store code after :=
        ⟨⟨(by intro index inst found fn; rfl),effect.invariant,effect.metadata,effect.extension⟩,by rw [effect.externs]⟩
      cases status with
      | Ok unit => cases unit; exact WP.spec.ret ⟨_,code,rfl,fresh,rfl,rfl,Or.inl ⟨_,rfl,rfl,rfl⟩⟩
      | Err error => exact WP.spec.ret ⟨_,code,rfl,fresh,rfl,rfl,Or.inr ⟨_,_,rfl,issued⟩⟩
    | publish bytes profile limits next =>
      dsimp only
      obtain ⟨⟨status,after⟩,actual,afterCode,effect,statusKind⟩ := WP.spec_imp_exists
        (publish_effect memory floats allocator correct allocation view laws code state.store held bytes profile limits)
      rw [actual,bind_ok]
      cases status with
      | Ok unit => cases unit; exact WP.spec.ret ⟨_,afterCode,rfl,effect,rfl,rfl,Or.inl ⟨_,rfl,rfl,rfl⟩⟩
      | Err error => exact WP.spec.ret ⟨_,afterCode,rfl,effect,rfl,rfl,Or.inr ⟨_,_,rfl,by simp⟩⟩
    | invoke index args next => exact False.elim (onlyLocal _ selected)
end Exec.Theorems.OpenReentrantControl
