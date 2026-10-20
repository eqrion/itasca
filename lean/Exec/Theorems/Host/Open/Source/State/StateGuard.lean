import Exec.Theorems.Host.Open.Source.State.Mode
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- One shared reached interpretation ties the active mode, saved stack and
source store to their actual native counterparts. -/
structure SourceStateGuard {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (native : State M) (source : Spec.OpenExecution.State SourceControl) (rank : Nat) : Prop where
  invariant : ExecutableInv view code native.store
  mode : SourceMode memory allocator view code native.store native.mode source.mode rank
  stack : SourceStack memory view code native.store native.stack source.stack
  storeEq : source.store=Store.decodeStore view code native.store

theorem SourceStateGuard.native {M A : Type} {memory : runtime.platform.MemoryBuffer M}
    {allocator : runtime.platform.Alloc A} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {native : State M} {source : Spec.OpenExecution.State SourceControl} {rank : Nat}
    (guard : SourceStateGuard memory allocator view code native source rank) : StateGuard memory view code native :=
  ⟨guard.invariant,guard.mode.native guard.invariant,guard.stack.native⟩

theorem SourceStateGuard.typed {M A : Type} {memory : runtime.platform.MemoryBuffer M}
    {allocator : runtime.platform.Alloc A} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {native : State M} {source : Spec.OpenExecution.State SourceControl} {rank : Nat}
    (guard : SourceStateGuard memory allocator view code native source rank) : source.Typed := by
  change Store_ok source.store ∧ Spec.OpenExecution.ModeTyped source.store source.mode ∧
    Spec.OpenExecution.StackTyped source.store source.stack
  rw [guard.storeEq]
  exact ⟨guard.invariant.source_typed,guard.mode.typed,guard.stack.typed⟩
end Exec.Theorems.OpenReentrantControl
