import Exec.Theorems.Host.Reentrant.ReentrantInvocation
import Exec.Theorems.Instantiation.InstantiateExecutableWorldSource
import Exec.Store.Instantiation.InstantiateNoStartExterns
import Exec.Spec.Invocation
import Exec.Spec.Wf
import Exec.Code.Module.CompileTotal

/-! Executable finite reentrancy with a separate execution for every nested
invocation. Selectors see only copied arguments; checked operations alone see
the store. Depth stages use already constructed child platforms. -/
noncomputable section
namespace Exec.Theorems.ReentrantCallbacks
open Aeneas Aeneas.Std SpecExt Exec.Interp

structure Effect {M : Type} (view : M → Slice U8) (beforeCode : Store.CodeInterpretation)
    (before : runtime.store.Store M) (afterCode : Store.CodeInterpretation) (after : runtime.store.Store M) : Prop
    extends ReturnedWorldEffect view (ExecutableInv view) beforeCode before afterCode after where
  externs : before.externs.length≤after.externs.length

theorem Effect.refl {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} (held : ExecutableInv view code store) : Effect view code store code store :=
  ⟨.refl held held.well_formed,Nat.le_refl _⟩

theorem Effect.trans {M : Type} {view : M → Slice U8} {a b c : Store.CodeInterpretation}
    {s t u : runtime.store.Store M} (first : Effect view a s b t) (second : Effect view b t c u) :
    Effect view a s c u :=
  ⟨first.toReturnedWorldEffect.trans second.toReturnedWorldEffect,Nat.le_trans first.externs second.externs⟩

end Exec.Theorems.ReentrantCallbacks
