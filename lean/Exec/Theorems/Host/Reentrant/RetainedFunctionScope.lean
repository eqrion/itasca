import Exec.Theorems.Host.Reentrant.ScopedReentrantInvocation
import Exec.Spec.ExtensionTyping
namespace Exec.Theorems.ReentrantCallbacks
open Aeneas Aeneas.Std SpecExt

/-- A retained independently specified function instance. The source body,
module address map and signature are fixed; mutable store contents may vary. -/
def functionScope {M : Type} (view : M → Slice U8) (identity : Usize) (index : Nat) (source : funcinst) : WorldScope M :=
  fun code store=>store.id=identity ∧ (Store.decodeStore view code store).FUNCS[index]?=some source

theorem functionScope_stable {M : Type} (view : M → Slice U8) (identity : Usize) (index : Nat) (source : funcinst) :
    ScopeStable view (functionScope view identity index source) := by
  intro code before afterCode after metadata agrees extension held
  exact ⟨metadata.identity.trans held.1,Spec.function_lookup_extend extension held.2⟩

/-- Multiple retained function contracts compose as a single world condition. -/
theorem ScopeStable.and {M : Type} {view : M → Slice U8} {left right : WorldScope M}
    (a : ScopeStable view left) (b : ScopeStable view right) :
    ScopeStable view (fun code store=>left code store ∧ right code store) := by
  intro code before afterCode after metadata agrees extension held
  exact ⟨a code before afterCode after metadata agrees extension held.1,
    b code before afterCode after metadata agrees extension held.2⟩
end Exec.Theorems.ReentrantCallbacks
