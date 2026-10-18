import Exec.Theorems.Api.ExecutableInv
namespace Exec.Theorems.ExecutableInv
open Aeneas Aeneas.Std

/-- Reinterpreting only fresh code keys preserves the complete public invariant. -/
theorem change_code {M : Type} {view : M → Slice U8}
    {before after : Store.CodeInterpretation} {store : runtime.store.Store M}
    (held : ExecutableInv view before store) (agrees : Store.CodeAgreesOn store before after) :
    ExecutableInv view after store :=
  ⟨held.toCertifiedApiStore.change_code agrees, held.segmentAccounting,
    held.capacities.code_agrees agrees⟩

theorem install_code {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (held : ExecutableInv view code store) (sources : List funccode) :
    ExecutableInv view (Store.installCode code store.instances.len.val sources) store :=
  held.change_code (Store.installCode_agrees store code sources)
end Exec.Theorems.ExecutableInv
