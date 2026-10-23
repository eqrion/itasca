import Exec.Theorems.Host.HostWorldSound
import Exec.Spec.Extend
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

/-- Store effects retained by returned public actions. This is a conclusion of
an action's proof, not a law imposed on arbitrary callbacks. -/
structure ReturnedWorldEffect {M : Type} (view : M → Slice U8)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (beforeCode : Store.CodeInterpretation) (before : runtime.store.Store M)
    (afterCode : Store.CodeInterpretation) (after : runtime.store.Store M) : Prop where
  agrees : Store.CodeAgreesOn before beforeCode afterCode
  invariant : Inv afterCode after
  metadata : FrameStorePrefix before after
  extension : Extend_store (Store.decodeStore view beforeCode before) (Store.decodeStore view afterCode after)

theorem ReturnedWorldEffect.refl {M : Type} {view : M → Slice U8}
    {Inv : Store.CodeInterpretation → runtime.store.Store M → Prop}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (valid : Inv code store) (wellFormed : wf_store (Store.decodeStore view code store)) :
    ReturnedWorldEffect view Inv code store code store :=
  ⟨(by intro index inst found fn; rfl),valid,.refl _,Spec.extend_store_refl _ wellFormed⟩

theorem ReturnedWorldEffect.trans {M : Type} {view : M → Slice U8}
    {Inv : Store.CodeInterpretation → runtime.store.Store M → Prop}
    {a b c : Store.CodeInterpretation} {s t u : runtime.store.Store M}
    (first : ReturnedWorldEffect view Inv a s b t)
    (second : ReturnedWorldEffect view Inv b t c u) : ReturnedWorldEffect view Inv a s c u :=
  ⟨first.agrees.trans_prefix first.metadata second.agrees,second.invariant,
    first.metadata.trans second.metadata,Spec.extend_store_trans first.extension second.extension⟩

end Exec.Theorems
