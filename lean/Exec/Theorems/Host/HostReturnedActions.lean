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

end Exec.Theorems
