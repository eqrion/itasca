import Exec.Theorems.Composition.Certified.CertifiedSupportedCode
import Exec.Interp.StructuredMachine.Execution
import Exec.Interp.Relations.FrameStorePrefix

namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std

/-- Changing ghost meanings only at unissued instance keys leaves the entire
active and suspended execution relation intact. No frame is reconstructed. -/
theorem Execution.change_code {emission : FunctionEmission} {supported : Exec.Abs.AState → Prop}
    {M : Type} {view : M → Slice U8} {before after : Exec.Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {source : Exec.Abs.AState} {expected : List valtype} {pc : Nat} {pending : Bool}
    (held : Execution emission supported view before store exec source expected pc pending)
    (agrees : Exec.Store.CodeAgreesOn store before after) :
    Execution emission supported view after store exec source expected pc pending :=
  { held with storeEq := held.storeEq.trans (Exec.Store.decodeStore_code_agrees view agrees).symm }

end Exec.Interp.StructuredMachine

namespace Exec.Store
open Aeneas Aeneas.Std

/-- Agreement on old issued keys composes through actual retained instances. -/
theorem CodeAgreesOn.trans_prefix {M : Type} {before middle : runtime.store.Store M}
    {first second third : CodeInterpretation}
    (left : CodeAgreesOn before first second)
    (retained : Interp.FrameStorePrefix before middle)
    (right : CodeAgreesOn middle second third) : CodeAgreesOn before first third := by
  intro index inst found function
  exact (right index inst (retained.instance_lookup found) function).trans
    (left index inst found function)
end Exec.Store
