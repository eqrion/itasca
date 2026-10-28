import Itasca.Runtime.Theorems.Composition.Certified.CertifiedSupportedCode
import Itasca.Runtime.Interp.StructuredMachine.Execution
import Itasca.Runtime.Interp.Relations.FrameStorePrefix

namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std

/-- Changing ghost meanings only at unissued instance keys leaves the entire
active and suspended execution relation intact. No frame is reconstructed. -/
theorem Execution.change_code {M : Type} {view : M → Slice U8} {before after : Itasca.Runtime.Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {source : Itasca.Runtime.Abs.AState} {expected : List valtype} {pc : Nat} {pending : Bool}
    (held : Execution view before store exec source expected pc pending)
    (agrees : Itasca.Runtime.Store.CodeAgreesOn store before after) :
    Execution view after store exec source expected pc pending :=
  { held with storeEq := held.storeEq.trans (Itasca.Runtime.Store.decodeStore_code_agrees view agrees).symm }

end Itasca.Runtime.Interp.StructuredMachine

namespace Itasca.Runtime.Store
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
end Itasca.Runtime.Store
