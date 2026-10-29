import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Interp.Machine.Emission.Local

/-!
Inversion of local get/write emission.

Main declarations: `emission_localGet_pure` and `emission_localWrite_pure`. A direct consumer is `Interp.Machine.Local.ExecutionOwned`.
-/

namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std
theorem emission_localGet_pure {compiled C before after emitted} (index : Nat)
    (head : Interp.emission compiled C before (.LOCAL_GET (.mk_uN index)) emitted after) :
    Code.LinearEmission C.LOCALS before (.LOCAL_GET (.mk_uN index)) emitted after :=
  scalarEmission_localGet_pure index (FloatHeads.project (.core (.pure (.local_get _))) head)
theorem emission_localWrite_pure {compiled C before after emitted} (index : Nat) (keep : Bool)
    (head : Interp.emission compiled C before (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) emitted after) :
    Code.LinearEmission C.LOCALS before (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) emitted after :=
  scalarEmission_localWrite_pure index keep (FloatHeads.project (by cases keep;exact .core (.pure (.local_set _));exact .core (.pure (.local_tee _))) head)
end Itasca.Runtime.Interp.StructuredMachine
