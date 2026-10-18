import Exec.Interp.StructuredMachine.FloatHeads
import Exec.Interp.FloatCore.LocalInversion
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std
variable {emission : FunctionEmission} [∀ compiled, FloatHeads (emission compiled)]
theorem emission_localGet_pure {compiled C before after emitted} (index : Nat)
    (head : emission compiled C before (.LOCAL_GET (.mk_uN index)) emitted after) :
    Code.LinearEmission C.LOCALS before (.LOCAL_GET (.mk_uN index)) emitted after :=
  floatCoreEmission_localGet_pure index (FloatHeads.project (.core (.slice (.local_get _))) head)
theorem emission_localWrite_pure {compiled C before after emitted} (index : Nat) (keep : Bool)
    (head : emission compiled C before (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) emitted after) :
    Code.LinearEmission C.LOCALS before (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) emitted after :=
  floatCoreEmission_localWrite_pure index keep (FloatHeads.project (by cases keep;exact .core (.slice (.local_set _));exact .core (.slice (.local_tee _))) head)
end Exec.Interp.StructuredMachine
