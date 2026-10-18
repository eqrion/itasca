import Exec.Interp.FloatCore.Linear
import Exec.Interp.Core.LocalInversion
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem floatCoreEmission_localGet_pure {C before after emitted} (index : Nat)
    (emission : Code.FloatCoreEmission C before (.LOCAL_GET (.mk_uN index)) emitted after) :
    Code.LinearEmission C.LOCALS before (.LOCAL_GET (.mk_uN index)) emitted after :=
  coreEmission_localGet_pure index (emission.core_inv rfl)

theorem floatCoreEmission_localWrite_pure {C before after emitted} (index : Nat) (keep : Bool)
    (emission : Code.FloatCoreEmission C before (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) emitted after) :
    Code.LinearEmission C.LOCALS before (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) emitted after :=
  coreEmission_localWrite_pure index keep (emission.core_inv (by cases keep <;> rfl))
end Exec.Interp
