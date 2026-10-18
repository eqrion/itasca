import Exec.Interp.Core.Linear
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem coreEmission_localGet_pure {C before after emitted} (index : Nat)
    (emission : Code.CoreEmission C before (.LOCAL_GET (.mk_uN index)) emitted after) :
    Code.LinearEmission C.LOCALS before (.LOCAL_GET (.mk_uN index)) emitted after := by
  generalize equality : instr.LOCAL_GET (.mk_uN index) = instruction at emission
  cases emission with
  | pure head => simpa only [←equality] using head
  | _ => simp_all [Abs.Memory.Load.source,Abs.Memory.Store.source]

theorem coreEmission_localWrite_pure {C before after emitted} (index : Nat) (keep : Bool)
    (emission : Code.CoreEmission C before (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) emitted after) :
    Code.LinearEmission C.LOCALS before (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) emitted after := by
  generalize equality : (if keep then instr.LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) = instruction at emission
  cases emission with
  | pure head => simpa only [equality] using head
  | _ => cases keep <;> simp_all [Abs.Memory.Load.source,Abs.Memory.Store.source]
end Exec.Interp
