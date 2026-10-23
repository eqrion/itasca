import Exec.Interp.Core.Linear
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem scalarEmission_localGet_pure {C before after emitted} (index : Nat)
    (emission : Code.ScalarEmission C before (.LOCAL_GET (.mk_uN index)) emitted after) :
    Code.LinearEmission C.LOCALS before (.LOCAL_GET (.mk_uN index)) emitted after := by
  generalize equality : instr.LOCAL_GET (.mk_uN index) = instruction at emission
  cases emission with
  | linear head => simpa only [←equality] using head
  | float stack other => cases other <;> simp [Abs.Float.Instruction.source,Abs.Memory.Load.source,Abs.Memory.Store.source] at equality
  | _ => simp_all [Abs.Memory.Load.source,Abs.Memory.Store.source]

theorem scalarEmission_localWrite_pure {C before after emitted} (index : Nat) (keep : Bool)
    (emission : Code.ScalarEmission C before (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) emitted after) :
    Code.LinearEmission C.LOCALS before (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) emitted after := by
  generalize equality : (if keep then instr.LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) = instruction at emission
  cases emission with
  | linear head => simpa only [equality] using head
  | float stack other => cases keep <;> cases other <;> simp [Abs.Float.Instruction.source,Abs.Memory.Load.source,Abs.Memory.Store.source] at equality
  | _ => cases keep <;> simp_all [Abs.Memory.Load.source,Abs.Memory.Store.source]
end Exec.Interp
