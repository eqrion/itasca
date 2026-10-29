import Itasca.Runtime.Interp.Machine.Emission.Integer

/-!
Inversion of local get/write emission.

Main declarations: `scalar_emission_local_get_pure` and `scalar_emission_local_write_pure`. A direct consumer is `Interp.Machine.Local.Inversion`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem scalar_emission_local_get_pure {C before after emitted} (index : Nat)
    (emission : Compiler.ScalarEmission C before (.LOCAL_GET (.mk_uN index)) emitted after) :
    Compiler.LinearEmission C.LOCALS before (.LOCAL_GET (.mk_uN index)) emitted after := by
  generalize equality : instr.LOCAL_GET (.mk_uN index) = instruction at emission
  cases emission with
  | linear head => simpa only [←equality] using head
  | float stack other => cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
  | _ => simp_all [SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source]

theorem scalar_emission_local_write_pure {C before after emitted} (index : Nat) (keep : Bool)
    (emission : Compiler.ScalarEmission C before (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) emitted after) :
    Compiler.LinearEmission C.LOCALS before (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) emitted after := by
  generalize equality : (if keep then instr.LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) = instruction at emission
  cases emission with
  | linear head => simpa only [equality] using head
  | float stack other => cases keep <;> cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
  | _ => cases keep <;> simp_all [SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source]
end Itasca.Runtime.Interp
