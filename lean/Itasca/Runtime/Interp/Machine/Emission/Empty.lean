import Itasca.Runtime.Interp.Machine.Emission.Integer

/-!
Pure scalar-emission inversion for nop and drop.

Main declarations: `scalar_emission_nop_pure` and `scalar_emission_drop_pure`. A direct consumer is `Interp.Machine.Coverage.Heads`.
-/

namespace Itasca.Runtime.Interp
open Aeneas.Std

theorem scalar_emission_nop_pure {C before after emitted}
    (emission : Compiler.ScalarEmission C before .NOP emitted after) :
    Compiler.LinearEmission C.LOCALS before .NOP emitted after := by
  generalize equality : instr.NOP = instruction at emission
  cases emission with
  | linear head => simpa only [←equality] using head
  | float stack other => cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
  | _ => simp_all [SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source]

theorem scalar_emission_drop_pure {C before after emitted}
    (emission : Compiler.ScalarEmission C before .DROP emitted after) :
    Compiler.LinearEmission C.LOCALS before .DROP emitted after := by
  generalize equality : instr.DROP = instruction at emission
  cases emission with
  | linear head => simpa only [←equality] using head
  | float stack other => cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
  | _ => simp_all [SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source]

end Itasca.Runtime.Interp
