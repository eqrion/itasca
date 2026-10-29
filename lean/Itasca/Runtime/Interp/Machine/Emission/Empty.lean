import Itasca.Runtime.Interp.Machine.Emission.Integer

/-!
Pure scalar-emission inversion for nop and drop.

Main declarations: `scalarEmission_nop_pure` and `scalarEmission_drop_pure`. A direct consumer is `Interp.Machine.Coverage.Heads`.
-/

namespace Itasca.Runtime.Interp
open Aeneas.Std

theorem scalarEmission_nop_pure {C before after emitted}
    (emission : Code.ScalarEmission C before .NOP emitted after) :
    Code.LinearEmission C.LOCALS before .NOP emitted after := by
  generalize equality : instr.NOP = instruction at emission
  cases emission with
  | linear head => simpa only [←equality] using head
  | float stack other => cases other <;> simp [Abs.Float.Instruction.source,Abs.Memory.Load.source,Abs.Memory.Store.source] at equality
  | _ => simp_all [Abs.Memory.Load.source,Abs.Memory.Store.source]

theorem scalarEmission_drop_pure {C before after emitted}
    (emission : Code.ScalarEmission C before .DROP emitted after) :
    Code.LinearEmission C.LOCALS before .DROP emitted after := by
  generalize equality : instr.DROP = instruction at emission
  cases emission with
  | linear head => simpa only [←equality] using head
  | float stack other => cases other <;> simp [Abs.Float.Instruction.source,Abs.Memory.Load.source,Abs.Memory.Store.source] at equality
  | _ => simp_all [Abs.Memory.Load.source,Abs.Memory.Store.source]

end Itasca.Runtime.Interp
