import Exec.Interp.Numeric.Float.FloatPoint
import Exec.Interp.Core.Linear
import Exec.Interp.Core.EmptyInversion
import Exec.Code.Local.Lowering.Float.FloatCoreProjection
namespace Exec.Interp
open Aeneas.Std

theorem floatCoreEmission_nop_pure {C before after emitted}
    (emission : Code.FloatCoreEmission C before .NOP emitted after) :
    Code.LinearEmission C.LOCALS before .NOP emitted after :=
  coreEmission_nop_pure (emission.core_inv rfl)

theorem floatCoreEmission_drop_pure {C before after emitted}
    (emission : Code.FloatCoreEmission C before .DROP emitted after) :
    Code.LinearEmission C.LOCALS before .DROP emitted after :=
  coreEmission_drop_pure (emission.core_inv rfl)
end Exec.Interp
