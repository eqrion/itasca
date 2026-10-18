import Exec.Interp.Machines.Cumulative.CumulativeHeadCoverage
import Exec.Abs.Simd.Source
namespace Exec.Interp

/-- Head families with a checked generic machine execution join. -/
inductive SupportedDispatchHead : instr → Prop where
  | cumulative {op} : CumulativeDispatchHead op → SupportedDispatchHead op
  | simd {op} : Abs.SimdInstr op → SupportedDispatchHead op
  | typedSelect (ty : valtype) : SupportedDispatchHead (.SELECT (some [ty]))

  | branchTable (depths : List labelidx) (fallback : labelidx) : SupportedDispatchHead (.BR_TABLE depths fallback)
end Exec.Interp
