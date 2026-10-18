import Exec.Abs.SimdCumulative
import Exec.Abs.CumulativeState
import Exec.Abs.Simd.Coverage

namespace Exec.Abs

abbrev FrameSimdCumulative := FrameSupported SimdCumulativeInstr
abbrev SimdCumulativeFunctions := FunctionsSupported SimdCumulativeInstr
abbrev SimdCumulativeState := SupportedState SimdCumulativeInstr

theorem CumulativeState.simd {s : AState} (covered : CumulativeState s) : SimdCumulativeState s := by
  have old : SupportedState CumulativeInstr s := ⟨covered.active,covered.functions⟩
  exact old.map (fun _ allowed => .cumulative allowed)

end Exec.Abs
