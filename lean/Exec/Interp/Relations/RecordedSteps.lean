import Exec.Interp.Relations.StepRecording
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt

/-- Execute at most `count` actual dispatches, stopping at the first reported
error and carrying the callsite log through every step. -/
def recordedSteps {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) :
    Nat → runtime.interp.Execution → runtime.store.Store M → P → List HostEvent →
      Result ((core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) × List HostEvent)
  | 0,exec,store,platform,prior => .ok ((.Ok (),exec,store,platform),prior)
  | count+1,exec,store,platform,prior => do
      let (out,trace) ← recordedStep memory hooks floats allocator exec store platform prior
      match out.1 with
      | .Err _ => .ok (out,trace)
      | .Ok _ => recordedSteps memory hooks floats allocator count out.2.1 out.2.2.1 out.2.2.2 trace
end Exec.Interp
