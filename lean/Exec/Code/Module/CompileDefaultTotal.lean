import Exec.Code.Module.CompileTotalDriver
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
open runtime.compiler

@[step] theorem compiler_default_limits_total :
    CompileLimits.Insts.CoreDefaultDefault.default ⦃ _ => True ⦄ := by
  unfold CompileLimits.Insts.CoreDefaultDefault.default
  step
  step

end Itasca.Runtime.Code
