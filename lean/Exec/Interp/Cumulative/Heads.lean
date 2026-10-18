import Exec.Interp.Cumulative.Machine
import Exec.Interp.StructuredMachine.FloatHeads
import Exec.Interp.StructuredMachine.ErasedHeads
namespace Exec.Interp.Cumulative

instance (compiled : runtime.bytecode.CompiledFunction) :
    StructuredMachine.FloatHeads (emission compiled) := by
  change StructuredMachine.FloatHeads (Code.CumulativeEmission compiled.indirect.val)
  infer_instance

instance (compiled : runtime.bytecode.CompiledFunction) :
    StructuredMachine.OrdinaryHeads (emission compiled) := by
  change StructuredMachine.OrdinaryHeads (Code.CumulativeEmission compiled.indirect.val)
  infer_instance

instance (compiled : runtime.bytecode.CompiledFunction) :
    StructuredMachine.ErasedHeads (emission compiled) := by
  change StructuredMachine.ErasedHeads (Code.CumulativeEmission compiled.indirect.val)
  infer_instance
end Exec.Interp.Cumulative
