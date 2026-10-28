import Exec.Abs.PureHead
import Exec.Abs.Memory.Descriptor
import Exec.Abs.Float.Descriptor

namespace Itasca.Runtime.Abs

/-- Source heads executed by `Core.instruction`: the `astep` heads, plus constants,
select and the global and memory accesses it resolves against the store. -/
inductive CoreHead : instr → Prop where
  | pure {source} : PureHead source → CoreHead source
  | const (ty : numtype) (value : num_) : CoreHead (.CONST ty value)
  | select : CoreHead (.SELECT none)
  | global_get (index : idx) : CoreHead (.GLOBAL_GET index)
  | global_set (index : idx) : CoreHead (.GLOBAL_SET index)
  | load (op : Memory.Load) (argument : memarg) : CoreHead (op.source argument)
  | store (op : Memory.Store) (argument : memarg) : CoreHead (op.source argument)

/-- Source heads lowered by the scalar emitter: `CoreHead` and scalar float operations. -/
inductive ScalarHead : instr → Prop where
  | core {source} : CoreHead source → ScalarHead source
  | float (op : Float.Instruction) : ScalarHead op.source

end Itasca.Runtime.Abs
