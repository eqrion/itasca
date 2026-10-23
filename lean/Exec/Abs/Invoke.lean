import Exec.Abs.Sim.Step
import Exec.Abs.Bound
import Exec.Abs.Sim.Terminal

namespace Exec.Abs
open SpecExt Exec.Spec

def entryState (s : store) (ambient : frame) (address : funcaddr)
    (moduleInst : moduleinst) (results : List valtype) (body : List instr)
    (args defaults : List val) : AState :=
  ⟨s, ambient, [⟨address, results, args ++ defaults, moduleInst,
    [⟨results, results, [], 0, []⟩], body, []⟩], []⟩

end Exec.Abs
