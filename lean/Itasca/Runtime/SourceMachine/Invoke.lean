import Itasca.Runtime.SourceMachine.Sim.Step
import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.SourceMachine.Sim.Terminal

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

def entryState (s : store) (ambient : frame) (address : funcaddr)
    (moduleInst : moduleinst) (results : List valtype) (body : List instr)
    (args defaults : List val) : AState :=
  ⟨s, ambient, [⟨address, results, args ++ defaults, moduleInst,
    [⟨results, results, [], 0, []⟩], body, []⟩], []⟩

end Itasca.Runtime.SourceMachine
