import Itasca.Runtime.SourceMachine.Indirect.Correct
import Itasca.Runtime.SourceMachine.Indirect.Transport
import Itasca.Runtime.SourceMachine.Supported.CoreStuck
import Itasca.Runtime.SourceMachine.Core.Pure
import Itasca.Runtime.SourceMachine.Core.Correct
import Itasca.Runtime.SourceMachine.Ownership.Core
import Itasca.Runtime.SourceMachine.Core.Bound
import Itasca.Runtime.SourceMachine.Core.Terminal
import Itasca.Runtime.SourceMachine.Core.Extension
import Itasca.Runtime.SourceMachine.Core.Step
import Itasca.Runtime.SourceMachine.Cumulative.Heap
import Itasca.Runtime.SourceMachine.Stateful.Bound
import Itasca.Runtime.SourceMachine.Float.Transition
import Itasca.Runtime.SourceMachine.Core
import Itasca.Runtime.SourceMachine.Float.Descriptor
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.StepSafety
namespace Itasca.Runtime.Abs.Cumulative
open SpecExt Itasca.Runtime.Spec Itasca.Runtime.Abs.Ownership

/-- Executable source transitions combine the deterministic mutable core with
the complete float result relation, preserving every permitted NaN result. -/
inductive Step : AState → AResult → Prop where
  | core {before result} (equation : Core.step before = result) (executable : result ≠ .stuck) : Step before result
  | scalar {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {op : Float.Instruction} {result : AResult}
      (transition : Float.Transition ⟨s,ambient,{f with code := op.source :: after}::rest,[]⟩
        {f with code := op.source :: after} rest after op result) :
      Step ⟨s,ambient,{f with code := op.source :: after}::rest,[]⟩ result

  | stateful {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {op : Stateful.Instruction} {result : AResult}
      (transition : Stateful.Transition ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩
        {f with code := op.source::after} rest after op result)
      (executable : result ≠ .stuck) :
      Step ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ result

  | indirect {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {table type : Nat} {result : AResult}
      (equation : Indirect.step ⟨s,ambient,{f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩
        f rest table type after = result) (executable : result ≠ .stuck) :
      Step ⟨s,ambient,{f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ result

end Itasca.Runtime.Abs.Cumulative
