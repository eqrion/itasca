import Exec.Abs.Indirect.Correct
import Exec.Abs.Indirect.Transport
import Exec.Abs.Supported.CoreStuck
import Exec.Abs.Core.Pure
import Exec.Abs.Core.Correct
import Exec.Abs.Ownership.Core
import Exec.Abs.Core.Bound
import Exec.Abs.Core.Terminal
import Exec.Abs.Core.Extension
import Exec.Abs.Core.Step
import Exec.Abs.Cumulative.Heap
import Exec.Abs.Stateful.Bound
import Exec.Abs.Float.Transition
import Exec.Abs.Core
import Exec.Abs.Float.Decode
import Exec.Abs.Numeric.Effect
import Exec.Abs.StepSafety
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
