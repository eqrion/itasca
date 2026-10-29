import Itasca.Runtime.Interp.Machine.Frames.SourceBase
import Itasca.Runtime.Integration.Execution.Dispatch.IndirectCall
import Itasca.Runtime.Integration.Execution.Dispatch.IndirectLookup
import Itasca.Runtime.Integration.Execution.Resources.Failure
import Itasca.Runtime.Interp.Machine.Calls.IndirectPoint
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallExclusions
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallInversion
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.SourceMachine.Cumulative.Step
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmission
import Itasca.Runtime.SourceMachine.Indirect.Operands
import Itasca.Runtime.Interp.Machine.Progress.Advance
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryExecution
import Itasca.Runtime.Interp.Relations.CompiledFunctions
import Itasca.Runtime.Compiler.Local.Control.Function.CumulativeFunctionContext
import Itasca.Runtime.Interp.Machine.Functions.CompiledFunctions
import Itasca.Runtime.Compiler.Body.Control.Table.CumulativeTableExclusion
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredCodePoint
import Itasca.Runtime.Interp.Machine.Calls.StructuredCall
import Itasca.Runtime.Interp.Calls.IndirectCallNext
import Itasca.Runtime.SourceMachine.Indirect.Results
import Itasca.Runtime.SourceMachine.Indirect.Correct
import Itasca.Runtime.SourceMachine.Indirect.Transport
import Itasca.Runtime.Interp.Calls.IndirectCallSlots
import Itasca.Runtime.Interp.Relations.SourceIndirectCallCause
import Itasca.Runtime.Interp.Calls.IndirectResolve
import Itasca.Runtime.Interp.Machine.Control.JumpExecution
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

def SourceIndirectHostBoundary {M : Type} (store : runtime.store.Store M) (source : SourceMachine.AState) : Prop :=
  ∃ (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (table type position : Nat) (after : List instr) (front : List val)
    (address : Usize) (function : runtime.store.FuncInst) (host : U64),
    source.frames={f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest ∧
    f.vals=front++[SourceMachine.integerVal .I32 position] ∧ position<2^32 ∧
    SourceMachine.Indirect.resolve source.store f table type position=some address.val ∧
    store.funcs.val[address.val]?=some function ∧ function.code=.Host host

def IndirectTrap (trap : runtime.Trap) : Prop :=
  trap=.TableOutOfBounds ∨ trap=.UninitializedElement ∨ trap=.IndirectCallTypeMismatch

end Itasca.Runtime.Integration
