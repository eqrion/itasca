import Itasca.Runtime.Interp.StructuredMachine.SourceBase
import Itasca.Runtime.Theorems.Composition.IndirectCallShaped
import Itasca.Runtime.Theorems.Composition.IndirectCallLookup
import Itasca.Runtime.Theorems.Composition.Cumulative.CumulativeExecutionOutcome
import Itasca.Runtime.Interp.StructuredMachine.IndirectPoint
import Itasca.Runtime.Code.Local.Relations.Calls.IndirectCallExclusions
import Itasca.Runtime.Code.Local.Relations.Calls.IndirectCallInversion
import Itasca.Runtime.Interp.StructuredMachine.Execution
import Itasca.Runtime.Abs.Cumulative.Step
import Itasca.Runtime.Code.Local.Relations.Common.StatefulEmission
import Itasca.Runtime.Abs.Indirect.Operands
import Itasca.Runtime.Interp.StructuredMachine.Advance
import Itasca.Runtime.Interp.StructuredMachine.OrdinaryExecution
import Itasca.Runtime.Interp.Relations.CompiledFunctions
import Itasca.Runtime.Code.Local.Control.Common.CumulativeFunctionContext
import Itasca.Runtime.Interp.StructuredMachine.CompiledFunctions
import Itasca.Runtime.Code.Body.Control.Table.CumulativeTableExclusion
import Itasca.Runtime.Code.Local.Control.Common.Structured
import Itasca.Runtime.Code.Local.Control.Common.StructuredComposition
import Itasca.Runtime.Code.Local.Control.Table.StructuredCodePoint
import Itasca.Runtime.Interp.StructuredMachine.StructuredCall
import Itasca.Runtime.Interp.Calls.IndirectCallNext
import Itasca.Runtime.Abs.Indirect.Results
import Itasca.Runtime.Abs.Indirect.Correct
import Itasca.Runtime.Abs.Indirect.Transport
import Itasca.Runtime.Interp.Calls.IndirectCallSlots
import Itasca.Runtime.Interp.Relations.SourceIndirectCallCause
import Itasca.Runtime.Interp.Calls.IndirectResolve
import Itasca.Runtime.Interp.StructuredMachine.JumpExecution
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

def SourceIndirectHostBoundary {M : Type} (store : runtime.store.Store M) (source : Abs.AState) : Prop :=
  ∃ (f : Abs.AFrame) (rest : List Abs.AFrame) (table type position : Nat) (after : List instr) (front : List val)
    (address : Usize) (function : runtime.store.FuncInst) (host : U64),
    source.frames={f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest ∧
    f.vals=front++[Abs.integerVal .I32 position] ∧ position<2^32 ∧
    Abs.Indirect.resolve source.store f table type position=some address.val ∧
    store.funcs.val[address.val]?=some function ∧ function.code=.Host host

def IndirectTrap (trap : runtime.Trap) : Prop :=
  trap=.TableOutOfBounds ∨ trap=.UninitializedElement ∨ trap=.IndirectCallTypeMismatch

end Itasca.Runtime.Theorems
