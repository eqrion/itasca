import Exec.Interp.StructuredMachine.SourceBase
import Exec.Theorems.Composition.IndirectCallShaped
import Exec.Theorems.Composition.IndirectCallLookup
import Exec.Theorems.Composition.Cumulative.CumulativeExecutionOutcome
import Exec.Interp.StructuredMachine.IndirectPoint
import Exec.Code.Local.Relations.Calls.IndirectCallExclusions
import Exec.Code.Local.Relations.Calls.IndirectCallInversion
import Exec.Interp.StructuredMachine.Execution
import Exec.Abs.Cumulative.Step
import Exec.Code.Local.Relations.Common.StatefulEmission
import Exec.Abs.Indirect.Operands
import Exec.Interp.StructuredMachine.Advance
import Exec.Interp.StructuredMachine.OrdinaryExecution
import Exec.Interp.Relations.CompiledFunctions
import Exec.Code.Local.Control.Common.CumulativeFunctionContext
import Exec.Interp.StructuredMachine.CompiledFunctions
import Exec.Code.Body.Control.Table.CumulativeTableExclusion
import Exec.Code.Local.Control.Common.Structured
import Exec.Code.Local.Control.Common.StructuredComposition
import Exec.Code.Local.Control.Table.StructuredCodePoint
import Exec.Interp.StructuredMachine.StructuredCall
import Exec.Interp.Calls.IndirectCallNext
import Exec.Abs.Indirect.Results
import Exec.Abs.Indirect.Correct
import Exec.Abs.Indirect.Transport
import Exec.Interp.Calls.IndirectCallSlots
import Exec.Interp.Relations.SourceIndirectCallCause
import Exec.Interp.Calls.IndirectResolve
import Exec.Interp.StructuredMachine.JumpExecution
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

def SourceIndirectHostBoundary {M : Type} (store : runtime.store.Store M) (source : Abs.AState) : Prop :=
  ∃ (f : Abs.AFrame) (rest : List Abs.AFrame) (table type position : Nat) (after : List instr) (front : List val)
    (address : Usize) (function : runtime.store.FuncInst) (host : U64),
    source.frames={f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest ∧
    f.vals=front++[Abs.integerVal .I32 position] ∧ position<2^32 ∧
    Abs.Indirect.resolve source.store f table type position=some address.val ∧
    store.funcs.val[address.val]?=some function ∧ function.code=.Host host

def IndirectTrap (trap : runtime.Trap) : Prop :=
  trap=.TableOutOfBounds ∨ trap=.UninitializedElement ∨ trap=.IndirectCallTypeMismatch

end Exec.Theorems
