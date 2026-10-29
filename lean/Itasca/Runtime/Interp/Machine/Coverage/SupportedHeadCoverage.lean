import Itasca.Runtime.Interp.Machine.Coverage.Heads
import Itasca.Runtime.Interp.Relations.HeadCoverage
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.SourceMachine.ModuleBindingsExtension
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.SourceMachine.Cumulative.Step
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmission
import Itasca.Runtime.Compiler.Body.Control.Table.CumulativeTableExclusion
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredCodePoint
import Itasca.Runtime.Interp.Machine.Point
import Itasca.Runtime.Compiler.Body.Lowering.Simd.SimdEmissionExclusion
import Itasca.Runtime.Compiler.Local.Source.TypedSelectEmission

/-!
Static emission syntax classifies each retained non-erased linear head.

Main declarations: `SupportedHeads`. A direct consumer is `Interp.Machine.Coverage.RecordingHeads`.
-/

namespace Itasca.Runtime.Interp
open Aeneas.Std

theorem linearEmission_ready_head {locals before op emitted after}
    (head : Code.LinearEmission locals before op emitted after)
    (ready : ReadyInstruction op) : DispatchHead op := by
  cases head with
  | nop => exact False.elim ready
  | drop => exact False.elim ready
  | const32 stack dst word slot => exact .ordinary (.const32 word)
  | const64 stack dst word slot => exact .ordinary (.const64 word)
  | binary stack ty binary a b left right =>
    cases binary with
    | add => exact .ordinary (.binary ty .add)
    | sub => exact .ordinary (.binary ty .sub)
    | eq => exact .ordinary (.binary ty .eq)
    | ltU => exact .ordinary (.binary ty .ltU)
    | mul => exact .numeric (.binary ty .MUL)
    | ne => exact .numeric (.compare ty .NE)
    | gtU => exact .numeric (.compare ty (.GT .U))
    | leU => exact .numeric (.compare ty (.LE .U))
    | geU => exact .numeric (.compare ty (.GE .U))
  | numeric stack op a b left right => exact .numeric op
  | eqz32 stack a slot => exact .ordinary (.eqz .I32)
  | eqz64 stack a slot => exact .ordinary (.eqz .I64)
  | localGet stack ty index src dst localType localPos stackPos => exact .ordinary (.localGet index)
  | localSet stack ty index dst src localType localPos stackPos => exact .ordinary (.localWrite index false)
  | localTee stack ty index dst src localType localPos stackPos => exact .ordinary (.localWrite index true)

theorem scalarEmission_ready_head {C before op emitted after}
    (head : Code.ScalarEmission C before op emitted after)
    (ready : ReadyInstruction op) : DispatchHead op := by
  cases head with
  | linear original => exact linearEmission_ready_head original ready
  | float32 stack dst bits slot => exact .float32 bits
  | float64 stack dst bits slot => exact .float64 bits
  | select => exact .select
  | globalGet stack mutability ty index dst globalType slot => exact .globalGet index
  | globalSet stack ty index src globalType slot => exact .globalSet index
  | load stack op argument address offset memory available sourceOffset slot => exact .load op argument
  | store stack op argument address value offset memory available sourceOffset addressSlot valueSlot => exact .store op argument
  | float stack op => exact .float op

end Itasca.Runtime.Interp

namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas.Std

/-- Static emission syntax classifies each retained non-erased linear head. -/
class SupportedHeads (emission : ContextEmission) : Prop where
  head : ∀ {C stack source emitted output}, ReadyInstruction source →
    emission C stack source emitted output → DispatchHead source

variable {jumpTables : List Aeneas.Std.U32}
theorem code_head_coverage {emission : ContextEmission} [SupportedHeads emission]
    {C returns locals code labels stack op source next output}
    (ready : ReadyInstruction op) :
    ∀ pc, Code.StructuredCode (emission C) C.TYPES C.FUNCS returns locals code jumpTables labels stack
      (op::source) pc next output → DispatchHead op := by
  intro pc relation
  generalize measureEq : code.length-pc = measure
  induction measure using Nat.strong_induction_on generalizing pc with
  | h measure ih =>
    cases relation with
    | linear head ordinary fragment rest => exact SupportedHeads.head ready head
    | skip forward fetched rest =>
      have bound := rest.entry_bound
      exact ih _ (by omega) _ rest rfl
    | block => exact False.elim ready
    | loop => exact .loop _ _
    | ifElse => exact .ordinary (.ifElse _ _ _)
    | branch => exact .ordinary (.branch _)
    | branchIf => exact .ordinary (.branchIf _)
    | call => exact .call _
    | unreachable => exact .unreachable
    | return_ => exact .return_
    | branchTable => exact .branchTable _ _

/-- Every non-erased head of the complete compiler relation selects a proved
machine branch. Branch-table layout itself is supplied by the indexed point. -/
instance (tables : Code.CompilerTables) : SupportedHeads (Code.ExecutableEmission tables) where
  head := by
    intro C stack source emitted output ready head
    cases head with
    | scalar h => exact scalarEmission_ready_head h ready
    | stateful h => cases h; exact .stateful _
    | indirect h => cases h; exact .indirect _ _
    | simd h => exact .simd h.allowed
    | typedSelect h => cases h; exact .typedSelect _
    | branchTable stack depths fallback selector start len => exact .branchTable depths fallback

theorem frame_head_coverage {sourceStore raw f compiled C targets next output}
    [SupportedHeads (emission compiled)]
    (point : FramePoint sourceStore raw f compiled C targets next output)
    (ready : ReadySource f) (op : instr) (after : List instr) (code : f.code=op::after) :
    DispatchHead op := by
  have readyOp : ReadyInstruction op := by
    cases op <;> simp_all only [ReadyInstruction,ReadySource,code]
  exact code_head_coverage readyOp raw.pc.val (by simpa only [code] using point.code.current)
end Itasca.Runtime.Interp.StructuredMachine
