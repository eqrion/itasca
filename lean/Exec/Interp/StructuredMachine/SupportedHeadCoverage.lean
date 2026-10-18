import Exec.Interp.StructuredMachine.SupportedHead
import Exec.Interp.StructuredMachine.Point
import Exec.Code.Body.Lowering.Simd.SimdEmissionExclusion
import Exec.Code.Local.Source.TypedSelectEmission
namespace Exec.Interp.StructuredMachine
open Aeneas.Std

/-- Static emission syntax classifies each retained non-erased linear head. -/
class SupportedHeads (emission : ContextEmission) : Prop where
  head : ∀ {C stack source emitted output}, ReadyInstruction source →
    emission C stack source emitted output → SupportedDispatchHead source

instance (pairs : List (U32 × U32)) : SupportedHeads (Code.CumulativeEmission pairs) where
  head ready head := by
    cases head with
    | left head => cases head with
      | core original => exact .cumulative (.core (coreEmission_ready_head original ready))
      | scalar => exact .cumulative (.scalar _)
    | right head => cases head; exact .cumulative (.stateful _)
    | indirect head => cases head; exact .cumulative (.indirect _ _)

instance (tables : Code.CompilerTables) : SupportedHeads (Code.SimdCumulativeEmission tables) where
  head ready head := by
    cases head with
    | left head => exact SupportedHeads.head ready head
    | right head => exact .simd head.allowed

instance : SupportedHeads Code.TypedSelectEmission where
  head ready head := by cases head; exact .typedSelect _

variable {jumpTables : List Aeneas.Std.U32}
theorem code_head_coverage {emission : ContextEmission} [SupportedHeads emission]
    {C returns locals code labels stack op source next output}
    (ready : ReadyInstruction op) :
    ∀ pc, Code.StructuredCodeWithTables (emission C) C.TYPES C.FUNCS returns locals code jumpTables labels stack
      (op::source) pc next output → SupportedDispatchHead op := by
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
    | loop => exact .cumulative (.core (.pure (.loop _ _)))
    | ifElse => exact .cumulative (.core (.pure (.ordinary (.ifElse _ _ _))))
    | branch => exact .cumulative (.core (.pure (.ordinary (.branch _))))
    | branchIf => exact .cumulative (.core (.pure (.ordinary (.branchIf _))))
    | call => exact .cumulative (.core (.pure (.call _)))
    | unreachable => exact .cumulative (.core (.pure .unreachable))
    | return_ => exact .cumulative (.core (.pure .return_))
    | branchTable => exact .branchTable _ _

theorem frame_head_coverage {emission : FunctionEmission} {sourceStore raw f compiled C targets next output}
    [SupportedHeads (emission compiled)]
    (point : FramePoint emission sourceStore raw f compiled C targets next output)
    (ready : ReadySource f) (op : instr) (after : List instr) (code : f.code=op::after) :
    SupportedDispatchHead op := by
  have readyOp : ReadyInstruction op := by
    cases op <;> simp_all only [ReadyInstruction,ReadySource,code]
  exact code_head_coverage readyOp raw.pc.val (by simpa only [code] using point.code.current)
end Exec.Interp.StructuredMachine
