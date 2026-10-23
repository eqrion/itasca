import Exec.Code.Local.Capacity.CallbackCapacity
import Exec.Code.Local.Capacity.ScopeDemand
import Exec.Code.Local.Source.SourceControlBudget
import Exec.Code.Local.Capacity.SourceBudgetAvailability
import Exec.Code.Local.Source.SourceBudget
import Exec.Code.Local.Source.SourceLengths
import Exec.Code.Local.Demand.ObservationDemand

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Multi-instruction callbacks use the same source footprint. Their larger
reserve and PC bounds are stated over source accounting, rather than a
successfully emitted branch sequence. -/
theorem callbackCapacity_of_source {A : Type}
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (bound position peak count : Nat)
    (code : SourceCodeBudget compiler position) (sources : SourceAligned compiler)
    (pc : 3*position+count ≤ U32.max) (reserve : 3*position+count ≤ bound)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max)
    (instructions : compiler.budget.instructions.val+count ≤ compiler.budget.limits.max_instructions.val)
    (operands : state.vals.length ≤ peak) (temporary : peak ≤ bound)
    (slots : compiler.function.local_slots.val+2*peak ≤ U32.max) :
    CallbackCapacity compiler state bound count := by
  have bytes : compiler.function.code.length ≤ 3*position := code
  have aligned : compiler.function.source_offsets.length = compiler.function.code.length := sources
  have machine : U32.max ≤ Usize.max := by scalar_tac
  constructor <;> simp only [alloc.vec.Vec.length] at * <;> omega

/-- Source control accounting bounds every scope map and physical frame
reserve, including maps retained after their corresponding frames close. -/
theorem scopeDemand_of_source {A : Type}
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (bound position : Nat) (demand : CallbackDemand compiler state bound)
    (controls : SourceControlBudget compiler position)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (reserve : position+2 ≤ bound)
    (room : compiler.budget.controls.val < compiler.budget.limits.max_controls.val) :
    ScopeDemand compiler state bound := by
  obtain ⟨maps,frames⟩ := controls.capacities sourceBound
  have count := controls.maps
  have nested := controls.frames
  refine ⟨demand.pc,demand.coordinate,maps,?_,frames,?_,room,demand.operands,demand.slots⟩ <;>
    simp only [alloc.vec.Vec.length] <;> omega

end Exec.Code
