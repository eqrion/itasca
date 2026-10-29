import Itasca.Runtime.Compiler.Local.Capacity.BudgetEffects
import Itasca.Runtime.Compiler.Local.Capacity.CallbackCapacity
import Itasca.Runtime.Compiler.Local.Capacity.ScopeDemand
import Itasca.Runtime.Compiler.Local.Source.SourceControlBudget
import Itasca.Runtime.Compiler.Local.Source.SourceBudget
import Itasca.Runtime.Compiler.Local.Source.SourceLengths
import Itasca.Runtime.Compiler.Local.Demand.ObservationDemand
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerMetadata

/-!
Source compilation budgets and the body resource-room certificate. Source-only instruction demands bound callback requests and establish BodyResourceRoom for successful replay.
-/

/-! ## Source Budget Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- A source-byte allowance for every compiler counter, relative to the
already prepared function budget. Limits and retained errors are unchanged. -/
def SourceCompilationBudget {A : Type} (initial current : runtime.compiler.Budget A)
    (rate : ChargeCounter → Nat) (position : Nat) : Prop :=
  CompilationBudgetEffect initial current (fun counter => rate counter * position)

theorem SourceCompilationBudget.initial {A : Type} (initial : runtime.compiler.Budget A)
    (rate : ChargeCounter → Nat) : SourceCompilationBudget initial initial rate 0 := by
  simpa [SourceCompilationBudget] using CompilationBudgetEffect.refl initial

/-- Callback charges are paid by the independently consumed source span.
In particular table labels may consume many bytes within a single reader. -/
theorem SourceCompilationBudget.advance {A : Type}
    {initial before after : runtime.compiler.Budget A} {rate allowance : ChargeCounter → Nat}
    {start finish : Nat} (held : SourceCompilationBudget initial before rate start)
    (effect : CompilationBudgetEffect before after allowance)
    (consumed : start ≤ finish)
    (paid : ∀ counter, allowance counter ≤ rate counter * (finish-start)) :
    SourceCompilationBudget initial after rate finish := by
  apply (held.trans effect).weaken
  intro counter
  have room := paid counter
  have sum : rate counter * start + rate counter * (finish-start) = rate counter * finish := by
    rw [← Nat.mul_add,Nat.add_sub_of_le consumed]
  omega

/-- An output limit and a source-paid remaining span imply actual counter
headroom. No absence-of-exhaustion or accepted callback premise occurs here. -/
theorem SourceCompilationBudget.room {A : Type}
    {initial current : runtime.compiler.Budget A} {rate : ChargeCounter → Nat}
    {position length amount bytes : Nat}
    (held : SourceCompilationBudget initial current rate position) (counter : ChargeCounter)
    (limit : (counter.used initial).val + rate counter * length ≤ (counter.limit initial).val)
    (remaining : position+bytes ≤ length) (paid : amount ≤ rate counter * bytes) :
    (counter.used current).val + amount ≤ (counter.limit current).val := by
  have used := (held.counts counter).2
  have frames : counter.limit current = counter.limit initial := by
    cases counter <;> simp only [ChargeCounter.limit,held.limits]
  have span : rate counter * position + rate counter * bytes ≤ rate counter * length := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ remaining
  rw [frames]
  omega

end Itasca.Runtime.Compiler

end

/-! ## Source Callback Demand -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Multi-instruction callbacks use the same source footprint. Their larger
reserve and PC bounds are stated over source accounting, rather than a
successfully emitted branch sequence. -/
theorem callback_capacity_of_source {A : Type}
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
theorem scope_demand_of_source {A : Type}
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

end Itasca.Runtime.Compiler

end

/-! ## Body Resource Room -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Conservative per-byte charges after function-start preparation. Expanded
locals are charged separately at function start; body instructions add none. -/
abbrev bodyResourceRate : ChargeCounter → Nat
  | .instructions => 3 | .branches => 1 | .controls => 1 | .locals => 0

/-- Independent output ceilings and temporary-storage demand for one body.
The stack peak comes from independent validation; no successful compilation,
emitted code, or accepted compiler callback trace occurs in this record. -/
structure BodyResourceRoom {A : Type} (initial : runtime.compiler.FunctionCompiler A)
    (length peak bound : Nat) : Prop where
  size : length ≤ limits.MAX_FUNCTION_BYTES.val
  counters : ∀ counter, (counter.used initial.budget).val + bodyResourceRate counter * length ≤
    (counter.limit initial.budget).val
  temporary : 3*length+3 ≤ bound
  operands : peak ≤ bound
  slots : initial.function.local_slots.val+2*peak ≤ U32.max
  coordinate : initial.function.body_start.val+length ≤ Usize.max

theorem BodyResourceRoom.source_bound {A : Type} {initial : runtime.compiler.FunctionCompiler A}
    {length peak bound} (room : BodyResourceRoom initial length peak bound) :
    length ≤ limits.MAX_MODULE_BYTES.val := by
  have size := room.size
  norm_num [limits.MAX_FUNCTION_BYTES,limits.MAX_MODULE_BYTES] at size ⊢
  omega

theorem BodyResourceRoom.pc {A : Type} {initial : runtime.compiler.FunctionCompiler A}
    {length peak bound} (room : BodyResourceRoom initial length peak bound) :
    3*length+3 ≤ U32.max := by
  have size := room.size
  norm_num [limits.MAX_FUNCTION_BYTES,U32.max_eq] at size ⊢
  omega

/-- Any source-paid span gives actual instruction, reserve, PC, coordinate,
and observed-stack capacity for a multi-instruction compiler callback. -/
theorem BodyResourceRoom.capacity {A : Type}
    {initial compiler : runtime.compiler.FunctionCompiler A} {length peak bound position count bytes}
    (room : BodyResourceRoom initial length peak bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate position)
    (metadata : CompilerStable initial compiler) (codeBudget : SourceCodeBudget compiler position)
    (sources : SourceAligned compiler) (cursor : compiler.next_source.val ≤ position)
    (remaining : position+bytes ≤ length) (paid : count ≤ 3*bytes)
    (state : code.OpIterState) (operands : state.vals.length ≤ peak) :
    CallbackCapacity compiler state bound count := by
  obtain ⟨_,_,_,_,_,_,localSlots,bodyStart,_⟩ := metadata.fields
  have instructionRoom := budget.room .instructions (room.counters .instructions) remaining paid
  have pc := room.pc
  have reserve := room.temporary
  have coordinate := room.coordinate
  have slots := room.slots
  have compilerCoordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max := by
    rw [bodyStart]
    omega
  have compilerSlots : compiler.function.local_slots.val+2*peak ≤ U32.max := by
    rw [localSlots]
    exact slots
  exact callback_capacity_of_source compiler state bound position peak count codeBudget sources
    (by omega) (by omega) compilerCoordinate instructionRoom operands room.operands compilerSlots

/-- Every ordinary callback is paid by its opcode byte. Its resource demand
is constructed from the source prefix and independent stack peak. -/
theorem BodyResourceRoom.demand {A : Type}
    {initial compiler : runtime.compiler.FunctionCompiler A} {length peak bound position}
    (room : BodyResourceRoom initial length peak bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate position)
    (metadata : CompilerStable initial compiler) (codeBudget : SourceCodeBudget compiler position)
    (sources : SourceAligned compiler) (cursor : compiler.next_source.val ≤ position)
    (remaining : position < length) (state : code.OpIterState) (operands : state.vals.length ≤ peak) :
    CallbackDemand compiler state bound :=
  (room.capacity budget metadata codeBudget sources cursor (count := 1) (bytes := 1) (by omega) (by decide) state operands).one (by decide)

/-- A structured opener additionally pays its control charge and both map
and frame reserves from source control accounting. -/
theorem BodyResourceRoom.scope {A : Type}
    {initial compiler : runtime.compiler.FunctionCompiler A} {length peak bound position}
    (room : BodyResourceRoom initial length peak bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate position)
    (metadata : CompilerStable initial compiler) (codeBudget : SourceCodeBudget compiler position)
    (sources : SourceAligned compiler) (cursor : compiler.next_source.val ≤ position)
    (controls : SourceControlBudget compiler position) (remaining : position < length)
    (state : code.OpIterState) (operands : state.vals.length ≤ peak) : ScopeDemand compiler state bound := by
  have demand := room.demand budget metadata codeBudget sources cursor remaining state operands
  have controlRoom := budget.room .controls (room.counters .controls) (bytes := 1) (amount := 1)
    (by omega) (by decide)
  change compiler.budget.controls.val+1 ≤ compiler.budget.limits.max_controls.val at controlRoom
  exact scope_demand_of_source compiler state bound position demand controls
    ((Nat.le_of_lt remaining).trans room.source_bound) (by have reserve := room.temporary; omega) (by omega)

end Itasca.Runtime.Compiler

end
