import Itasca.Runtime.Code.Local.Capacity.SourceCallbackDemand
import Itasca.Runtime.Code.Local.Callbacks.Common.CompilerMetadata

namespace Itasca.Runtime.Code
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
  exact callbackCapacity_of_source compiler state bound position peak count codeBudget sources
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
  exact scopeDemand_of_source compiler state bound position demand controls
    ((Nat.le_of_lt remaining).trans room.source_bound) (by have reserve := room.temporary; omega) (by omega)

end Itasca.Runtime.Code
