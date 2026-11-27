import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchContracts
import Itasca.Runtime.Compiler.Local.Lowering.Emission.CopyContracts
import Itasca.Runtime.Compiler.Local.Capacity.AuxiliaryGrowth
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Frame
import Itasca.Runtime.Compiler.Local.Lowering.Integer.OperandEffects
import Itasca.Runtime.Compiler.Local.Lowering.Float.LoweringAndEffects
import Itasca.Runtime.Compiler.Local.Source.TypedRunClosed
import Itasca.Runtime.Compiler.Local.Source.SourceTactics
import Itasca.Runtime.Compiler.Local.IndependentBodyDemand
import Itasca.Runtime.Compiler.Local.Callbacks.MetadataPreservation
import Itasca.Runtime.Compiler.Local.Relations.Memory.MemoryEmission
import Itasca.Runtime.Compiler.Local.Relations.Select.SelectOperands
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrames
import Itasca.Runtime.Compiler.Local.Lowering.LoweringLocal
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlCoordinates
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectAndStatefulCallbacks

open WebAssembly

/-!
Proofs for Runtime / Compiler / Local / Capacity.

This module collects CallbackBudgets, LocalAndCallAvailability.
Each section documents its contracts and consumers.
-/

/-! ## CallbackBudgets -/

section

open Itasca.Representation

/-!
# Callback Budgets

Callback budget effects bound compiler resource use, including dormant and unreachable instruction cases.
-/

/-! ## BudgetEffects -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Numerical counter growth and retained budget metadata, independently
parameterized by an allowance for each compiler resource. -/
structure CompilationBudgetEffect {A : Type} (before after : runtime.compiler.Budget A)
    (allowance : ChargeCounter → Nat) : Prop where
  limits : after.limits = before.limits
  error : after.error = before.error
  counts : ∀ counter, (counter.used before).val ≤ (counter.used after).val ∧
    (counter.used after).val ≤ (counter.used before).val + allowance counter

theorem CompilationBudgetEffect.refl {A : Type} (budget : runtime.compiler.Budget A) :
    CompilationBudgetEffect budget budget (fun _ => 0) :=
  ⟨rfl,rfl,by intro counter; exact ⟨Nat.le_refl _,by omega⟩⟩

theorem CompilationBudgetEffect.trans {A : Type} {before middle after : runtime.compiler.Budget A}
    {first second : ChargeCounter → Nat} (a : CompilationBudgetEffect before middle first)
    (b : CompilationBudgetEffect middle after second) :
    CompilationBudgetEffect before after (fun counter => first counter + second counter) := by
  refine ⟨b.limits.trans a.limits,b.error.trans a.error,?_⟩
  intro counter
  have initial := a.counts counter
  have final := b.counts counter
  constructor <;> omega

theorem CompilationBudgetEffect.weaken {A : Type} {before after : runtime.compiler.Budget A}
    {first second : ChargeCounter → Nat} (effect : CompilationBudgetEffect before after first)
    (bounded : ∀ counter, first counter ≤ second counter) : CompilationBudgetEffect before after second := by
  refine ⟨effect.limits,effect.error,?_⟩
  intro counter
  have used := effect.counts counter
  have room := bounded counter
  constructor <;> omega

/-- An exact single-counter frame supplies the corresponding independent
resource effect while preserving all uncharged counters. -/
theorem CompilationBudgetEffect.of_counter {A : Type} (counter : ChargeCounter)
    (before : runtime.compiler.Budget A) (used : Usize) (amount : Nat)
    (lower : (counter.used before).val ≤ used.val)
    (upper : used.val ≤ (counter.used before).val+amount) :
    CompilationBudgetEffect before (counter.replace before used)
      (fun selected => if selected = counter then amount else 0) := by
  constructor
  · cases counter <;> rfl
  · cases counter <;> rfl
  · intro selected
    cases counter <;> cases selected <;>
      simp only [ChargeCounter.used,ChargeCounter.replace] at lower upper ⊢ <;>
      simp <;> omega

/-- A zero allowance retains the exact native counter, not merely an upper bound. -/
theorem CompilationBudgetEffect.uncharged {A : Type} {before after : runtime.compiler.Budget A}
    {allowance : ChargeCounter → Nat} (effect : CompilationBudgetEffect before after allowance)
    (counter : ChargeCounter) (zero : allowance counter = 0) : counter.used after = counter.used before := by
  have bounds := effect.counts counter
  apply UScalar.eq_of_val_eq
  omega

end Itasca.Compiler

end

/-! ## EmissionFrameAvailability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Successful available emission retains every compiler field except the two
appended vectors and the single instruction counter. This exact frame supports
aggregate resource accounting across complete function bodies. -/
theorem compiler_emit_available_frame {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (pcBound : compiler.function.code.length ≤ U32.max)
    (codeFits : compiler.function.code.length < Usize.max)
    (sourcesFit : compiler.function.source_offsets.length < Usize.max)
    (codeRequest : compiler.function.code.length+1 ≤ bound)
    (sourceRequest : compiler.function.source_offsets.length+1 ≤ bound)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max)
    (room : compiler.budget.instructions.val < compiler.budget.limits.max_instructions.val) :
    runtime.compiler.FunctionCompiler.emit ops compiler instruction ⦃ out =>
      out.1 = .Ok () ∧ ∃ used code sources,
        out.2 = {compiler with
          budget := {compiler.budget with instructions := used}
          function := {compiler.function with code,source_offsets := sources}} ∧
        used.val = compiler.budget.instructions.val+1 ∧
        code.val = compiler.function.code.val ++ [instruction] ∧
        sources.val.map (fun value => value.val) = compiler.function.source_offsets.val.map (fun value => value.val) ++
          [compiler.function.body_start.val+compiler.next_source.val] ⦄ := by
  exact runtime.compiler.FunctionCompiler.emit.available ops bound available compiler instruction
    pcBound codeFits sourcesFit codeRequest sourceRequest coordinate room

end Itasca.Compiler

end

/-! ## FinishBudgetAvailability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- The actual emission/observation callback tail consumes exactly one
instruction and preserves every other budget counter and marker. -/
theorem finish_op_available_budget {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (instruction : runtime.bytecode.Instr) :
    runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state instruction ⦃ out =>
      out.1 = .Ok () ∧ ∃ used, out.2.budget = {compiler.budget with instructions := used} ∧
        used.val = compiler.budget.instructions.val+1 ⦄ := by
  exact runtime.compiler.lower.FunctionCompiler.finish_op.available ops bound available compiler state demand instruction

/-- The complete integer numeric family has a source-independent resource
allowance of one instruction; the dead path observes without charging it. -/
theorem compiler_numeric_available_effect {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (front : List valtype) (op : SourceMachine.Numeric.Instruction)
    (layout : compiler.reachable = true →
      CompilerLayout compiler (front ++ List.replicate op.arity (integerType op.input))) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (integerOpcode op) 0#u32 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨left,right,readLeft,readRight,_,_⟩ := numeric_operands ops compiler front op (layout live)
    rw [lower_numeric_eq ops compiler state op left right live readLeft readRight]
    apply WP.spec_mono (finish_op_available_budget ops bound available compiler state demand _)
    intro out post
    obtain ⟨used,same,usedEq⟩ := post.2
    rw [same]
    exact ⟨post.1,.of_counter .instructions compiler.budget used 1 (by simp [ChargeCounter.used]; omega)
      (by simpa [ChargeCounter.used] using (show used.val ≤ compiler.budget.instructions.val+1 by omega))⟩
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

/-- Scalar FP and conversion callbacks have the same compile-time resource
effect; floating-point execution behavior is not involved. -/
theorem compiler_float_available_effect {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (front : List valtype) (op : SourceMachine.Float.Instruction)
    (layout : compiler.reachable = true →
      CompilerLayout compiler (front ++ List.replicate op.arity (valtype_numtype op.input))) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (floatOpcode op) 0#u32 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨left,right,readLeft,readRight,_,_⟩ := float_operands ops compiler front op (layout live)
    rw [lower_float_eq ops compiler state op left right live readLeft readRight]
    apply WP.spec_mono (finish_op_available_budget ops bound available compiler state demand _)
    intro out post
    obtain ⟨used,same,usedEq⟩ := post.2
    rw [same]
    exact ⟨post.1,.of_counter .instructions compiler.budget used 1 (by simp [ChargeCounter.used]; omega)
      (by simpa [ChargeCounter.used] using (show used.val ≤ compiler.budget.instructions.val+1 by omega))⟩
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

/-- One emitted ordinary instruction has a complete compositional resource
effect; observation adds no charge to any counter. -/
theorem finish_op_available_effect {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (instruction : runtime.bytecode.Instr) :
    runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state instruction ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  apply WP.spec_mono (finish_op_available_budget ops bound available compiler state demand instruction)
  intro out post
  obtain ⟨used,same,usedEq⟩ := post.2
  rw [same]
  exact ⟨post.1,.of_counter .instructions compiler.budget used 1
    (by simp [ChargeCounter.used]; omega) (by simpa [ChargeCounter.used] using
      (show used.val ≤ compiler.budget.instructions.val+1 by omega))⟩

end Itasca.Compiler

end

/-! ## CopyBudgetAvailability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Exact branch instruction charging yields the shared counter-wise budget effect. -/
theorem BranchBudget.compilation {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {count : Nat} (effect : BranchBudget before after count) :
    CompilationBudgetEffect before.budget after.budget
      (fun counter => if counter = .instructions then count else 0) := by
  obtain ⟨used, budget, charged⟩ := effect
  rw [budget]
  exact .of_counter .instructions before.budget used count
    (by simp only [ChargeCounter.used]; omega)
    (by simp only [ChargeCounter.used]; omega)

end Itasca.Compiler

end

/-! ## CallbackCapacity -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Independent room for a callback that emits several instructions. The final
PC is representable too, so guard patches can name the point after emission. -/
structure CallbackCapacity {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bound count : Nat) : Prop where
  pc : compiler.function.code.length + count ≤ U32.max
  codeCapacity : compiler.function.code.length + count ≤ Usize.max
  sourceCapacity : compiler.function.source_offsets.length + count ≤ Usize.max
  codeReserve : compiler.function.code.length + count ≤ bound
  sourceReserve : compiler.function.source_offsets.length + count ≤ bound
  coordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max
  instructions : compiler.budget.instructions.val + count ≤ compiler.budget.limits.max_instructions.val
  operands : state.vals.length ≤ bound
  slots : compiler.function.local_slots.val + 2*state.vals.length ≤ U32.max

theorem CallbackCapacity.mono {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {state bound count smaller} (capacity : CallbackCapacity compiler state bound count)
    (less : smaller ≤ count) : CallbackCapacity compiler state bound smaller := by
  rcases capacity with ⟨pc,code,sources,codeReserve,sourceReserve,coordinate,instructions,operands,slots⟩
  exact ⟨by omega,by omega,by omega,by omega,by omega,coordinate,by omega,operands,slots⟩

/-- At least one remaining instruction pays for an ordinary emission. -/
theorem CallbackCapacity.one {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {state bound count} (capacity : CallbackCapacity compiler state bound count)
    (positive : 0 < count) : CallbackDemand compiler state bound := by
  rcases capacity with ⟨pc,code,sources,codeReserve,sourceReserve,coordinate,instructions,operands,slots⟩
  exact ⟨by omega,by omega,by omega,by omega,by omega,coordinate,by omega,operands,slots⟩

/-- One emitted instruction consumes one unit of the independently reserved
capacity. Unchanged compiler fields follow from the exact emission frame. -/
theorem CallbackCapacity.after_emission {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {state bound count instruction} (capacity : CallbackCapacity before state bound (count+1))
    (emitted : Emitted before after instruction)
    (effect : CompilationBudgetEffect before.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) :
    CallbackCapacity after state bound count := by
  obtain ⟨budget,code,sources,frame,appended,recorded⟩ := emitted
  have codeCount : code.length = before.function.code.length+1 := by simp [alloc.vec.Vec.length,appended]
  have sourceCount : sources.length = before.function.source_offsets.length+1 := by
    have lengths := congrArg List.length recorded
    simpa [alloc.vec.Vec.length] using lengths
  have limits := effect.limits
  have used := (effect.counts .instructions).2
  rw [frame] at limits used ⊢
  simp only [ChargeCounter.used,↓reduceIte] at used
  rcases capacity with ⟨pc,codeCapacity,sourceCapacity,codeReserve,sourceReserve,coordinate,instructions,operands,slots⟩
  refine ⟨?_,?_,?_,?_,?_,coordinate,?_,operands,slots⟩
  · change code.length + count ≤ U32.max; omega
  · change code.length + count ≤ Usize.max; omega
  · change sources.length + count ≤ Usize.max; omega
  · change code.length + count ≤ bound; omega
  · change sources.length + count ≤ bound; omega
  · change budget.instructions.val + count ≤ budget.limits.max_instructions.val
    rw [limits]
    omega

/-- Replacing control frames leaves the emission and observation demand
unchanged. Label updates do not alter code, slots, or resource counters. -/
theorem CallbackCapacity.with_frames {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {state bound count} (capacity : CallbackCapacity compiler state bound count)
    (frames : alloc.vec.Vec runtime.compiler.Frame) :
    CallbackCapacity {compiler with frames} state bound count :=
  ⟨capacity.pc,capacity.codeCapacity,capacity.sourceCapacity,capacity.codeReserve,
    capacity.sourceReserve,capacity.coordinate,capacity.instructions,capacity.operands,capacity.slots⟩

end Itasca.Compiler

end

/-! ## ScopeDemand -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Bounds for the map/frame allocations common to every scope opening. -/
structure ScopeDemand {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bound : Nat) : Prop where
  pc : compiler.function.code.length ≤ U32.max
  coordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max
  mapsCapacity : compiler.function.controls.length < Usize.max
  mapsReserve : compiler.function.controls.length + 1 ≤ bound
  framesCapacity : compiler.frames.length < Usize.max
  framesReserve : compiler.frames.length + 1 ≤ bound
  control : compiler.budget.controls.val < compiler.budget.limits.max_controls.val
  operands : state.vals.length ≤ bound
  slots : compiler.function.local_slots.val + 2*state.vals.length ≤ U32.max

end Itasca.Compiler

end

/-! ## BodyResourceRoom -/

section

/-!
Source compilation budgets and the body resource-room certificate. Source-only instruction demands bound callback requests and establish BodyResourceRoom for successful replay.
-/

/-! ## Source Budget Availability -/

section

namespace Itasca.Compiler
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

end Itasca.Compiler

end

/-! ## Source Callback Demand -/

section

namespace Itasca.Compiler
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

end Itasca.Compiler

end

/-! ## Body Resource Room -/

section

namespace Itasca.Compiler
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

end Itasca.Compiler

end

end

/-! ## MemoryAvailability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Every scalar/packed load callback accepts from its typed address layout
and independent resource demand. Compilation touches no memory buffer. -/
theorem compiler_memory_load_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (front : List valtype)
    (op : SourceMachine.Memory.Load) (offset alignment : U32)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ [.I32])) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (memoryLoadOpcode op) offset alignment 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨address,read,_⟩ := memory_load_operand ops compiler front (layout live)
    rw [lower_memory_load_eq ops compiler state op offset alignment address live read]
    exact finish_op_available_effect ops bound available compiler state demand _
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

/-- Every scalar/packed store callback has the same acceptance and resource
bound, including f32/f64 and both integer widths. -/
theorem compiler_memory_store_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (front : List valtype)
    (op : SourceMachine.Memory.Store) (offset alignment : U32)
    (layout : compiler.reachable = true →
      CompilerLayout compiler (front ++ [.I32,valtype_numtype op.type])) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (memoryStoreOpcode op) offset alignment 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨address,value,addressRead,valueRead,_,_⟩ := memory_store_operands ops compiler front op.type (layout live)
    rw [lower_memory_store_eq ops compiler state op offset alignment address value live addressRead valueRead]
    exact finish_op_available_effect ops bound available compiler state demand _
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Compiler

end

/-! ## AuxiliaryAvailability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Pair-table insertion accepts its independently bounded index and reserve
request. Its exact append is retained for indirect-call and bulk-table code. -/
theorem compiler_pair_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (first second : U32)
    (indexBound : compiler.function.indirect.length ≤ U32.max)
    (capacity : compiler.function.indirect.length < Usize.max)
    (request : compiler.function.indirect.length + 1 ≤ bound) :
    runtime.compiler.FunctionCompiler.pair ops compiler first second ⦃ out =>
      ∃ index pairs, out.1 = .Ok index ∧ index.val = compiler.function.indirect.length ∧
        out.2 = {compiler with function := {compiler.function with indirect := pairs}} ∧
        pairs.val = compiler.function.indirect.val ++ [(first,second)] ⦄ := by
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.pair.available ops bound available compiler first second
    indexBound capacity request)
  rintro ⟨status, after⟩ ⟨index, accepted, pairs, same, appended, indexEq⟩
  exact ⟨index, pairs, accepted, indexEq, same, appended⟩

end Itasca.Compiler

end

/-! ## SelectAvailability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Both forms of select accept scalar, reference, or vector layouts, with
one instruction of budget and no charge to other compiler counters. -/
theorem compiler_select_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (front : List valtype) (ty : valtype)
    (typed : Bool)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ [ty,ty,.I32])) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (if typed then 28#u16 else 27#u16) 0#u32 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨left,right,condition,hl,hr,hc,_,position,_⟩ := select_operands ops compiler front ty (layout live)
    obtain ⟨difference,subtract,_⟩ := WP.spec_imp_exists
      (UScalar.sub_spec (x := right) (y := left) (by omega))
    rw [lower_select_eq ops compiler state left right condition difference typed live hl hr hc subtract]
    exact finish_op_available_effect ops bound available compiler state demand _
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

/-- Nop and drop only observe the stack, irrespective of reachability. -/
theorem compiler_nop_drop_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (drop : Bool) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (if drop then 26#u16 else 1#u16) 0#u32 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ out.2.budget = compiler.budget ⦄ := by
  have dispatch : runtime.compiler.lower.FunctionCompiler.op ops compiler state
      (if drop then 26#u16 else 1#u16) 0#u32 0#u32 0#u128 =
      runtime.compiler.FunctionCompiler.observe ops compiler state := by
    exact lower_empty_eq ops compiler state drop
  rw [dispatch]
  exact compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots

end Itasca.Compiler

end

/-! ## UnreachableAvailability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- The actual unreachable callback accepts on live and dead input paths.
It consumes at most one instruction and retains every other budget counter. -/
theorem compiler_on_unreachable_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable ops compiler state ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable.available ops bound available compiler state demand)
  rintro ⟨status, after⟩ ⟨accepted, used, frame, usedEq⟩
  dsimp only at frame usedEq ⊢
  rw [frame]
  refine ⟨accepted, .of_counter .instructions compiler.budget used 1 ?_ ?_⟩
  · simp only [ChargeCounter.used]
    split at usedEq <;> scalar_tac
  · simp only [ChargeCounter.used]
    split at usedEq <;> scalar_tac

end Itasca.Compiler

end

end

/-! ## LocalAndCallAvailability -/

section

open Itasca.Representation

/-!
# Local And Call Availability

Local-variable, call and dormant operation callbacks have sufficient resources under the source-derived capacity premises.
-/

/-! ## DeadOpAvailability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Every ordinary opcode on a dead input path only observes the validator
stack. No opcode constructor or live operand layout is needed. -/
theorem compiler_dead_op_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (opcode : U16) (a b : U32) (bits : U128)
    (dead : compiler.reachable ≠ true)
    (request : state.vals.length ≤ bound)
    (slotsFit : compiler.function.local_slots.val+2*state.vals.length ≤ U32.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state opcode a b bits ⦃ out =>
      out.1 = .Ok () ∧ out.2.budget = compiler.budget ⦄ := by
  cases compiler with
  | mk signatures params budget batchStart function frames reachable nextSource before height offsets depths =>
    cases reachable with
    | true => exact False.elim (dead rfl)
    | false =>
      let current : runtime.compiler.FunctionCompiler A :=
        ⟨signatures,params,budget,batchStart,function,frames,false,nextSource,before,height,offsets,depths⟩
      change runtime.compiler.FunctionCompiler.observe ops current state ⦃ out =>
        out.1 = .Ok () ∧ out.2.budget = budget ⦄
      exact compiler_observe_available_budget ops bound available current state request slotsFit

end Itasca.Compiler

end

/-! ## LocalVariableAvailability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

set_option maxRecDepth 4096 in
theorem lower_local_get_live_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (demand : CallbackDemand compiler state bound)
    (before : List valtype) (index : U32) (ty : Itasca.wasm_types.ValueType)
    (layout : CompilerLayout compiler before) (reachable : compiler.reachable = true)
    (found : compiler.function.locals.val[index.val]? = some ty)
 :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 32#u16 index 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨localSlot, atSlot, slotPosition⟩ := layout.local_slot index ty found
  have sourceType : (compilerLocals compiler)[index.val]? = some (Itasca.Translation.valueType ty) := by
    simp [compilerLocals, List.getElem?_map, found]
  have different : localSlot ≠ compiler.height := by
    have smaller := layout.local_before_operand_region sourceType
    intro equal
    rw [equal] at slotPosition
    rw [← slotPosition, layout.localSlots, layout.height] at smaller
    omega
  have run := runtime.compiler.lower.FunctionCompiler.op.local_get ops compiler state index 0#u32 0#u128 reachable
  rw [run]
  step as ⟨i, hi⟩
  have iVal : i.val = index.val := by scalar_tac
  have offsetsBound : i.val < compiler.local_offsets.val.length := by rw [iVal]; exact (List.getElem?_eq_some_iff.mp atSlot).1
  step as ⟨src, hsrc⟩
  have srcEq : src = localSlot := by
    simp only [iVal] at hsrc
    exact hsrc.trans (List.getElem?_eq_some_iff.mp atSlot).2
  rw [srcEq]
  step as ⟨j, hj⟩
  have jVal : j.val = index.val := by scalar_tac
  have localsBound : j.val < compiler.function.locals.val.length := by rw [jVal]; exact (List.getElem?_eq_some_iff.mp found).1
  step as ⟨rawType, htype⟩
  have typeEq : rawType = ty := by
    simp only [jVal] at htype
    exact htype.trans (List.getElem?_eq_some_iff.mp found).2
  erw [typeEq, copy_observe_eq ops compiler state ty compiler.height localSlot different]
  exact finish_op_available_effect ops bound available compiler state demand _

set_option maxRecDepth 4096 in
theorem lower_local_write_live_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (demand : CallbackDemand compiler state bound)
    (before : List valtype) (index : U32) (ty : Itasca.wasm_types.ValueType) (tee : Bool)
    (layout : CompilerLayout compiler (before ++ [Itasca.Translation.valueType ty]))
    (reachable : compiler.reachable = true)
    (found : compiler.function.locals.val[index.val]? = some ty)
 :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (if tee then 34#u16 else 33#u16) index 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨localSlot, atSlot, slotPosition⟩ := layout.local_slot index ty found
  obtain ⟨operand, operandRead, operandPosition⟩ := last_operand ops compiler before _ layout
  have sourceType : (compilerLocals compiler)[index.val]? = some (Itasca.Translation.valueType ty) := by
    simp [compilerLocals, List.getElem?_map, found]
  have different : operand ≠ localSlot := by
    have smaller := layout.local_before_operand_region sourceType
    intro equal
    rw [← equal] at slotPosition
    rw [← slotPosition, layout.localSlots, operandPosition] at smaller
    omega
  have run := runtime.compiler.lower.FunctionCompiler.op.local_set_or_tee ops compiler state tee index 0#u32 0#u128 reachable
  rw [run]
  step as ⟨i, hi⟩
  have iVal : i.val = index.val := by scalar_tac
  have offsetsBound : i.val < compiler.local_offsets.val.length := by rw [iVal]; exact (List.getElem?_eq_some_iff.mp atSlot).1
  step as ⟨dst, hdst⟩
  have dstEq : dst = localSlot := by
    simp only [iVal] at hdst
    exact hdst.trans (List.getElem?_eq_some_iff.mp atSlot).2
  rw [dstEq, operandRead]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step as ⟨j, hj⟩
  have jVal : j.val = index.val := by scalar_tac
  have localsBound : j.val < compiler.function.locals.val.length := by rw [jVal]; exact (List.getElem?_eq_some_iff.mp found).1
  step as ⟨rawType, htype⟩
  have typeEq : rawType = ty := by
    simp only [jVal] at htype
    exact htype.trans (List.getElem?_eq_some_iff.mp found).2
  rw [typeEq]
  have copyEq := copy_observe_eq ops compiler state ty localSlot operand different
  simp only [core.result.Result.Insts.CoreOpsTry.branch] at copyEq
  erw [copyEq]
  exact finish_op_available_effect ops bound available compiler state demand _

/-- Local accesses in unreachable code only rebuild the observed stack;
valid live accesses use the checked local and operand coordinates above. -/
theorem compiler_local_variable_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (before : List valtype)
    (index : U32) (ty : Itasca.wasm_types.ValueType) (write tee : Bool)
    (layout : compiler.reachable = true → CompilerLayout compiler
      (if write then before ++ [Itasca.Translation.valueType ty] else before))
    (found : compiler.reachable = true → compiler.function.locals.val[index.val]? = some ty) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state
      (if write then (if tee then 34#u16 else 33#u16) else 32#u16) index 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · cases write
    · exact lower_local_get_live_available ops bound available compiler state demand before index ty
        (layout live) live (found live)
    · exact lower_local_write_live_available ops bound available compiler state demand before index ty tee
        (layout live) live (found live)
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Compiler

end

/-! ## StatefulAvailability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Every reference, table, memory-size/growth, and bulk-memory callback
accepts from its source signature and independently bounded storage. Pair
storage is charged only for table.copy and table.init. -/
theorem compiler_stateful_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (C : context)
    (front input output : List valtype) (op : SourceMachine.Stateful.Instruction)
    (signature : SourceMachine.Stateful.Signature C op input output) (a b : U32)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ input))
    (pairIndex : statefulUsesPair op = true → compiler.function.indirect.length ≤ U32.max)
    (pairCapacity : statefulUsesPair op = true → compiler.function.indirect.length < Usize.max)
    (pairReserve : statefulUsesPair op = true → compiler.function.indirect.length + 1 ≤ bound) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (statefulOpcode op) a b 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨first,second,reads,_,_⟩ := stateful_operands ops compiler C front input output op signature (layout live)
    by_cases paired : statefulUsesPair op = true
    · obtain ⟨⟨status,after⟩,actual,index,pairs,accepted,_,frame,_⟩ := WP.spec_imp_exists
        (compiler_pair_available ops bound available compiler a b
          (pairIndex paired) (pairCapacity paired) (pairReserve paired))
      dsimp only at accepted frame
      subst status
      have read : runtime.compiler.FunctionCompiler.operand ops after 3#usize = .ok (.Ok first) := by
        rw [frame]
        have arity : op.arity = 3 := by cases op <;> simp_all [statefulUsesPair,SourceMachine.Stateful.Instruction.arity]
        simpa [StatefulReads,arity,statefulDepth,runtime.compiler.FunctionCompiler.operand.eq] using reads.1
      rw [lower_stateful_pair_eq ops compiler after state op first second a b index live paired actual read]
      have afterDemand : CallbackDemand after state bound := by
        rw [frame]
        exact ⟨demand.pc,demand.codeCapacity,demand.sourceCapacity,demand.codeReserve,
          demand.sourceReserve,demand.coordinate,demand.instruction,demand.operands,demand.slots⟩
      have budget : after.budget = compiler.budget := by rw [frame]
      simpa only [budget] using finish_op_available_effect ops bound available after state afterDemand
        (statefulInstruction op first second a index)
    · have single : statefulUsesPair op = false := Bool.eq_false_iff.mpr paired
      rw [lower_stateful_eq ops compiler state op first second a b 0#u32 live single reads]
      exact finish_op_available_effect ops bound available compiler state demand _
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Compiler

end

/-! ## BranchLabelAvailability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Each streamed branch-table label, including the default label, accepts
from independent branch budget and scratch-vector bounds. -/
theorem compiler_branch_label_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (depth : U32)
    (room : compiler.budget.branches.val < compiler.budget.limits.max_branch_table_entries.val)
    (capacity : compiler.table_depths.length < Usize.max)
    (request : compiler.table_depths.length + 1 ≤ bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label ops compiler state depth
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
          (fun counter => if counter = .branches then 1 else 0) ∧
        out.2.table_depths.val = compiler.table_depths.val ++ [depth] ⦄ := by
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.available
    ops bound available compiler state depth room capacity request)
  rintro ⟨status, after⟩ ⟨accepted, used, frame, usedEq, appended⟩
  refine ⟨accepted, ?_, appended⟩
  rw [frame]
  exact CompilationBudgetEffect.of_counter .branches compiler.budget used 1
    (by change compiler.budget.branches.val ≤ used.val; omega)
    (by change used.val ≤ compiler.budget.branches.val + 1; omega)

end Itasca.Compiler

end

/-! ## CallAvailability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Direct calls accept from their captured source parameter width and typed
argument layout. Checked subtraction is discharged from the layout. -/
theorem compiler_call_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (front params : List valtype)
    (index paramSlots : U32)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ params))
    (signature : compiler.reachable = true → compiler.func_param_slots.val[index.val]? = some paramSlots)
    (parameterWidth : paramSlots.val = slots params) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 16#u16 index 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.call ops compiler state index 0#u32 0#u128 live
    rw [run]
    step as ⟨i,hi⟩
    have atIndex : i.val = index.val := by scalar_tac
    have inRange : i.val < compiler.func_param_slots.length := by
      have found := (List.getElem?_eq_some_iff.mp (signature live)).1
      simpa [atIndex] using found
    step as ⟨slots,hslots⟩
    have same : slots = paramSlots := by
      simp only [atIndex] at hslots
      exact hslots.trans (List.getElem?_eq_some_iff.mp (signature live)).2
    rw [same]
    have height := (layout live).height
    simp only [slots_append] at height
    step as ⟨o,ho⟩
    cases o with
    | none => simp only at ho; omega
    | some base =>
      simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      exact finish_op_available_effect ops bound available compiler state demand _
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

/-- Indirect calls additionally reserve one pair descriptor. Their parameter
and table-index arithmetic follows from the independently typed live stack. -/
theorem compiler_indirect_call_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (front params : List valtype)
    (a b : U32) (signature : runtime.compiler.Signature)
    (layout : compiler.reachable = true → CompilerLayout compiler ((front ++ params) ++ [.I32]))
    (metadata : compiler.reachable = true → compiler.signatures.val[a.val]? = some signature)
    (parameterWidth : signature.param_slots.val = slots params)
    (pairIndex : compiler.function.indirect.length ≤ U32.max)
    (pairCapacity : compiler.function.indirect.length < Usize.max)
    (pairReserve : compiler.function.indirect.length + 1 ≤ bound) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 17#u16 a b 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · rw [lower_indirect_call_dispatch ops compiler state a b live]
    unfold indirectCallLowering
    step as ⟨i,hi⟩
    have atIndex : i.val = a.val := by scalar_tac
    have inRange : i.val < compiler.signatures.length := by
      have found := (List.getElem?_eq_some_iff.mp (metadata live)).1
      simpa [atIndex] using found
    step as ⟨sig,hsig⟩
    have same : sig = signature := by
      simp only [atIndex] at hsig
      exact hsig.trans (List.getElem?_eq_some_iff.mp (metadata live)).2
    rw [same]
    have height := (layout live).height
    simp only [slots_append,slots,width,Nat.add_zero] at height
    have maximum := compiler.height.hmax
    step as ⟨o,ho⟩
    cases o with
    | none => simp only at ho; scalar_tac
    | some total =>
      simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      have totalWidth : total.val = signature.param_slots.val + 1 := by simp only at ho; omega
      step as ⟨o,ho⟩
      cases o with
      | none => simp only at ho; omega
      | some base =>
        simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
        step with compiler_pair_available ops bound available compiler b a pairIndex pairCapacity pairReserve
          as ⟨status,paired,index,pairs,accepted,_,frame,_⟩
        rw [accepted]
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
        obtain ⟨operand,read,_⟩ := last_operand ops compiler (front ++ params) .I32 (layout live)
        have pairedRead : runtime.compiler.FunctionCompiler.operand ops paired 1#usize = .ok (.Ok operand) := by
          rw [frame]
          simpa only [runtime.compiler.FunctionCompiler.operand.eq] using read
        rw [pairedRead]
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
        have afterDemand : CallbackDemand paired state bound := by
          rw [frame]
          exact ⟨demand.pc,demand.codeCapacity,demand.sourceCapacity,demand.codeReserve,
            demand.sourceReserve,demand.coordinate,demand.instruction,demand.operands,demand.slots⟩
        have budget : paired.budget = compiler.budget := by rw [frame]
        simpa only [budget] using finish_op_available_effect ops bound available paired state afterDemand
          (.CallIndirect index operand base)
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Compiler

end

end
