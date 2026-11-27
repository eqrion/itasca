import Itasca.Runtime.Compiler.Local.Relations.Instructions.WellFormedAcceptance
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Callbacks.MetadataPreservation
import Itasca.Runtime.Compiler.Local.Relations.Instructions.InstructionCheckAcceptance
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Relations.Function.CapturedContext
import Itasca.Runtime.Compiler.Local.Relations.Function.EnvironmentContracts
import Itasca.Runtime.Compiler.Local.Control.CodeSegmentsAndPositions
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSkipSafety
import Itasca.Runtime.Compiler.Local.Relations.Table.ControlTablePreservation
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CallbackRetention
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupAlgebra
import Itasca.Runtime.Compiler.Local.Publication.ScopeEntryPublication
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrames
import Itasca.Runtime.Compiler.Local.Coordinates.ScalarSourceCoordinates
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSuccessConditional
import Itasca.Runtime.Compiler.Local.Lowering.Integer.OperandEffects
import Itasca.Runtime.Compiler.Local.Lowering.ScalarTablePreservation
import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchAndTerminalEffects
import Itasca.Runtime.Compiler.Local.Relations.Operations.CoreBasicEmissions
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchLiteral
import Itasca.Runtime.Compiler.Local.Source.StartJumpTableBounds
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableFrames

/-!
Proofs for Runtime / Compiler / Local / Checking.

This module collects ScopeInstructionPrefixes, BranchAndScalarChecks.
Each section documents its contracts and consumers.
-/

/-! ## ScopeInstructionPrefixes -/

section

open Itasca.Representation

/-!
# Scope instruction-prefix checks

Instruction compiler effects and source-coordinate facts establish checked prefixes across
scope transitions. Entry/close control cases retain exit-slot and instruction bounds for
subsequent publication.
-/

/-! ## OpenInstructionCompiler -/

section

/-!
The compiler instruction-prefix certificate, its monotone checks and append operations. PendingInstructionSite and CompilerInstructionPrefix connect low-level open checks to the compiler start invariant.
-/

/-! ## Instruction Check Monotone -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation
set_option maxRecDepth 4096

/-- Capacity and table lengths used by the bytecode checker only increase
while compiling the rest of a function. Contents are irrelevant to this local
check; their semantic correspondence is tracked by the executable relation. -/
structure InstructionCheckExtends (before after : runtime.bytecode.CompiledFunction) : Prop where
  slots : before.slot_count.val ≤ after.slot_count.val
  code : before.code.length ≤ after.code.length
  indirect : before.indirect.length ≤ after.indirect.length
  simd : before.simd.length ≤ after.simd.length
  constants : before.v128_pool.length ≤ after.v128_pool.length
  targets : before.jump_tables.length ≤ after.jump_tables.length

private theorem slots_fit_arithmetic (function : runtime.bytecode.CompiledFunction) (start count : U32) :
    runtime.bytecode.CompiledFunction.slots_fit function start count =
      .ok (decide (start.val+count.val ≤ function.slot_count.val)) := by
  obtain ⟨result,called,exactBound⟩ := WP.spec_imp_exists (slots_fit_spec function start count)
  rw [called]
  congr 1
  cases result <;> simp_all

private theorem checked_difference_monotone (before after start count : Usize)
    (growth : before.val ≤ after.val)
    (accepted : (do let remaining ← before-start; Result.ok (decide (count ≤ remaining))) = .ok true) :
    (do let remaining ← after-start; Result.ok (decide (count ≤ remaining))) = .ok true := by
  obtain ⟨remaining,subtracted,returned⟩ := bind_ok_inv _ _ _ accepted
  have arithmetic := UScalar.sub_equiv before start
  rw [subtracted] at arithmetic
  simp at arithmetic
  have fits : count ≤ remaining := by simpa only [Result.ok.injEq,decide_eq_true_eq] using returned
  have checked : (do let rest ← after-start; Result.ok (decide (count ≤ rest))) ⦃ result => result = true ⦄ := by
    step as ⟨rest,restEq⟩
    simp only [decide_eq_true_eq]
    scalar_tac
  obtain ⟨result,called,rfl⟩ := WP.spec_imp_exists checked
  exact called

-- The residual checker still has generated rejection branches; check them once here.
set_option maxHeartbeats 600000 in
/-- The residual checker has only core operand/table bounds. Its rejected
instruction families close before any arithmetic reasoning is performed. -/
private theorem other_instruction_monotone (before after : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (growth : InstructionCheckExtends before after)
    (accepted : runtime.bytecode.CompiledFunction.other_valid before instruction = .ok true) :
    runtime.bytecode.CompiledFunction.other_valid after instruction = .ok true := by
  obtain ⟨slots,code,indirect,simd,constants,targets⟩ := growth
  -- Use the compact constructor equations; splitting the unfolded matcher
  -- would regenerate its quadratic-size auxiliary proofs in this module.
  cases instruction <;>
    simp only [runtime.bytecode.CompiledFunction.other_valid] at accepted ⊢ <;>
    simp_all only [slots_fit_arithmetic,bind_ok,lift,Result.ok.injEq,decide_eq_true_eq,Bool.false_eq_true]
  all_goals
    (try split_ifs at accepted) <;>
    ((try simp_all only [Result.ok.injEq,decide_eq_true_eq,Bool.false_eq_true]);
      (try split_ifs)) <;>
    (try simp_all only [Result.ok.injEq,decide_eq_true_eq,Bool.false_eq_true])
  all_goals first | scalar_tac | exact checked_difference_monotone _ _ _ _ (by simpa using targets) accepted

private theorem non_simd_instruction_monotone (before after : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (growth : InstructionCheckExtends before after)
    (noSimd : runtime.bytecode.Instr.simd instruction = .ok none)
    (accepted : runtime.bytecode.CompiledFunction.instruction_valid before instruction = .ok true) :
    runtime.bytecode.CompiledFunction.instruction_valid after instruction = .ok true := by
  have slots := growth.slots
  obtain ⟨scalar,scalarRun,_⟩ := WP.spec_imp_exists (instruction_scalar_total instruction)
  unfold runtime.bytecode.CompiledFunction.instruction_valid at accepted ⊢
  simp only [scalarRun,bind_ok] at accepted ⊢
  cases scalar with
  | some values =>
    rcases values with ⟨opcode,dst,left,right⟩
    dsimp only at accepted ⊢
    simp only [slots_fit_arithmetic,bind_ok,uncurry_apply_pair] at accepted ⊢
    split_ifs at accepted ⊢ <;> simp_all only [Result.ok.injEq,decide_eq_true_eq,Bool.false_eq_true] <;> scalar_tac
  | none =>
    obtain ⟨load,loadRun,_⟩ := WP.spec_imp_exists (instruction_load_total instruction)
    simp only [loadRun,bind_ok] at accepted ⊢
    cases load with
    | some values =>
      rcases values with ⟨opcode,dst,address,offset⟩
      dsimp only at accepted ⊢
      simp only [slots_fit_arithmetic,bind_ok,uncurry_apply_pair] at accepted ⊢
      split_ifs at accepted ⊢ <;> simp_all only [Result.ok.injEq,decide_eq_true_eq,Bool.false_eq_true] <;> scalar_tac
    | none =>
      obtain ⟨store,storeRun,_⟩ := WP.spec_imp_exists (instruction_store_total instruction)
      simp only [storeRun,bind_ok] at accepted ⊢
      cases store with
      | some values =>
        rcases values with ⟨opcode,address,value,offset⟩
        dsimp only at accepted ⊢
        simp only [slots_fit_arithmetic,bind_ok,uncurry_apply_pair] at accepted ⊢
        split_ifs at accepted ⊢ <;> simp_all only [Result.ok.injEq,decide_eq_true_eq,Bool.false_eq_true] <;> scalar_tac
      | none =>
        simp only [noSimd,bind_ok] at accepted ⊢
        exact other_instruction_monotone before after instruction growth accepted

/-- Every earlier instruction check remains valid as code, slot capacity, and
function-local metadata tables grow. Branch patching itself is handled
separately because it changes the stored instruction. -/
theorem instruction_valid_monotone (before after : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (growth : InstructionCheckExtends before after)
    (accepted : runtime.bytecode.CompiledFunction.instruction_valid before instruction = .ok true) :
    runtime.bytecode.CompiledFunction.instruction_valid after instruction = .ok true := by
  obtain ⟨view,projected,_⟩ := WP.spec_imp_exists (instruction_simd_total instruction)
  cases view with
  | none => exact non_simd_instruction_monotone before after instruction growth projected accepted
  | some view =>
    obtain ⟨opcode,dst,input,entry⟩ := view
    exact simd_instruction_monotone before after instruction opcode dst input entry projected growth.slots growth.simd accepted

end Itasca.Compiler

end

/-! ## Checked Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Every instruction in this concrete code vector passes its local checker.
Open control fixups require a separate pending-branch invariant. -/
def CheckedInstructionPrefix (function : runtime.bytecode.CompiledFunction) : Prop :=
  ∀ instruction ∈ function.code.val,
    runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true

theorem CheckedInstructionPrefix.indexed {function : runtime.bytecode.CompiledFunction}
    (held : CheckedInstructionPrefix function) (index : Nat) (bound : index < function.code.length) :
    runtime.bytecode.CompiledFunction.instruction_valid function function.code.val[index] = .ok true :=
  held _ (List.getElem_mem bound)

theorem InstructionCheckExtends.refl (function : runtime.bytecode.CompiledFunction) :
    InstructionCheckExtends function function := ⟨le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl⟩

theorem InstructionCheckExtends.trans {first middle last : runtime.bytecode.CompiledFunction}
    (left : InstructionCheckExtends first middle) (right : InstructionCheckExtends middle last) :
    InstructionCheckExtends first last :=
  ⟨left.slots.trans right.slots,left.code.trans right.code,left.indirect.trans right.indirect,
    left.simd.trans right.simd,left.constants.trans right.constants,left.targets.trans right.targets⟩

/-- Actual emission extends all checker capacities, without changing tables. -/
theorem Emitted.instruction_check_extends {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction : runtime.bytecode.Instr} (emitted : Emitted before after instruction) :
    InstructionCheckExtends before.function after.function := by
  obtain ⟨budget,code,sources,rfl,appended,_⟩ := emitted
  refine ⟨le_rfl,?_,le_rfl,le_rfl,le_rfl,le_rfl⟩
  change before.function.code.val.length ≤ code.val.length
  rw [appended,List.length_append,List.length_singleton]
  omega

end Itasca.Compiler

end

/-! ## Open Instruction Check -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Earlier bytecode may contain forward branches whose owner has not closed.
Resolved targets may equal the current end; final return emission makes that
end a valid instruction address. Other forms already pass the actual checker. -/
inductive OpenInstructionCheck (function : runtime.bytecode.CompiledFunction)
    (pending : Nat → Prop) (index : Nat) : runtime.bytecode.Instr → Prop
  | checked {instruction} (accepted : runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true) :
      OpenInstructionCheck function pending index instruction
  | jump {target} (ready : target.val ≤ function.code.length ∨ pending index) :
      OpenInstructionCheck function pending index (.Jump target)
  | zero {condition target} (slot : condition.val+1 ≤ function.slot_count.val)
      (ready : target.val ≤ function.code.length ∨ pending index) :
      OpenInstructionCheck function pending index (.JumpIfZero condition target)
  | nonzero {condition target} (slot : condition.val+1 ≤ function.slot_count.val)
      (ready : target.val ≤ function.code.length ∨ pending index) :
      OpenInstructionCheck function pending index (.JumpIfNonZero condition target)

/-- Numerical growth and preservation of pending owners retain a prefix check. -/
theorem OpenInstructionCheck.grow {before after : runtime.bytecode.CompiledFunction}
    {pending next : Nat → Prop} {index instruction}
    (held : OpenInstructionCheck before pending index instruction)
    (growth : InstructionCheckExtends before after) (owners : pending index → next index) :
    OpenInstructionCheck after next index instruction := by
  have ready {target : U32} (prior : target.val ≤ before.code.length ∨ pending index) :
      target.val ≤ after.code.length ∨ next index := prior.imp (fun bound => bound.trans growth.code) owners
  cases held with
  | checked accepted => exact .checked (instruction_valid_monotone before after instruction growth accepted)
  | jump prior => exact .jump (ready prior)
  | zero slot prior => exact .zero (slot.trans growth.slots) (ready prior)
  | nonzero slot prior => exact .nonzero (slot.trans growth.slots) (ready prior)

/-- Strict final code growth publishes every resolved branch, while retaining
all earlier instruction checks and slot bounds. -/
theorem OpenInstructionCheck.publish {before after : runtime.bytecode.CompiledFunction}
    {index instruction} (held : OpenInstructionCheck before (fun _ => False) index instruction)
    (growth : InstructionCheckExtends before after) (strict : before.code.length < after.code.length) :
    runtime.bytecode.CompiledFunction.instruction_valid after instruction = .ok true := by
  cases held with
  | checked accepted => exact instruction_valid_monotone before after instruction growth accepted
  | jump ready => exact (CoreInstructionBounds.jump ((ready.resolve_right id).trans_lt strict)).accepts
  | zero slot ready =>
    exact (CoreInstructionBounds.jumpIfZero (slot.trans growth.slots) ((ready.resolve_right id).trans_lt strict)).accepts
  | nonzero slot ready =>
    exact (CoreInstructionBounds.jumpIfNonZero (slot.trans growth.slots) ((ready.resolve_right id).trans_lt strict)).accepts

/-- All stored instructions, including bytes skipped after a source terminator,
retain their own check. Semantic reachability alone does not imply this fact. -/
def OpenInstructionPrefix (function : runtime.bytecode.CompiledFunction) (pending : Nat → Prop) : Prop :=
  ∀ index instruction, function.code.val[index]? = some instruction → OpenInstructionCheck function pending index instruction

end Itasca.Compiler

end

/-! ## Open Instruction Append -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- New ordinary emissions preserve every stored instruction check, including
pending branches in earlier code. Their ownership is transported explicitly. -/
theorem OpenInstructionPrefix.append {before after : runtime.bytecode.CompiledFunction}
    {pending next : Nat → Prop} (held : OpenInstructionPrefix before pending)
    (growth : InstructionCheckExtends before after) (owners : ∀ index, pending index → next index)
    (fragment : List runtime.bytecode.Instr) (code : after.code.val = before.code.val++fragment)
    (fresh : ∀ instruction ∈ fragment,
      runtime.bytecode.CompiledFunction.instruction_valid after instruction = .ok true) :
    OpenInstructionPrefix after next := by
  intro index instruction found
  rw [code] at found
  by_cases inside : index < before.code.val.length
  · rw [List.getElem?_append_left inside] at found
    exact (held index instruction found).grow growth (owners index)
  · rw [List.getElem?_append_right (by omega : before.code.val.length ≤ index)] at found
    obtain ⟨bound,equal⟩ := List.getElem?_eq_some_iff.mp found
    exact .checked (fresh instruction (equal ▸ List.getElem_mem bound))

/-- Literal lowering preserves checker capacities when its captured tables are
unchanged. This is independent of its execution simulation. -/
theorem Lowered.instruction_check_extends {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {instruction stack}
    (lowered : Lowered before after instruction stack)
    (tables : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function) :
    InstructionCheckExtends before.function after.function := by
  have lengths := congrArg (fun tables => (tables.indirect.length,tables.simd.length,tables.constants.length,tables.jumpTables.length)) tables
  simp only [CompilerTables.ofFunction,Prod.mk.injEq] at lengths
  refine ⟨lowered.2.2.2.2,?_,?_,?_,?_,?_⟩
  · change before.function.code.val.length ≤ after.function.code.val.length
    rw [lowered.1,List.length_append,List.length_singleton]
    omega
  · change before.function.indirect.val.length ≤ after.function.indirect.val.length
    omega
  · change before.function.simd.val.length ≤ after.function.simd.val.length
    omega
  · change before.function.v128_pool.val.length ≤ after.function.v128_pool.val.length
    omega
  · change before.function.jump_tables.val.length ≤ after.function.jump_tables.val.length
    omega

/-- Unchanged captured tables and numerical code/slot growth preserve all
checker index spaces, independently of compiler control-stack mutations. -/
theorem InstructionCheckExtends.of_tables_equal (before after : runtime.bytecode.CompiledFunction)
    (tables : CompilerTables.ofFunction after = CompilerTables.ofFunction before)
    (slots : before.slot_count.val ≤ after.slot_count.val) (code : before.code.length ≤ after.code.length) :
    InstructionCheckExtends before after := by
  have lengths := congrArg (fun tables => (tables.indirect.length,tables.simd.length,tables.constants.length,tables.jumpTables.length)) tables
  simp only [CompilerTables.ofFunction,Prod.mk.injEq] at lengths
  refine ⟨slots,code,?_,?_,?_,?_⟩
  · change before.indirect.val.length ≤ after.indirect.val.length
    omega
  · change before.simd.val.length ≤ after.simd.val.length
    omega
  · change before.v128_pool.val.length ≤ after.v128_pool.val.length
    omega
  · change before.jump_tables.val.length ≤ after.jump_tables.val.length
    omega

/-- A lowered instruction with source-derived operands extends the open check
invariant without assuming validity of the completed function. -/
theorem Lowered.open_instruction_prefix {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {instruction stack} {pending next : Nat → Prop}
    (lowered : Lowered before after instruction stack)
    (tables : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function)
    (held : OpenInstructionPrefix before.function pending) (owners : ∀ index, pending index → next index)
    (valid : runtime.bytecode.CompiledFunction.instruction_valid after.function instruction = .ok true) :
    OpenInstructionPrefix after.function next :=
  held.append (lowered.instruction_check_extends tables) owners [instruction] lowered.1 (by simpa using valid)

end Itasca.Compiler

end

/-! ## Open Instruction Compiler -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- A pending branch site has a physical owner that will patch its target.
The code check also covers instructions outside semantically reachable paths. -/
def PendingInstructionSite (compiler : runtime.compiler.FunctionCompiler A) (index : Nat) : Prop :=
  ∃ frame ∈ compiler.frames.val, ∃ site : Usize, site.val = index ∧
    (frame.if_pc = some site ∨ site ∈ frame.fixups.val)

def CompilerInstructionPrefix (compiler : runtime.compiler.FunctionCompiler A) : Prop :=
  OpenInstructionPrefix compiler.function (PendingInstructionSite compiler)

/-- Actual fresh construction and function-start establish the empty checked
prefix without assuming an accepted instruction trace or function certificate. -/
theorem compiler_start_instruction_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (signatures : Slice runtime.compiler.Signature)
    (functionSlots : Slice U32) (budget : runtime.compiler.Budget A) (batchStart : Usize)
    (initial started : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (signature : runtime.compiler.Signature)
    (bodyBegin bodyEnd : Usize)
    (lookup : signatures.val[typeIndex.val]? = some signature)
    (beginFits : batchStart.val+bodyBegin.val ≤ Usize.max)
    (endFits : batchStart.val+bodyEnd.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (begun : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial ctx typeIndex bodyBegin bodyEnd = .ok (.Ok (),started)) : CompilerInstructionPrefix started := by
  have newPost := compiler_new ops signatures functionSlots budget batchStart
  rw [created,WP.spec_ok] at newPost
  obtain ⟨layout,emptyLocals,emptyOperands,emptyMaps,emptyFrames,emptyCode,reachable,sigs,widths,coordinate⟩ := newPost
  have startPost := compiler_function_start_raw ops law initial ctx typeIndex signature bodyBegin bodyEnd
    (by simpa only [sigs] using lookup) (by simpa only [coordinate] using beginFits)
    (by simpa only [coordinate] using endFits) emptyLocals layout emptyOperands
    (by simp [emptyMaps]; scalar_tac) (by simp [emptyFrames]; scalar_tac)
  rw [begun,WP.spec_ok] at startPost
  obtain ⟨_,code,_⟩ := startPost rfl
  intro index instruction found
  rw [code,emptyCode] at found
  simp at found

end Itasca.Compiler

end

end

/-! ## CoreEmissionInstructionPrefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Source layouts at the two ends of actual lowering bound both operand
regions in the resulting function. -/
theorem Lowered.source_capacities {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction : runtime.bytecode.Instr} {input output : List valtype} (lowered : Lowered before after instruction output)
    (layout : CompilerLayout before input) (live : before.reachable = true) :
    slots (compilerLocals before)+slots input ≤ after.function.slot_count.val ∧
    slots (compilerLocals before)+slots output ≤ after.function.slot_count.val := by
  refine ⟨(layout.live_slots_fit live).trans lowered.2.2.2.2,?_⟩
  simpa only [lowered.2.2.1] using lowered.2.1.live_slots_fit (lowered.2.2.2.1.trans live)

/-- Actual ordinary lowering derives every new instruction check from its
source emission record and preserves the open prefix's earlier checks. -/
theorem Lowered.float_core_instruction_prefix {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {instruction input output source C}
    (lowered : Lowered before after instruction output) (layout : CompilerLayout before input)
    (live : before.reachable = true) (locals : C.LOCALS = compilerLocals before)
    (emission : ScalarEmission C input source [instruction] output)
    (tables : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function)
    (held : CompilerInstructionPrefix before) (frames : after.frames = before.frames) :
    CompilerInstructionPrefix after := by
  obtain ⟨inputs,outputs⟩ := lowered.source_capacities layout live
  have valid := emission.instructions_accept after.function (by simpa only [locals] using inputs) (by simpa only [locals] using outputs)
  apply lowered.open_instruction_prefix tables held (valid := valid instruction (by simp))
  intro index owned
  simpa only [PendingInstructionSite,frames] using owned

end Itasca.Compiler

end

/-! ## LinearEmissionInstructionPrefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Literal, local, and integer lowering derives its instruction check from
source stack regions and retains every prior pending branch owner. -/
theorem Lowered.linear_instruction_prefix {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {instruction input output source}
    (lowered : Lowered before after instruction output) (layout : CompilerLayout before input)
    (live : before.reachable = true)
    (emission : LinearEmission (compilerLocals before) input source [instruction] output)
    (tables : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function)
    (held : CompilerInstructionPrefix before) (frames : after.frames = before.frames) :
    CompilerInstructionPrefix after := by
  obtain ⟨inputs,outputs⟩ := lowered.source_capacities layout live
  have valid := emission.instructions_accept after.function inputs outputs
  apply lowered.open_instruction_prefix tables held (valid := valid instruction (by simp))
  intro index owned
  simpa only [PendingInstructionSite,frames] using owned

end Itasca.Compiler

end

/-! ## FrameExitSlotBounds -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- A recorded forward exit retains enough slots for its result transfer even
when subsequent source instructions are unreachable and observations clear the
operand stack. Loop backedges do not set this flag. -/
def FrameExitSlotBounds (compiler : runtime.compiler.FunctionCompiler A) : Prop :=
  ∀ frame ∈ compiler.frames.val, frame.end_reachable = true →
    frame.height.val+frame.results.val ≤ compiler.function.slot_count.val

/-- Fixed frames retain recorded exits as slot capacity increases. -/
theorem FrameExitSlotBounds.retained {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : FrameExitSlotBounds before) (frames : after.frames.val = before.frames.val)
    (capacity : before.function.slot_count.val ≤ after.function.slot_count.val) : FrameExitSlotBounds after := by
  intro frame member live
  rw [frames] at member
  exact (held frame member live).trans capacity

/-- Fresh scope entry has no recorded forward exit. -/
theorem FrameExitSlotBounds.push {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : FrameExitSlotBounds before) (frame : runtime.compiler.Frame)
    (frames : after.frames.val = before.frames.val++[frame]) (fresh : frame.end_reachable = false)
    (capacity : before.function.slot_count.val ≤ after.function.slot_count.val) : FrameExitSlotBounds after := by
  intro selected member live
  rw [frames] at member
  rcases List.mem_append.mp member with old | last
  · exact (held selected old live).trans capacity
  · have same : selected = frame := by simpa only [List.mem_singleton] using last
    subst selected
    simp [fresh] at live

/-- Scope close removes one owner while retaining outer exit bounds. -/
theorem FrameExitSlotBounds.pop {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : FrameExitSlotBounds before) (frame : runtime.compiler.Frame)
    (frames : before.frames.val = after.frames.val++[frame])
    (capacity : before.function.slot_count.val ≤ after.function.slot_count.val) : FrameExitSlotBounds after := by
  intro selected member live
  exact (held selected (by rw [frames]; exact List.mem_append_left _ member) live).trans capacity

/-- An actual forward branch or live ELSE records a checked result interval.
Changing fixups does not change the selected frame's transfer geometry. -/
theorem FrameExitSlotBounds.record {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : FrameExitSlotBounds before) (index : Nat) (frame : runtime.compiler.Frame)
    (fixups : alloc.vec.Vec Usize)
    (frames : after.frames.val = before.frames.val.set index {frame with end_reachable := true,fixups})
    (capacity : before.function.slot_count.val ≤ after.function.slot_count.val)
    (region : frame.height.val+frame.results.val ≤ after.function.slot_count.val) : FrameExitSlotBounds after := by
  intro selected member live
  rw [frames] at member
  rcases List.mem_or_eq_of_mem_set member with old | fresh
  · exact (held selected old live).trans capacity
  · subst selected
    exact region

end Itasca.Compiler

end

/-! ## OpenInstructionFragment -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Appending a control fragment retains old checks and supplies each new word's
own check at its absolute bytecode coordinate, including pending branch sites. -/
theorem OpenInstructionPrefix.append_open {before after : runtime.bytecode.CompiledFunction}
    {pending next : Nat → Prop} (held : OpenInstructionPrefix before pending)
    (growth : InstructionCheckExtends before after) (owners : ∀ index, pending index → next index)
    (fragment : List runtime.bytecode.Instr) (code : after.code.val = before.code.val++fragment)
    (fresh : ∀ index instruction, fragment[index]? = some instruction →
      OpenInstructionCheck after next (before.code.length+index) instruction) :
    OpenInstructionPrefix after next := by
  intro index instruction found
  rw [code] at found
  by_cases inside : index < before.code.val.length
  · rw [List.getElem?_append_left inside] at found
    exact (held index instruction found).grow growth (owners index)
  · rw [List.getElem?_append_right (by omega : before.code.val.length ≤ index)] at found
    have checked := fresh (index-before.code.val.length) instruction found
    have same : before.code.length+(index-before.code.val.length) = index := by
      change before.code.val.length+(index-before.code.val.length) = index
      omega
    simpa only [same] using checked

end Itasca.Compiler

end

/-! ## InstructionAppendEffect -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Concrete append effects separate local emission checks and ownership
transport from the retained prefix. This also supports temporary table builders. -/
def InstructionAppendEffect {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  InstructionCheckExtends before.function after.function ∧
    ∃ fragment : List runtime.bytecode.Instr,
      after.function.code.val = before.function.code.val++fragment ∧
      (∀ index, PendingInstructionSite before index → PendingInstructionSite after index) ∧
      (∀ index instruction, fragment[index]? = some instruction →
        OpenInstructionCheck after.function (PendingInstructionSite after) (before.function.code.length+index) instruction)

/-- Every recorded append effect preserves a complete prefix check. -/
theorem InstructionAppendEffect.apply {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (effect : InstructionAppendEffect before after) (held : CompilerInstructionPrefix before) :
    CompilerInstructionPrefix after := by
  obtain ⟨growth,fragment,code,owners,fresh⟩ := effect
  exact held.append_open growth owners fragment code fresh

/-- Metadata preparation followed by a branch append has the same concrete
append effect at the original instruction position. -/
theorem InstructionAppendEffect.prepend_unchanged {A : Type}
    {before middle after : runtime.compiler.FunctionCompiler A}
    (first : InstructionAppendEffect before middle)
    (unchanged : middle.function.code = before.function.code)
    (second : InstructionAppendEffect middle after) : InstructionAppendEffect before after := by
  obtain ⟨growth,_,_,owners,_⟩ := first
  obtain ⟨growth',fragment,code,owners',fresh⟩ := second
  refine ⟨growth.trans growth',fragment,?_,fun index owned => owners' index (owners index owned),?_⟩
  · simpa only [unchanged] using code
  · simpa only [unchanged] using fresh

/-- A table builder temporarily defers checking its one dispatch word until
its target rows have been appended. Every other stored instruction is checked. -/
def OpenInstructionPrefixExcept (function : runtime.bytecode.CompiledFunction) (pending : Nat → Prop)
    (omitted : Nat) : Prop :=
  ∀ index instruction, index ≠ omitted → function.code.val[index]? = some instruction →
    OpenInstructionCheck function pending index instruction

def CompilerInstructionPrefixExcept (compiler : runtime.compiler.FunctionCompiler A) (omitted : Nat) : Prop :=
  OpenInstructionPrefixExcept compiler.function (PendingInstructionSite compiler) omitted

/-- Appending a checked branch stub preserves every table-builder obligation
apart from its explicitly deferred dispatch word. -/
theorem InstructionAppendEffect.apply_except {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (effect : InstructionAppendEffect before after) (omitted : Nat)
    (held : CompilerInstructionPrefixExcept before omitted) : CompilerInstructionPrefixExcept after omitted := by
  obtain ⟨growth,fragment,code,owners,fresh⟩ := effect
  intro index instruction different found
  rw [code] at found
  by_cases prior : index < before.function.code.val.length
  · rw [List.getElem?_append_left prior] at found
    exact (held index instruction different found).grow growth (owners index)
  · rw [List.getElem?_append_right (by omega : before.function.code.val.length ≤ index)] at found
    have checked := fresh (index-before.function.code.val.length) instruction found
    have same : before.function.code.length+(index-before.function.code.val.length) = index := by
      change before.function.code.val.length+(index-before.function.code.val.length) = index
      omega
    simpa only [same] using checked

/-- Deferral is discharged by an actual check of the retained dispatch word. -/
theorem CompilerInstructionPrefixExcept.complete {A : Type} {compiler : runtime.compiler.FunctionCompiler A} {omitted : Nat}
    (held : CompilerInstructionPrefixExcept compiler omitted)
    (dispatch : ∀ instruction, compiler.function.code.val[omitted]? = some instruction →
      runtime.bytecode.CompiledFunction.instruction_valid compiler.function instruction = .ok true) :
    CompilerInstructionPrefix compiler := by
  intro index instruction found
  by_cases same : index = omitted
  · subst index
    exact .checked (dispatch instruction found)
  · exact held index instruction same found

end Itasca.Compiler

end

/-! ## ForwardBranchInstructionPrefix -/

section

/-!
Checked prefixes for forward branches, including pending-site replacement and transfer instruction acceptance. Resolving a branch preserves all earlier open checks.
-/

/-! ## Branch Instruction Acceptance -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- A branch's overlap-safe copy fits from the independently checked source
and destination regions. Scalar/two-word copies are specialized by the runtime. -/
theorem transfer_instruction_accepts (function : runtime.bytecode.CompiledFunction)
    (dst src count : U32) (order : dst.val ≤ src.val)
    (source : src.val+count.val ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.instruction_valid function (transferInstruction dst src count) = .ok true := by
  unfold transferInstruction
  split
  · rename_i one
    exact (CoreInstructionBounds.copy (by omega) (by omega)).accepts
  · split
    · rename_i two
      exact (CoreInstructionBounds.copy2 (by omega) (by omega)).accepts
    · exact (CoreInstructionBounds.copyN (by omega) source order).accepts

/-- Every word in an unconditional branch fragment checks, with only the final
jump allowed to wait for its recorded control-frame owner. -/
theorem branch_instructions_open_checks (function : runtime.bytecode.CompiledFunction)
    (pending : Nat → Prop) (start : Nat) (dst src count target : U32)
    (order : dst.val ≤ src.val) (source : src.val+count.val ≤ function.slot_count.val)
    (ready : target.val ≤ function.code.length ∨ pending (start+(branchInstructions dst src count target).length-1)) :
    ∀ index instruction, (branchInstructions dst src count target)[index]? = some instruction →
      OpenInstructionCheck function pending (start+index) instruction := by
  by_cases elided : count = 0#u32 ∨ src = dst
  · simp only [branchInstructions,if_pos elided,List.length_singleton,Nat.add_sub_cancel] at ready
    intro index instruction found
    cases index with
    | zero =>
      have same : .Jump target = instruction := by simpa [branchInstructions,elided] using found
      rw [← same,Nat.add_zero]
      exact .jump ready
    | succ index => simp [branchInstructions,elided] at found
  · simp only [branchInstructions,if_neg elided,List.length_cons,List.length_nil] at ready
    intro index instruction found
    cases index with
    | zero =>
      have same : transferInstruction dst src count = instruction := by simpa [branchInstructions,elided] using found
      rw [← same]
      exact .checked (transfer_instruction_accepts function dst src count order source)
    | succ index =>
      cases index with
      | zero =>
        have same : .Jump target = instruction := by simpa [branchInstructions,elided] using found
        rw [← same]
        apply OpenInstructionCheck.jump
        simpa only [Nat.reduceAdd,show start+2-1 = start+1 by omega] using ready
      | succ index => simp [branchInstructions,elided] at found

/-- Conditional branch fragments check the selector and transfer immediately;
only their selected label target may remain pending. The skip address already
names the fragment's continuation. -/
theorem branch_if_instructions_open_checks (function : runtime.bytecode.CompiledFunction)
    (pending : Nat → Prop) (start : Nat) (dst src count target condition resume : U32)
    (order : dst.val ≤ src.val) (source : src.val+count.val ≤ function.slot_count.val)
    (test : condition.val+1 ≤ function.slot_count.val)
    (continuation : ¬ (count = 0#u32 ∨ src = dst) → resume.val ≤ function.code.length)
    (ready : target.val ≤ function.code.length ∨ pending (start+(branchIfInstructions dst src count target condition resume).length-1)) :
    ∀ index instruction, (branchIfInstructions dst src count target condition resume)[index]? = some instruction →
      OpenInstructionCheck function pending (start+index) instruction := by
  by_cases elided : count = 0#u32 ∨ src = dst
  · simp only [branchIfInstructions,if_pos elided,List.length_singleton,Nat.add_sub_cancel] at ready
    intro index instruction found
    cases index with
    | zero =>
      have same : .JumpIfNonZero condition target = instruction := by simpa [branchIfInstructions,elided] using found
      rw [← same,Nat.add_zero]
      exact .nonzero test ready
    | succ index => simp [branchIfInstructions,elided] at found
  · simp only [branchIfInstructions,if_neg elided,List.length_cons,List.length_nil] at ready
    intro index instruction found
    cases index with
    | zero =>
      have same : .JumpIfZero condition resume = instruction := by simpa [branchIfInstructions,elided] using found
      rw [← same]
      exact .zero test (.inl (continuation elided))
    | succ index =>
      cases index with
      | zero =>
        have same : transferInstruction dst src count = instruction := by simpa [branchIfInstructions,elided] using found
        rw [← same]
        exact .checked (transfer_instruction_accepts function dst src count order source)
      | succ index =>
        cases index with
        | zero =>
          have same : .Jump target = instruction := by simpa [branchIfInstructions,elided] using found
          rw [← same]
          apply OpenInstructionCheck.jump
          simpa only [Nat.reduceAdd,show start+3-1 = start+2 by omega] using ready
        | succ index => simp [branchIfInstructions,elided] at found

end Itasca.Compiler

end

/-! ## Pending Instruction Replace -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Recording a branch changes one frame's liveness and extends its fixups.
Every earlier pending instruction retains an owner, even if equal frame values
occur at more than one position. -/
theorem pending_instruction_replace {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (index : Nat) (frame replacement : runtime.compiler.Frame)
    (lookup : before.frames.val[index]? = some frame)
    (frames : after.frames.val = before.frames.val.set index replacement)
    (guard : replacement.if_pc = frame.if_pc)
    (fixups : ∀ site ∈ frame.fixups.val, site ∈ replacement.fixups.val)
    (position : Nat) (owned : PendingInstructionSite before position) : PendingInstructionSite after position := by
  obtain ⟨owner,member,site,atSite,kind⟩ := owned
  by_cases selected : owner = frame
  · subst owner
    have bound := (List.getElem?_eq_some_iff.mp lookup).1
    have found : after.frames.val[index]? = some replacement := by
      rw [frames,List.getElem?_set_self bound]
    obtain ⟨within,equal⟩ := List.getElem?_eq_some_iff.mp found
    refine ⟨replacement,equal ▸ List.getElem_mem within,site,atSite,?_⟩
    exact kind.imp (fun guarded => guard.trans guarded) (fixups site)
  · obtain ⟨ownerIndex,inside,equal⟩ := List.getElem_of_mem member
    have original : before.frames.val[ownerIndex]? = some owner := by
      simp [List.getElem?_eq_getElem inside,equal]
    have different : index ≠ ownerIndex := by
      intro same
      rw [← same,lookup] at original
      exact selected (Option.some.inj original).symm
    have found : after.frames.val[ownerIndex]? = some owner := by
      rw [frames,List.getElem?_set_ne different]
      exact original
    obtain ⟨within,equal⟩ := List.getElem?_eq_some_iff.mp found
    exact ⟨owner,equal ▸ List.getElem_mem within,site,atSite,kind⟩

/-- A captured fixup entry witnesses ownership at its exact code coordinate. -/
theorem pending_instruction_fixup {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (index : Nat) (frame : runtime.compiler.Frame) (site : Usize)
    (lookup : compiler.frames.val[index]? = some frame) (member : site ∈ frame.fixups.val) :
    PendingInstructionSite compiler site.val := by
  obtain ⟨within,equal⟩ := List.getElem?_eq_some_iff.mp lookup
  exact ⟨frame,equal ▸ List.getElem_mem within,site,rfl,Or.inr member⟩

end Itasca.Compiler

end

/-! ## Forward Branch Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Actual forward branching preserves every old instruction check, validates
its transfer, and records the final jump's pending owner. The skip parameter
also covers branch-table target stubs. -/
theorem compiler_branch_forward_instruction_effect {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : before.frames.val[index.val]? = some frame)
    (position : index.val+depth.val+1 = before.frames.val.length)
    (forward : frame.kind ≠ .Loop)
    (sourcePosition : source.val+frame.results.val+skip.val = before.height.val)
    (order : frame.height.val ≤ source.val)
    (sourceFits : source.val+frame.results.val ≤ before.function.slot_count.val)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : before.function.code.val.length+2 ≤ Usize.max)
    (offsetsFit : before.function.source_offsets.val.length+2 ≤ Usize.max)
    (coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth skip false = .ok (.Ok (),after)) :
    InstructionAppendEffect before after := by
  obtain ⟨fixups,site,frames,code,siteAt,appended⟩ : ∃ fixups site,
      after.frames.val = before.frames.val.set index.val {frame with end_reachable := true,fixups} ∧
      after.function.code.val = before.function.code.val++branchInstructions frame.height source frame.results core.num.U32.MAX ∧
      site.val = before.function.code.length+(branchInstructions frame.height source frame.results core.num.U32.MAX).length-1 ∧
      fixups.val = frame.fixups.val++[site] := by
    by_cases elided : frame.results = 0#u32 ∨ source = frame.height
    · have effect := branch_elided_forward_with_skip ops law before frame index depth source skip lookup position forward elided
        sourcePosition fixupsFit (by omega) (by omega) coordinateFits
      rw [called,WP.spec_ok] at effect
      obtain ⟨code,fixups,site,siteAt,frames,appended⟩ := effect rfl
      exact ⟨fixups,site,frames,by simpa [branchInstructions,elided] using code,
        by simpa [branchInstructions,elided] using siteAt,appended⟩
    · have effect := branch_transfer_forward_with_skip ops law before frame index depth source skip lookup position forward
        (fun eq => elided (.inl eq)) (fun eq => elided (.inr eq)) sourcePosition fixupsFit codeFits offsetsFit coordinateFits
      rw [called,WP.spec_ok] at effect
      obtain ⟨code,fixups,site,siteAt,frames,appended⟩ := effect rfl
      exact ⟨fixups,site,frames,by simpa [branchInstructions,elided] using code,
        by simpa [branchInstructions,elided,Nat.add_sub_assoc] using siteAt,appended⟩
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_branch_tables ops law before after depth skip false called)
    (compiler_branch_stable_result ops law before after depth skip false (.Ok ()) called).capacity
    (compiler_branch_code_mono ops law before after depth skip false (.Ok ()) called)
  have bound := (List.getElem?_eq_some_iff.mp lookup).1
  have selected : after.frames.val[index.val]? = some {frame with end_reachable := true,fixups} := by
    rw [frames,List.getElem?_set_self bound]
  have pending := pending_instruction_fixup after index.val _ site selected (by change site ∈ fixups.val; simp [appended])
  refine ⟨growth,_,code,?_,?_⟩
  · intro position owned
    exact pending_instruction_replace index.val frame _ lookup frames rfl
      (by intro site member; change site ∈ fixups.val; rw [appended]; exact List.mem_append_left _ member) position owned
  · apply branch_instructions_open_checks after.function (PendingInstructionSite after) before.function.code.length
      frame.height source frame.results core.num.U32.MAX order (sourceFits.trans growth.slots)
    exact .inr (by rw [← siteAt]; exact pending)

/-- Apply the concrete append effect to the current checked prefix. -/
theorem compiler_branch_forward_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : before.frames.val[index.val]? = some frame)
    (position : index.val+depth.val+1 = before.frames.val.length)
    (forward : frame.kind ≠ .Loop)
    (sourcePosition : source.val+frame.results.val+skip.val = before.height.val)
    (order : frame.height.val ≤ source.val)
    (sourceFits : source.val+frame.results.val ≤ before.function.slot_count.val)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : before.function.code.val.length+2 ≤ Usize.max)
    (offsetsFit : before.function.source_offsets.val.length+2 ≤ Usize.max)
    (coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth skip false = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after :=
  (compiler_branch_forward_instruction_effect ops law before after frame index depth source skip lookup position forward sourcePosition order sourceFits fixupsFit codeFits offsetsFit coordinateFits called).apply held

end Itasca.Compiler

end

end

/-! ## OpenInstructionPatch -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Patching a branch to the current exit replaces its outstanding target
obligation. Condition operands retain their existing slot bounds. -/
theorem OpenInstructionCheck.retarget {before after : runtime.bytecode.CompiledFunction}
    {pending next : Nat → Prop} {index instruction}
    (held : OpenInstructionCheck before pending index instruction)
    (growth : InstructionCheckExtends before after) (target : U32)
    (inside : target.val ≤ after.code.length) :
    OpenInstructionCheck after next index (retarget instruction target) := by
  cases held with
  | checked accepted =>
    unfold Itasca.Compiler.retarget
    split
    · exact .jump (.inl inside)
    · exact .zero (Nat.le_trans (by have bound := jump_if_zero_valid_bounds before _ _ accepted; omega) growth.slots) (.inl inside)
    · exact .nonzero (Nat.le_trans (by have bound := jump_if_non_zero_valid_bounds before _ _ accepted; omega) growth.slots) (.inl inside)
    · exact .checked (instruction_valid_monotone before after _ growth accepted)
  | jump _ => exact .jump (.inl inside)
  | zero slot _ => exact .zero (slot.trans growth.slots) (.inl inside)
  | nonzero slot _ => exact .nonzero (slot.trans growth.slots) (.inl inside)

/-- Once the patched target names a stored instruction, the branch check is
complete; pending ownership is no longer needed for that word. -/
theorem OpenInstructionCheck.retarget_accepts {before after : runtime.bytecode.CompiledFunction}
    {pending : Nat → Prop} {index instruction}
    (held : OpenInstructionCheck before pending index instruction)
    (growth : InstructionCheckExtends before after) (target : U32)
    (inside : target.val < after.code.length) :
    runtime.bytecode.CompiledFunction.instruction_valid after (Itasca.Compiler.retarget instruction target) = .ok true := by
  cases held with
  | checked accepted =>
    by_cases jump : ∃ old, instruction = .Jump old
    · obtain ⟨old,rfl⟩ := jump
      exact (CoreInstructionBounds.jump inside).accepts
    by_cases zero : ∃ condition old, instruction = .JumpIfZero condition old
    · obtain ⟨condition,old,rfl⟩ := zero
      have bound := jump_if_zero_valid_bounds before condition old accepted
      exact (CoreInstructionBounds.jumpIfZero (by have capacity := growth.slots; omega) inside).accepts
    by_cases nonzero : ∃ condition old, instruction = .JumpIfNonZero condition old
    · obtain ⟨condition,old,rfl⟩ := nonzero
      have bound := jump_if_non_zero_valid_bounds before condition old accepted
      exact (CoreInstructionBounds.jumpIfNonZero (by have capacity := growth.slots; omega) inside).accepts
    have same : Itasca.Compiler.retarget instruction target = instruction := by
      unfold Itasca.Compiler.retarget
      split <;> simp_all
    rw [same]
    exact instruction_valid_monotone before after instruction growth accepted
  | jump _ => exact (CoreInstructionBounds.jump inside).accepts
  | zero slot _ => exact (CoreInstructionBounds.jumpIfZero (slot.trans growth.slots) inside).accepts
  | nonzero slot _ => exact (CoreInstructionBounds.jumpIfNonZero (slot.trans growth.slots) inside).accepts

/-- Patching removes precisely the target obligations at the listed bytecode
positions. Every unpatched pending site must retain its owner. -/
theorem OpenInstructionPrefix.patch {before after : runtime.bytecode.CompiledFunction}
    {pending next : Nat → Prop} (held : OpenInstructionPrefix before pending)
    (growth : InstructionCheckExtends before after) (sites : List Usize) (target : U32)
    (code : after.code.val = patchCode before.code.val sites target)
    (inside : target.val ≤ after.code.length)
    (owners : ∀ index, (∀ site ∈ sites, site.val ≠ index) → pending index → next index) :
    OpenInstructionPrefix after next := by
  intro index instruction found
  rw [code,patch_code_get] at found
  split at found
  · rename_i changed
    cases original : before.code.val[index]? with
    | none => simp [original] at found
    | some prior =>
      have same : retarget prior target = instruction := by simpa [original] using found
      rw [← same]
      exact (held index prior original).retarget growth target inside
  · rename_i unchanged
    exact (held index instruction found).grow growth (owners index (by simpa using unchanged))

end Itasca.Compiler

end

/-! ## ScopeEntryInstructionPrefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

private theorem pending_append {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {frame : runtime.compiler.Frame} (frames : after.frames.val = before.frames.val++[frame])
    (index : Nat) (owned : PendingInstructionSite before index) : PendingInstructionSite after index := by
  obtain ⟨owner,member,site,position,kind⟩ := owned
  refine ⟨owner,?_,site,position,kind⟩
  rw [frames]
  exact List.mem_append_left _ member

/-- Actual live and dead scope entry preserves checking of every old instruction.
LOOP checks its hook; IF checks its condition and records ownership of the new
forward guard. The premises describe only the current source-reader boundary. -/
theorem compiler_scope_entry_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (geometry : ScopeEntryGeometry before state bt) (mode : ScopeEntryMode geometry kind)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_enter_tables ops law before after state kind bt called)
    (compiler_enter_stable_result ops law before after state kind bt (.Ok ()) called).capacity
    (compiler_enter_code_mono ops law before after state kind bt called)
  cases mode with
  | block live position =>
    have effect := enter_block ops law before state geometry.ctrl geometry.prior bt geometry.signature geometry.pc
      geometry.controls geometry.selected geometry.valuesFit geometry.heightFits geometry.sourceFits position
      geometry.mapsFit geometry.framesFit live
    rw [called,WP.spec_ok] at effect
    obtain ⟨code,_,height,source,_,_,frames,_⟩ := effect rfl
    exact held.append growth (pending_append frames) [] (by simpa using congrArg alloc.vec.Vec.val code) (by simp)
  | loop live position codeFits offsetsFit =>
    have effect := enter_loop ops law before state geometry.ctrl geometry.prior bt geometry.signature geometry.pc
      geometry.controls geometry.selected geometry.valuesFit geometry.heightFits geometry.sourceFits position codeFits offsetsFit
      geometry.mapsFit geometry.framesFit live
    rw [called,WP.spec_ok] at effect
    obtain ⟨code,_,height,source,_,_,frames,_⟩ := effect rfl
    apply held.append growth (pending_append frames) [.LoopHead] code
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    exact CoreInstructionBounds.accepts .loopHead
  | if_ stack layout live position codeFits offsetsFit =>
    have effect := enter_if ops law before state geometry.ctrl geometry.prior bt geometry.signature geometry.pc
      stack layout codeFits offsetsFit geometry.controls geometry.selected geometry.valuesFit geometry.heightFits
      geometry.sourceFits position geometry.mapsFit geometry.framesFit live
    rw [called,WP.spec_ok] at effect
    obtain ⟨_,condition,height,source,conditionPosition,code,_,_,frames,_⟩ := effect rfl
    apply held.append_open growth (pending_append frames) [.JumpIfZero condition core.num.U32.MAX] code
    intro index instruction found
    cases index with
    | zero =>
      have same : .JumpIfZero condition core.num.U32.MAX = instruction := by simpa using found
      rw [← same]
      apply OpenInstructionCheck.zero
      · have fits := layout.live_slots_fit live
        simp only [slots_append,slots,width] at fits
        have capacity := growth.slots
        omega
      · apply Or.inr
        unfold PendingInstructionSite
        rw [frames]
        refine ⟨_,List.mem_append_right _ (List.mem_singleton_self _),_,?_,Or.inl rfl⟩
        rfl
    | succ index => simp at found
  | dead kind dormant position =>
    have effect := enter_dead ops law before state geometry.ctrl geometry.prior kind bt geometry.signature geometry.pc
      geometry.controls geometry.selected geometry.valuesFit geometry.heightFits geometry.sourceFits position
      geometry.mapsFit geometry.framesFit dormant
    rw [called,WP.spec_ok] at effect
    obtain ⟨code,_,height,source,_,_,frames,_⟩ := effect rfl
    exact held.append growth (pending_append frames) [] (by simpa using congrArg alloc.vec.Vec.val code) (by simp)

end Itasca.Compiler

end

end

/-! ## BranchAndScalarChecks -/

section

open Itasca.Representation

/-!
# Branch And Scalar Checks

Scalar exit slots and loop or branch prefixes satisfy instruction-check acceptance for their emitted code.
-/

/-! ## ScalarExitSlotBounds -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation
set_option maxRecDepth 4096

/-- Ordinary metadata retention preserves all previously recorded result regions. -/
theorem CompilerOrdinaryStable.exit_slots {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (stable : CompilerOrdinaryStable before after) (held : FrameExitSlotBounds before) : FrameExitSlotBounds after :=
  held.retained (congrArg alloc.vec.Vec.val stable.frames) stable.capacity

end Itasca.Compiler

end

/-! ## ConditionalInstructionPrefix -/

section

/-!
Checked instruction-prefix preservation for forward and loop conditional branches, used by branch callback certification.
-/

/-! ## Conditional Forward Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Actual conditional forward branching checks its condition and transfer,
retains the local skip address, and records its final jump's pending owner. -/
theorem compiler_branch_if_forward_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition resume : U32)
    (lookup : before.frames.val[index.val]? = some frame)
    (position : index.val+depth.val+1 = before.frames.val.length) (forward : frame.kind ≠ .Loop)
    (sourcePosition : source.val+frame.results.val+1 = before.height.val)
    (conditionAt : before.before.val[before.before.val.length-1]? = some condition)
    (resumePosition : resume.val = before.function.code.val.length+3)
    (order : frame.height.val ≤ source.val)
    (sourceFits : source.val+frame.results.val ≤ before.function.slot_count.val)
    (test : condition.val+1 ≤ before.function.slot_count.val)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth 1#u32 true = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  obtain ⟨fixups,site,frames,code,siteAt,appended⟩ : ∃ fixups site,
      after.frames.val = before.frames.val.set index.val {frame with end_reachable := true,fixups} ∧
      after.function.code.val = before.function.code.val++branchIfInstructions frame.height source frame.results core.num.U32.MAX condition resume ∧
      site.val = before.function.code.length+(branchIfInstructions frame.height source frame.results core.num.U32.MAX condition resume).length-1 ∧
      fixups.val = frame.fixups.val++[site] := by
    by_cases elided : frame.results = 0#u32 ∨ source = frame.height
    · obtain ⟨code,fixups,site,siteAt,frames,appended⟩ := branch_if_elided_forward_success ops law before frame index depth source condition
        lookup position forward elided sourcePosition conditionAt after called
      exact ⟨fixups,site,frames,by simpa [branchIfInstructions,elided] using code,
        by simpa [branchIfInstructions,elided] using siteAt,appended⟩
    · obtain ⟨code,fixups,site,siteAt,frames,appended⟩ := branch_if_transfer_forward_success ops law before frame index depth source condition resume
        lookup position forward (fun eq => elided (.inl eq)) (fun eq => elided (.inr eq)) sourcePosition conditionAt resumePosition after called
      exact ⟨fixups,site,frames,by simpa [branchIfInstructions,elided] using code,
        by simpa [branchIfInstructions,elided,Nat.add_sub_assoc] using siteAt,appended⟩
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_branch_tables ops law before after depth 1#u32 true called)
    (compiler_branch_stable_result ops law before after depth 1#u32 true (.Ok ()) called).capacity
    (compiler_branch_code_mono ops law before after depth 1#u32 true (.Ok ()) called)
  have bound := (List.getElem?_eq_some_iff.mp lookup).1
  have selected : after.frames.val[index.val]? = some {frame with end_reachable := true,fixups} := by
    rw [frames,List.getElem?_set_self bound]
  have pending := pending_instruction_fixup after index.val _ site selected (by change site ∈ fixups.val; simp [appended])
  refine held.append_open growth ?_ _ code ?_
  · intro position owned
    exact pending_instruction_replace index.val frame _ lookup frames rfl
      (by intro site member; change site ∈ fixups.val; rw [appended]; exact List.mem_append_left _ member) position owned
  · apply branch_if_instructions_open_checks after.function (PendingInstructionSite after) before.function.code.length
      frame.height source frame.results core.num.U32.MAX condition resume order (sourceFits.trans growth.slots) (test.trans growth.slots)
    · intro transfer
      change resume.val ≤ after.function.code.val.length
      rw [code,branchIfInstructions,if_neg transfer,List.length_append]
      simp only [List.length_cons,List.length_nil]
      omega
    · exact .inr (by rw [← siteAt]; exact pending)

end Itasca.Compiler

end

/-! ## Conditional Loop Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Actual conditional loop branching checks its selector and transfer, retains
its backward target, and preserves all previously recorded pending owners. -/
theorem compiler_branch_if_loop_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition resume : U32)
    (lookup : before.frames.val[index.val]? = some frame)
    (position : index.val+depth.val+1 = before.frames.val.length) (loop : frame.kind = .Loop)
    (sourcePosition : source.val+frame.params.val+1 = before.height.val)
    (conditionAt : before.before.val[before.before.val.length-1]? = some condition)
    (resumePosition : resume.val = before.function.code.val.length+3)
    (order : frame.height.val ≤ source.val)
    (sourceFits : source.val+frame.params.val ≤ before.function.slot_count.val)
    (test : condition.val+1 ≤ before.function.slot_count.val)
    (target : frame.start_pc.val ≤ before.function.code.length)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth 1#u32 true = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have effect : after.function.code.val = before.function.code.val++branchIfInstructions frame.height source frame.params frame.start_pc condition resume ∧
      after.frames = before.frames := by
    by_cases elided : frame.params = 0#u32 ∨ source = frame.height
    · obtain ⟨code,frames⟩ := branch_if_elided_loop_success ops law before frame index depth source condition
        lookup position loop elided sourcePosition conditionAt after called
      exact ⟨by simpa [branchIfInstructions,elided] using code,frames⟩
    · obtain ⟨code,frames⟩ := branch_if_transfer_loop_success ops law before frame index depth source condition resume
        lookup position loop (fun eq => elided (.inl eq)) (fun eq => elided (.inr eq)) sourcePosition conditionAt resumePosition after called
      exact ⟨by simpa [branchIfInstructions,elided] using code,frames⟩
  obtain ⟨code,frames⟩ := effect
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_branch_tables ops law before after depth 1#u32 true called)
    (compiler_branch_stable_result ops law before after depth 1#u32 true (.Ok ()) called).capacity
    (compiler_branch_code_mono ops law before after depth 1#u32 true (.Ok ()) called)
  refine held.append_open growth ?_ _ code ?_
  · intro index owned
    simpa only [PendingInstructionSite,frames] using owned
  · apply branch_if_instructions_open_checks after.function (PendingInstructionSite after) before.function.code.length
      frame.height source frame.params frame.start_pc condition resume order (sourceFits.trans growth.slots) (test.trans growth.slots)
    · intro transfer
      change resume.val ≤ after.function.code.val.length
      rw [code,branchIfInstructions,if_neg transfer,List.length_append]
      simp only [List.length_cons,List.length_nil]
      omega
    · exact .inl (target.trans growth.code)

end Itasca.Compiler

end

end

/-! ## NumericInstructionPrefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std SourceMachine.Numeric

/-- Observation preserves every instruction's operand check and pending branch
owner, including in an unreachable source region. -/
theorem compiler_observe_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.observe ops before state = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have stable := compiler_observe_stable ops law before after state called
  have frame := compiler_observe_frame ops law before state
  rw [called,WP.spec_ok] at frame
  dsimp only at frame
  have growth : InstructionCheckExtends before.function after.function := by
    refine ⟨stable.capacity,?_,?_,?_,?_,?_⟩ <;> rw [frame] <;> exact le_rfl
  have same : after.function.code.val = before.function.code.val := by rw [frame]
  refine held.append growth ?_ [] (by simpa using same) (by simp)
  intro index owned
  have frames : after.frames = before.frames := by rw [frame]
  simpa only [PendingInstructionSite,frames] using owned

end Itasca.Compiler

end

/-! ## BranchCallbackExitSlots -/

section

/-!
Exit-slot bounds for branch instructions and their public compiler callbacks. The callback theorem includes observation and branch-specific slot obligations.
-/

/-! ## Branch Exit Slot Bounds -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- The source transfer interval pays for a recorded forward exit. This holds
for ordinary branches and selector-skipping table stubs. -/
theorem compiler_branch_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (frame : runtime.compiler.Frame) (depth source skip : U32)
    (found : before.frames.val[index.val]? = some frame)
    (position : index.val+depth.val+1 = before.frames.val.length)
    (sourcePosition : source.val+(frameBranchWidth frame).val+skip.val = before.height.val)
    (order : frame.height.val ≤ source.val)
    (sourceFits : source.val+(frameBranchWidth frame).val ≤ before.function.slot_count.val)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth skip false = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  have capacity := (compiler_branch_stable_result ops law before after depth skip false (.Ok ()) called).capacity
  by_cases loop : frame.kind = .Loop
  · have operands : source.val+frame.params.val+skip.val = before.height.val := by
      simpa only [frameBranchWidth,loop] using sourcePosition
    obtain ⟨_,frames⟩ := compiler_branch_loop_skip_success ops law before frame index depth source skip
      found position loop operands after called
    exact held.retained (congrArg alloc.vec.Vec.val frames) capacity
  · have width : frameBranchWidth frame = frame.results := by
      cases kind : frame.kind <;> simp_all [frameBranchWidth]
    obtain ⟨fixups,frames,_⟩ := compiler_branch_forward_skip_success ops law before frame index depth source skip
      found position loop (by simpa only [width] using sourcePosition) after called
    apply held.record index.val frame fixups frames capacity
    rw [width] at sourceFits
    omega

/-- A conditional branch records the same checked exit interval while retaining
its condition and local continuation in the ordinary instruction invariant. -/
theorem compiler_branch_if_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (frame : runtime.compiler.Frame) (depth source condition resume : U32)
    (found : before.frames.val[index.val]? = some frame)
    (position : index.val+depth.val+1 = before.frames.val.length)
    (sourcePosition : source.val+(frameBranchWidth frame).val+1 = before.height.val)
    (conditionAt : before.before.val[before.before.val.length-1]? = some condition)
    (resumeAt : resume.val = before.function.code.val.length+3)
    (order : frame.height.val ≤ source.val)
    (sourceFits : source.val+(frameBranchWidth frame).val ≤ before.function.slot_count.val)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth 1#u32 true = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  have capacity := (compiler_branch_stable_result ops law before after depth 1#u32 true (.Ok ()) called).capacity
  by_cases loop : frame.kind = .Loop
  · have operands : source.val+frame.params.val+1 = before.height.val := by
      simpa only [frameBranchWidth,loop] using sourcePosition
    have frames : after.frames = before.frames := by
      by_cases elided : frame.params = 0#u32 ∨ source = frame.height
      · exact (branch_if_elided_loop_success ops law before frame index depth source condition
          found position loop elided operands conditionAt after called).2
      · exact (branch_if_transfer_loop_success ops law before frame index depth source condition resume
          found position loop (fun eq => elided (.inl eq)) (fun eq => elided (.inr eq)) operands conditionAt resumeAt after called).2
    exact held.retained (congrArg alloc.vec.Vec.val frames) capacity
  · have width : frameBranchWidth frame = frame.results := by
      cases kind : frame.kind <;> simp_all [frameBranchWidth]
    have operands : source.val+frame.results.val+1 = before.height.val := by simpa only [width] using sourcePosition
    obtain ⟨fixups,frames⟩ : ∃ fixups, after.frames.val = before.frames.val.set index.val
        {frame with end_reachable := true,fixups} := by
      by_cases elided : frame.results = 0#u32 ∨ source = frame.height
      · obtain ⟨_,fixups,_,_,frames,_⟩ := branch_if_elided_forward_success ops law before frame index depth source condition
          found position loop elided operands conditionAt after called
        exact ⟨fixups,frames⟩
      · obtain ⟨_,fixups,_,_,frames,_⟩ := branch_if_transfer_forward_success ops law before frame index depth source condition resume
          found position loop (fun eq => elided (.inl eq)) (fun eq => elided (.inr eq)) operands conditionAt resumeAt after called
        exact ⟨fixups,frames⟩
    apply held.record index.val frame fixups frames capacity
    rw [width] at sourceFits
    omega

end Itasca.Compiler

end

/-! ## Branch Callback Exit Slots -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

/-- Actual operand observation preserves every recorded forward-exit region. -/
theorem compiler_observe_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (held : FrameExitSlotBounds before)
    (called : runtime.compiler.FunctionCompiler.observe ops before state = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  have frame := compiler_observe_frame ops law before state
  rw [called,WP.spec_ok] at frame
  dsimp only at frame
  have frames : after.frames = before.frames := by rw [frame]
  exact held.retained (congrArg alloc.vec.Vec.val frames) (compiler_observe_stable ops law before after state called).capacity

/-- Lift a source-derived raw branch preservation proof through actual br and
its final dead-stack observation. Forward/loop adapters discharge the local
branch premise; no body-level target trace is assumed here. -/
theorem compiler_br_callback_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (held : FrameExitSlotBounds before)
    (branch : before.reachable = true → ∀ middle,
      runtime.compiler.control.FunctionCompiler.branch ops before depth 0#u32 false = .ok (.Ok (),middle) →
      FrameExitSlotBounds middle)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops before state depth types = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br.inv ops before after state depth types (.Ok ()) called with
  | dead dead observed => exact compiler_observe_exit_slots ops law before after state held observed
  | @branched middle _ _ live emitted observed =>
    have checked := branch live middle emitted
    apply compiler_observe_exit_slots ops law {middle with reachable := false} after state _ observed
    exact checked.retained rfl le_rfl

/-- Lift source-derived conditional branch checking through actual br_if and
its stack observation, including a dead prefix that emits no branch. -/
theorem compiler_br_if_callback_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (held : FrameExitSlotBounds before)
    (branch : before.reachable = true → ∀ middle,
      runtime.compiler.control.FunctionCompiler.branch ops before depth 1#u32 true = .ok (.Ok (),middle) →
      FrameExitSlotBounds middle)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops before state depth types = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if.inv ops before after state depth types (.Ok ()) called with
  | dead dead observed => exact compiler_observe_exit_slots ops law before after state held observed
  | @branched middle _ _ live emitted observed =>
    exact compiler_observe_exit_slots ops law middle after state (branch live middle emitted) observed

end Itasca.Compiler

end

end

/-! ## BranchCallbackInstructionPrefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

/-- Lift a source-derived raw branch preservation proof through actual br and
its final dead-stack observation. Forward/loop adapters discharge the local
branch premise; no body-level target trace is assumed here. -/
theorem compiler_br_callback_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (held : CompilerInstructionPrefix before)
    (branch : before.reachable = true → ∀ middle,
      runtime.compiler.control.FunctionCompiler.branch ops before depth 0#u32 false = .ok (.Ok (),middle) →
      CompilerInstructionPrefix middle)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops before state depth types = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br.inv ops before after state depth types (.Ok ()) called with
  | dead dead observed => exact compiler_observe_open_instructions ops law before after state held observed
  | @branched middle _ _ live emitted observed =>
    have checked := branch live middle emitted
    apply compiler_observe_open_instructions ops law {middle with reachable := false} after state _ observed
    have owners : PendingInstructionSite {middle with reachable := false} = PendingInstructionSite middle := by
      funext index
      rfl
    simpa only [CompilerInstructionPrefix, owners] using checked

/-- Lift source-derived conditional branch checking through actual br_if and
its stack observation, including a dead prefix that emits no branch. -/
theorem compiler_br_if_callback_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (held : CompilerInstructionPrefix before)
    (branch : before.reachable = true → ∀ middle,
      runtime.compiler.control.FunctionCompiler.branch ops before depth 1#u32 true = .ok (.Ok (),middle) →
      CompilerInstructionPrefix middle)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops before state depth types = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if.inv ops before after state depth types (.Ok ()) called with
  | dead dead observed => exact compiler_observe_open_instructions ops law before after state held observed
  | @branched middle _ _ live emitted observed =>
    exact compiler_observe_open_instructions ops law middle after state (branch live middle emitted) observed

/-- Every ordinary dead opcode performs only observation, regardless of its
immediates or numeric/reference/SIMD family. -/
theorem compiler_dead_op_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (dead : before.reachable = false) (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (dead)] at called
  exact compiler_observe_open_instructions ops law before after state held called

end Itasca.Compiler

end

/-! ## DeadInstructionPrefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Every dead ordinary lowerer observes without changing code or frames.
Both maintained invariants survive independently of the opcode or immediates. -/
theorem compiler_dead_op_checked_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (dead : before.reachable = false) (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  have checked := compiler_dead_op_open_instructions ops law before after state opcode a b bits dead held called
  rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (dead)] at called
  exact ⟨checked,compiler_observe_exit_slots ops law before after state exits called⟩

end Itasca.Compiler

end

/-! ## TerminalInstructionPrefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Ordinary append effects preserve all older checks when frame ownership is
unchanged, including terminal callbacks that subsequently become unreachable. -/
theorem CompilerInstructionPrefix.append_with_frames {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} (held : CompilerInstructionPrefix before)
    (growth : InstructionCheckExtends before.function after.function) (frames : after.frames = before.frames)
    (fragment : List runtime.bytecode.Instr) (code : after.function.code.val = before.function.code.val++fragment)
    (fresh : ∀ instruction ∈ fragment,
      runtime.bytecode.CompiledFunction.instruction_valid after.function instruction = .ok true) :
    CompilerInstructionPrefix after := by
  refine held.append growth ?_ fragment code fresh
  intro index owned
  simpa only [PendingInstructionSite,frames] using owned

/-- The trap callback checks its emitted trap instruction, or emits no code
when the source prefix is already unreachable. -/
theorem compiler_unreachable_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable ops before state = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_unreachable_tables ops law before after state called)
    (compiler_unreachable_stable_result ops law before after state (.Ok ()) called).capacity
    (compiler_unreachable_code_mono ops law before after state called)
  cases live : before.reachable with
  | false =>
    have effect := callback_unreachable_dead ops law before state live
    rw [called,WP.spec_ok] at effect
    dsimp only at effect
    exact held.append_with_frames growth (by rw [effect]) [] (by simpa using congrArg alloc.vec.Vec.val effect.code) (by simp)
  | true =>
    have effect := callback_unreachable ops law before state live codeFits sourceFits coordinateFits
    rw [called,WP.spec_ok] at effect
    obtain ⟨_,code,frames,_⟩ := effect rfl
    apply held.append_with_frames growth frames [.Unreachable] code
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    exact CoreInstructionBounds.accepts .unreachable

/-- Live RETURN's source suffix fits the current frame; later observation
retains that capacity and every previously stored instruction check. -/
theorem compiler_return_live_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (body : runtime.compiler.Frame) (source : U32)
    (live : before.reachable = true) (bodyFrame : before.frames.val[0]? = some body)
    (height : before.height.val = source.val+body.results.val)
    (heightFits : before.height.val ≤ before.function.slot_count.val)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops before state = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_return_tables ops law before after state called)
    (compiler_return_stable_result ops law before after state (.Ok ()) called).capacity
    (compiler_return_code_mono ops law before after state called)
  have effect := callback_return ops law before state body source live bodyFrame height codeFits sourceFits coordinateFits
  rw [called,WP.spec_ok] at effect
  obtain ⟨_,code,frames,_⟩ := effect rfl
  apply held.append_with_frames growth frames [.Return source body.results] code
  intro instruction member
  simp only [List.mem_singleton] at member
  subst instruction
  exact (CoreInstructionBounds.return_ (by have capacity := growth.slots; omega)).accepts

/-- A return in dead source code only observes the source stack. -/
theorem compiler_return_dead_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (dead : before.reachable = false)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops before state = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_return_tables ops law before after state called)
    (compiler_return_stable_result ops law before after state (.Ok ()) called).capacity
    (compiler_return_code_mono ops law before after state called)
  have effect := callback_return_dead ops law before state dead
  rw [called,WP.spec_ok] at effect
  dsimp only at effect
  exact held.append_with_frames growth (by rw [effect]) [] (by simpa using congrArg alloc.vec.Vec.val effect.code) (by simp)

end Itasca.Compiler

end

/-! ## NoopInstructionPrefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- NOP and DROP perform only the final operand observation on both live and
dead paths. They preserve all instruction and recorded exit-slot checks. -/
theorem compiler_nop_drop_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (drop : Bool)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (if drop then 26#u16 else 1#u16)
      0#u32 0#u32 0#u128 = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  have dispatch : runtime.compiler.lower.FunctionCompiler.op ops before state
      (if drop then 26#u16 else 1#u16) 0#u32 0#u32 0#u128 = runtime.compiler.FunctionCompiler.observe ops before state := by
    exact lower_empty_eq ops before state drop
  rw [dispatch] at called
  exact ⟨compiler_observe_open_instructions ops law before after state held called,
    compiler_observe_exit_slots ops law before after state exits called⟩

end Itasca.Compiler

end

/-! ## TableCallbackExitSlots -/

section

/-!
Exit-slot bounds for br_table targets, the target loop and the compiler callback. The final callback retains both label and branch-table slot requirements.
-/

/-! ## Table Exit Slot Bounds -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Each actual table arm records an exit only for its source-bounded result
region. Loop arms retain the existing flags and bounds. -/
theorem compiler_table_branch_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (lookup : before.table_depths.val[index.val]? = some depth)
    (transfers : TableTransferBounds before) (heightFits : before.height.val ≤ before.function.slot_count.val)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  obtain ⟨_,_,_,_,effect⟩ := compiler_table_target_code ops law before after index depth lookup called
  have capacity := (compiler_table_branch_fixed ops law before after index depth lookup called).stable.capacity
  cases effect with
  | loop selected frame source found position kind operands code frames =>
    exact held.retained (congrArg alloc.vec.Vec.val frames) capacity
  | forward selected frame source fixups site found position kind operands code frames appended siteAt =>
    have region := (transfers depth (List.mem_of_getElem? lookup) selected frame found position).1
    have width : frameBranchWidth frame = frame.results := by cases eq : frame.kind <;> simp_all [frameBranchWidth]
    rw [width] at region
    exact held.record selected.val frame fixups frames capacity (by omega)

/-- A finite table run retains all source transfer bounds needed by subsequent
arms and all slot bounds recorded by previous forward exits. -/
theorem TableBranchRun.exit_slots {A : Type} {ops : runtime.platform.Alloc A}
    (law : Platform.AllocCorrect ops) {before after : runtime.compiler.FunctionCompiler A} {index : Nat}
    (run : TableBranchRun ops before index after) (transfers : TableTransferBounds before)
    (heightFits : before.height.val ≤ before.function.slot_count.val) (held : FrameExitSlotBounds before) :
    FrameExitSlotBounds after := by
  induction run with
  | done => exact held
  | @cons before middle after index inside called rest ih =>
    let depth := before.table_depths.val[index.val]
    have lookup : before.table_depths.val[index.val]? = some depth := List.getElem?_eq_getElem inside
    obtain ⟨_,_,_,height,code⟩ := compiler_table_target_code ops law before middle index depth lookup called
    have depths := compiler_table_branch_depths ops before middle index (.Ok ()) called
    have capacity := (compiler_table_branch_fixed ops law before middle index depth lookup called).stable.capacity
    exact ih (transfers.advance code depths height) (by rw [height]; exact heightFits.trans capacity)
      (compiler_table_branch_exit_slots ops law before middle index depth lookup transfers heightFits held called)

/-- The actual dispatch emission and finite target builder retain all branch
exit bounds independently of their final instruction-check certificate. -/
theorem compiler_lower_table_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (transfers : TableTransferBounds before) (heightFits : before.height.val ≤ before.function.slot_count.val)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  obtain ⟨start,len,selector,emitted,_,_,_,emission,run⟩ := compiler_lower_table_success ops law before after called
  have growth := emission.instruction_check_extends
  obtain ⟨budget,code,sources,frame,appended,_⟩ := emission
  subst emitted
  apply run.exit_slots law _ heightFits (held.retained rfl le_rfl)
  intro depth member index frame found position
  have region := transfers depth member index frame found position
  refine ⟨region.1,fun loop => (region.2 loop).trans ?_⟩
  change before.function.code.length ≤ code.length
  exact growth.code

end Itasca.Compiler

end

/-! ## Table Callback Exit Slots -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

/-- Collecting a table label preserves instruction checks and pending owners. -/
theorem compiler_table_label_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (held : FrameExitSlotBounds before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops before state depth = .ok (.Ok (),after)) : FrameExitSlotBounds after := by
  obtain ⟨budget,depths,frame,_⟩ := compiler_table_label_success ops law before after state depth called
  exact held.retained (by rw [frame]) (by rw [frame])

/-- Lift the source-derived raw table proof through the final default label,
scratch-buffer clearing, and dead-stack observation of the actual callback. -/
theorem compiler_br_table_callback_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (held : FrameExitSlotBounds before)
    (lower : ∀ labeled,
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
        ops before state fallback = .ok (.Ok (),labeled) → labeled.reachable = true → ∀ lowered,
      runtime.compiler.control.FunctionCompiler.lower_table_branches ops labeled = .ok (.Ok (),lowered) →
      FrameExitSlotBounds lowered)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types = .ok (.Ok (),after)) : FrameExitSlotBounds after := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table.inv ops before after state fallback types (.Ok ()) called with
  | @live labeled lowered cleared _ _ labelCall live lowerCall clearCall observed =>
    have checked := lower labeled labelCall live lowered lowerCall
    exact compiler_observe_exit_slots ops law {lowered with reachable := false, table_depths := cleared}
      after state (checked.retained rfl le_rfl) observed
  | @dead labeled cleared _ _ labelCall dead clearCall observed =>
    have checked := compiler_table_label_exit_slots ops law before labeled state fallback held labelCall
    exact compiler_observe_exit_slots ops law {labeled with table_depths := cleared}
      after state (checked.retained rfl le_rfl) observed

end Itasca.Compiler

end

end

/-! ## LoopBranchInstructionPrefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Actual loop branching checks its overlap-safe transfer and retained backward
target, preserving every earlier pending owner. Skip also covers table stubs. -/
theorem compiler_branch_loop_instruction_effect {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : before.frames.val[index.val]? = some frame)
    (position : index.val+depth.val+1 = before.frames.val.length)
    (loop : frame.kind = .Loop)
    (sourcePosition : source.val+frame.params.val+skip.val = before.height.val)
    (order : frame.height.val ≤ source.val)
    (sourceFits : source.val+frame.params.val ≤ before.function.slot_count.val)
    (target : frame.start_pc.val ≤ before.function.code.length)
    (codeFits : before.function.code.val.length+2 ≤ Usize.max)
    (offsetsFit : before.function.source_offsets.val.length+2 ≤ Usize.max)
    (coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth skip false = .ok (.Ok (),after)) :
    InstructionAppendEffect before after := by
  have effect : after.function.code.val = before.function.code.val++branchInstructions frame.height source frame.params frame.start_pc ∧
      after.frames = before.frames := by
    by_cases elided : frame.params = 0#u32 ∨ source = frame.height
    · have effect := branch_elided_loop_with_skip ops law before frame index depth source skip lookup position loop elided
        sourcePosition (by omega) (by omega) coordinateFits
      rw [called,WP.spec_ok] at effect
      obtain ⟨code,frames⟩ := effect rfl
      exact ⟨by simpa [branchInstructions,elided] using code,frames⟩
    · have effect := branch_transfer_loop_with_skip ops law before frame index depth source skip lookup position loop
        (fun eq => elided (.inl eq)) (fun eq => elided (.inr eq)) sourcePosition codeFits offsetsFit coordinateFits
      rw [called,WP.spec_ok] at effect
      obtain ⟨code,frames⟩ := effect rfl
      exact ⟨by simpa [branchInstructions,elided] using code,frames⟩
  obtain ⟨code,frames⟩ := effect
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_branch_tables ops law before after depth skip false called)
    (compiler_branch_stable_result ops law before after depth skip false (.Ok ()) called).capacity
    (compiler_branch_code_mono ops law before after depth skip false (.Ok ()) called)
  refine ⟨growth,_,code,?_,?_⟩
  · intro index owned
    simpa only [PendingInstructionSite,frames] using owned
  · exact branch_instructions_open_checks after.function (PendingInstructionSite after) before.function.code.length
      frame.height source frame.params frame.start_pc order (sourceFits.trans growth.slots) (.inl (target.trans growth.code))

/-- Apply the concrete append effect to the current checked prefix. -/
theorem compiler_branch_loop_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : before.frames.val[index.val]? = some frame)
    (position : index.val+depth.val+1 = before.frames.val.length)
    (loop : frame.kind = .Loop)
    (sourcePosition : source.val+frame.params.val+skip.val = before.height.val)
    (order : frame.height.val ≤ source.val)
    (sourceFits : source.val+frame.params.val ≤ before.function.slot_count.val)
    (target : frame.start_pc.val ≤ before.function.code.length)
    (codeFits : before.function.code.val.length+2 ≤ Usize.max)
    (offsetsFit : before.function.source_offsets.val.length+2 ≤ Usize.max)
    (coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth skip false = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after :=
  (compiler_branch_loop_instruction_effect ops law before after frame index depth source skip lookup position loop sourcePosition order sourceFits target codeFits offsetsFit coordinateFits called).apply held

end Itasca.Compiler

end

end
