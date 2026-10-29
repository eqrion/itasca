import Itasca.Runtime.Compiler.Local.Relations.Instructions.SimdInstructionAcceptance
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTablePreservation
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerMetadata
import Itasca.Runtime.Compiler.Local.Relations.Instructions.CoreInstructionAcceptance
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Lowering
import Itasca.Runtime.Compiler.Local.Relations.Function.FunctionStartRaw
import Itasca.Runtime.Compiler.Local.Relations.Function.FunctionEntry

/-!
The compiler instruction-prefix certificate, its monotone checks and append operations. PendingInstructionSite and CompilerInstructionPrefix connect low-level open checks to the compiler start invariant.
-/

/-! ## Instruction Check Monotone -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

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
    simp only [WP.spec_ok,decide_eq_true_eq]
    scalar_tac
  obtain ⟨result,called,rfl⟩ := WP.spec_imp_exists checked
  exact called

private theorem non_simd_instruction_monotone (before after : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (growth : InstructionCheckExtends before after)
    (noSimd : runtime.bytecode.Instr.simd instruction = .ok none)
    (accepted : runtime.bytecode.CompiledFunction.instruction_valid before instruction = .ok true) :
    runtime.bytecode.CompiledFunction.instruction_valid after instruction = .ok true := by
  obtain ⟨slots,code,indirect,simd,constants,targets⟩ := growth
  cases instruction
  all_goals simp only [runtime.bytecode.Instr.simd,Result.ok.injEq,reduceCtorEq] at noSimd
  all_goals simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,
    runtime.bytecode.Instr.scalar,runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,
    runtime.bytecode.Instr.simd,slots_fit_arithmetic,bind_ok,lift,uncurry_apply_pair] at accepted ⊢
  all_goals simp_all only [bind_ok,ite_true,ite_false,Result.ok.injEq,decide_eq_true_eq]
  all_goals try dsimp only at accepted ⊢
  all_goals try split_ifs at accepted
  all_goals try simp_all only [Result.ok.injEq,decide_eq_true_eq,Bool.false_eq_true]
  all_goals try split_ifs
  all_goals try simp_all only [Result.ok.injEq,decide_eq_true_eq,Bool.false_eq_true]
  all_goals first | scalar_tac | exact checked_difference_monotone _ _ _ _ (by simpa using targets) accepted

/-- Every earlier instruction check remains valid as code, slot capacity, and
function-local metadata tables grow. Branch patching itself is handled
separately because it changes the stored instruction. -/
theorem instruction_valid_monotone (before after : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (growth : InstructionCheckExtends before after)
    (accepted : runtime.bytecode.CompiledFunction.instruction_valid before instruction = .ok true) :
    runtime.bytecode.CompiledFunction.instruction_valid after instruction = .ok true := by
  have total : ∃ view, runtime.bytecode.Instr.simd instruction = .ok view := by
    cases instruction <;> exact ⟨_,rfl⟩
  obtain ⟨view,projected⟩ := total
  cases view with
  | none => exact non_simd_instruction_monotone before after instruction growth projected accepted
  | some view =>
    obtain ⟨opcode,dst,input,entry⟩ := view
    exact simd_instruction_monotone before after instruction opcode dst input entry projected growth.slots growth.simd accepted

end Itasca.Runtime.Compiler

end

/-! ## Checked Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## Open Instruction Check -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## Open Instruction Append -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## Open Instruction Compiler -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end
