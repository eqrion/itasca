import Itasca.Runtime.Compiler.Local.Lowering.Emission.OpEquations
import Itasca.Runtime.Compiler.Local.Lowering.Simd.Contracts
import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentData
import Itasca.Module.Layout
import Itasca.Runtime.Compiler.Local.Capacity.CallbackBudgets
import Itasca.Runtime.Compiler.Local.Relations.Global.GlobalSafety
import Itasca.Runtime.Compiler.Local.Lowering.LoweringLocal
import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchAndTerminalEffects
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CallbackRetention
import Itasca.Runtime.Compiler.Local.Lowering.Simd.Emission
import Mathlib.Tactic.IntervalCases
import Itasca.Runtime.Compiler.Local.Lowering.Simd.Callbacks
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ClosingContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrames

/-!
Proofs for Runtime / Compiler / Local / Capacity.

This module collects SegmentBoundsAndLiteralAvailability, ConditionalAndSimdAvailability.
Each section documents its contracts and consumers.
-/

/-! ## SegmentBoundsAndLiteralAvailability -/

section

open Itasca.Representation

/-!
# Segment Bounds And Literal Availability

Segment bounds and literal callback demands provide the resource premises for normal compiler return.
-/

/-! ## SegmentBound -/

section

/-! Source framing bounds the synthetic initialization program counter. -/
namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Binary

private theorem leb_positive {bytes value} (h : Itasca.Binary.Leb128.Encoding bytes value) :
    1 ≤ bytes.length := by
  obtain ⟨before, last, rfl, _⟩ := h
  simp

private theorem vec_positive {α : Type} {R : α → List U8 → Prop} {values bytes}
    (h : VecEncoding R values bytes) : 1 ≤ bytes.length := by
  obtain ⟨count, entries, hc, _, rfl⟩ := h
  have := leb_positive hc
  simp only [List.length_append]
  omega

private theorem element_bytes {entry bytes}
    (h : ElementEncoding entry bytes) : 2 ≤ bytes.length := by
  cases h with
  | activeIndices hf _ he | activeExpressions hf _ he =>
    have := leb_positive hf
    have := vec_positive he
    simp only [List.length_append]
    omega
  | passiveIndices hf he | declarativeIndices hf he | passiveExpressions hf he | declarativeExpressions hf he =>
    have := leb_positive hf
    have := vec_positive he
    simp only [List.length_append, List.length_singleton]
    omega
  | explicitIndices hf _ _ he | explicitExpressions hf _ _ he =>
    have := leb_positive hf
    have := vec_positive he
    simp only [List.length_append, List.length_singleton]
    omega

private theorem active_positive {index explicit bytes}
    (h : ActiveIndexEncoding index explicit bytes) : 1 ≤ bytes.length := by
  cases h with
  | implicit hf => exact leb_positive hf
  | explicit hf _ => have := leb_positive hf; simp only [List.length_append]; omega

private theorem data_bytes {entry bytes}
    (h : DataEncoding entry bytes) : 2 ≤ bytes.length := by
  cases h with
  | active hi _ he =>
    have := active_positive hi
    have := vec_positive he
    simp only [List.length_append]
    omega
  | passive hf he =>
    have := leb_positive hf
    have := vec_positive he
    simp only [List.length_append]
    omega

private theorem rep_size {α : Type} {R : α → List U8 → Prop} {values bytes}
    (h : Rep R values bytes) (minimum : ∀ value bytes, R value bytes → 2 ≤ bytes.length) :
    2 * values.length ≤ bytes.length := by
  induction h with
  | nil => simp
  | cons hx _ ih =>
    have := minimum _ _ hx
    simp only [List.length_cons, List.length_append]
    omega

private theorem padded_size {α : Type} {R : α → List U8 → Prop} {id values bytes}
    (h : PaddedEncoding id (VecEncoding R) [] values bytes)
    (minimum : ∀ value bytes, R value bytes → 2 ≤ bytes.length) :
    2 * values.length ≤ bytes.length := by
  obtain ⟨customs, sec, _, hs, rfl⟩ := h
  cases hs with
  | absent => simp
  | present hp =>
    obtain ⟨size, payload, _, ⟨count, entries, _, hr, rfl⟩, rfl⟩ := hp
    have := rep_size hr minimum
    simp only [List.length_append, List.length_cons]
    omega

/-- Segment vectors consume at least two bytes per entry, including empty
passive segments. This holds for Wasm 2.0 and non-minimal LEBs. -/
theorem segment_count_bytes {R raw bytes}
    (h : ModuleEncodingWith R raw bytes) :
    2 * (raw.elements.length + raw.data.length) ≤ bytes.length := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    codes, datas, customs, _, _, _, _, _, _, _, _, hel, _, _, hd, _, rfl, _⟩ := h
  have he := padded_size hel (fun _ _ h => element_bytes h)
  have hd := padded_size hd (fun _ _ h => data_bytes h)
  simp only [List.length_append]
  omega

private theorem flatten_bound {α : Type} (blocks : List (List α))
    (bounded : ∀ block ∈ blocks, block.length ≤ 5) :
    blocks.flatten.length ≤ 5 * blocks.length := by
  induction blocks with
  | nil => simp
  | cons block blocks ih =>
    have head := bounded block (by simp)
    have tail := ih (fun block member => bounded block (by simp [member]))
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    omega

/-- At most five instructions are emitted for any source segment, followed by
one return. No allocator or runtime execution assumption enters this bound. -/
theorem SegmentProgram.length_bound {module function}
    (certificate : SegmentProgram module function) :
    function.code.length ≤
      5 * (module.module.env.elements.length + module.module.tail.data.length) + 1 := by
  obtain ⟨elements, datas, cert⟩ := certificate
  have he : elements.flatten.length ≤ 5 * elements.length := by
    apply flatten_bound
    intro block member
    obtain ⟨index, bound, found⟩ := List.mem_iff_getElem.mp member
    have sourceBound : index < module.module.env.elements.val.length := by
      have := cert.elementCount
      simp only [alloc.vec.Vec.length] at this
      omega
    obtain ⟨instructions, read, program⟩ := cert.elements index _ (List.getElem?_eq_getElem sourceBound)
    have same : instructions = block := by
      rw [List.getElem?_eq_getElem bound, found] at read
      exact Option.some.inj read.symm
    subst instructions
    cases program <;> simp
  have hd : datas.flatten.length ≤ 5 * datas.length := by
    apply flatten_bound
    intro block member
    obtain ⟨index, bound, found⟩ := List.mem_iff_getElem.mp member
    have sourceBound : index < module.module.tail.data.val.length := by
      have := cert.dataCount
      simp only [alloc.vec.Vec.length] at this
      omega
    obtain ⟨instructions, read, program⟩ := cert.datas index _ (List.getElem?_eq_getElem sourceBound)
    have same : instructions = block := by
      rw [List.getElem?_eq_getElem bound, found] at read
      exact Option.some.inj read.symm
    subst instructions
    cases program <;> simp
  rw [alloc.vec.Vec.length, cert.instructions]
  simp only [List.length_append, List.length_singleton]
  have := cert.elementCount
  have := cert.dataCount
  omega

/-- The fixed one-GiB validator cap and the binary segment framing leave ample
room below the interpreter's 32-bit program counter. The two count equalities
are source/metadata coherence, not execution-correctness premises. -/
theorem SegmentProgram.pc_bound {module function raw bytes R}
    (certificate : SegmentProgram module function)
    (encoding : ModuleEncodingWith R raw bytes)
    (moduleBound : bytes.length ≤ Itasca.limits.MAX_MODULE_BYTES.val)
    (elements : module.module.env.elements.length = raw.elements.length)
    (datas : module.module.tail.data.length = raw.data.length) :
    function.code.length < U32.max := by
  have codeBound := certificate.length_bound
  have sourceBound := segment_count_bytes encoding
  simp only [Itasca.limits.MAX_MODULE_BYTES] at moduleBound
  rw [elements, datas] at codeBound
  norm_num [U32.max_eq] at *
  omega

end Itasca.Compiler

end

/-! ## LiteralBudgetAvailability -/

section

/-!
Literal callback availability and its exact capacity effect. ScalarLiteralKind cases establish the budgeted scalar and vector literal results.
-/

/-! ## Literal Availability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

inductive ScalarLiteralKind where
  | i32 | i64 | f32 | f64

def ScalarLiteralKind.opcode : ScalarLiteralKind → U16
  | .i32 => 65#u16 | .i64 => 66#u16 | .f32 => 67#u16 | .f64 => 68#u16

def ScalarLiteralKind.lowering {A : Type} (kind : ScalarLiteralKind) (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (bits : U128) :
    Result (core.result.Result Unit Itasca.error.VisitError × runtime.compiler.FunctionCompiler A) :=
  match kind with
  | .i32 | .f32 => do
    let word ← lift (UScalar.cast .U32 bits)
    runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (.Const32 compiler.height word)
  | .i64 | .f64 => do
    let word ← lift (UScalar.cast .U64 bits)
    runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (.Const64 compiler.height word)

end Itasca.Compiler

end

/-! ## Literal Budget Availability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Scalar literal callbacks charge at most one instruction and retain all
other compiler resource counters, including in dead code. -/
theorem compiler_literal_available_effect {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (kind : ScalarLiteralKind) (bits : U128) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state kind.opcode 0#u32 0#u32 bits
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · have dispatch : runtime.compiler.lower.FunctionCompiler.op ops compiler state kind.opcode 0#u32 0#u32 bits =
        kind.lowering ops compiler state bits := by
      cases kind with
      | i32 => exact runtime.compiler.lower.FunctionCompiler.op.i32_const ops compiler state _ _ bits live
      | i64 => exact runtime.compiler.lower.FunctionCompiler.op.i64_const ops compiler state _ _ bits live
      | f32 => exact runtime.compiler.lower.FunctionCompiler.op.f32_const ops compiler state _ _ bits live
      | f64 => exact runtime.compiler.lower.FunctionCompiler.op.f64_const ops compiler state _ _ bits live
    rw [dispatch]
    cases kind <;> simp only [ScalarLiteralKind.lowering,lift,bind_ok]
    all_goals
      apply WP.spec_mono (finish_op_available_budget ops bound available compiler state demand _)
      intro out post
      obtain ⟨used,same,usedEq⟩ := post.2
      rw [same]
      exact ⟨post.1,.of_counter .instructions compiler.budget used 1
        (by simp [ChargeCounter.used]; omega) (by simpa [ChargeCounter.used] using
          (show used.val ≤ compiler.budget.instructions.val+1 by omega))⟩
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

/-- The vector-literal emitter changes precisely the instruction counter;
its separate pool reserve is paid by the independent source ledger bound. -/
theorem compiler_vector_literal_available_budget {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound)
    (poolBound : compiler.function.v128_pool.length ≤ compiler.function.code.length) (bits : U128) :
    runtime.compiler.simd.FunctionCompiler.simd_op ops compiler state 524#u16 0#u32 bits
      ⦃ out => out.1 = .Ok () ∧ ∃ used, out.2.budget = {compiler.budget with instructions := used} ∧
        used.val = compiler.budget.instructions.val+1 ⦄ := by
  apply runtime.compiler.simd.FunctionCompiler.simd_op.available ops bound available compiler state 524#u16 0#u32 bits
  exact .constant demand
    (by have room := demand.pc; omega)
    (by have room := demand.codeCapacity; omega)
    (by have room := demand.codeReserve; omega)

end Itasca.Compiler

end

end

/-! ## GlobalAvailability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Global reads accept for every observed stack, including unreachable code
and vector-valued globals, under independent compilation demand. -/
theorem compiler_global_get_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (index : U32) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 35#u16 index 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨wide,top,_⟩ := WP.spec_imp_exists (top_is_v128_total state.vals.deref)
    rw [lower_global_get_eq ops compiler state index wide live top]
    exact finish_op_available_effect ops bound available compiler state demand _
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

/-- Global writes accept from the independently typed operand layout. The
height subtraction is justified by that layout, rather than assumed normal. -/
theorem compiler_global_set_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (index : U32)
    (front : List valtype) (ty : valtype)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ [ty])) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 36#u16 index 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨source,read,position⟩ := last_operand ops compiler front ty (layout live)
    have height := (layout live).height
    simp only [slots_append,slots,Nat.add_zero] at height
    obtain ⟨difference,subtract,_⟩ := WP.spec_imp_exists
      (UScalar.sub_spec (x := compiler.height) (y := source) (by omega))
    rw [lower_global_set_eq ops compiler state index source difference live read subtract]
    exact finish_op_available_effect ops bound available compiler state demand _
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Compiler

end

end

/-! ## ConditionalAndSimdAvailability -/

section

open Itasca.Representation

/-!
# Conditional And Simd Availability

Conditional branches and SIMD callbacks satisfy their resource requirements under the compiler capacity invariants.
-/

/-! ## ConditionalBranchAvailability -/

section

/-!
Allocator availability for elided and emitted conditional branches, composed into successful callback replay.
-/

/-! ## Conditional Elided Availability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

end Itasca.Compiler

end

/-! ## Conditional Transfer Availability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

end Itasca.Compiler

end

/-! ## Conditional Branch Availability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- The actual br_if callback also accepts unreachable paths, which only
observe the validator stack and retain the compilation budget. -/
theorem compiler_on_br_if_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 3)
    (frame : runtime.compiler.Frame) (index : Usize) (depth condition : U32) (resultType : Itasca.signature.ResultType)
    (lookup : compiler.reachable = true → compiler.frames.val[index.val]? = some frame)
    (position : compiler.reachable = true → index.val + depth.val + 1 = compiler.frames.val.length)
    (widthFits : compiler.reachable = true →
      (match frame.kind with | .Loop => frame.params | _ => frame.results).val + 1 ≤ compiler.height.val)
    (conditionAt : compiler.reachable = true → compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (fixupsCapacity : frame.fixups.length < Usize.max)
    (fixupsReserve : frame.fixups.length + 1 ≤ bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops compiler state depth resultType ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 3 else 0) ⦄ := by
  have ready : compiler.reachable = true → BranchCallbackReady ops compiler depth true bound := by
    intro live
    let selected : BranchSelection compiler depth := ⟨index, frame, lookup live, position live⟩
    have width : (branchWidth frame).val + 1 ≤ compiler.height.val := by
      change (match frame.kind with | .Loop => frame.params | _ => frame.results).val + 1 ≤ compiler.height.val
      exact widthFits live
    let source : U32 := UScalar.ofNatCore (compiler.height.val - ((branchWidth frame).val + 1)) (by scalar_tac)
    have sourcePosition : source.val + (branchWidth frame).val + 1 = compiler.height.val := by
      change compiler.height.val - ((branchWidth frame).val + 1) + (branchWidth frame).val + 1 = compiler.height.val
      omega
    obtain ⟨answer, called, same⟩ := WP.spec_imp_exists
      (compiler_condition ops compiler condition (conditionAt live))
    have operandRead : runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok condition) :=
      same ▸ called
    have countBound : branchInstructionCount true frame source ≤ 3 := by
      unfold branchInstructionCount
      split <;> simp
    have base : BranchCapacity compiler bound (branchInstructionCount true frame source) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, capacity.coordinate, ?_⟩
      · have h := capacity.pc; omega
      · have h := capacity.codeCapacity; omega
      · have h := capacity.sourceCapacity; omega
      · have h := capacity.codeReserve; omega
      · have h := capacity.sourceReserve; omega
      · have h := capacity.instructions; omega
    have demand : BranchDemand compiler frame bound (branchInstructionCount true frame source) := {
      toBranchCapacity := base
      fixups := fun _ => fixupsCapacity
      fixupsReserve := fun _ => fixupsReserve }
    refine ⟨selected, source, ?_, ?_, demand⟩
    · simpa [branchCallbackSkip] using sourcePosition
    · intro _
      exact ⟨condition, operandRead⟩
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if.available
    ops bound available compiler state depth resultType ready capacity.operands capacity.slots)
  intro out post
  rcases out with ⟨status, after⟩
  rcases post with ⟨statusEq, callbackBudget⟩
  subst status
  obtain ⟨used, budgetEq, lower, upper⟩ := callbackBudget.bounds
  refine ⟨rfl, ?_⟩
  rw [budgetEq]
  exact CompilationBudgetEffect.of_counter .instructions compiler.budget used 3 lower upper

end Itasca.Compiler

end

end

/-! ## ElseDispatchAvailability -/

section

/-!
Availability of else callbacks in live, dormant and unentered cases. The final dispatch theorem chooses the actual case without assuming callback success.
-/

/-! ## Else Availability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Live else entry accepts a bounded skip-fixup append, one emitted jump,
and its owned guard patch. Only the instruction counter changes. -/
theorem compiler_else_live_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (guard : Usize) (condition target : U32)
    (frames : compiler.frames.val = prior ++ [frame])
    (reachable : compiler.reachable = true) (guardPc : frame.if_pc = some guard)
    (guardCode : compiler.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX))
    (position : target.val = compiler.function.code.val.length + 1)
    (fixupsCapacity : frame.fixups.length < Usize.max)
    (fixupsReserve : frame.fixups.length + 1 ≤ bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  have guardSites : ∀ guard, frame.if_pc = some guard →
      ∃ kind old, compiler.function.code.val[guard.val]? = some (BranchKind.instruction kind old) := by
    intro queried h
    have same : queried = guard := Option.some.inj (h.symm.trans guardPc)
    subst queried
    exact ⟨.zero condition, core.num.U32.MAX, by simpa [BranchKind.instruction] using guardCode⟩
  have targetFits : target.val ≤ U32.max := by scalar_tac
  have guardBound : frame.if_pc ≠ none →
      compiler.function.code.length + (if compiler.reachable then 1 else 0) ≤ U32.max := by
    intro _
    rw [reachable]
    simp only [if_true]
    rw [← position]
    omega
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.available
    ops bound available compiler state bt
    ⟨frame, prior, frames, guardSites, guardBound, demand.operands, demand.slots,
      (by intro live; simp [live, fixupsCapacity, fixupsReserve, demand.pc, demand.codeCapacity,
        demand.sourceCapacity, demand.codeReserve, demand.sourceReserve, demand.coordinate, demand.instruction])⟩)
  intro out post
  rcases out with ⟨status, after⟩
  rcases post with ⟨statusOk, used, budgetEq, usedEq⟩
  subst status
  refine ⟨rfl, ?_⟩
  rw [budgetEq]
  exact CompilationBudgetEffect.of_counter .instructions compiler.budget used 1
    (by simp [ChargeCounter.used, reachable] at usedEq ⊢; omega)
    (by simp [ChargeCounter.used, reachable] at usedEq ⊢; omega)

/-- An else path without fallthrough emits no instruction and retains the complete budget. -/
theorem compiler_else_dead_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (guard : Usize) (condition target : U32)
    (frames : compiler.frames.val = prior ++ [frame])
    (reachable : compiler.reachable = false) (guardPc : frame.if_pc = some guard)
    (guardCode : compiler.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX))
    (position : target.val = compiler.function.code.val.length)
    (request : state.vals.length ≤ bound)
    (slotsFit : compiler.function.local_slots.val + 2*state.vals.length ≤ U32.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ out =>
      out.1 = .Ok () ∧ out.2.budget = compiler.budget ⦄ := by
  have guardSites : ∀ queried, frame.if_pc = some queried →
      ∃ kind old, compiler.function.code.val[queried.val]? = some (BranchKind.instruction kind old) := by
    intro queried h
    have same : queried = guard := Option.some.inj (h.symm.trans guardPc)
    subst queried
    exact ⟨.zero condition, core.num.U32.MAX, by simpa [BranchKind.instruction] using guardCode⟩
  have guardBound : frame.if_pc ≠ none →
      compiler.function.code.length + (if compiler.reachable then 1 else 0) ≤ U32.max := by
    intro _
    rw [reachable]
    scalar_tac
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.available
    ops bound available compiler state bt
    ⟨frame, prior, frames, guardSites, guardBound, request, slotsFit,
      (by intro live; simp [reachable] at live)⟩)
  intro out post
  rcases out with ⟨status, after⟩
  rcases post with ⟨statusOk, used, budgetEq, usedEq⟩
  subst status
  have usedEqOld : used.val = compiler.budget.instructions.val := by
    simp [reachable] at usedEq
    simpa using usedEq
  have usedSame : used = compiler.budget.instructions := by
    apply UScalar.eq_of_val_eq
    exact usedEqOld
  rw [budgetEq, usedSame]
  exact ⟨rfl, rfl⟩

/-- An else path without fallthrough emits no instruction and retains the complete budget. -/
theorem compiler_else_unentered_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (frames : compiler.frames.val = prior ++ [frame])
    (reachable : compiler.reachable = false) (guardPc : frame.if_pc = none)
    (request : state.vals.length ≤ bound)
    (slotsFit : compiler.function.local_slots.val + 2*state.vals.length ≤ U32.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ out =>
      out.1 = .Ok () ∧ out.2.budget = compiler.budget ⦄ := by
  have guardSites : ∀ queried, frame.if_pc = some queried →
      ∃ kind old, compiler.function.code.val[queried.val]? = some (BranchKind.instruction kind old) := by
    intro queried h
    simp [guardPc] at h
  have guardBound : frame.if_pc ≠ none →
      compiler.function.code.length + (if compiler.reachable then 1 else 0) ≤ U32.max := by
    intro h
    simp [guardPc] at h
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.available
    ops bound available compiler state bt
    ⟨frame, prior, frames, guardSites, guardBound, request, slotsFit,
      (by intro live; simp [reachable] at live)⟩)
  intro out post
  rcases out with ⟨status, after⟩
  rcases post with ⟨statusOk, used, budgetEq, usedEq⟩
  subst status
  have usedEqOld : used.val = compiler.budget.instructions.val := by
    simp [reachable] at usedEq
    simpa using usedEq
  have usedSame : used = compiler.budget.instructions := by
    apply UScalar.eq_of_val_eq
    exact usedEqOld
  rw [budgetEq, usedSame]
  exact ⟨rfl, rfl⟩

end Itasca.Compiler

end

/-! ## Else Dispatch Availability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

private theorem representable_pc (count : Nat) (bounded : count ≤ U32.max) :
    ∃ pc : U32, pc.val = count := by
  have fits : count < 2^UScalarTy.U32.numBits := by scalar_tac
  exact ⟨U32.ofNatCore count fits,U32.ofNatCore_val_eq fits⟩

/-- Every valid else state accepts. Numeric capacity constructs the target
PC; retained guard ownership and entry metadata discharge the live/dead cases.
No successful callback equation is supplied by the caller. -/
theorem compiler_else_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 1) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (frames : compiler.frames.val = prior ++ [frame])
    (liveGuard : compiler.reachable = true → frame.if_pc ≠ none)
    (guardOwned : ∀ guard, frame.if_pc = some guard → ∃ condition,
      compiler.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX))
    (fixupsCapacity : frame.fixups.length < Usize.max)
    (fixupsReserve : frame.fixups.length + 1 ≤ bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨target,position⟩ := representable_pc (compiler.function.code.length+1) capacity.pc
    cases guardPc : frame.if_pc with
    | none => exact False.elim (liveGuard live guardPc)
    | some guard =>
      obtain ⟨condition,guardCode⟩ := guardOwned guard guardPc
      exact compiler_else_live_available ops bound available compiler state (capacity.one (by decide)) bt
        frame prior guard condition target frames live guardPc guardCode position fixupsCapacity fixupsReserve
  · have dead : compiler.reachable = false := Bool.eq_false_iff.mpr live
    cases guardPc : frame.if_pc with
    | none =>
      apply WP.spec_mono (compiler_else_unentered_available ops bound available compiler state bt frame prior frames
        dead guardPc capacity.operands capacity.slots)
      intro out post
      rw [post.2]
      exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩
    | some guard =>
      obtain ⟨condition,guardCode⟩ := guardOwned guard guardPc
      obtain ⟨target,position⟩ := representable_pc compiler.function.code.length (by have room := capacity.pc; omega)
      apply WP.spec_mono (compiler_else_dead_available ops bound available compiler state bt frame prior guard condition
        target frames dead guardPc guardCode position capacity.operands capacity.slots)
      intro out post
      rw [post.2]
      exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Compiler

end

end

/-! ## SimdOpAvailability -/

section

/-!
Availability of SIMD opcode construction and compiler callbacks. Immediate-meaning certificates discharge constructor obligations before constant/nonconstant replay.
-/

/-! ## Simd Constructor Availability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Independent source opcode meaning excludes every reserved constructor
case. This covers all nonconstant SIMD families, without assuming construction
or successful compilation. -/
private theorem simd_constructor_available_low {C opcode immediate input source output}
    (meaning : SimdImmediateMeaning C opcode immediate input source output)
    (bounded : opcode.val < 128) (dst operand entry : U32) :
    ∃ instruction, runtime.bytecode.Instr.make_simd opcode dst operand entry = .ok (some instruction) := by
  rcases opcode with ⟨⟨number,numberBound⟩⟩
  change number < 128 at bounded
  interval_cases number <;> first
    | exact ⟨_,rfl⟩
    | (cases meaning with
      | pure _ _ _ _ _ decoded _ => change none = some _ at decoded; contradiction
      | lane _ _ _ decoded _ _ => change none = some _ at decoded; contradiction
      | memory _ _ _ decoded _ _ _ _ _ _ => change none = some _ at decoded; contradiction)

private theorem simd_constructor_available_high {C opcode immediate input source output}
    (meaning : SimdImmediateMeaning C opcode immediate input source output)
    (lower : 128 ≤ opcode.val) (bounded : opcode.val < 256) (dst operand entry : U32) :
    ∃ instruction, runtime.bytecode.Instr.make_simd opcode dst operand entry = .ok (some instruction) := by
  rcases opcode with ⟨⟨number,numberBound⟩⟩
  change number < 256 at bounded
  change 128 ≤ number at lower
  interval_cases number <;> first
    | exact ⟨_,rfl⟩
    | (cases meaning with
      | pure _ _ _ _ _ decoded _ => change none = some _ at decoded; contradiction
      | lane _ _ _ decoded _ _ => change none = some _ at decoded; contradiction
      | memory _ _ _ decoded _ _ _ _ _ _ => change none = some _ at decoded; contradiction)

theorem SimdImmediateMeaning.constructor_available {C opcode immediate input source output}
    (meaning : SimdImmediateMeaning C opcode immediate input source output)
    (bounded : opcode.val < 256) (dst operand entry : U32) :
    ∃ instruction, runtime.bytecode.Instr.make_simd opcode dst operand entry = .ok (some instruction) := by
  by_cases low : opcode.val < 128
  · exact simd_constructor_available_low meaning low dst operand entry
  · exact simd_constructor_available_high meaning (by omega) bounded dst operand entry

end Itasca.Compiler

end

/-! ## Simd Availability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Nonconstant SIMD lowering accepts from independent source meaning and
stack lengths. Temporary arithmetic and the immediate-table request are
bounded explicitly; source meaning discharges constructor coverage. -/
theorem compiler_simd_nonconstant_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (C : context)
    (front input output : List valtype) (source : instr)
    (opcode : U16) (sub a : U32) (bits : U128)
    (number : opcode.val = 512 + sub.val) (bounded : sub.val < 256)
    (nonconstant : sub.val ≠ 12)
    (meaning : SimdImmediateMeaning C sub (simdImmediate sub a bits) input source output)
    (layout : CompilerLayout compiler (front ++ input))
    (postLength : state.vals.val.length = (front ++ output).length)
    (operandCapacity : compiler.before.length < Usize.max)
    (tableIndex : compiler.function.simd.length ≤ U32.max)
    (tableCapacity : compiler.function.simd.length < Usize.max)
    (tableReserve : compiler.function.simd.length + 1 ≤ bound) :
    runtime.compiler.simd.FunctionCompiler.simd_op ops compiler state opcode a bits
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  have notConstant : opcode ≠ 524#u16 := by
    intro same
    have numeric := congrArg UScalar.val same
    change opcode.val = 524 at numeric
    omega
  obtain ⟨reduced, reducedEq, subEq⟩ := simd_opcode_reduction opcode sub number
  have beforeLength := layout.operands_length
  have outputs := meaning.output_count
  have positive := meaning.input_positive
  simp only [List.length_append] at beforeLength postLength
  have addSpec := Usize.checked_add_bv_spec (alloc.vec.Vec.len compiler.before)
    (if simdStores sub then 0#usize else 1#usize)
  cases added : Usize.checked_add (alloc.vec.Vec.len compiler.before)
      (if simdStores sub then 0#usize else 1#usize) with
  | none =>
    simp only [added] at addSpec
    split at addSpec <;> scalar_tac
  | some total =>
    simp only [added] at addSpec
    have totalCount : total.val = compiler.before.length + (if simdStores sub then 0 else 1) := by
      split at addSpec <;> simp_all only [↓reduceIte] <;> scalar_tac
    have subSpec := Usize.checked_sub_bv_spec total (alloc.vec.Vec.len state.vals)
    cases subtracted : Usize.checked_sub total (alloc.vec.Vec.len state.vals) with
    | none => simp only [subtracted] at subSpec; scalar_tac
    | some consumed =>
      simp only [subtracted] at subSpec
      have consumedCount : consumed.val = input.length := by scalar_tac
      obtain ⟨status, read, operand, accepted, _⟩ := WP.spec_imp_exists
        (compiler_operand ops compiler _ layout consumed (by omega)
          (by simp only [consumedCount, List.length_append]; omega))
      subst status
      have prepared : SimdOperandInput ops compiler state opcode :=
        ⟨reduced, total, consumed, operand, reducedEq,
          by simpa only [← subEq] using added, subtracted, read,
          by
            intro entry
            simpa only [← subEq] using meaning.constructor_available bounded operand operand entry⟩
      have resources : SimdTailDemand compiler state bound :=
        ⟨demand, tableIndex, tableCapacity, tableReserve⟩
      apply WP.spec_mono (runtime.compiler.simd.FunctionCompiler.simd_op.available ops bound available
        compiler state opcode a bits (.general opcode notConstant (by omega) (by omega) prepared resources))
      intro out post
      obtain ⟨used, same, usedEq⟩ := post.2
      rw [same]
      exact ⟨post.1, .of_counter .instructions compiler.budget used 1
        (by simp only [ChargeCounter.used]; omega)
        (by simp only [ChargeCounter.used]; omega)⟩

end Itasca.Compiler

end

/-! ## Simd Op Availability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Actual ordinary dispatch for every meaningful nonconstant SIMD opcode
accepts on live and dead paths. The immediate ledger bounds its own reserve. -/
theorem compiler_simd_nonconstant_op_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (C : context)
    (front input output : List valtype) (source : instr)
    (opcode : U16) (sub a b : U32) (bits : U128)
    (number : opcode.val = 512+sub.val) (bounded : sub.val < 256) (nonconstant : sub.val ≠ 12)
    (meaning : SimdImmediateMeaning C sub (simdImmediate sub a bits) input source output)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ input))
    (postLength : compiler.reachable = true → state.vals.val.length = (front ++ output).length)
    (operandCapacity : compiler.before.length < Usize.max)
    (tableBound : compiler.function.simd.length ≤ compiler.function.code.length) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state opcode a b bits ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨out,actual,post⟩ := WP.spec_imp_exists
      (compiler_simd_nonconstant_available ops bound available compiler state demand C front input output source
        opcode sub a bits number bounded nonconstant meaning (layout live) (postLength live) operandCapacity
        (tableBound.trans demand.pc) (tableBound.trans_lt demand.codeCapacity)
        ((Nat.add_le_add_right tableBound 1).trans demand.codeReserve))
    exact WP.exists_imp_spec ⟨out,
      (lower_simd_dispatch ops compiler state opcode a b bits live (by omega) (by omega)).trans actual,post⟩
  · apply WP.spec_mono (compiler_dead_op_available ops bound available compiler state opcode a b bits live
      demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

/-- The actual vector-constant dispatch accepts its bounded pool append and
instruction charge, including dead code where no pool entry is allocated. -/
theorem compiler_simd_constant_op_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (bits : U128)
    (poolBound : compiler.function.v128_pool.length ≤ compiler.function.code.length) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 524#u16 0#u32 0#u32 bits ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨out,actual,post⟩ := WP.spec_imp_exists
      (compiler_vector_literal_available_budget ops bound available compiler state demand poolBound bits)
    obtain ⟨used,budgetEq,usedEq⟩ := post.2
    have effect : CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) := by
      rw [budgetEq]
      exact .of_counter .instructions compiler.budget used 1
        (by simp [ChargeCounter.used]; omega) (by simp [ChargeCounter.used]; omega)
    exact WP.exists_imp_spec ⟨out,
      (lower_simd_dispatch ops compiler state 524#u16 0#u32 0#u32 bits live (by decide) (by decide)).trans actual,
      post.1,effect⟩
  · apply WP.spec_mono (compiler_dead_op_available ops bound available compiler state 524#u16 0#u32 0#u32 bits live
      demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Compiler

end

end

/-! ## SimdCallbacksAvailability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- The vector-constant hook preserves the actual packed source bits in
its pool and charges at most one instruction. -/
theorem compiler_on_simd_const_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (lo hi : U64)
    (poolBound : compiler.function.v128_pool.length ≤ compiler.function.code.length) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_const compiler state lo hi ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [compiler_simd_constant_callback ops compiler state lo hi]
  exact compiler_simd_constant_op_available ops bound available compiler state demand (initializerBits lo hi) poolBound

end Itasca.Compiler

end

end
