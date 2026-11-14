import Itasca.Runtime.Compiler.Local.Lowering.Emission.OpEquations
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdContracts
import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentData
import Itasca.Module.Layout
import Itasca.Runtime.Compiler.Local.Capacity.UnreachableAvailability
import Itasca.Runtime.Compiler.Local.Relations.Global.GlobalSafety
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal

/-!
Sections, each formerly its own module: SegmentBound, LiteralBudgetAvailability, GlobalAvailability.
-/

/-! ## SegmentBound -/

section

/-! Source framing bounds the synthetic initialization program counter. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ModuleBinary

private theorem leb_positive {bytes value} (h : Itasca.Leb128.Encoding bytes value) :
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
    (h : ElementEncodingFor entry bytes) : 2 ≤ bytes.length := by
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
    (h : DataEncodingFor entry bytes) : 2 ≤ bytes.length := by
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

end Itasca.Runtime.Compiler

end

/-! ## LiteralBudgetAvailability -/

section

/-!
Literal callback availability and its exact capacity effect. ScalarLiteralKind cases establish the budgeted scalar and vector literal results.
-/

/-! ## Literal Availability -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## Literal Budget Availability -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

end

/-! ## GlobalAvailability -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end
