import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericSafety
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdDispatch
import Mathlib.Tactic.IntervalCases
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdBitsCallbacks
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdEffects
import Itasca.Runtime.Compiler.Local.Relations.Instructions.WellFormedAcceptance
import Itasca.Runtime.Compiler.Local.Relations.Instructions.InstructionCheckAcceptance

/-!
Sections, each formerly its own module: SimdSafetyCallbacks, SimdInstructionAcceptance.
-/

/-! ## SimdSafetyCallbacks -/

section

/-!
Normal return of SIMD constructors and callbacks. Constant, pure, lane and memory cases retain their distinct immediate and capacity premises.
-/

/-! ## Simd Safety -/

section

/-! SIMD lowering returns normally from raw compiler stacks, including rejected
operand and allocation outcomes. Successful lowering records the validator stack. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

theorem make_simd_total (op dst source entry : U32) (bound : op.val < 256) :
    runtime.bytecode.Instr.make_simd op dst source entry ⦃ _ => True ⦄ := by
  rcases op with ⟨⟨n,hn⟩⟩
  change n < 256 at bound
  interval_cases n <;> with_unfolding_all (exact WP.spec.ret trivial)

@[step] theorem compiler_simd_constant_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a : U32) (bits : U128)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (poolFits : compiler.function.v128_pool.val.length < Usize.max) :
    runtime.compiler.simd.FunctionCompiler.simd_op ops compiler state 524#u16 a bits ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  unfold runtime.compiler.simd.FunctionCompiler.simd_op
  split <;> try contradiction
  step with bounded_index (alloc.vec.Vec.len compiler.function.v128_pool) as ⟨answer,_⟩
  cases answer with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok entry =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with budget_push ops law compiler.budget compiler.function.v128_pool bits poolFits as ⟨answer,budget,values,post⟩
    rcases post with ⟨rfl,_,_⟩ | ⟨rfl,_,_⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      exact finish_op_observed ops law _ state _ codeFits sourceFits coordinateFits
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

@[step] theorem compiler_simd_nonconstant_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a : U32) (bits : U128)
    (lower : 512 ≤ opcode.val) (upper : opcode.val ≤ 767)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (tableFits : compiler.function.simd.val.length < Usize.max) :
    simdLowering ops compiler state opcode a bits ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  unfold simdLowering
  step as ⟨reduced,number⟩
  simp only [lift,bind_ok,simd_stores_eq,simd_outputs_eq]
  generalize subEq : UScalar.cast .U32 reduced = sub
  have subBound : sub.val < 256 := by scalar_tac
  cases added : Usize.checked_add (alloc.vec.Vec.len compiler.before)
      (if simdStores sub then 0#usize else 1#usize) with
  | none => simp [added,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | some total =>
    simp only [added,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    cases subtracted : Usize.checked_sub total (alloc.vec.Vec.len state.vals) with
    | none => simp [subtracted,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | some consumed =>
      simp only [subtracted,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      step with compiler_operand_total ops compiler consumed as ⟨answer,_⟩
      cases answer with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok source =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
        step with bounded_index (alloc.vec.Vec.len compiler.function.simd) as ⟨answer,_⟩
        cases answer with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok entry =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,simd_lane_eq]
          step with budget_push ops law compiler.budget compiler.function.simd ({offset := a,lane := simdLane sub a bits,bits} : runtime.bytecode.SimdImmediate) tableFits as ⟨answer,budget,values,post⟩
          rcases post with ⟨rfl,_,_⟩ | ⟨rfl,_,_⟩
          · simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
            step with make_simd_total sub source source entry subBound as ⟨instruction⟩
            cases instruction with
            | none => simp [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | some instruction =>
              simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
              exact finish_op_observed ops law _ state _ codeFits sourceFits coordinateFits
          · simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- SIMD dispatch is normal even when raw operand bookkeeping rejects the opcode.
Successful callbacks retain the raw polymorphic stack observation. -/
@[step] theorem compiler_simd_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (lower : 512 ≤ opcode.val) (upper : opcode.val < 768)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (poolFits : compiler.function.v128_pool.val.length < Usize.max)
    (tableFits : compiler.function.simd.val.length < Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state opcode a b bits ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases live : compiler.reachable = true
  · rw [lower_simd_dispatch ops compiler state opcode a b bits live lower upper]
    by_cases constant : opcode = 524#u16
    · subst opcode
      exact compiler_simd_constant_total ops law compiler state a bits
        codeFits sourceFits coordinateFits poolFits
    · rw [compiler_simd_nonconstant_eq ops compiler state opcode a bits constant lower (by omega)]
      exact compiler_simd_nonconstant_total ops law compiler state opcode a bits lower (by omega)
        codeFits sourceFits coordinateFits tableFits
  · have dead : runtime.compiler.lower.FunctionCompiler.op ops compiler state opcode a b bits =
        runtime.compiler.FunctionCompiler.observe ops compiler state := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_neg live]
    rw [dead]
    exact compiler_observe_stack ops law compiler state

end Itasca.Runtime.Compiler

end

/-! ## Simd Safety Callbacks -/

section

/-! Normal return of every SIMD compiler callback from the actual visitor. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem compiler_on_simd_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (sub : U32) (bound : sub.val < 256)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (poolFits : compiler.function.v128_pool.val.length < Usize.max)
    (tableFits : compiler.function.simd.val.length < Usize.max) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd compiler state sub ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  let opcode : U16 := UScalar.ofNatCore (512 + sub.val) (by scalar_tac)
  have number : opcode.val = 512 + sub.val := rfl
  rw [compiler_simd_callback ops compiler state sub opcode bound number]
  exact compiler_simd_total ops law compiler state opcode _ _ _ (by omega) (by omega)
    codeFits sourceFits coordinateFits poolFits tableFits

@[step] theorem compiler_on_simd_lane_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (sub : U32) (lane : U8) (bound : sub.val < 256)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (poolFits : compiler.function.v128_pool.val.length < Usize.max)
    (tableFits : compiler.function.simd.val.length < Usize.max) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_lane compiler state sub lane ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  let opcode : U16 := UScalar.ofNatCore (512 + sub.val) (by scalar_tac)
  have number : opcode.val = 512 + sub.val := rfl
  rw [compiler_simd_lane_callback ops compiler state sub opcode bound number lane]
  exact compiler_simd_total ops law compiler state opcode _ _ _ (by omega) (by omega)
    codeFits sourceFits coordinateFits poolFits tableFits

@[step] theorem compiler_on_simd_memory_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (sub : U32) (arg : Itasca.code.MemArg) (bound : sub.val < 256)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (poolFits : compiler.function.v128_pool.val.length < Usize.max)
    (tableFits : compiler.function.simd.val.length < Usize.max) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_memory compiler state sub arg ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  let opcode : U16 := UScalar.ofNatCore (512 + sub.val) (by scalar_tac)
  have number : opcode.val = 512 + sub.val := rfl
  rw [compiler_simd_memory_callback ops compiler state sub opcode bound number arg]
  exact compiler_simd_total ops law compiler state opcode _ _ _ (by omega) (by omega)
    codeFits sourceFits coordinateFits poolFits tableFits

@[step] theorem compiler_on_simd_memory_lane_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (sub : U32) (arg : Itasca.code.MemArg) (lane : U8) (bound : sub.val < 256)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (poolFits : compiler.function.v128_pool.val.length < Usize.max)
    (tableFits : compiler.function.simd.val.length < Usize.max) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_memory_lane compiler state sub arg lane ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  let opcode : U16 := UScalar.ofNatCore (512 + sub.val) (by scalar_tac)
  have number : opcode.val = 512 + sub.val := rfl
  rw [compiler_simd_memory_lane_callback ops compiler state sub opcode bound number arg lane]
  exact compiler_simd_total ops law compiler state opcode _ _ _ (by omega) (by omega)
    codeFits sourceFits coordinateFits poolFits tableFits

@[step] theorem compiler_on_simd_const_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (lo hi : U64)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (poolFits : compiler.function.v128_pool.val.length < Usize.max)
    (tableFits : compiler.function.simd.val.length < Usize.max) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_const compiler state lo hi ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  rw [compiler_simd_constant_callback ops compiler state lo hi]
  exact compiler_simd_total ops law compiler state _ _ _ _ (by decide) (by decide)
    codeFits sourceFits coordinateFits poolFits tableFits

@[step] theorem compiler_on_simd_shuffle_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (lo hi : U64)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (poolFits : compiler.function.v128_pool.val.length < Usize.max)
    (tableFits : compiler.function.simd.val.length < Usize.max) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_shuffle compiler state lo hi ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  rw [compiler_simd_shuffle_callback ops compiler state lo hi]
  exact compiler_simd_total ops law compiler state _ _ _ _ (by decide) (by decide)
    codeFits sourceFits coordinateFits poolFits tableFits

end Itasca.Runtime.Compiler

end

end

/-! ## SimdInstructionAcceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

private theorem source_width_some (ty : valtype) :
    (simdSourceWidth (some ty)).val = width ty := by cases ty <;> rfl

private theorem source_width_none : (simdSourceWidth none).val = 0 := rfl

/-- The checker reads the first three source operand widths. Their sum never
exceeds the full independently typed input region. -/
theorem simd_source_shape_input_bound (input output : List valtype) :
    (simdSourceShape input output).1.val+(simdSourceShape input output).2.1.val+
      (simdSourceShape input output).2.2.1.val ≤ slots input := by
  cases input with
  | nil => simp [simdSourceShape,source_width_none,slots]
  | cons a rest =>
    cases rest with
    | nil => simp [simdSourceShape,source_width_some,source_width_none,slots]
    | cons b rest =>
      cases rest with
      | nil => simp [simdSourceShape,source_width_some,source_width_none,slots]
      | cons c rest =>
        simp only [simdSourceShape,List.getElem?_cons_zero,List.getElem?_cons_succ,source_width_some,slots]
        omega

/-- The first result width is bounded by the complete source output region. -/
theorem simd_source_shape_output_bound (input output : List valtype) :
    (simdSourceShape input output).2.2.2.val ≤ slots output := by
  cases output with
  | nil => simp [simdSourceShape,source_width_none,slots]
  | cons a rest =>
    simp only [simdSourceShape,List.getElem?_cons_zero,source_width_some,slots]
    omega

/-- Every actual SIMD emission satisfies instruction checking from its source
widths, constructor roundtrip, and captured immediate or constant table entry. -/
theorem SimdEmission.instructions_accept {immediates constants C before source emitted after}
    (emission : SimdEmission immediates constants C before source emitted after)
    (function : runtime.bytecode.CompiledFunction)
    (immediateTable : immediates = function.simd.val) (constantTable : constants = function.v128_pool.val)
    (inputs : slots C.LOCALS+slots before ≤ function.slot_count.val)
    (outputs : slots C.LOCALS+slots after ≤ function.slot_count.val) :
    ∀ instruction ∈ emitted,
      runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  cases emission with
  | instruction front input output source opcode operand entry immediate instruction meaning metadata constructed position =>
    intro selected member
    simp only [List.mem_singleton] at member
    subst selected
    have projection := make_simd_roundtrip_bounded opcode operand operand entry instruction meaning.opcode_bound constructed
    have inputWidths := simd_source_shape_input_bound input output
    have outputWidth := simd_source_shape_output_bound input output
    dsimp only [simdSourceShape] at inputWidths outputWidth
    have row := (List.getElem?_eq_some_iff.mp metadata).1
    rw [immediateTable] at row
    simp only [slots_append] at inputs outputs
    apply simd_instruction_accepts function instruction opcode operand operand entry _ _ _ _ projection meaning.shape
    · omega
    · omega
    · exact row
  | constant front bits dst entry metadata position =>
    intro selected member
    simp only [List.mem_singleton] at member
    subst selected
    have row := (List.getElem?_eq_some_iff.mp metadata).1
    rw [constantTable] at row
    simp only [slots_append,slots,width] at outputs
    exact (CoreInstructionBounds.constV128 (by omega) row).accepts

end Itasca.Runtime.Compiler

end
