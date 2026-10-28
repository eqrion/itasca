import Itasca.Runtime.Code.Local.Lowering.Simd.SimdSourceShape
import Itasca.Runtime.Code.Local.Relations.Common.SimdInstructionAcceptance
import Itasca.Runtime.Code.Local.Relations.Common.CoreInstructionAcceptance

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

private theorem source_width_some (ty : valtype) :
    (simdSourceWidth (some ty)).val = width ty := by cases ty <;> rfl

private theorem source_width_none : (simdSourceWidth none).val = 0 := rfl

/-- The checker reads the first three source operand widths. Their sum never
exceeds the full independently typed input region. -/
theorem simdSourceShape_input_bound (input output : List valtype) :
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
theorem simdSourceShape_output_bound (input output : List valtype) :
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
    have inputWidths := simdSourceShape_input_bound input output
    have outputWidth := simdSourceShape_output_bound input output
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

end Itasca.Runtime.Code
