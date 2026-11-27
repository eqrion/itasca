import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdEmissions
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables

open WebAssembly

open Itasca.Representation

/-!
# Independent SIMD callback meaning

SIMD callbacks have source meanings determined by the instruction tables and constant pool. Declared-reference and opcode-bound facts follow from that syntax, without assuming callback execution.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Independent source meaning of a SIMD callback, including the constant
pool case. Its fields are syntactic, not a promise about callback execution. -/
inductive SimdCallbackMeaning (C : context) : U32 → U32 → U128 → List wasm_types.ValueType → instr → Option wasm_types.ValueType → Prop
  | instruction {sub a bits input source output}
      (meaning : SimdImmediateMeaning C sub (simdImmediate sub a bits) (Body.Simd.inputTypes input) source (Body.Simd.outputTypes output)) :
      SimdCallbackMeaning C sub a bits input source output
  | constant (a : U32) (bits : U128) :
      SimdCallbackMeaning C 12#u32 a bits [] (.VCONST .V128 (.mk_uN bits.val)) (some .V128)

namespace SimdCallbackMeaning

theorem opcode_bound {C sub a bits input source output}
    (meaning : SimdCallbackMeaning C sub a bits input source output) : sub.val < 256 := by
  cases meaning with
  | instruction h => exact h.opcode_bound
  | constant => decide

end SimdCallbackMeaning

theorem SimdImmediateMeaning.declared {C sub immediate input source output}
    (meaning : SimdImmediateMeaning C sub immediate input source output) (references : List funcidx) :
    Spec.DeclaredReferences.Instruction references source := by
  cases meaning with
  | pure sub immediate source input output decoded typing =>
    obtain ⟨op, meaning, rfl, rfl, rfl⟩ := pure_classification decoded typing
    exact op.declared references
  | lane sub immediate op meaning lane position => exact op.declared references _
  | memory sub immediate op meaning arg lane memory available offset position => exact op.declared references _ _
  | shuffle immediate lo hi bits => exact Body.Simd.shuffle_declared references lo hi

namespace SimdCallbackMeaning
theorem declared {C sub a bits input source output}
    (meaning : SimdCallbackMeaning C sub a bits input source output) (references : List funcidx) :
    Spec.DeclaredReferences.Instruction references source := by
  cases meaning with
  | instruction h => exact h.declared references
  | constant => simp [Spec.DeclaredReferences.Instruction,Spec.DeclaredReferences.instructionIndices]
end SimdCallbackMeaning
end Itasca.Compiler
