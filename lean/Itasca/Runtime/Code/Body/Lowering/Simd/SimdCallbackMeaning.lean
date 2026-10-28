import Itasca.Runtime.Code.Body.Reader.Simd.SimdReaderMeaning
import Itasca.Runtime.Code.Local.Callbacks.Table.CompilerTables
import Itasca.Runtime.Code.Body.Reader.Simd.ReaderSimdShuffle
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Independent source meaning of a SIMD callback, including the constant
pool case. Its fields are syntactic, not a promise about callback execution. -/
inductive SimdCallbackMeaning (C : context) : U32 → U32 → U128 → List types.ValueType → instr → Option types.ValueType → Prop
  | instruction {sub a bits input source output}
      (meaning : SimdImmediateMeaning C sub (simdImmediate sub a bits) (Wasm2.Simd.inputTypes input) source (Wasm2.Simd.outputTypes output)) :
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
    DeclaredReferences.Instruction references source := by
  cases meaning with
  | pure sub immediate op meaning => exact op.declared references
  | lane sub immediate op meaning lane position => exact op.declared references _
  | memory sub immediate op meaning arg lane memory available offset position => exact op.declared references _ _
  | shuffle immediate lo hi bits => exact Wasm2.Simd.shuffle_declared references lo hi

namespace SimdCallbackMeaning
theorem declared {C sub a bits input source output}
    (meaning : SimdCallbackMeaning C sub a bits input source output) (references : List funcidx) :
    DeclaredReferences.Instruction references source := by
  cases meaning with
  | instruction h => exact h.declared references
  | constant => simp [DeclaredReferences.Instruction,DeclaredReferences.instructionIndices]
end SimdCallbackMeaning
end Itasca.Runtime.Code
