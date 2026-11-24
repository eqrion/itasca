import Itasca.Runtime.SourceMachine.Simd.MemoryTransition
import Itasca.Runtime.Compiler.Local.Definitions
import Itasca.Runtime.Compiler.Local.Lowering.Simd.ConstructionChecks

/-!
# SIMD emission tags

Linear and scalar emission relations constrain the tags of emitted SIMD instructions. Body constructions use these exclusions to distinguish instruction families syntactically.
-/

namespace Itasca.Compiler

theorem LinearEmission.simd_tag {locals before source emitted after}
    (head : LinearEmission locals before source emitted after) : SourceMachine.simdSourceTag source = false := by
  cases head with
  | binary stack ty op => cases op <;> rfl
  | numeric stack op => cases op <;> rfl
  | _ => rfl

theorem ScalarEmission.simd_tag {C before source emitted after}
    (head : ScalarEmission C before source emitted after) : SourceMachine.simdSourceTag source = false := by
  cases head with
  | linear head => exact head.simd_tag
  | load stack op => cases op <;> rfl
  | store stack op => cases op <;> rfl
  | float stack op => cases op <;> rfl
  | _ => rfl
end Itasca.Compiler
