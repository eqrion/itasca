import Exec.Interp.Cumulative.Heads
import Exec.Interp.StructuredMachine.SupportedHeadCoverage
import Exec.Interp.StructuredMachine.SimdProjection
import Exec.Interp.StructuredMachine.TypedSelectHeads
import Exec.Interp.StructuredMachine.StatefulProjection
import Exec.Interp.StructuredMachine.IndirectProjection
namespace Exec.Interp.StructuredMachine
open Aeneas.Std
private def typedSelectTag : instr → Bool
  | .SELECT (some _) => true
  | _ => false
private theorem linear_not_typed_select {locals before source emitted after}
    (head : Code.LinearEmission locals before source emitted after) : typedSelectTag source = false := by
  cases head with
  | binary stack ty op => cases op <;> rfl
  | numeric stack op => cases op with
    | conversion op => cases op <;> rfl
    | _ => rfl
  | _ => rfl

private theorem core_not_typed_select {C before source emitted after}
    (head : Code.CoreEmission C before source emitted after) : typedSelectTag source = false := by
  cases head with
  | pure head => exact linear_not_typed_select head
  | _ => rfl

private theorem float_not_typed_select {C before source emitted after}
    (head : Code.FloatCoreEmission C before source emitted after) : typedSelectTag source = false := by
  cases head with
  | core head => exact core_not_typed_select head
  | scalar stack op => cases op <;> rfl

private theorem cumulative_not_typed_select {pairs C before source emitted after}
    (head : Code.CumulativeEmission pairs C before source emitted after) : typedSelectTag source = false := by
  cases head with
  | left head => exact float_not_typed_select head
  | right head => cases head with
    | instruction stack input output op => cases op <;> rfl
  | indirect head => cases head; rfl

instance (pairs : List (U32 × U32)) (simd : List runtime.bytecode.SimdImmediate) (constants : List U128) :
    SimdProjection (Code.CumulativeEmission pairs) simd constants where
  project allowed head := by
    have impossible := allowed.source_tag.symm.trans head.simd_tag
    contradiction

instance (pairs : List (U32 × U32)) : TypedSelectHeads (Code.CumulativeEmission pairs) where
  project head := by
    have impossible := cumulative_not_typed_select head
    contradiction

instance (compiled : runtime.bytecode.CompiledFunction) : SupportedHeads (Cumulative.emission compiled) := by
  unfold Cumulative.emission
  infer_instance
instance (compiled : runtime.bytecode.CompiledFunction) :
    SimdProjection (Cumulative.emission compiled) compiled.simd.val compiled.v128_pool.val := by
  unfold Cumulative.emission
  infer_instance
instance (compiled : runtime.bytecode.CompiledFunction) : TypedSelectHeads (Cumulative.emission compiled) := by
  unfold Cumulative.emission
  infer_instance
end Exec.Interp.StructuredMachine
