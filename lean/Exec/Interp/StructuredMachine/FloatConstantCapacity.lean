import Exec.Interp.StructuredMachine.FloatConstantPoint
import Exec.Interp.Relations.Capacity
namespace Itasca.Runtime.Interp.StructuredMachine.FloatConstant
variable {family : ContextEmission} [FloatHeads family]
open Aeneas Aeneas.Std

theorem float32_point_capacity (compiled : runtime.bytecode.CompiledFunction)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (C : context) (returns stack : List valtype) (labels : List Code.LabelTarget)
    (value : fN) (after : List instr) (next : Nat) (output : List valtype) :
    ∀ pc, Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS compiled.code.val compiled.jump_tables.val labels stack
      (.CONST .F32 (.mk_num__1 .F32 value)::after) pc next output →
      Code.slots C.LOCALS + Code.slots stack < compiled.slot_count.val := by
  intro pc point
  generalize measureEq : compiled.code.val.length-pc = measure
  induction measure using Nat.strong_induction_on generalizing pc with
  | h measure ih =>
    rcases corePoint_float32_head value after point with ⟨target,forward,fetch,tail⟩ | ⟨dst,bits,valueEq,position,fetch,tail⟩
    · have bound := tail.current.entry_bound
      exact ih (compiled.code.val.length-target.val) (by omega) target.val tail rfl
    · have bound := Code.const32_valid_bounds compiled dst bits (Code.well_formed_fetched compiled checked pc _ fetch)
      simpa only [position] using bound

theorem float64_point_capacity (compiled : runtime.bytecode.CompiledFunction)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (C : context) (returns stack : List valtype) (labels : List Code.LabelTarget)
    (value : fN) (after : List instr) (next : Nat) (output : List valtype) :
    ∀ pc, Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS compiled.code.val compiled.jump_tables.val labels stack
      (.CONST .F64 (.mk_num__1 .F64 value)::after) pc next output →
      Code.slots C.LOCALS + Code.slots stack < compiled.slot_count.val := by
  intro pc point
  generalize measureEq : compiled.code.val.length-pc = measure
  induction measure using Nat.strong_induction_on generalizing pc with
  | h measure ih =>
    rcases corePoint_float64_head value after point with ⟨target,forward,fetch,tail⟩ | ⟨dst,bits,valueEq,position,fetch,tail⟩
    · have bound := tail.current.entry_bound
      exact ih (compiled.code.val.length-target.val) (by omega) target.val tail rfl
    · have bound := Code.const64_valid_bounds compiled dst bits (Code.well_formed_fetched compiled checked pc _ fetch)
      simpa only [position] using bound

end Itasca.Runtime.Interp.StructuredMachine.FloatConstant
