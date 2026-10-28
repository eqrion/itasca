import Itasca.Runtime.Interp.StructuredMachine.IntegerConstantPoint
import Itasca.Runtime.Interp.Relations.Capacity
namespace Itasca.Runtime.Interp.StructuredMachine.IntegerConstant
variable {family : ContextEmission} [FloatHeads family]
open Aeneas Aeneas.Std

theorem integer32_point_capacity (compiled : runtime.bytecode.CompiledFunction)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (C : context) (returns stack : List valtype) (labels : List Code.LabelTarget)
    (value : U32) (after : List instr) (next : Nat) (output : List valtype) :
    ∀ pc, Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS compiled.code.val compiled.jump_tables.val labels stack
      (.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))::after) pc next output →
      Code.slots C.LOCALS + Code.slots stack < compiled.slot_count.val := by
  intro pc point
  generalize measureEq : compiled.code.val.length-pc = measure
  induction measure using Nat.strong_induction_on generalizing pc with
  | h measure ih =>
    rcases corePoint_integer32_head value after point with ⟨target,forward,fetch,tail⟩ | ⟨dst,bits,valueEq,position,fetch,tail⟩
    · have bound := tail.current.entry_bound
      exact ih (compiled.code.val.length-target.val) (by omega) target.val tail rfl
    · have bound := Code.const32_valid_bounds compiled dst bits (Code.well_formed_fetched compiled checked pc _ fetch)
      simpa only [position] using bound

theorem integer64_point_capacity (compiled : runtime.bytecode.CompiledFunction)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (C : context) (returns stack : List valtype) (labels : List Code.LabelTarget)
    (value : U64) (after : List instr) (next : Nat) (output : List valtype) :
    ∀ pc, Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS compiled.code.val compiled.jump_tables.val labels stack
      (.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val))::after) pc next output →
      Code.slots C.LOCALS + Code.slots stack < compiled.slot_count.val := by
  intro pc point
  generalize measureEq : compiled.code.val.length-pc = measure
  induction measure using Nat.strong_induction_on generalizing pc with
  | h measure ih =>
    rcases corePoint_integer64_head value after point with ⟨target,forward,fetch,tail⟩ | ⟨dst,bits,valueEq,position,fetch,tail⟩
    · have bound := tail.current.entry_bound
      exact ih (compiled.code.val.length-target.val) (by omega) target.val tail rfl
    · have bound := Code.const64_valid_bounds compiled dst bits (Code.well_formed_fetched compiled checked pc _ fetch)
      simpa only [position] using bound

end Itasca.Runtime.Interp.StructuredMachine.IntegerConstant
