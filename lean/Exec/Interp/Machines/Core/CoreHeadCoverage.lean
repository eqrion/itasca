import Exec.Interp.Relations.HeadCoverage
import Exec.Interp.Core.Point
namespace Exec.Interp
open Aeneas.Std

/-- Exact ready source heads accepted by the contextual compiler certificate.
Indices and constant words are recovered from emitted syntax, not assumed. -/
inductive CoreDispatchHead : instr → Prop where
  | pure {op : instr} (head : DispatchHead op) : CoreDispatchHead op
  | float32 (bits : U32) : CoreDispatchHead (.CONST .F32 (.mk_num__1 .F32 (SpecExt.Builtins.floatOfBits 32 bits.val)))
  | float64 (bits : U64) : CoreDispatchHead (.CONST .F64 (.mk_num__1 .F64 (SpecExt.Builtins.floatOfBits 64 bits.val)))
  | select : CoreDispatchHead (.SELECT none)
  | globalGet (index : U32) : CoreDispatchHead (.GLOBAL_GET (.mk_uN index.val))
  | globalSet (index : U32) : CoreDispatchHead (.GLOBAL_SET (.mk_uN index.val))
  | load (op : Abs.Memory.Load) (argument : memarg) : CoreDispatchHead (op.source argument)
  | store (op : Abs.Memory.Store) (argument : memarg) : CoreDispatchHead (op.source argument)

theorem linearEmission_ready_head {locals before op emitted after}
    (head : Code.LinearEmission locals before op emitted after)
    (ready : ReadyInstruction op) : DispatchHead op := by
  cases head with
  | nop => exact False.elim ready
  | drop => exact False.elim ready
  | const32 stack dst word slot => exact .ordinary (.const32 word)
  | const64 stack dst word slot => exact .ordinary (.const64 word)
  | binary stack ty binary a b left right =>
    cases binary with
    | add => exact .ordinary (.binary ty .add)
    | sub => exact .ordinary (.binary ty .sub)
    | eq => exact .ordinary (.binary ty .eq)
    | ltU => exact .ordinary (.binary ty .ltU)
    | mul => exact .numeric (.binary ty .MUL)
    | ne => exact .numeric (.compare ty .NE)
    | gtU => exact .numeric (.compare ty (.GT .U))
    | leU => exact .numeric (.compare ty (.LE .U))
    | geU => exact .numeric (.compare ty (.GE .U))
  | numeric stack op a b left right => exact .numeric op
  | eqz32 stack a slot => exact .ordinary (.eqz .I32)
  | eqz64 stack a slot => exact .ordinary (.eqz .I64)
  | localGet stack ty index src dst localType localPos stackPos => exact .ordinary (.localGet index)
  | localSet stack ty index dst src localType localPos stackPos => exact .ordinary (.localWrite index false)
  | localTee stack ty index dst src localType localPos stackPos => exact .ordinary (.localWrite index true)

theorem coreEmission_ready_head {C before op emitted after}
    (head : Code.CoreEmission C before op emitted after)
    (ready : ReadyInstruction op) : CoreDispatchHead op := by
  cases head with
  | pure original => exact .pure (linearEmission_ready_head original ready)
  | float32 stack dst bits slot => exact .float32 bits
  | float64 stack dst bits slot => exact .float64 bits
  | select => exact .select
  | globalGet stack mutability ty index dst globalType slot => exact .globalGet index
  | globalSet stack ty index src globalType slot => exact .globalSet index
  | load stack op argument address offset memory available sourceOffset slot => exact .load op argument
  | store stack op argument address value offset memory available sourceOffset addressSlot valueSlot => exact .store op argument

/-- A finite chain of retained forward jumps cannot obscure the exact head
classification of a compiled source instruction. -/
theorem coreCodeRel_head_coverage {C returns locals code labels stack op source next output}
    (ready : ReadyInstruction op) :
    ∀ pc, Code.StructuredCode (Code.CoreEmission C) C.TYPES C.FUNCS returns locals code labels stack
      (op::source) pc next output → CoreDispatchHead op := by
  intro pc relation
  generalize measureEq : code.length-pc = measure
  induction measure using Nat.strong_induction_on generalizing pc with
  | h measure ih =>
    cases relation with
    | linear head fragment rest => exact coreEmission_ready_head head ready
    | skip forward fetched rest =>
      have bound := rest.entry_bound
      exact ih _ (by omega) _ rest rfl
    | block => exact False.elim ready
    | loop => exact .pure (.loop _ _)
    | ifElse => exact .pure (.ordinary (.ifElse _ _ _))
    | branch => exact .pure (.ordinary (.branch _))
    | branchIf => exact .pure (.ordinary (.branchIf _))
    | call => exact .pure (.call _)
    | unreachable => exact .pure .unreachable
    | return_ => exact .pure .return_

theorem core_head_coverage {sourceStore raw f compiled C targets next output}
    (point : CoreFramePoint sourceStore raw f compiled C targets next output)
    (ready : ReadySource f) (op : instr) (after : List instr) (code : f.code = op::after) :
    CoreDispatchHead op := by
  have readyOp : ReadyInstruction op := by
    cases op <;> simp_all only [ReadyInstruction,ReadySource,code]
  exact coreCodeRel_head_coverage readyOp raw.pc.val (by simpa only [code] using point.code.current)
end Exec.Interp
