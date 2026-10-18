import Exec.Abs.Numeric.Decode
import Exec.Interp.Machines.Slice.SliceOpcode
import Exec.Interp.Control.NormalizeClosure

namespace Exec.Interp
open Aeneas.Std

/-- Source forms remaining after zero-byte normalization. -/
def ReadyInstruction : instr → Prop
  | .NOP | .DROP | .BLOCK _ _ => False
  | _ => True

inductive DispatchHead : instr → Prop where
  | numeric (op : Abs.Numeric.Instruction) : DispatchHead op.source
  | ordinary (op : OrdinaryOpcode) : DispatchHead op.source
  | loop (bt : blocktype) (body : List instr) : DispatchHead (.LOOP bt body)
  | call (index : U32) : DispatchHead (.CALL (.mk_uN index.val))
  | return_ : DispatchHead .RETURN
  | unreachable : DispatchHead .UNREACHABLE

theorem numeric_head_coverage (op : Abs.Numeric.Instruction)
    (slice : Abs.SliceInstr op.source) : DispatchHead op.source := by
  exact .numeric op

/-- Compiler syntax supplies encoded words and indices, including through an
arbitrary finite chain of administrative forward jumps. -/
theorem codeRel_head_coverage {types functions returns locals code labels stack op source next output}
    (slice : Abs.SliceInstr op) (ready : ReadyInstruction op) :
    ∀ pc, Code.CodeRel types functions returns locals code labels stack (op :: source) pc next output →
      DispatchHead op := by
  intro pc relation
  generalize measureEq : code.length - pc = measure
  induction measure using Nat.strong_induction_on generalizing pc with
  | h measure ih =>
    cases relation with
    | linear head fragment rest =>
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
      | numeric stack op a b left right => exact numeric_head_coverage op slice
      | eqz32 stack a slot => exact .ordinary (.eqz .I32)
      | eqz64 stack a slot => exact .ordinary (.eqz .I64)
      | localGet stack ty index src dst localType localPos stackPos => exact .ordinary (.localGet index)
      | localSet stack ty index dst src localType localPos stackPos => exact .ordinary (.localWrite index false)
      | localTee stack ty index dst src localType localPos stackPos => exact .ordinary (.localWrite index true)
    | skip forward fetched rest =>
      have bound := rest.entry_bound
      exact ih _ (by omega) _ rest rfl
    | block => exact False.elim ready
    | loop => exact .loop _ _
    | ifElse => exact .ordinary (.ifElse _ _ _)
    | branch => exact .ordinary (.branch _)
    | branchIf => exact .ordinary (.branchIf _)
    | call => exact .call _
    | unreachable => exact .unreachable
    | return_ => exact .return_

theorem structured_head_coverage {raw f compiled functions targets next output}
    (point : StructuredFramePoint raw f compiled functions targets next output)
    (slice : Abs.FrameSlice f) (ready : ReadySource f)
    (op : instr) (after : List instr) (code : f.code = op :: after) : DispatchHead op := by
  have allowed : Abs.SliceInstr op := slice.1 op (by rw [code]; exact List.mem_cons_self ..)
  have readyOp : ReadyInstruction op := by
    cases op <;> simp_all only [ReadyInstruction, ReadySource, code]
  exact codeRel_head_coverage allowed readyOp raw.pc.val (by simpa only [code] using point.code.current)

end Exec.Interp
