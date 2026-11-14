import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.Interp.Numeric.Integer.IntCounts
import Itasca.Runtime.Interp.Relations.Defaults
import Itasca.Runtime.SourceMachine.Sim.Structured
import Itasca.Runtime.Interp.Relations.StackPreservation

/-!
Sections, each formerly its own module: Integer, Empty, Binary, Opcode, Local.
-/

/-! ## Integer -/

section

/-!
Pure scalar-emission inversion for integer operations.

Main declarations: `scalar_emission_numeric_pure`. A direct consumer is `Interp.Machine.Numeric`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem scalar_emission_numeric_pure {C before after emitted} (op : SourceMachine.Numeric.Instruction)
    (emission : Compiler.ScalarEmission C before op.source emitted after) :
    Compiler.LinearEmission C.LOCALS before op.source emitted after := by
  generalize equality : op.source = instruction at emission
  cases emission with
  | linear head => simpa only [equality] using head
  | float stack other =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Numeric.decodeInstruction] at decoded
  | _ =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    simp [SourceMachine.Numeric.decodeInstruction,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at decoded
end Itasca.Runtime.Interp

end

/-! ## Empty -/

section

/-!
Pure scalar-emission inversion for nop and drop.

Main declarations: `scalar_emission_nop_pure` and `scalar_emission_drop_pure`. A direct consumer is `Interp.Machine.Coverage.Heads`.
-/

namespace Itasca.Runtime.Interp
open Aeneas.Std

theorem scalar_emission_nop_pure {C before after emitted}
    (emission : Compiler.ScalarEmission C before .NOP emitted after) :
    Compiler.LinearEmission C.LOCALS before .NOP emitted after := by
  generalize equality : instr.NOP = instruction at emission
  cases emission with
  | linear head => simpa only [←equality] using head
  | float stack other => cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
  | _ => simp_all [SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source]

theorem scalar_emission_drop_pure {C before after emitted}
    (emission : Compiler.ScalarEmission C before .DROP emitted after) :
    Compiler.LinearEmission C.LOCALS before .DROP emitted after := by
  generalize equality : instr.DROP = instruction at emission
  cases emission with
  | linear head => simpa only [←equality] using head
  | float stack other => cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
  | _ => simp_all [SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source]

end Itasca.Runtime.Interp

end

/-! ## Binary -/

section

/-!
Binary instructions in the initial proved abstract slice.

Main declarations: `SliceBinary` and `SliceBinary.operation`. A direct consumer is `Interp.Machine.Emission.Opcode`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Binary instructions in the initial proved abstract slice. -/
inductive SliceBinary where
  | add | sub | eq | ltU

def SliceBinary.operation : SliceBinary → Compiler.IntegerBinary
  | .add => .add | .sub => .sub | .eq => .eq | .ltU => .ltU

end Itasca.Runtime.Interp

end

/-! ## Opcode -/

section

/-!
Operand-bearing source forms covered by the ordinary integer slice. The encoded constants and indices are recovered from compiler evidence.

Main declarations: `OrdinaryOpcode` and `OrdinaryOpcode.source`. A direct consumer is `Interp.Machine.History.Append`.
-/

namespace Itasca.Runtime.Interp
open Aeneas.Std

/-- Operand-bearing source forms covered by the ordinary integer slice. The
encoded constants and indices are recovered from compiler evidence. -/
inductive OrdinaryOpcode where
  | const32 (value : U32) | const64 (value : U64)
  | binary (ty : Inn) (op : SliceBinary)
  | eqz (ty : Inn)
  | localGet (index : U32) | localWrite (index : U32) (keep : Bool)
  | branch (depth : Nat) | branchIf (depth : Nat)
  | ifElse (bt : blocktype) (yes no : List instr)

def OrdinaryOpcode.source : OrdinaryOpcode → instr
  | .const32 value => .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))
  | .const64 value => .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val))
  | .binary ty op => op.operation.source ty
  | .eqz ty => .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ)
  | .localGet index => .LOCAL_GET (.mk_uN index.val)
  | .localWrite index keep => if keep then .LOCAL_TEE (.mk_uN index.val) else .LOCAL_SET (.mk_uN index.val)
  | .branch depth => .BR (.mk_uN depth)
  | .branchIf depth => .BR_IF (.mk_uN depth)
  | .ifElse bt yes no => .IFELSE bt yes no

end Itasca.Runtime.Interp

end

/-! ## Local -/

section

/-!
Inversion of local get/write emission.

Main declarations: `scalar_emission_local_get_pure` and `scalar_emission_local_write_pure`. A direct consumer is `Interp.Machine.Local.Inversion`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem scalar_emission_local_get_pure {C before after emitted} (index : Nat)
    (emission : Compiler.ScalarEmission C before (.LOCAL_GET (.mk_uN index)) emitted after) :
    Compiler.LinearEmission C.LOCALS before (.LOCAL_GET (.mk_uN index)) emitted after := by
  generalize equality : instr.LOCAL_GET (.mk_uN index) = instruction at emission
  cases emission with
  | linear head => simpa only [←equality] using head
  | float stack other => cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
  | _ => simp_all [SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source]

theorem scalar_emission_local_write_pure {C before after emitted} (index : Nat) (keep : Bool)
    (emission : Compiler.ScalarEmission C before (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) emitted after) :
    Compiler.LinearEmission C.LOCALS before (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) emitted after := by
  generalize equality : (if keep then instr.LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) = instruction at emission
  cases emission with
  | linear head => simpa only [equality] using head
  | float stack other => cases keep <;> cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
  | _ => cases keep <;> simp_all [SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source]
end Itasca.Runtime.Interp

end
