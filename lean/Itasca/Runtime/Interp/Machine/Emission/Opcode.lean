import Itasca.Runtime.Interp.Relations.PrefixDispatch
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.Interp.Machine.Emission.Binary

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
