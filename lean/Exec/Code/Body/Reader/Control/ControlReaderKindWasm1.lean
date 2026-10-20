import Exec.Code.Body.Reader.Control.ControlReaderKind
import Itasca.Visitor.EventDispatch

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
namespace ControlReaderKind

/-- Wasm 1 readers retain their binary single-result block descriptors. -/
def ParameterWasm1 : ControlReaderKind → Type
  | .block => code.BlockType
  | .loop => code.BlockType
  | .if_ => code.BlockType
  | .else_ => code.BlockType
  | .end_ => code.LabelKind × code.BlockType
  | .br => U32 × code.BlockType
  | .br_if => U32 × code.BlockType
  | .return_ => Unit
  | .call => U32
  | .call_indirect => U32

def readWasm1 (kind : ControlReaderKind) (st : code.OpIterState) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) : Result (core.result.Result kind.ParameterWasm1 error.OpError × code.OpIterState) :=
  match kind with
  | .block => code.read_block st data
  | .loop => code.read_loop st data
  | .if_ => code.read_if st data
  | .else_ => code.read_else st
  | .end_ => code.read_end st
  | .br => code.read_br st data
  | .br_if => code.read_br_if st data
  | .return_ => code.read_return st ctx
  | .call => code.read_call st data env
  | .call_indirect => code.read_call_indirect st data env

def actionWasm1 : (kind : ControlReaderKind) → kind.ParameterWasm1 → Action
  | .block => fun arg => .block (Control.signature arg)
  | .loop => fun arg => .loop (Control.signature arg)
  | .if_ => fun arg => .if_ (Control.signature arg)
  | .else_ => fun arg => .else_ (Control.signature arg)
  | .end_ => fun arg => .end_ arg.1 (Control.signature arg.2)
  | .br => fun arg => .br arg.1 (Control.resultView arg.2)
  | .br_if => fun arg => .br_if arg.1 (Control.resultView arg.2)
  | .return_ => fun _ => .return_
  | .call => .call
  | .call_indirect => fun arg => .call_indirect arg 0#u32

/-- Every Wasm 1 inventory entry agrees with actual extracted raw dispatch. -/
theorem dispatch_wasm1 {V : Type} (kind : ControlReaderKind) (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (before : V) :
    code.step visitor st data env ctx kind.opcode before =
      CoreVisitor.run (kind.readWasm1 st data env ctx)
        (fun log state value => invoke visitor log (.op state (kind.actionWasm1 value))) before := by
  cases kind
  · simpa only [opcode,ParameterWasm1,readWasm1,actionWasm1,global_simps] using dispatch_block visitor st data env ctx before
  · simpa only [opcode,ParameterWasm1,readWasm1,actionWasm1,global_simps] using dispatch_loop visitor st data env ctx before
  · simpa only [opcode,ParameterWasm1,readWasm1,actionWasm1,global_simps] using dispatch_if visitor st data env ctx before
  · simpa only [opcode,ParameterWasm1,readWasm1,actionWasm1,global_simps] using dispatch_else visitor st data env ctx before
  · simpa only [opcode,ParameterWasm1,readWasm1,actionWasm1,global_simps] using dispatch_end visitor st data env ctx before
  · simpa only [opcode,ParameterWasm1,readWasm1,actionWasm1,global_simps] using dispatch_br visitor st data env ctx before
  · simpa only [opcode,ParameterWasm1,readWasm1,actionWasm1,global_simps] using dispatch_br_if visitor st data env ctx before
  · simpa only [opcode,ParameterWasm1,readWasm1,actionWasm1,global_simps] using dispatch_return visitor st data env ctx before
  · simpa only [opcode,ParameterWasm1,readWasm1,actionWasm1,global_simps] using dispatch_call visitor st data env ctx before
  · simpa only [opcode,ParameterWasm1,readWasm1,actionWasm1,global_simps] using dispatch_call_indirect visitor st data env ctx before

end ControlReaderKind
end Exec.Code
