import Itasca.Visitor.Dispatch
import Itasca.Visitor.Events
import Itasca.Visitor.Basic

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

theorem dispatch_block {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_BLOCK v =
      CoreVisitor.run (code.read_block st data) (fun v s a => invoke visitor v (.op s (.block (Control.signature a)))) v := by
  simpa only [invoke] using OpDispatch.dispatch_block visitor st data env ctx v

theorem dispatch_loop {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_LOOP v =
      CoreVisitor.run (code.read_loop st data) (fun v s a => invoke visitor v (.op s (.loop (Control.signature a)))) v := by
  simpa only [invoke] using OpDispatch.dispatch_loop visitor st data env ctx v

theorem dispatch_if {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_IF v =
      CoreVisitor.run (code.read_if st data) (fun v s a => invoke visitor v (.op s (.if_ (Control.signature a)))) v := by
  simpa only [invoke] using OpDispatch.dispatch_if visitor st data env ctx v

theorem dispatch_else {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_ELSE v =
      CoreVisitor.run (code.read_else st) (fun v s a => invoke visitor v (.op s (.else_ (Control.signature a)))) v := by
  simpa only [invoke] using OpDispatch.dispatch_else visitor st data env ctx v

theorem dispatch_end {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_END v =
      CoreVisitor.run (code.read_end st) (fun v s arg => invoke visitor v (.op s (.end_ arg.1 (Control.signature arg.2)))) v := by
  simpa only [invoke] using OpDispatch.dispatch_end visitor st data env ctx v

theorem dispatch_br {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_BR v =
      CoreVisitor.run (code.read_br st data) (fun v s arg => invoke visitor v (.op s (.br arg.1 (Control.resultView arg.2)))) v := by
  simpa only [invoke] using OpDispatch.dispatch_br visitor st data env ctx v

theorem dispatch_br_if {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_BR_IF v =
      CoreVisitor.run (code.read_br_if st data) (fun v s arg => invoke visitor v (.op s (.br_if arg.1 (Control.resultView arg.2)))) v := by
  simpa only [invoke] using OpDispatch.dispatch_br_if visitor st data env ctx v

theorem dispatch_return {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_RETURN v =
      CoreVisitor.run (code.read_return st ctx) (fun v s _ => invoke visitor v (.op s .return_)) v := by
  simpa only [invoke] using OpDispatch.dispatch_return visitor st data env ctx v

end Itasca.VisitorTrace
