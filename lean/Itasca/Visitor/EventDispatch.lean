import Itasca.Visitor.Dispatch
import Itasca.Visitor.EventTables
import Itasca.Handler.EnvDispatch
import Itasca.Handler.Select
import Itasca.Handler.NumericDispatch
import Itasca.Visitor.Events
import Itasca.Visitor.Basic

/-!
# Step dispatch to events

The `VisitorTrace.dispatch_*` theorems restate the dispatch of `code.step` for every instruction
as `CoreVisitor.run` of its reader followed by `invoke` of the matching `Event`. Together with
`Visitor/EventTables` they let trace proofs treat each instruction step as reading its immediates
and then reporting one event. Covers the Wasm 1.0 instructions.
-/

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

/-- `code.step` on `code.OP_NOP` reads no immediates and calls the hook for the `nop` event. -/
theorem dispatch_nop {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_NOP v =
      CoreVisitor.run (.ok (.Ok (), st)) (fun v s _ => invoke visitor v (.op s (.nop))) v := by
  simpa only [invoke] using OpDispatch.dispatch_nop visitor st data env ctx v

/-- `code.step` on `code.OP_UNREACHABLE` runs `code.read_unreachable` and then calls the hook for
the `unreachable` event. -/
theorem dispatch_unreachable {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_UNREACHABLE v =
      CoreVisitor.run (code.read_unreachable st) (fun v s _ => invoke visitor v (.op s (.unreachable))) v := by
  simpa only [invoke] using OpDispatch.dispatch_unreachable visitor st data env ctx v

/-- `code.step` on `code.OP_DROP` runs `code.read_drop` and then calls the hook for the `drop`
event. -/
theorem dispatch_drop {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_DROP v =
      CoreVisitor.run (code.read_drop st) (fun v s a => invoke visitor v (.op s (.drop a))) v := by
  simpa only [invoke] using OpDispatch.dispatch_drop visitor st data env ctx v

/-- `code.step` on `code.OP_I32_CONST` runs `code.read_i32_const` and then calls the hook for the
`i32_const` event. -/
theorem dispatch_i32_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_I32_CONST v =
      CoreVisitor.run (code.read_i32_const st data) (fun v s a => invoke visitor v (.op s (.i32_const a))) v := by
  simpa only [invoke] using OpDispatch.dispatch_i32_const visitor st data env ctx v

/-- `code.step` on `code.OP_I64_CONST` runs `code.read_i64_const` and then calls the hook for the
`i64_const` event. -/
theorem dispatch_i64_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_I64_CONST v =
      CoreVisitor.run (code.read_i64_const st data) (fun v s a => invoke visitor v (.op s (.i64_const a))) v := by
  simpa only [invoke] using OpDispatch.dispatch_i64_const visitor st data env ctx v

/-- `code.step` on `code.OP_F32_CONST` runs `code.read_f32_const` and then calls the hook for the
`f32_const` event. -/
theorem dispatch_f32_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_F32_CONST v =
      CoreVisitor.run (code.read_f32_const st data) (fun v s a => invoke visitor v (.op s (.f32_const a))) v := by
  simpa only [invoke] using OpDispatch.dispatch_f32_const visitor st data env ctx v

/-- `code.step` on `code.OP_F64_CONST` runs `code.read_f64_const` and then calls the hook for the
`f64_const` event. -/
theorem dispatch_f64_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_F64_CONST v =
      CoreVisitor.run (code.read_f64_const st data) (fun v s a => invoke visitor v (.op s (.f64_const a))) v := by
  simpa only [invoke] using OpDispatch.dispatch_f64_const visitor st data env ctx v

/-- `code.step` on `code.OP_SELECT` runs `code.read_select` and then calls the hook for the `select`
event. -/
theorem dispatch_select {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_SELECT v =
      CoreVisitor.run (code.read_select st) (fun v s a => invoke visitor v (.op s (.select a))) v :=
  code.step_select.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_LOCAL_GET` runs `code.read_local_get` and then calls the hook for the
`local_get` event. -/
theorem dispatch_local_get {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_LOCAL_GET v =
      CoreVisitor.run (code.read_local_get st data ctx) (fun v s a => invoke visitor v (.op s (.local_get a))) v :=
  code.step_local_get.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_LOCAL_SET` runs `code.read_local_set` and then calls the hook for the
`local_set` event. -/
theorem dispatch_local_set {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_LOCAL_SET v =
      CoreVisitor.run (code.read_local_set st data ctx) (fun v s a => invoke visitor v (.op s (.local_set a))) v :=
  code.step_local_set.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_LOCAL_TEE` runs `code.read_local_tee` and then calls the hook for the
`local_tee` event. -/
theorem dispatch_local_tee {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_LOCAL_TEE v =
      CoreVisitor.run (code.read_local_tee st data ctx) (fun v s a => invoke visitor v (.op s (.local_tee a))) v :=
  code.step_local_tee.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_GLOBAL_GET` runs `code.read_global_get` and then calls the hook for the
`global_get` event. -/
theorem dispatch_global_get {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_GLOBAL_GET v =
      CoreVisitor.run (code.read_global_get st data env) (fun v s a => invoke visitor v (.op s (.global_get a))) v :=
  code.step_global_get.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_GLOBAL_SET` runs `code.read_global_set` and then calls the hook for the
`global_set` event. -/
theorem dispatch_global_set {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_GLOBAL_SET v =
      CoreVisitor.run (code.read_global_set st data env) (fun v s a => invoke visitor v (.op s (.global_set a))) v :=
  code.step_global_set.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_CALL` runs `code.read_call` and then calls the hook for the `call`
event. -/
theorem dispatch_call {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_CALL v =
      CoreVisitor.run (code.read_call st data env) (fun v s a => invoke visitor v (.op s (.call a))) v :=
  code.step_call.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_CALL_INDIRECT` runs `code.read_call_indirect` and then calls the hook
for the `call_indirect` event. -/
theorem dispatch_call_indirect {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_CALL_INDIRECT v =
      CoreVisitor.run (code.read_call_indirect st data env) (fun v s a => invoke visitor v (.op s (.call_indirect a 0#u32))) v :=
  code.step_call_indirect.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_MEMORY_SIZE` runs `code.read_memory_size` and then calls the hook for
the `memory_size` event. -/
theorem dispatch_memory_size {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_MEMORY_SIZE v =
      CoreVisitor.run (code.read_memory_size st data env) (fun v s _ => invoke visitor v (.op s (.memory_size))) v :=
  code.step_memory_size.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_MEMORY_GROW` runs `code.read_memory_grow` and then calls the hook for
the `memory_grow` event. -/
theorem dispatch_memory_grow {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_MEMORY_GROW v =
      CoreVisitor.run (code.read_memory_grow st data env) (fun v s _ => invoke visitor v (.op s (.memory_grow))) v :=
  code.step_memory_grow.dispatch visitor st data env ctx v

/-- A numeric opcode with a binary row and a callback runs `Numeric.read` and then reports the
numeric event of that callback. -/
theorem dispatch_numeric {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (opcode : U8) (operation : Numeric.Operation) (hook : NumericHook)
    (hrow : Numeric.opcodeMeaning opcode = some operation)
    (hhook : NumericHook.ofOpcode opcode = some hook) :
    code.step visitor st data env ctx opcode v =
      CoreVisitor.run (Numeric.read operation st)
        (fun v s (_ : Unit) => invoke visitor v (.op s (.numeric hook))) v := by
  rw [code.step.numeric_dispatch visitor st data env ctx opcode v (Numeric.NumericOp.bounds hrow).1,
    code.step_numeric.dispatch visitor st opcode operation v hrow]
  simp only [visit_numeric, hhook]

/-- A load or store opcode with a binary row and a callback runs `code.read_load` or
`code.read_store` and then reports the memory event of that callback. -/
theorem dispatch_memory {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (opcode : U8) (operation : MemoryMeaning.Operation) (hook : MemoryHook)
    (hrow : MemoryMeaning.opcodeMeaning opcode = some operation)
    (hhook : MemoryHook.ofOpcode opcode = some hook) :
    code.step visitor st data env ctx opcode v =
      CoreVisitor.run
        (if operation.store then code.read_store st data env operation.ty operation.naturalAlign
          else code.read_load st data env operation.ty operation.naturalAlign)
        (fun v s arg => invoke visitor v (.op s (.memory hook arg))) v := by
  rw [code.step_memory.dispatch visitor st data env ctx v opcode operation hrow]
  simp only [visit_memory, hhook]

end Itasca.VisitorTrace

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

/-- `code.step` on `code.OP_BLOCK` runs `code.read_block` and then calls the hook for the `block`
event. -/
theorem dispatch_block {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_BLOCK v =
      CoreVisitor.run (code.read_block st data) (fun v s a => invoke visitor v (.op s (.block (Control.signature a)))) v := by
  simpa only [invoke] using OpDispatch.dispatch_block visitor st data env ctx v

/-- `code.step` on `code.OP_LOOP` runs `code.read_loop` and then calls the hook for the `loop`
event. -/
theorem dispatch_loop {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_LOOP v =
      CoreVisitor.run (code.read_loop st data) (fun v s a => invoke visitor v (.op s (.loop (Control.signature a)))) v := by
  simpa only [invoke] using OpDispatch.dispatch_loop visitor st data env ctx v

/-- `code.step` on `code.OP_IF` runs `code.read_if` and then calls the hook for the `if` event. -/
theorem dispatch_if {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_IF v =
      CoreVisitor.run (code.read_if st data) (fun v s a => invoke visitor v (.op s (.if_ (Control.signature a)))) v := by
  simpa only [invoke] using OpDispatch.dispatch_if visitor st data env ctx v

/-- `code.step` on `code.OP_ELSE` runs `code.read_else` and then calls the hook for the `else`
event. -/
theorem dispatch_else {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_ELSE v =
      CoreVisitor.run (code.read_else st) (fun v s a => invoke visitor v (.op s (.else_ (Control.signature a)))) v := by
  simpa only [invoke] using OpDispatch.dispatch_else visitor st data env ctx v

/-- `code.step` on `code.OP_END` runs `code.read_end` and then calls the hook for the `end` event. -/
theorem dispatch_end {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_END v =
      CoreVisitor.run (code.read_end st) (fun v s arg => invoke visitor v (.op s (.end_ arg.1 (Control.signature arg.2)))) v := by
  simpa only [invoke] using OpDispatch.dispatch_end visitor st data env ctx v

/-- `code.step` on `code.OP_BR` runs `code.read_br` and then calls the hook for the `br` event. -/
theorem dispatch_br {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_BR v =
      CoreVisitor.run (code.read_br st data) (fun v s arg => invoke visitor v (.op s (.br arg.1 (Control.resultView arg.2)))) v := by
  simpa only [invoke] using OpDispatch.dispatch_br visitor st data env ctx v

/-- `code.step` on `code.OP_BR_IF` runs `code.read_br_if` and then calls the hook for the `br_if`
event. -/
theorem dispatch_br_if {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_BR_IF v =
      CoreVisitor.run (code.read_br_if st data) (fun v s arg => invoke visitor v (.op s (.br_if arg.1 (Control.resultView arg.2)))) v := by
  simpa only [invoke] using OpDispatch.dispatch_br_if visitor st data env ctx v

/-- `code.step` on `code.OP_RETURN` runs `code.read_return` and then calls the hook for the `return`
event. -/
theorem dispatch_return {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_RETURN v =
      CoreVisitor.run (code.read_return st ctx) (fun v s _ => invoke visitor v (.op s .return_)) v := by
  simpa only [invoke] using OpDispatch.dispatch_return visitor st data env ctx v

end Itasca.VisitorTrace
