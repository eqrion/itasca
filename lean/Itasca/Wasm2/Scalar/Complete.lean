import Itasca.Wasm2.Step.ScalarContext
import Itasca.Wasm1.Complete.Scalar
import Itasca.Wasm1.Complete.Env

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Every independently encoded scalar instruction accepts its principal
SpecTec typing. This imposes neither a Wasm 1.0 environment restriction nor a
restriction on the active frame's input or output arity. -/
theorem scalar_complete (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (C : context) (st : code.OpIterState) (f : Completeness.Frame st) (opcode : U8)
    (op : instr) (bytes : List U8) (next : Usize) (front input output : List valtype)
    (hc : EnvTranslation.Matches env ctx C) (hsize : st.vals.val.length < Usize.max)
    (hscalar : opcode.val ∉ controlOpcodes)
    (hi : Wasm1.Immediate opcode (.plain op) bytes) (hb : Wasm1.BytesAt data st.pos bytes next)
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ input))
    (ht : Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output))) :
    Completeness.StepResult f data env ctx opcode next (front ++ output) := by
  cases hi with
  | unreachable => exact Completeness.unreachable f hb ht
  | nop => exact Completeness.nop f hb ht hr
  | br | brIf | brTable | return_ | call | callIndirect =>
      simp [controlOpcodes] at hscalar
  | drop => exact f.step_drop data env ctx next C front input output hb ht hr
  | select => exact f.step_select data env ctx next C front input output hb hsize ht hr
  | localGet idx he => exact Completeness.localGet f data env ctx C hc idx _ next he hb front input output ht hr hsize
  | localSet idx he => exact Completeness.localSet f data env ctx C hc idx _ next he hb front input output ht hr
  | localTee idx he => exact Completeness.localTee f data env ctx C hc idx _ next he hb front input output ht hr hsize
  | globalGet idx he => exact Completeness.globalGet f data env ctx C hc idx _ next he hb front input output ht hr hsize
  | globalSet idx he => exact Completeness.globalSet f data env ctx C hc idx _ next he hb front input output ht hr
  | memory opcode operation arg hmap ha ho =>
      exact Completeness.memory f data env ctx C hc opcode operation hmap arg _ _ next ha ho hb
        front input output ht hr hsize
  | memorySize => exact Completeness.memorySize f data env ctx C hc next hb front input output ht hr hsize
  | memoryGrow => exact Completeness.memoryGrow f data env ctx C hc next hb front input output ht hr hsize
  | i32Const value he => exact f.step_i32Const data env ctx value _ next C front input output he hb hsize ht hr
  | i64Const value he => exact f.step_i64Const data env ctx value _ next C front input output he hb hsize ht hr
  | f32Const value he => exact f.step_f32Const data env ctx value _ next C front input output he hb hsize ht hr
  | f64Const value he => exact f.step_f64Const data env ctx value _ next C front input output he hb hsize ht hr
  | numeric opcode operation hmap =>
      exact f.step_numeric data env ctx opcode operation next C front input output hmap hb hsize ht hr

end Itasca.Wasm2
