import Itasca.MultiValue.ScalarTotal
import Itasca.Body.CompletenessStep

open Aeneas Aeneas.Std

namespace Itasca.MultiValue

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Shared scalar dispatch observes local types but never function results. -/
theorem scalar_context {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ctx ctx' : code.Context) (opcode : U8) (v : V)
    (hscalar : opcode.val ∉ controlOpcodes) (hlocals : ctx.locals = ctx'.locals) :
    code.step visitor st data env ctx opcode v =
      code.step visitor st data env ctx' opcode v := by
  obtain ⟨⟨n, hn⟩⟩ := opcode
  change n < 256 at hn
  change n ∉ controlOpcodes at hscalar
  simp only [controlOpcodes, List.mem_cons, not_or] at hscalar
  interval_cases n <;> try simp_all
  all_goals try simp only [code.step, global_simps]
  all_goals try (first | rfl | simp [code.read_local_get, code.read_local_set, code.read_local_tee,
    code.take_local, code.local_type, hlocals])

/-- Every independently encoded scalar instruction accepts its principal
SpecTec typing. This imposes neither a Wasm 1.0 environment restriction nor a
restriction on the active frame's input or output arity. -/
theorem scalar_complete (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (C : context) (st : code.OpIterState) (f : Completeness.Frame st) (opcode : U8)
    (op : instr) (bytes : List U8) (next : Usize) (front input output : List valtype)
    (hc : EnvTranslation.Matches env ctx C) (hsize : st.vals.val.length < Usize.max)
    (hscalar : opcode.val ∉ controlOpcodes)
    (hi : Wasm.Immediate opcode (.plain op) bytes) (hb : Wasm.BytesAt data st.pos bytes next)
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
      exact Completeness.memory_contract data env ctx C st f opcode operation arg _ _ next front input output
        hc hsize hmap ha ho hb hr ht
  | memorySize => exact Completeness.memorySize f data env ctx C hc next hb front input output ht hr hsize
  | memoryGrow => exact Completeness.memoryGrow f data env ctx C hc next hb front input output ht hr hsize
  | i32Const value he => exact f.step_i32Const data env ctx value _ next C front input output he hb hsize ht hr
  | i64Const value he => exact f.step_i64Const data env ctx value _ next C front input output he hb hsize ht hr
  | f32Const value he => exact f.step_f32Const data env ctx value _ next C front input output he hb hsize ht hr
  | f64Const value he => exact f.step_f64Const data env ctx value _ next C front input output he hb hsize ht hr
  | numeric opcode operation hmap =>
      exact f.step_numeric data env ctx opcode operation next C front input output hmap hb hsize ht hr

end Itasca.MultiValue
