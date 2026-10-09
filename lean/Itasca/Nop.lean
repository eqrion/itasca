import Itasca.ScalarMatch
import Itasca.SpecChecks
import Itasca.ReadByte

open Aeneas Aeneas.Std

namespace Itasca

/-- NOP preserves validator state and threads an accepting visitor's state. -/
theorem code.step_nop {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (v v' : V)
    (hvisit : visitor.on_nop v st = .ok (.Ok (), v')) :
    code.step visitor st data env ctx code.OP_NOP v = .ok (.Ok (), st, v') := by
  simp only [global_simps]
  simp [hvisit, code.visit, core.result.Result.Insts.CoreOpsTry.branch]

/-- A visitor's rejection remains a validation error and preserves validator state. -/
theorem code.step_nop_rejected {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (v v' : V) (e : error.VisitError)
    (hvisit : visitor.on_nop v st = .ok (.Err e, v')) :
    code.step visitor st data env ctx code.OP_NOP v = .ok (.Err (.Visitor e), st, v') := by
  simp only [global_simps]
  simp [hvisit, code.visit, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- The successful NOP step has the generated specification's empty stack effect. -/
theorem code.step_nop_typed {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (v v' : V) (C : context) (hC : wf_context C)
    (hvisit : visitor.on_nop v st = .ok (.Ok (), v')) :
    code.step visitor st data env ctx code.OP_NOP v = .ok (.Ok (), st, v') ∧
      Instr_ok C instr.NOP (.mk_functype (.mk_list []) (.mk_list [])) :=
  ⟨code.step_nop visitor st data env ctx v v' hvisit, SpecChecks.nop_typed C hC⟩

/-- Decode byte 0x01, advance the cursor, and perform the specification's NOP step.
The visitor may change its own state; the value and control stacks are preserved. -/
theorem code.read_and_step_nop {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (v v' : V) (C : context) (hC : wf_context C)
    (h : st.pos.val < data.length) (hbyte : data.val[st.pos.val] = 1#u8)
    (hvisit : ∀ st', visitor.on_nop v st' = .ok (.Ok (), v')) :
    ∃ next, code.read_op st data = .ok (.Ok code.OP_NOP, { st with pos := next }) ∧
      next.val = st.pos.val + 1 ∧
      code.step visitor { st with pos := next } data env ctx code.OP_NOP v =
        .ok (.Ok (), { st with pos := next }, v') ∧
      Instr_ok C instr.NOP (.mk_functype (.mk_list []) (.mk_list [])) := by
  obtain ⟨next, hread, hnext⟩ := code.read_op_success st data h
  refine ⟨next, ?_, hnext, code.step_nop_typed visitor _ data env ctx v v' C hC (hvisit _)⟩
  simpa only [hbyte, code.OP_NOP] using hread

end Itasca
