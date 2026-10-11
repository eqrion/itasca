import Itasca.Body.Stack
import Itasca.Body.ScalarMatch

open Aeneas Aeneas.Std

namespace Itasca

/-- Conversions, unary operations, and tests replace one concrete operand. -/
@[step]
theorem code.read_conversion.concrete (st : code.OpIterState)
    (pre : List code.StackType) (input output : types.ValueType)
    (hvals : st.vals.val = pre ++ [.Val input])
    (hbase : (Control.base st).val ≤ pre.length) :
    code.read_conversion st input output ⦃ r =>
      r.1 = .Ok () ∧ r.2.vals.val = pre ++ [.Val output] ∧
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ⦄ := by
  have hbound := st.vals.property
  unfold code.read_conversion
  step with code.pop_with_type.concrete st pre input hvals hbase
  simp only [r_post, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step*

/-- Binary operations and comparisons consume two operands and push their result type. -/
@[step]
theorem code.read_binary.concrete (st : code.OpIterState)
    (pre : List code.StackType) (input output : types.ValueType)
    (hvals : st.vals.val = pre ++ [.Val input, .Val input])
    (hbase : (Control.base st).val ≤ pre.length) :
    code.read_binary st input output ⦃ r =>
      r.1 = .Ok () ∧ r.2.vals.val = pre ++ [.Val output] ∧
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ⦄ := by
  have hbound := st.vals.property
  have hv : st.vals.val = (pre ++ [.Val input]) ++ [.Val input] := by
    simpa only [List.append_assoc, List.singleton_append] using hvals
  have hb : (Control.base st).val ≤ (pre ++ [code.StackType.Val input]).length := by
    simp only [List.length_append, List.length_singleton]
    omega
  unfold code.read_binary
  step with code.pop_with_type.concrete st _ input hv hb
  simp only [r_post, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have hb1 : (Control.base st1).val ≤ pre.length := by
    simpa [Control.base, r_post2] using hbase
  step with code.pop_with_type.concrete st1 pre input r_post1 hb1
  simp only [r1_post, bind_ok]
  step*

/-- A unary operation at an unreachable frame base still pushes its concrete result. -/
@[step]
theorem code.read_conversion.polymorphic (st : code.OpIterState)
    (input output : types.ValueType)
    (hbase : alloc.vec.Vec.len st.vals = Control.base st)
    (hpoly : Control.polymorphic st = true)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_conversion st input output ⦃ r =>
      r.1 = .Ok () ∧ r.2.vals.val = st.vals.val ++ [.Val output] ∧
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ⦄ := by
  simp only [code.read_conversion, code.pop_with_type.polymorphic st input hbase hpoly,
    bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  step*

/-- Both binary inputs may be supplied by the same unreachable frame base. -/
@[step]
theorem code.read_binary.polymorphic (st : code.OpIterState)
    (input output : types.ValueType)
    (hbase : alloc.vec.Vec.len st.vals = Control.base st)
    (hpoly : Control.polymorphic st = true)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_binary st input output ⦃ r =>
      r.1 = .Ok () ∧ r.2.vals.val = st.vals.val ++ [.Val output] ∧
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ⦄ := by
  obtain ⟨st', hr, hv, hc, hp⟩ :=
    WP.spec_imp_exists (code.push_val.spec st (.Val output) hsize)
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok (), st'), ?_, rfl, hv, hc, hp⟩
  simp [code.read_binary, code.pop_with_type.polymorphic st input hbase hpoly,
    core.result.Result.Insts.CoreOpsTry.branch, hr]

private theorem i32_add_conversion : code.convert_types code.OP_I32_ADD = .ok none := by
  simp [global_simps]

private theorem i32_add_binary :
    code.binary_types code.OP_I32_ADD = .ok (some (.I32, .I32)) := by
  simp [global_simps]

private theorem i32_add_visit {V : Type} (visitor : code.OpVisitor V)
    (v : V) (st : code.OpIterState) :
    code.visit_numeric visitor v st code.OP_I32_ADD = visitor.on_i32_add v st := by
  simp [global_simps]

namespace Numeric

def i32Add : instr := .BINOP .I32 (.mk_binop__0 .I32 .ADD)

theorem i32Add_wf : wf_instr i32Add :=
  .instr_case_15 _ _ (.binop__case_0 _ _ _ rfl)

theorem i32Add_typed (C : context) (hC : wf_context C) :
    Instr_ok C i32Add (.mk_functype (.mk_list [.I32, .I32]) (.mk_list [.I32])) :=
  .binop C _ _ hC i32Add_wf

end Numeric

/-- Concrete i32.add validation calls the corresponding hook with the updated stack. -/
theorem code.step_numeric.i32_add {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (pre : List code.StackType) (v v' : V)
    (hvals : st.vals.val = pre ++ [.Val .I32, .Val .I32])
    (hbase : (Control.base st).val ≤ pre.length)
    (hvisit : ∀ st', st'.vals.val = pre ++ [.Val .I32] →
      st'.ctrls = st.ctrls → st'.pos = st.pos →
      visitor.on_i32_add v st' = .ok (.Ok (), v')) :
    ∃ st', code.step_numeric visitor st code.OP_I32_ADD v = .ok (.Ok (), st', v') ∧
      st'.vals.val = pre ++ [.Val .I32] ∧ st'.ctrls = st.ctrls ∧ st'.pos = st.pos := by
  obtain ⟨⟨res, st'⟩, hr, hok, hv, hc, hp⟩ :=
    WP.spec_imp_exists (code.read_binary.concrete st pre .I32 .I32 hvals hbase)
  dsimp only at hok hv hc hp
  rw [hok] at hr
  refine ⟨st', ?_, hv, hc, hp⟩
  simp [code.step_numeric, hr,
    core.result.Result.Insts.CoreOpsTry.branch, hvisit st' hv hc hp, code.visit]

private theorem i32_add_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_I32_ADD v =
      code.step_numeric visitor st code.OP_I32_ADD v := by
  simp [global_simps]

/-- The full instruction dispatcher validates i32.add with SpecTec's numeric stack effect. -/
theorem code.step_i32_add_typed {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (pre : List code.StackType) (v v' : V)
    (C : context) (hC : wf_context C)
    (hvals : st.vals.val = pre ++ [.Val .I32, .Val .I32])
    (hbase : (Control.base st).val ≤ pre.length)
    (hvisit : ∀ st', st'.vals.val = pre ++ [.Val .I32] →
      st'.ctrls = st.ctrls → st'.pos = st.pos →
      visitor.on_i32_add v st' = .ok (.Ok (), v')) :
    ∃ st', code.step visitor st data env ctx code.OP_I32_ADD v = .ok (.Ok (), st', v') ∧
      st'.vals.val = pre ++ [.Val .I32] ∧ st'.ctrls = st.ctrls ∧ st'.pos = st.pos ∧
      Instr_ok C Numeric.i32Add (.mk_functype (.mk_list [.I32, .I32]) (.mk_list [.I32])) := by
  obtain ⟨st', hr, hv, hc, hp⟩ := code.step_numeric.i32_add visitor st pre v v' hvals hbase hvisit
  exact ⟨st', (i32_add_dispatch visitor st data env ctx v).trans hr,
    hv, hc, hp, Numeric.i32Add_typed C hC⟩

end Itasca
