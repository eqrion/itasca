import Itasca.Wasm1.Complete.Frame
import Itasca.Handler.ScalarComplete
import Itasca.Visitor.StepErasure
import Itasca.Visitor.Basic

open Aeneas Aeneas.Std

namespace Itasca.Numeric

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The principal generated typing of a mapped numeric opcode has exactly its independent effect. -/
theorem signature (opcode : U8) (op : Operation) (hmap : NumericOp opcode op)
    (C : context) (ins outs : List valtype)
    (ht : Instr_ok C op.instruction (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = op.inputs.map Translate.valueType ∧ outs = [Translate.valueType op.output] := by
  unfold NumericOp opcodeMeaning at hmap
  split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap <;> try contradiction
  all_goals subst op
  all_goals cases ht; simp [Operation.inputs, unary, binary, test, relation, conversion, valueType,
    Translate.valueType, valtype_numtype]

end Itasca.Numeric

namespace Itasca.Wasm1.Completeness

private theorem same_ctrls {st} (f : Frame st) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (opcode : U8) (next : Usize) (out : List valtype)
    (s : code.OpIterState) (after : List code.StackType)
    (hs : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data env ctx opcode () =
      .ok (.Ok (), s, ()))
    (hp : s.pos = next) (hc : s.ctrls = st.ctrls) (hv : s.vals.val = f.outer ++ after)
    (hl : after.length ≤ f.operands.length + 1)
    (ht : Sequence.Realizes (Control.polymorphic st) after out) :
    StepResult f data env ctx opcode next out := by
  refine ⟨s, hs, hp, f.output_of_same_ctrls hc hv ht, ?_⟩
  simp only [hv, f.vals, List.length_append]
  omega

/-- Numeric dispatch accepts its generated principal typing on the represented stack. -/
theorem Frame.step_numeric {st} (f : Frame st) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (opcode : U8) (op : Numeric.Operation) (next : Usize)
    (C : context) (front ins outs : List valtype)
    (hmap : Numeric.NumericOp opcode op) (hb : Wasm1.BytesAt data st.pos [] next)
    (hsize : st.vals.val.length < Usize.max)
    (ht : Instr_ok C op.instruction (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins)) :
    StepResult f data env ctx opcode next (front ++ outs) := by
  obtain ⟨rfl, rfl⟩ := Numeric.signature opcode op hmap C ins outs ht
  obtain ⟨s, after, hs, hc, hp, hv, hl, hout⟩ := Numeric.read.complete op st f.outer f.operands front
    f.vals f.base_eq hsize (by simpa [f.poly_eq] using hr)
  apply same_ctrls f data env ctx opcode next _ s after _ (hp.trans hb.empty.symm) hc hv hl hout
  rw [code.step.numeric_dispatch _ _ _ _ _ _ _ hmap.bounds.1,
    code.step_numeric.dispatch _ _ _ _ _ hmap]
  simp [CoreVisitor.run, hs, VisitorErasure.visit_numeric_empty, code.visit,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- Drop consumes the type supplied by its principal typing rule. -/
theorem Frame.step_drop {st} (f : Frame st) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (next : Usize) (C : context) (front ins outs : List valtype)
    (hb : Wasm1.BytesAt data st.pos [] next)
    (ht : Instr_ok C .DROP (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins)) :
    StepResult f data env ctx 0x1A#u8 next (front ++ outs) := by
  cases ht with
  | drop _ t _ _ =>
      obtain ⟨value, s, after, hs, hc, hp, hv, hl, _, hout⟩ :=
        code.read_drop.complete st f.outer f.operands front t f.vals f.base_eq
          (by simpa [f.poly_eq] using hr)
      apply same_ctrls f data env ctx 0x1A#u8 next _ s after _ (hp.trans hb.empty.symm) hc hv
        (by omega) (by simpa using hout)
      simp [global_simps, hs, code.OpVisitor.on_drop.default, code.visit,
        core.result.Result.Insts.CoreOpsTry.branch]

/-- Implicit select retains the common principal operand interpretation. -/
theorem Frame.step_select {st} (f : Frame st) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (next : Usize) (C : context) (front ins outs : List valtype)
    (hb : Wasm1.BytesAt data st.pos [] next) (hsize : st.vals.val.length < Usize.max)
    (ht : Instr_ok C (.SELECT none) (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins)) :
    StepResult f data env ctx 0x1B#u8 next (front ++ outs) := by
  cases ht with
  | select_impl _ t _ _ _ hsub htype _ _ =>
      obtain ⟨hfun, hext⟩ := StackSemantics.select_type_not_reference hsub htype
      obtain ⟨value, s, after, hs, hc, hp, hv, hl, _, hout⟩ :=
        code.read_select.complete st f.outer f.operands front t f.vals f.base_eq hsize hfun hext
          (by simpa [f.poly_eq] using hr)
      apply same_ctrls f data env ctx 0x1B#u8 next _ s after _ (hp.trans hb.empty.symm) hc hv hl hout
      simp [hs, code.OpVisitor.on_select.default, code.visit, core.result.Result.Insts.CoreOpsTry.branch]

/-- Exact scalar bytes and principal typing force successful constant dispatch. -/
theorem Frame.step_i32Const {st} (f : Frame st) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (value : I32) (bytes : List U8) (next : Usize)
    (C : context) (front ins outs : List valtype)
    (he : SignedLeb32.Encoding bytes value.val) (hbytes : Wasm1.BytesAt data st.pos bytes next)
    (hsize : st.vals.val.length < Usize.max)
    (ht : Instr_ok C (Spec.i32Const value) (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins)) :
    StepResult f data env ctx 0x41#u8 next (front ++ outs) := by
  have heffect : ins = [] ∧ outs = [.I32] := by cases ht; exact ⟨rfl, rfl⟩
  rcases heffect with ⟨rfl, rfl⟩
  obtain ⟨s, after, hs, hc, hp, hv, hl, hout⟩ :=
    code.read_i32_const.complete st data value next f.outer f.operands front
      ⟨bytes, hbytes.suffix, hbytes.length, hbytes.bound, he⟩ f.vals hsize
      (by simpa [f.poly_eq] using hr)
  apply same_ctrls f data env ctx 0x41#u8 next _ s after _ hp hc hv (by omega) hout
  simp [global_simps, hs, code.OpVisitor.on_i32_const.default, code.visit,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- Exact scalar bytes and principal typing force successful constant dispatch. -/
theorem Frame.step_i64Const {st} (f : Frame st) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (value : I64) (bytes : List U8) (next : Usize)
    (C : context) (front ins outs : List valtype)
    (he : SignedLeb64.Encoding bytes value.val) (hbytes : Wasm1.BytesAt data st.pos bytes next)
    (hsize : st.vals.val.length < Usize.max)
    (ht : Instr_ok C (ScalarConst.i64 value) (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins)) :
    StepResult f data env ctx 0x42#u8 next (front ++ outs) := by
  have heffect : ins = [] ∧ outs = [.I64] := by cases ht; exact ⟨rfl, rfl⟩
  rcases heffect with ⟨rfl, rfl⟩
  obtain ⟨s, after, hs, hc, hp, hv, hl, hout⟩ :=
    code.read_i64_const.complete st data value next f.outer f.operands front
      ⟨bytes, hbytes.suffix, hbytes.length, hbytes.bound, he⟩ f.vals hsize
      (by simpa [f.poly_eq] using hr)
  apply same_ctrls f data env ctx 0x42#u8 next _ s after _ hp hc hv (by omega) hout
  simp [global_simps, hs, code.OpVisitor.on_i64_const.default, code.visit,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- Exact scalar bytes and principal typing force successful constant dispatch. -/
theorem Frame.step_f32Const {st} (f : Frame st) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (value : U32) (bytes : List U8) (next : Usize)
    (C : context) (front ins outs : List valtype)
    (he : FloatBits.Encoding 4 bytes value.val) (hbytes : Wasm1.BytesAt data st.pos bytes next)
    (hsize : st.vals.val.length < Usize.max)
    (ht : Instr_ok C (ScalarConst.f32 value) (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins)) :
    StepResult f data env ctx 0x43#u8 next (front ++ outs) := by
  have heffect : ins = [] ∧ outs = [.F32] := by cases ht; exact ⟨rfl, rfl⟩
  rcases heffect with ⟨rfl, rfl⟩
  obtain ⟨s, after, hs, hc, hp, hv, hl, hout⟩ :=
    code.read_f32_const.complete st data value next f.outer f.operands front
      ⟨bytes, hbytes.suffix, by simpa [he.1] using hbytes.length, hbytes.bound, he⟩ f.vals hsize
      (by simpa [f.poly_eq] using hr)
  apply same_ctrls f data env ctx 0x43#u8 next _ s after _ hp hc hv (by omega) hout
  simp [global_simps, hs, code.OpVisitor.on_f32_const.default, code.visit,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- Exact scalar bytes and principal typing force successful constant dispatch. -/
theorem Frame.step_f64Const {st} (f : Frame st) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (value : U64) (bytes : List U8) (next : Usize)
    (C : context) (front ins outs : List valtype)
    (he : FloatBits.Encoding 8 bytes value.val) (hbytes : Wasm1.BytesAt data st.pos bytes next)
    (hsize : st.vals.val.length < Usize.max)
    (ht : Instr_ok C (ScalarConst.f64 value) (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins)) :
    StepResult f data env ctx 0x44#u8 next (front ++ outs) := by
  have heffect : ins = [] ∧ outs = [.F64] := by cases ht; exact ⟨rfl, rfl⟩
  rcases heffect with ⟨rfl, rfl⟩
  obtain ⟨s, after, hs, hc, hp, hv, hl, hout⟩ :=
    code.read_f64_const.complete st data value next f.outer f.operands front
      ⟨bytes, hbytes.suffix, by simpa [he.1] using hbytes.length, hbytes.bound, he⟩ f.vals hsize
      (by simpa [f.poly_eq] using hr)
  apply same_ctrls f data env ctx 0x44#u8 next _ s after _ hp hc hv (by omega) hout
  simp [global_simps, hs, code.OpVisitor.on_f64_const.default, code.visit,
    core.result.Result.Insts.CoreOpsTry.branch]

end Itasca.Wasm1.Completeness

open Aeneas Aeneas.Std

namespace Itasca.Wasm1.Completeness

theorem nop {st data env ctx C next front ins outs}
    (f : Frame st) (hb : Wasm1.BytesAt data st.pos [] next)
    (hop : Instr_ok C .NOP (.mk_functype (.mk_list ins) (.mk_list outs)))
    (ht : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins)) :
    StepResult f data env ctx 0x01#u8 next (front ++ outs) := by
  cases hop
  have he : next = st.pos := hb.empty
  subst next
  refine ⟨st, ?_, rfl, f.output_self ht, by omega⟩
  simp [global_simps, code.OpVisitor.on_nop.default, code.visit,
    core.result.Result.Insts.CoreOpsTry.branch]

theorem unreachable {st data env ctx C next front ins outs}
    (f : Frame st) (hb : Wasm1.BytesAt data st.pos [] next)
    (_hop : Instr_ok C .UNREACHABLE (.mk_functype (.mk_list ins) (.mk_list outs))) :
    StepResult f data env ctx 0x00#u8 next (front ++ outs) := by
  have he : next = st.pos := hb.empty
  subst next
  obtain ⟨s, hr, hv, _, hc, hp⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec st f.parents f.current f.ctrls
      (by simp [f.base, f.vals]))
  have hv' : s.vals.val = f.outer := by simpa [f.vals, f.base] using hv
  refine ⟨s, ?_, hp, ⟨true, [], hc, by simpa using hv',
    Sequence.realizes_polymorphic_empty _⟩, ?_⟩
  · simp [global_simps, code.read_unreachable, hr,
      code.OpVisitor.on_unreachable.default, code.visit,
      core.result.Result.Insts.CoreOpsTry.branch]
  · simp only [hv', f.vals, List.length_append]
    omega

end Itasca.Wasm1.Completeness
