import Itasca.SignedConst
import Itasca.SignedLeb64
import Itasca.FloatBits
import Itasca.CoreVisitor

open Aeneas Aeneas.Std

namespace Itasca.ScalarConst

/-- An I64 is represented in SpecTec by its unsigned 64-bit bit pattern. -/
def i64 (value : I64) : instr :=
  .CONST .I64 (.mk_num__0 .I64 (.mk_uN (value.val % 18446744073709551616).toNat))

theorem i64_wf (value : I64) : wf_instr (i64 value) := by
  apply wf_instr.instr_case_13
  apply wf_num_.num__case_0 _ .I64 _ (by decide) _ rfl
  apply wf_uN.uN_case_0
  have hmod := Int.emod_lt_of_pos value.val (by decide : (0 : Int) < 18446744073709551616)
  have hnonneg := Int.emod_nonneg value.val (by decide : (18446744073709551616 : Int) ≠ 0)
  norm_num [size, valtype_Inn] at hmod hnonneg ⊢
  omega

/-- IEEE fields are translated directly, preserving the sign of zero and NaN payloads. -/
def floatValue (fractionBits exponentBits bits : Nat) : fN :=
  let fraction := bits % 2 ^ fractionBits
  let exponent := bits / 2 ^ fractionBits % 2 ^ exponentBits
  let magnitude :=
    if exponent = 0 then fNmag.SUBNORM fraction
    else if exponent = 2 ^ exponentBits - 1 then
      if fraction = 0 then fNmag.INF else fNmag.NAN fraction
    else fNmag.NORM fraction ((exponent : Int) - (2 ^ (exponentBits - 1) - 1 : Nat))
  if bits < 2 ^ (fractionBits + exponentBits) then .POS magnitude else .NEG magnitude

def f32 (bits : U32) : instr := .CONST .F32 (.mk_num__1 .F32 (floatValue 23 8 bits.val))
def f64 (bits : U64) : instr := .CONST .F64 (.mk_num__1 .F64 (floatValue 52 11 bits.val))

theorem floatValue_wf32 (bits : Nat) : wf_fN 32 (floatValue 23 8 bits) := by
  have hm : bits % 2 ^ 23 < 2 ^ 23 := Nat.mod_lt _ (by decide)
  have he : bits / 2 ^ 23 % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by decide)
  have hmag : wf_fNmag 32
      (if bits / 2 ^ 23 % 2 ^ 8 = 0 then .SUBNORM (bits % 2 ^ 23)
       else if bits / 2 ^ 23 % 2 ^ 8 = 2 ^ 8 - 1 then
         if bits % 2 ^ 23 = 0 then .INF else .NAN (bits % 2 ^ 23)
       else .NORM (bits % 2 ^ 23) ((bits / 2 ^ 23 % 2 ^ 8 : Nat) - (2 ^ (8 - 1) - 1 : Nat) : Int)) := by
    generalize hmdef : bits % 2 ^ 23 = fraction at *
    generalize hedef : bits / 2 ^ 23 % 2 ^ 8 = exponent at *
    split
    · apply wf_fNmag.fNmag_case_1 32 (2 - 2 ^ (8 - 1))
      exact ⟨hm, by decide⟩
    · split
      · split
        · exact .fNmag_case_2 _
        · apply wf_fNmag.fNmag_case_3
          exact ⟨Nat.one_le_iff_ne_zero.mpr (by assumption), hm⟩
      · apply wf_fNmag.fNmag_case_0
        refine ⟨hm, ?_, ?_⟩ <;> norm_num [E, expon, Int.toNat] at * <;> omega
  unfold floatValue
  split
  · exact .fN_case_0 _ _ hmag
  · exact .fN_case_1 _ _ hmag

theorem f32_wf (bits : U32) : wf_instr (f32 bits) := by
  apply wf_instr.instr_case_13
  exact wf_num_.num__case_1 _ .F32 _ (floatValue_wf32 bits.val) rfl

theorem floatValue_wf64 (bits : Nat) : wf_fN 64 (floatValue 52 11 bits) := by
  have hm : bits % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have he : bits / 2 ^ 52 % 2 ^ 11 < 2 ^ 11 := Nat.mod_lt _ (by decide)
  have hmag : wf_fNmag 64
      (if bits / 2 ^ 52 % 2 ^ 11 = 0 then .SUBNORM (bits % 2 ^ 52)
       else if bits / 2 ^ 52 % 2 ^ 11 = 2 ^ 11 - 1 then
         if bits % 2 ^ 52 = 0 then .INF else .NAN (bits % 2 ^ 52)
       else .NORM (bits % 2 ^ 52) ((bits / 2 ^ 52 % 2 ^ 11 : Nat) - (2 ^ (11 - 1) - 1 : Nat) : Int)) := by
    generalize hmdef : bits % 2 ^ 52 = fraction at *
    generalize hedef : bits / 2 ^ 52 % 2 ^ 11 = exponent at *
    split
    · apply wf_fNmag.fNmag_case_1 64 (2 - 2 ^ (11 - 1))
      exact ⟨hm, by decide⟩
    · split
      · split
        · exact .fNmag_case_2 _
        · apply wf_fNmag.fNmag_case_3
          exact ⟨Nat.one_le_iff_ne_zero.mpr (by assumption), hm⟩
      · apply wf_fNmag.fNmag_case_0
        refine ⟨hm, ?_, ?_⟩ <;> norm_num [E, expon, Int.toNat] at * <;> omega
  unfold floatValue
  split
  · exact .fN_case_0 _ _ hmag
  · exact .fN_case_1 _ _ hmag

theorem f64_wf (bits : U64) : wf_instr (f64 bits) := by
  apply wf_instr.instr_case_13
  exact wf_num_.num__case_1 _ .F64 _ (floatValue_wf64 bits.val) rfl

end Itasca.ScalarConst

namespace Itasca.ScalarConst

theorem i64_typed (C : context) (hC : wf_context C) (value : I64) :
    Instr_ok C (i64 value) (.mk_functype (.mk_list []) (.mk_list [.I64])) :=
  .const C .I64 _ hC (i64_wf value)

theorem i64_framed (C : context) (hC : wf_context C) (value : I64) (ts : List valtype) :
    Instrs_ok C [i64 value] (.mk_functype (.mk_list ts) (.mk_list (ts ++ [.I64]))) := by
  simpa using Instrs_ok.frame C [i64 value] ts [] [.I64]
    (.instr C _ [] [.I64] (i64_typed C hC value) hC (i64_wf value))
    hC (by simpa [Forall] using i64_wf value)

theorem f32_typed (C : context) (hC : wf_context C) (value : U32) :
    Instr_ok C (f32 value) (.mk_functype (.mk_list []) (.mk_list [.F32])) :=
  .const C .F32 _ hC (f32_wf value)

theorem f32_framed (C : context) (hC : wf_context C) (value : U32) (ts : List valtype) :
    Instrs_ok C [f32 value] (.mk_functype (.mk_list ts) (.mk_list (ts ++ [.F32]))) := by
  simpa using Instrs_ok.frame C [f32 value] ts [] [.F32]
    (.instr C _ [] [.F32] (f32_typed C hC value) hC (f32_wf value))
    hC (by simpa [Forall] using f32_wf value)

theorem f64_typed (C : context) (hC : wf_context C) (value : U64) :
    Instr_ok C (f64 value) (.mk_functype (.mk_list []) (.mk_list [.F64])) :=
  .const C .F64 _ hC (f64_wf value)

theorem f64_framed (C : context) (hC : wf_context C) (value : U64) (ts : List valtype) :
    Instrs_ok C [f64 value] (.mk_functype (.mk_list ts) (.mk_list (ts ++ [.F64]))) := by
  simpa using Instrs_ok.frame C [f64 value] ts [] [.F64]
    (.instr C _ [] [.F64] (f64_typed C hC value) hC (f64_wf value))
    hC (by simpa [Forall] using f64_wf value)

end Itasca.ScalarConst

namespace Itasca
/-- A successfully decoded constant advances the cursor and appends one I64 operand. -/
@[step]
theorem code.read_i64_const.from_read (st : code.OpIterState) (data : Slice U8)
    (value : I64) (next : Usize)
    (hread : reader.read_s64_leb data st.pos = .ok (.Ok (value, next)))
    (hsize : st.vals.val.length < Usize.max) :
    code.read_i64_const st data ⦃ r => r.1 = .Ok value ∧
      r.2.vals.val = st.vals.val ++ [.Val .I64] ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = next ⦄ := by
  rw [code.read_i64_const, hread]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step*

/-- A malformed constant leaves the entire validator state unchanged. -/
theorem code.read_i64_const.failed_read (st : code.OpIterState) (data : Slice U8)
    (e : error.OpError) (hread : reader.read_s64_leb data st.pos = .ok (.Err e)) :
    code.read_i64_const st data = .ok (.Err e, st) := by
  simp [code.read_i64_const, hread, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Total constant decoding under the single push's capacity bound. -/
@[step]
theorem code.read_i64_const.spec (st : code.OpIterState) (data : Slice U8)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_i64_const st data ⦃ r => r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok value => SignedLeb64.Decoded data st.pos value.val r.2.pos ∧
          r.2.vals.val = st.vals.val ++ [.Val .I64]
      | .Err e => SignedLeb64.Rejected data st.pos e ∧ r.2 = st ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_s64_leb.spec data st.pos)
  cases r with
  | Err e =>
    rw [code.read_i64_const.failed_read st data e hr]
    simp only [WP.spec_ok]
    exact ⟨trivial, hp, trivial⟩
  | Ok r =>
    rcases r with ⟨value, next⟩
    obtain ⟨r, hresult, hok, hv, hc, hpos⟩ := WP.spec_imp_exists
      (code.read_i64_const.from_read st data value next hr hsize)
    rw [hresult]
    simp only [WP.spec_ok, hok, hpos]
    exact ⟨hc, hp, hv⟩

/-- A successfully decoded constant advances the cursor and appends one F32 operand. -/
@[step]
theorem code.read_f32_const.from_read (st : code.OpIterState) (data : Slice U8)
    (value : U32) (next : Usize)
    (hread : reader.read_f32_bits data st.pos = .ok (.Ok (value, next)))
    (hsize : st.vals.val.length < Usize.max) :
    code.read_f32_const st data ⦃ r => r.1 = .Ok value ∧
      r.2.vals.val = st.vals.val ++ [.Val .F32] ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = next ⦄ := by
  rw [code.read_f32_const, hread]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step*

/-- A malformed constant leaves the entire validator state unchanged. -/
theorem code.read_f32_const.failed_read (st : code.OpIterState) (data : Slice U8)
    (e : error.OpError) (hread : reader.read_f32_bits data st.pos = .ok (.Err e)) :
    code.read_f32_const st data = .ok (.Err e, st) := by
  simp [code.read_f32_const, hread, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Total constant decoding under the single push's capacity bound. -/
@[step]
theorem code.read_f32_const.spec (st : code.OpIterState) (data : Slice U8)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_f32_const st data ⦃ r => r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok value => FloatBits.Decoded 4 data st.pos value.val r.2.pos ∧
          r.2.vals.val = st.vals.val ++ [.Val .F32]
      | .Err e => FloatBits.Rejected 4 data st.pos e ∧ r.2 = st ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_f32_bits.spec data st.pos)
  cases r with
  | Err e =>
    rw [code.read_f32_const.failed_read st data e hr]
    simp only [WP.spec_ok]
    exact ⟨trivial, hp, trivial⟩
  | Ok r =>
    rcases r with ⟨value, next⟩
    obtain ⟨r, hresult, hok, hv, hc, hpos⟩ := WP.spec_imp_exists
      (code.read_f32_const.from_read st data value next hr hsize)
    rw [hresult]
    simp only [WP.spec_ok, hok, hpos]
    exact ⟨hc, hp, hv⟩

/-- A successfully decoded constant advances the cursor and appends one F64 operand. -/
@[step]
theorem code.read_f64_const.from_read (st : code.OpIterState) (data : Slice U8)
    (value : U64) (next : Usize)
    (hread : reader.read_f64_bits data st.pos = .ok (.Ok (value, next)))
    (hsize : st.vals.val.length < Usize.max) :
    code.read_f64_const st data ⦃ r => r.1 = .Ok value ∧
      r.2.vals.val = st.vals.val ++ [.Val .F64] ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = next ⦄ := by
  rw [code.read_f64_const, hread]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step*

/-- A malformed constant leaves the entire validator state unchanged. -/
theorem code.read_f64_const.failed_read (st : code.OpIterState) (data : Slice U8)
    (e : error.OpError) (hread : reader.read_f64_bits data st.pos = .ok (.Err e)) :
    code.read_f64_const st data = .ok (.Err e, st) := by
  simp [code.read_f64_const, hread, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Total constant decoding under the single push's capacity bound. -/
@[step]
theorem code.read_f64_const.spec (st : code.OpIterState) (data : Slice U8)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_f64_const st data ⦃ r => r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok value => FloatBits.Decoded 8 data st.pos value.val r.2.pos ∧
          r.2.vals.val = st.vals.val ++ [.Val .F64]
      | .Err e => FloatBits.Rejected 8 data st.pos e ∧ r.2 = st ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_f64_bits.spec data st.pos)
  cases r with
  | Err e =>
    rw [code.read_f64_const.failed_read st data e hr]
    simp only [WP.spec_ok]
    exact ⟨trivial, hp, trivial⟩
  | Ok r =>
    rcases r with ⟨value, next⟩
    obtain ⟨r, hresult, hok, hv, hc, hpos⟩ := WP.spec_imp_exists
      (code.read_f64_const.from_read st data value next hr hsize)
    rw [hresult]
    simp only [WP.spec_ok, hok, hpos]
    exact ⟨hc, hp, hv⟩


end Itasca

namespace Itasca.Sequence

theorem TypedPrefix.i64Const {C : context} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C ops poly vals)
    (hC : wf_context C) (value : I64) :
    TypedPrefix C (ops ++ [ScalarConst.i64 value]) poly (vals ++ [.Val .I64]) := by
  apply h.append hC _ (ScalarConst.i64_wf value)
  intro out hout
  obtain ⟨before, rfl, hb⟩ := Realizes.snoc_val .I64 hout
  exact ⟨before, hb, ScalarConst.i64_framed C hC value before⟩

theorem TypedPrefix.f32Const {C : context} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C ops poly vals)
    (hC : wf_context C) (value : U32) :
    TypedPrefix C (ops ++ [ScalarConst.f32 value]) poly (vals ++ [.Val .F32]) := by
  apply h.append hC _ (ScalarConst.f32_wf value)
  intro out hout
  obtain ⟨before, rfl, hb⟩ := Realizes.snoc_val .F32 hout
  exact ⟨before, hb, ScalarConst.f32_framed C hC value before⟩

theorem TypedPrefix.f64Const {C : context} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C ops poly vals)
    (hC : wf_context C) (value : U64) :
    TypedPrefix C (ops ++ [ScalarConst.f64 value]) poly (vals ++ [.Val .F64]) := by
  apply h.append hC _ (ScalarConst.f64_wf value)
  intro out hout
  obtain ⟨before, rfl, hb⟩ := Realizes.snoc_val .F64 hout
  exact ⟨before, hb, ScalarConst.f64_framed C hC value before⟩

end Itasca.Sequence

namespace Itasca
private theorem i64_const_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_I64_CONST v =
      CoreVisitor.run (code.read_i64_const st data) visitor.on_i64_const v := by
  simp [code.step, global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- Lift the handler's totality and successful result through the exact i64_const dispatch and visitor. -/
theorem code.step_i64_const.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : I64 → code.OpIterState → Prop)
    (hread : code.read_i64_const st data ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : ∀ s a, ∃ result v', visitor.on_i64_const v s a = .ok (result, v')) :
    code.step visitor st data env ctx code.OP_I64_CONST v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [i64_const_dispatch]
  exact CoreVisitor.run.spec _ _ v Q P hread hvisitor

private theorem f32_const_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_F32_CONST v =
      CoreVisitor.run (code.read_f32_const st data) visitor.on_f32_const v := by
  simp [code.step, global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- Lift the handler's totality and successful result through the exact f32_const dispatch and visitor. -/
theorem code.step_f32_const.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : U32 → code.OpIterState → Prop)
    (hread : code.read_f32_const st data ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : ∀ s a, ∃ result v', visitor.on_f32_const v s a = .ok (result, v')) :
    code.step visitor st data env ctx code.OP_F32_CONST v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [f32_const_dispatch]
  exact CoreVisitor.run.spec _ _ v Q P hread hvisitor

private theorem f64_const_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_F64_CONST v =
      CoreVisitor.run (code.read_f64_const st data) visitor.on_f64_const v := by
  simp [code.step, global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- Lift the handler's totality and successful result through the exact f64_const dispatch and visitor. -/
theorem code.step_f64_const.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : U64 → code.OpIterState → Prop)
    (hread : code.read_f64_const st data ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : ∀ s a, ∃ result v', visitor.on_f64_const v s a = .ok (result, v')) :
    code.step visitor st data env ctx code.OP_F64_CONST v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [f64_const_dispatch]
  exact CoreVisitor.run.spec _ _ v Q P hread hvisitor


end Itasca
