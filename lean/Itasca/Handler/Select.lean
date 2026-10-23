import Itasca.Handler.SimplePrefix
import Itasca.Visitor.Total

/-!
# Select handler

Lemmas about the extracted untyped `select`: `code.join_stack_type.spec`, the effect predicate
`StackSemantics.SelectEffect`, and `code.read_select.segment` for the operand segment.
`StackSemantics.selectedType_typed` types the selected operand, which accepts numeric and bottom
operands and rejects references.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- `code.join_stack_type` terminates, and every type accepting a successful join is accepted by
both operands. A failure is `TypeMismatch`. -/
theorem code.join_stack_type.spec (a b : code.StackType) :
    code.join_stack_type a b ⦃ r => match r with
      | .Ok t => ∀ u, Sequence.Accepts t u → Sequence.Accepts a u ∧ Sequence.Accepts b u
      | .Err e => e = .TypeMismatch ⦄ := by
  cases a with
  | Bot => simp [code.join_stack_type, Sequence.Accepts]
  | Val a =>
    cases b with
    | Bot => simp [code.join_stack_type, Sequence.Accepts]
    | Val b =>
      cases a <;> cases b <;>
        simp [code.join_stack_type, types.ValueType.Insts.CoreCmpPartialEqValueType.eq,
          Sequence.Accepts]

namespace StackSemantics

/-- Whether a stack type is allowed for an untyped `select`: numeric and vector values and `Bot`,
but no reference types. -/
def Selectable : code.StackType → Prop
  | .Val .FuncRef | .Val .ExternRef => False
  | _ => True

instance (t : code.StackType) : Decidable (Selectable t) := by
  cases t with
  | Bot => exact isTrue trivial
  | Val t =>
    cases t with
    | I32 | I64 | F32 | F64 | V128 => exact isTrue trivial
    | FuncRef | ExternRef => exact isFalse (fun h => h)

/-- An operand accepted at a non-reference type is selectable. -/
theorem Selectable.of_accepts {t : code.StackType} {u : valtype}
    (ha : Sequence.Accepts t u) (hf : u ≠ .FUNCREF) (he : u ≠ .EXTERNREF) :
    Selectable t := by
  cases t with
  | Bot => trivial
  | Val t =>
    cases t <;> simp_all [Selectable, Sequence.Accepts, Translate.valueType]

/-- A subtype of a numeric or vector type is not a reference type. -/
theorem select_type_not_reference {t t' : valtype} {nt : numtype} {vt : vectype}
    (hsub : Valtype_sub t t')
    (ht : t' = valtype_numtype nt ∨ t' = valtype_vectype vt) :
    t ≠ .FUNCREF ∧ t ≠ .EXTERNREF := by
  cases hsub with
  | bot => simp
  | refl =>
    rcases ht with rfl | rfl
    · cases nt <;> simp [valtype_numtype]
    · cases vt
      simp [valtype_vectype]

/-- The SpecTec type a select operand is read at, with `Bot` as `BOT`. -/
def selectedType : code.StackType → valtype
  | .Val t => Translate.valueType t
  | .Bot => .BOT

/-- An operand accepts its own `selectedType`. -/
theorem selectedType_accepts (t : code.StackType) : Sequence.Accepts t (selectedType t) := by
  cases t <;> simp [selectedType, Sequence.Accepts]

/-- `selectedType` is a subtype of every type the operand accepts. -/
theorem selectedType_sub {t : code.StackType} {u : valtype} (h : Sequence.Accepts t u) :
    Valtype_sub (selectedType t) u := by
  cases t with
  | Bot => exact .bot u
  | Val t => change u = Translate.valueType t at h; subst u; exact .refl _

/-- Untyped `select` is typed at a selectable operand type, including a bottom operand that can
later be subsumed. -/
theorem selectedType_typed (C : context) (hC : wf_context C) (t : code.StackType) (hs : Selectable t) :
    Instr_ok C (.SELECT none)
      (.mk_functype (.mk_list [selectedType t, selectedType t, .I32])
        (.mk_list [selectedType t])) := by
  cases t with
  | Bot => exact .select_impl C .BOT .I32 .I32 .V128 (.bot _) (.inl rfl) hC (.instr_case_3 _)
  | Val t =>
    cases t with
    | I32 => exact .select_impl C _ _ .I32 .V128 (.refl _) (.inl rfl) hC (.instr_case_3 _)
    | I64 => exact .select_impl C _ _ .I64 .V128 (.refl _) (.inl rfl) hC (.instr_case_3 _)
    | F32 => exact .select_impl C _ _ .F32 .V128 (.refl _) (.inl rfl) hC (.instr_case_3 _)
    | F64 => exact .select_impl C _ _ .F64 .V128 (.refl _) (.inl rfl) hC (.instr_case_3 _)
    | V128 => exact .select_impl C _ _ .I32 .V128 (.refl _) (.inr rfl) hC (.instr_case_3 _)
    | FuncRef | ExternRef => exact False.elim hs

/-- The effect of an untyped `select`: the result `t` is selectable, and a stack realizing the
remainder extends to one with two operands of type `t` and an `i32` condition. -/
def SelectEffect (poly : Bool) (before : List code.StackType) (t : code.StackType)
    (after : List code.StackType) : Prop :=
  Selectable t ∧ ∃ rest, after = rest ++ [t] ∧ ∀ ts, Sequence.Realizes poly rest ts →
    Sequence.Realizes poly before (ts ++ [selectedType t, selectedType t, .I32])

end StackSemantics

/-- `code.is_select_type` decides `Selectable`. -/
@[simp] theorem code.is_select_type.eq (t : code.StackType) :
    code.is_select_type t = .ok (decide (StackSemantics.Selectable t)) := by
  cases t with
  | Bot => rfl
  | Val t => cases t <;> rfl

/-- `code.read_select` on the current frame's operand segment terminates, including all `Bot`
combinations, with a `SelectEffect` outcome or `EmptyStack` or `TypeMismatch`. -/
theorem code.read_select.segment (st : code.OpIterState)
    (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_select st ⦃ r =>
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ after, r.2.vals.val = outer ++ after ∧ after.length ≤ segment.length + 1 ∧
        match r.1 with
        | .Ok t => StackSemantics.SelectEffect (Control.polymorphic st) segment t after
        | .Err e => e = .EmptyStack ∨ e = .TypeMismatch ⦄ := by
  obtain ⟨⟨cond, s1⟩, hr1, hc1, hp1, rest1, hv1, hl1, ho1⟩ :=
    WP.spec_imp_exists (code.pop_with_type.realizes st outer segment .I32 hvals hbase)
  dsimp only at hc1 hp1 hv1 hl1 ho1
  cases cond with
  | Err e =>
    rw [WP.spec_equiv_exists]
    refine ⟨(.Err e, s1), ?_, hc1, hp1, rest1, hv1, by omega, ho1⟩
    simp [code.read_select, hr1, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok tc =>
    have hb1 : (Control.base s1).val = outer.length := by simpa [Control.base, hc1] using hbase
    have hpoly1 : Control.polymorphic s1 = Control.polymorphic st := by simp [Control.polymorphic, hc1]
    obtain ⟨⟨val2, s2⟩, hr2, hc2, hp2, rest2, hv2, ho2⟩ :=
      WP.spec_imp_exists (code.pop_stack_type.segment s1 outer rest1 hv1 hb1)
    dsimp only at hc2 hp2 hv2 ho2
    rw [hpoly1] at ho2
    have hl2 := ho2.length
    cases val2 with
    | Err e =>
      rw [WP.spec_equiv_exists]
      refine ⟨(.Err e, s2), ?_, hc2.trans hc1, hp2.trans hp1, rest2, hv2, by omega, .inl ho2.1⟩
      simp [code.read_select, hr1, hr2, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok t2 =>
      have hb2 : (Control.base s2).val = outer.length := by simpa [Control.base, hc2] using hb1
      have hpoly2 : Control.polymorphic s2 = Control.polymorphic st := by
        simpa [Control.polymorphic, hc2] using hpoly1
      obtain ⟨⟨val1, s3⟩, hr3, hc3, hp3, rest3, hv3, ho3⟩ :=
        WP.spec_imp_exists (code.pop_stack_type.segment s2 outer rest2 hv2 hb2)
      dsimp only at hc3 hp3 hv3 ho3
      rw [hpoly2] at ho3
      have hl3 := ho3.length
      cases val1 with
      | Err e =>
        rw [WP.spec_equiv_exists]
        refine ⟨(.Err e, s3), ?_, hc3.trans (hc2.trans hc1), hp3.trans (hp2.trans hp1),
          rest3, hv3, by omega, .inl ho3.1⟩
        simp [code.read_select, hr1, hr2, hr3, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok t1 =>
        obtain ⟨joined, hj, hjoin⟩ := WP.spec_imp_exists (code.join_stack_type.spec t2 t1)
        cases joined with
        | Err e =>
          rw [WP.spec_equiv_exists]
          refine ⟨(.Err e, s3), ?_, hc3.trans (hc2.trans hc1), hp3.trans (hp2.trans hp1),
            rest3, hv3, by omega, .inr hjoin⟩
          simp [code.read_select, hr1, hr2, hr3, hj, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok t =>
          by_cases hselect : StackSemantics.Selectable t
          · have hcap : s3.vals.val.length < Usize.max := by
              simp only [hvals, List.length_append] at hsize
              simp only [hv3, List.length_append]
              omega
            obtain ⟨s4, hr4, hv4, hc4, hp4⟩ :=
              WP.spec_imp_exists (code.push_val.spec s3 t hcap)
            rw [WP.spec_equiv_exists]
            refine ⟨(.Ok t, s4), ?_, hc4.trans (hc3.trans (hc2.trans hc1)),
              hp4.trans (hp3.trans (hp2.trans hp1)), rest3 ++ [t], ?_, ?_, hselect, rest3, rfl, ?_⟩
            · simp [code.read_select, hr1, hr2, hr3, hj, hr4, code.is_select_type.eq, hselect, core.result.Result.Insts.CoreOpsTry.branch]
            · simpa [List.append_assoc, hv3] using hv4
            · simp only [List.length_append, List.length_singleton]; omega
            · intro ts hs
              obtain ⟨ht2, ht1⟩ := hjoin _ (StackSemantics.selectedType_accepts t)
              simpa [List.append_assoc, Translate.valueType] using
                ho1.2 _ (ho2.realizes _ _ ht2 (ho3.realizes ts _ ht1 hs))
          · rw [WP.spec_equiv_exists]
            refine ⟨(.Err .TypeMismatch, s3), ?_, hc3.trans (hc2.trans hc1),
              hp3.trans (hp2.trans hp1), rest3, hv3, by omega, .inr rfl⟩
            simp [code.read_select, hr1, hr2, hr3, hj, code.is_select_type.eq, hselect,
              core.result.Result.Insts.CoreOpsTry.branch]

/-- `code.step` on `select` runs `code.read_select` and then the visitor's `on_select` hook. -/
theorem code.step_select.dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_SELECT v =
      CoreVisitor.run (code.read_select st) visitor.on_select v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

end Itasca
