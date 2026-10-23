import Itasca.Wasm2.ResultStackSemantics

/-!
# Operand suffix compatibility

The non-destructive operand check that `br_table` applies to each target. `Wasm2.Fits`
and `Wasm2.Suffix` independently specify that the top of an operand stack is compatible with a
signature, `code.check_suffix_loop.spec` is the exact contract of the extracted loop, and
`code.check_suffix.spec` and `.complete` give soundness, totality and completeness of
`code.check_suffix`.
-/

open Aeneas Aeneas.Std

set_option maxRecDepth 2048

namespace Itasca.Wasm2

/-- Compatibility from the top of an operand stack downwards. Each target is
compared to the original operands; a `Bot` is never specialized to one target. -/
def Fits : Bool → List code.StackType → List types.ValueType → Prop
  | _, _, [] => True
  | poly, [], _ :: _ => poly = true
  | poly, v :: vs, t :: ts =>
      Sequence.Accepts v (Translate.valueType t) ∧ Fits poly vs ts

@[simp] theorem Fits.nil (poly : Bool) (vs : List code.StackType) : Fits poly vs [] := by
  cases vs <;> trivial

@[simp] theorem Fits.unreachable (ts : List types.ValueType) : Fits true [] ts := by
  cases ts <;> trivial

/-- Independent compatibility of a signature with the current operand suffix. -/
def Suffix (st : code.OpIterState) (ts : List types.ValueType) : Prop :=
  Fits (Control.polymorphic st)
    (st.vals.val.drop (Control.base st).val).reverse ts.reverse

end Itasca.Wasm2

namespace Itasca

/-- Exact loop contract: rejection is equivalent to incompatibility of the
remaining signature with the unchanged stack slice. -/
theorem code.check_suffix_loop.spec (st : code.OpIterState) (env : module.Env)
    (view : signature.ResultType) (ts : List types.ValueType)
    (hts : Wasm2.resolve env view = some ts) (stack i : Usize)
    (hb : (Control.base st).val ≤ stack.val) (hs : stack.val ≤ st.vals.val.length)
    (hi : i.val ≤ ts.length) :
    code.check_suffix_loop st.vals st.ctrls st.pos env view (Control.base st) stack i ⦃ r =>
      r = .Ok () ↔ Wasm2.Fits (Control.polymorphic st)
        ((st.vals.val.take stack.val).drop (Control.base st).val).reverse
        (ts.take i.val).reverse ⦄ := by
  unfold code.check_suffix_loop
  apply loop.spec_decr_nat (fun p => p.2.val)
    (fun p => (Control.base st).val ≤ p.1.val ∧ p.1.val ≤ st.vals.val.length ∧
      p.2.val ≤ ts.length ∧
      (Wasm2.Fits (Control.polymorphic st)
          ((st.vals.val.take stack.val).drop (Control.base st).val).reverse
          (ts.take i.val).reverse ↔
        Wasm2.Fits (Control.polymorphic st)
          ((st.vals.val.take p.1.val).drop (Control.base st).val).reverse
          (ts.take p.2.val).reverse))
  · rintro ⟨s, j⟩ ⟨hb', hs', hj, he⟩
    dsimp only at hb' hs' hj he
    unfold code.check_suffix_loop.body
    dsimp only
    split
    · rename_i hz
      simpa [hz] using he.symm
    · rename_i hnz
      step
      have hj' : i2.val < ts.length := by omega
      have hjstep : j.val = i2.val + 1 := by omega
      have ht : (ts.take j.val).reverse = ts[i2.val] :: (ts.take i2.val).reverse := by
        rw [hjstep, List.take_succ_eq_append_getElem hj']
        simp
      rw [signature.ResultType.get.complete view env ts hts i2]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        List.getElem?_eq_getElem hj']
      split
      · rename_i hbase
        have hempty : ((st.vals.val.take s.val).drop (Control.base st).val).reverse = [] := by
          rw [hbase]
          simp
        step with code.cur_polymorphic.spec st
        subst b
        split
        · rename_i hpoly
          simp only [WP.spec_ok]
          refine ⟨hb', hs', by omega, ?_, by omega⟩
          simpa [hempty, ht, hpoly, Wasm2.Fits] using he
        · rename_i hpoly
          simp only [WP.spec_ok]
          simpa [hempty, ht, Wasm2.Fits, hpoly] using he.symm
      · rename_i hbase
        have hbne : s.val ≠ (Control.base st).val := fun h => hbase (UScalar.eq_of_val_eq h)
        step
        have hidx : stack1.val < st.vals.val.length := by omega
        have hbstep : (Control.base st).val ≤ stack1.val := by omega
        have hsstep : s.val = stack1.val + 1 := by omega
        have hv : ((st.vals.val.take s.val).drop (Control.base st).val).reverse =
            st.vals.val[stack1.val] ::
              ((st.vals.val.take stack1.val).drop (Control.base st).val).reverse := by
          rw [hsstep, List.take_succ_eq_append_getElem hidx,
            List.drop_append_of_le_length (by simp; omega)]
          simp
        step as ⟨operand, hop⟩
        rw [hop]
        clear hop
        split
        · rename_i actual hactual
          step with core.cmp.PartialEq.ne.trait_default.spec
            types.ValueType.Insts.CoreCmpPartialEqValueType _ _ (types.ValueType.eq_spec _ _)
            as ⟨different, hdifferent⟩
          split
          · rename_i hne
            have hbad : Translate.valueType actual ≠ Translate.valueType ts[i2.val] :=
              fun h => (hdifferent.mp hne) (Translate.valueType_injective h)
            simp only [WP.spec_ok]
            simpa [hv, ht, hactual, Wasm2.Fits, Sequence.Accepts, eq_comm, hbad] using he.symm
          · rename_i heq
            have hequal : actual = ts[i2.val] := by simpa [heq] using hdifferent
            simp only [WP.spec_ok]
            refine ⟨hbstep, by omega, by omega, ?_, by omega⟩
            simpa [hv, ht, hactual, Wasm2.Fits, Sequence.Accepts, eq_comm, hequal] using he
        · rename_i hbot
          simp only [WP.spec_ok]
          refine ⟨hbstep, by omega, by omega, ?_, by omega⟩
          simpa [hv, ht, hbot, Wasm2.Fits, Sequence.Accepts] using he
  · exact ⟨hb, hs, hi, Iff.rfl⟩

/-- The actual non-destructive suffix checker is total, sound, and complete
for the independently specified operand compatibility relation. -/
theorem code.check_suffix.spec (st : code.OpIterState) (env : module.Env)
    (view : signature.ResultType) (hshape : Control.Shape st) :
    code.check_suffix st env view ⦃ r =>
      r = .Ok () ↔ ∃ ts, Wasm2.resolve env view = some ts ∧ Wasm2.Suffix st ts ⦄ := by
  unfold code.check_suffix
  step with code.cur_base.spec st
  subst base
  obtain ⟨r, hr, ht⟩ := WP.spec_imp_exists (signature.ResultType.len.spec view env)
  rw [hr]
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ht.2]
  | Ok n =>
    obtain ⟨ts, hts, hn⟩ := ht
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply WP.spec_mono (code.check_suffix_loop.spec st env view ts hts
      (alloc.vec.Vec.len st.vals) n hshape.base_le (by simp) (by omega))
    intro res hs
    simpa [hts, hn, Wasm2.Suffix] using hs

end Itasca
