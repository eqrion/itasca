import Exec.Code.Local.Source.SourceStacks
namespace Exec.Code
open Aeneas Aeneas.Std
open Itasca

private theorem translated_not_bot (ty : types.ValueType) : Translate.valueType ty ≠ valtype.BOT := by
  cases ty <;> simp [Translate.valueType]

/-- A monomorphic realization of concrete validator operands contains no
bottom type. This extracts the needed fact from actual handler postconditions. -/
theorem concrete_realization {values : List code.StackType} {types : List valtype}
    (known : ConcreteStack values) (realized : Sequence.Realizes false values types) :
    valtype.BOT ∉ types := by
  obtain ⟨front, suffix, empty, related, rfl⟩ := realized
  rw [empty rfl, List.nil_append]
  induction related with
  | nil => simp
  | @cons value ty rest types accepted related ih =>
    have here := known value (by simp)
    have tail : ConcreteStack rest := fun v member => known v (by simp [member])
    have head : ty ≠ valtype.BOT := by
      cases value with
      | Bot => exact False.elim (here rfl)
      | Val v =>
        change ty = Translate.valueType v at accepted
        rw [accepted]
        exact translated_not_bot v
    simpa only [List.mem_cons, not_or] using And.intro (Ne.symm head) (ih tail)

theorem stackTypes_concrete {values : List code.StackType}
    (known : valtype.BOT ∉ Sequence.stackTypes values) : ConcreteStack values := by
  intro value member eq
  subst value
  apply known
  exact List.mem_map.mpr ⟨code.StackType.Bot, member, rfl⟩

/-- Handler stack-transfer contracts preserve concrete remainders on live
paths. The premise comes from the actual reader's accepted equation. -/
theorem concrete_stack_transfer {before after : List code.StackType} {inputs : List valtype}
    (known : ConcreteStack before)
    (transfer : ∀ types, Sequence.Realizes false after types →
      Sequence.Realizes false before (types ++ inputs)) : ConcreteStack after := by
  apply stackTypes_concrete
  have noBot := concrete_realization known
    (transfer _ (Sequence.realizes_default false after))
  exact fun member => noBot (List.mem_append_left _ member)

/-- Select's returned type and remaining operands are concrete whenever its
accepted semantic effect starts from a concrete monomorphic segment. -/
theorem concrete_select_effect {before after : List code.StackType} {selected : code.StackType}
    (known : ConcreteStack before)
    (effect : StackSemantics.SelectEffect false before selected after) :
    ConcreteStack after ∧ selected ≠ .Bot := by
  obtain ⟨selectable, rest, rfl, transfer⟩ := effect
  have restKnown := concrete_stack_transfer known transfer
  have noBot := concrete_realization known (transfer _ (Sequence.realizes_default false rest))
  have selectedKnown : selected ≠ .Bot := by
    intro eq
    subst selected
    simp [StackSemantics.selectedType] at noBot
  exact ⟨concreteStack_append.mpr ⟨restKnown, by simpa [ConcreteStack] using selectedKnown⟩, selectedKnown⟩
theorem concrete_numeric_effect {before after : List code.StackType} {inputs output}
    (known : ConcreteStack before)
    (effect : StackSemantics.NumericEffect false before inputs output after) :
    ConcreteStack after := by
  obtain ⟨rest, rfl, transfer⟩ := effect
  exact concreteStack_append.mpr ⟨concrete_stack_transfer known transfer, by simp [ConcreteStack]⟩

theorem concrete_popped {before after : List code.StackType} {value}
    (known : ConcreteStack before) (popped : StackSemantics.Popped false before value after) :
    ConcreteStack after ∧ value ≠ .Bot := by
  cases popped with
  | explicit =>
    obtain ⟨tail, head⟩ := concreteStack_append.mp known
    exact ⟨tail, head _ (by simp)⟩

/-- Accepted numeric readers preserve the exact live concrete stack; this
covers every scalar opcode through its canonical numeric dispatch table. -/
theorem numeric_read_concrete (op : Numeric.Operation) (st out : code.OpIterState)
    (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length)
    (size : st.vals.val.length < Usize.max)
    (known : ConcreteStack st.vals.val) (live : Control.polymorphic st = false)
    (accepted : Numeric.read op st = .ok (.Ok (), out)) :
    ConcreteStack out.vals.val ∧ out.ctrls = st.ctrls ∧ out.pos = st.pos := by
  have effect := Numeric.read.segment op st outer segment values base size
  rw [accepted, WP.spec_ok] at effect
  obtain ⟨controls, position, after, resultValues, length, numeric⟩ := effect
  rw [live] at numeric
  rw [values] at known
  obtain ⟨outerKnown, segmentKnown⟩ := concreteStack_append.mp known
  refine ⟨?_, controls, position⟩
  rw [resultValues]
  exact concreteStack_append.mpr ⟨outerKnown, concrete_numeric_effect segmentKnown numeric⟩

/-- An accepted untyped select cannot introduce a bottom operand in a live
concrete stack, even though the generic validator also supports dead stacks. -/
theorem select_read_concrete (st out : code.OpIterState) (selected : code.StackType)
    (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length)
    (size : st.vals.val.length < Usize.max)
    (known : ConcreteStack st.vals.val) (live : Control.polymorphic st = false)
    (accepted : code.read_select st = .ok (.Ok selected, out)) :
    ConcreteStack out.vals.val ∧ selected ≠ .Bot ∧ out.ctrls = st.ctrls ∧ out.pos = st.pos := by
  have effect := code.read_select.segment st outer segment values base size
  rw [accepted, WP.spec_ok] at effect
  obtain ⟨controls, position, after, resultValues, length, selectedEffect⟩ := effect
  rw [live] at selectedEffect
  rw [values] at known
  obtain ⟨outerKnown, segmentKnown⟩ := concreteStack_append.mp known
  obtain ⟨afterKnown, selectedKnown⟩ := concrete_select_effect segmentKnown selectedEffect
  refine ⟨?_, selectedKnown, controls, position⟩
  rw [resultValues]
  exact concreteStack_append.mpr ⟨outerKnown, afterKnown⟩
end Exec.Code
